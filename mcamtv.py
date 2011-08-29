#!/usr/bin/env python
"""\
Majority Choice Approval (M) Transferable Vote, a PR extension of
the ER-Bucklin(whole) single-winner method to multi-winner elections.
Copyright (C) 2011,  Louis G. "Ted" Stern

This code is an independently reimplemented simplification of Jameson
Quinn's PR-MCA, AKA Approval Threshold Transferable Vote (AT-TV), to
which he retains copyright.

http://www.mail-archive.com/election-methods@lists.electorama.com/msg07066.html
Copyright (C) 2011, Jameson Quinn

The main difference is that my version is straight ER-Bucklin, while
JQ selects, from among those whose rescaled Bucklin score exceeds the
quota, the candidate whose Range score (with a different weighting) is
greatest.

Other minor differences from AT-TV:

* I use a different Droop quota that is slightly larger than N/(M+1).
* I calculate the Bucklin rescaling factor using locked vote sums to minimize
  vote loss

For more information, see the README for this project.
"""
# For faster reverse sorting (in 2.4+):
from operator import itemgetter
from textwrap import fill, dedent
import re, os, sys

# Default maximum range/score
DEFAULT_MAX_SCORE = 5

DEFAULT_N_SCORE = DEFAULT_MAX_SCORE + 1

# Default number of seats in a multi-winner election
DEFAULT_NSEATS = 7

# Utility function to sort a dictionary in reverse order of values
def reverse_sort_dict(d):
    return sorted(d.iteritems(), key=itemgetter(1), reverse=True)

# shared dict of constants for different quota types
qconst = {'hare':0.0, 'droop':1.0}

# Set up for Hare or Droop quotas:
def calc_quota(n, nseats=DEFAULT_NSEATS, qtype='droop'):

    # Hare quota = Nvotes / Nseats
    # Droop quota = modified version of int(Nvotes / (Nseats + 1)) + 1
    #
    # Calculate Droop quota using the usual Cumulative Voting style in
    # which each voter gets Nseats votes:
    #
    #  multiply number of voters * number of seats,
    #    (this is like standard CV giving each voter "nseats" votes)
    #  divide by [<number of seats> + one]
    #  round down to nearest integer
    #  add one
    #  Finally, divide by nseats to get fraction of original votes.
    #
    #  With Droop, it is like rounding up from Nvotes/(Nseats+1) to the
    #  nearest 1/nseats of a vote.
    #
    #  By using qconst[qtype], this formula works for Hare also.
    return (float(int(float(n*nseats)/
                      (float(nseats)+qconst[qtype])))+qconst[qtype]
            )/float(nseats)

class Ballot(dict):
    def __init__(self,csv_string='',cand_list=[]):
        # Parse the csv_string
        scores = []
        for i, v in enumerate(csv_string.rstrip().split(',')):
            if v:
                intv = int(v)
                if intv:
                    scores.append((cand_list[i],intv))
        # Now initialize with the list of 2-tuples
        dict.__init__(self,scores)

        self.rescale = 1.0

class Election(object):

    def __init__(self,
                 ballots=[],
                 candidates=set([]),
                 csv_input=None,
                 csv_output=None,
                 qtype='droop',
                 max_score=DEFAULT_MAX_SCORE,
                 nseats=DEFAULT_NSEATS,
                 range_style=0):
        "Initialize from a list of ballots or a CSV input file"

        # Number of seats to fill:
        self.nseats = nseats

        # Quota type
        self.qtype = qtype
        if qtype not in qconst.keys():
            print "Error, qtype not recognized"
            sys.exit(1)

        # ------------------------------------------------------------
        # Absorb ballots, from input list and/or from file or stdin

        if ballots:
            self.ballots = ballots
        else:
            self.ballots = []

        self.candidates = candidates
        if csv_input:
            if csv_input == '-':
                self.csv_ballots(stdin=True)
            else:
                self.csv_ballots(filename=csv_input)

        # Initialize lists and sets of candidates:

        self.seated = set([])
        self.ordered_seated = []
        self.standing = self.candidates
        self.ordered_candidates=sorted(self.candidates)

        # Maximum Bucklin score:
        self.max_score = max_score
        self.threshold = max_score
        self.n_score = self.max_score + 1

        if csv_output:
            if csv_output == '-':
                self.csv_output = sys.stdout
            else:
                self.csv_output = open(csv_output, 'w')

        # Count the number of votes
        self.nvotes = len(self.ballots)

        # Calculate quota
        self.quota = calc_quota(self.nvotes,
                                self.nseats,
                                qtype=self.qtype)

        # Set up initial line of CSV output file:
        # Format is
        #
        # | Cand1 | Cand2 | ... | CandX | Winner name
        # +-------+-------+-----+-------+------------
        # |       |       |     |       |

        quota_string = "%s quota = %g out of %g\n" % \
            ( self.qtype.capitalize(),
              self.quota,
              self.nvotes )

        self.csv_lines = [','.join(self.ordered_candidates + [quota_string])]


        return

    def csv_ballots(self,
                    filename=None,
                    stdin=False):
        "Read ballots from a csv file.  First line is names of candidates."
        if stdin:
            f = sys.stdin
        else:
            f = open(filename,'r')

        # List of candidate names in the first line:
        keys = f.readline().rstrip().split(',')
        self.candidates.update(set(keys))

        # Following lines are the ballots:
        for line in f:
            ballot = Ballot(line,keys)

            # If the ballot is non-empty, append the ballot
            # to the list of ballots
            if len(ballot):
                self.ballots.append(ballot)

        if not stdin:
            f.close()
        return

    def compute_totals(self, factor=1.0, winner=None):
        """\
Loop over ballots.

As part of ballot loop, adjust rescale factor if ballot had the winner at
a score over the threshold.

Check whether ballot has any standing candidates.

If so, accumulate totals and locksums at each score level for each
standing candidate, and keep track of weighted total vote.
"""

        totals = [dict([(c,0.0) for c in self.standing])]
        locksums = [dict([(c,0.0) for c in self.standing])]
        total_vote = 0.0

        # Initialize dicts for each rating level.  We already
        # initialized above for score==0, but it is never used.
        for i in xrange(self.max_score):
            totals.append(dict([(c,0.0) for c in self.standing]))
            locksums.append(dict([(c,0.0) for c in self.standing]))

        # In a single loop over the ballots, we
        #
        # a) Rescale the ballot using the factor from the previous winner,
        #    if applicable (i.e. if this is not the first total calculation).
        #
        # b) Accumulate totals and locksums for each score level using
        #    the current rescale factor (after change above).
        #
        # "total_vote" is not used, but is accumulated as a check against
        # vote count.
        #
        for ballot in self.ballots:
            # Rescale ballot using factor from previous winner
            if winner:
                if ballot.has_key(winner):
                    if ballot[winner] >= self.threshold:
                        ballot.rescale *= factor

            rescale = ballot.rescale
            if rescale > 0.0:
                standing = set(ballot.keys()) & self.standing
                n = len(standing)
                if n > 0:
                    total_vote += rescale
                    for c in standing:
                        score = ballot[c]
                        totals[score][c] += rescale
                        if n == 1:
                            locksums[score][c] += rescale

        return totals, locksums, total_vote

# For keeping track of running totals in a Comma Separated Variable file
# that could be imported into a spreadsheet ...
    def print_running_total(self, threshold, ordered_scores):
        """Print CSV line of running total"""

        csv_line = ""

        # This creates a "<formatted score> (<position>)" label for
        # each standing candidate.
        labels = {}
        for i, pair in enumerate(ordered_scores):
            c, score = pair
            labels[c] = "%15.5f (%d)" % (score, i+1)

        # And this prints out the appropriate label for all
        # standing candidates.

        return ','.join([labels.get(c,'')
                         for c in self.ordered_candidates])

    def bucklin_score(self, totals, locksums):
        """\
Return Bucklin winner, Bucklin score and winner's locksum, adjusting the
threshold if necessary."""

        # Candidates we're calculating totals for:
        standing = totals[1].keys()

        # Initial bucklin scores for each candidate:
        total = dict([(c,0.0) for c in standing])
        locksum = dict([(c,0.0) for c in standing])

        threshold = self.max_score
        while self.threshold > 0:
            while threshold >= self.threshold:
                for c in standing:
                    total[c] += totals[threshold][c]
                    locksum[c] += locksums[threshold][c]

                ordered_scores = reverse_sort_dict(total)

                (winner, win_score) = ordered_scores[0]
                lockval = locksum[winner]

                csv_line = self.print_running_total(threshold, ordered_scores)
                if ((win_score >= self.quota) or
                    ((threshold == self.threshold) and
                     (self.threshold == 1))):
                    csv_line += ",Approval Level = %d; Seating %s; Locksum = %.5g\n" % (threshold, winner, lockval)
                    self.csv_lines.append(csv_line)
                    return winner, win_score, lockval
                else:
                    csv_line += ",Approval Level = %d; Quota not reached\n" % threshold
                    self.csv_lines.append(csv_line)

                threshold -= 1

            self.threshold -= 1
            print "Dropping approval threshold level to ", self.threshold

        return winner, win_score, lockval

    def run_election(self,
                     verbose=True,
                     debug=False,
                     terse=False):
        "Run the election."

        # make output extremely terse, if selected
        if terse:
            verbose = False

        if debug:
            verbose = True
            terse = False

        # Initiale rescaling factor and winner
        factor = 1.0
        winner = None
        eps = 1.e-9
        n_seated = len(self.seated)
        n_needed = self.nseats - n_seated
        n_standing = len(self.standing)
        fallback = 0

        vote_count = float(self.nvotes)

        # Main loop:
        for i in xrange(self.nseats):

            # Calculate weighted totals and locksums.
            #
            # To avoid multiple loops through the ballots,
            # the rescaling for the previous winner's
            # rescale factor is done in the same loop.
            #
            # NB: Since we're rescaling ballots from the previous
            # iteration, total_votes is returned as the total number of
            # rescaled ballots before removing the new winner.
            #
            totals, locksums, total_vote = self.compute_totals(factor,
                                                               winner=winner)
            if not terse:
                print "total_vote = ", total_vote
                print "vote_count = ", vote_count

            # Given the totals and locksums for each approval level,
            # get the Bucklin winner, winner's Bucklin score and Locksum
            (winner,
             win_score,
             locksum) = self.bucklin_score(totals, locksums)

            factor = min( max(win_score - self.quota, 0.0)/
                          max(win_score - locksum,eps),
                          1.0 )

            vote_count -= min(max(locksum, self.quota),win_score)

            self.seated.add(winner)
            self.ordered_seated.append(winner)
            self.standing.remove(winner)

            n_seated += 1
            n_needed -= 1
            n_standing -= 1

            if not terse:
                print "Candidate %s seated in position %i" % ( winner,
                                                               n_seated), \
                    ", Bucklin score = %.5g" % win_score, \
                    ", Approval Threshold =", self.threshold, \
                    ", Quota = %.5g" % self.quota, \
                    ", Locksum = %.5g" % locksum, \
                    ", Rescale factor = %.5g" % factor
                print ""

        # Write CSV output
        self.csv_output.writelines(self.csv_lines)

        print "Winning set in order seated =",
        print "{" + ','.join([self.ordered_seated[i]
                              for i in range(self.nseats)]) + "}"

        print "Leftover vote =", vote_count
        return

if __name__ == "__main__":
    from optparse import OptionParser

    usage="""%prog \\
            [-n|--nseats NSEATS] \\
            [-q|--quota-type QTYPE] \\
            [-i|--csv-input INPUT_FILENAME.csv] \\
            [-o|--csv-output OUTPUT_FILENAME.csv] \\
            [-v|--verbose] \\
            [-D|--debug]

%prog is a script to run Majority Choice Approval (M) Transferable Voting
(MCAMTV), AKA ER-Bucklin(whole), to implement a Proportional
Representation (PR) election, using a set of tabulated ballots with
ratings for each candidate.

The Comma Separated Variable format is assumed to be in the form

	name1,name2,name3,...
        ,,,,,9,,,6,,7,,,2,...
        ,,9,8,7,6,1,2,0,...

with the list of candidates on the first line, and non-zero scores
for the respective candidates as ballots on following lines.
"""
    version = "Version: %prog 0.1"

    parser = OptionParser(usage=usage, version=version)

    parser.add_option('-n',
                      '--nseats',
                      type=int,
                      default=7,
                      help=fill(dedent("""\
                      Number of winning seats for election.  [Default: 7]""")))

    parser.add_option('-m',
                      '--max-score',
                      type=int,
                      default=5,
                      help=fill(dedent("""\
                      Maximum score.  [Default: %d]""" % DEFAULT_MAX_SCORE )))

    parser.add_option('-q',
                      '--quota-type',
                      type='string',
                      default='droop',
                      help=fill(dedent("""\
                      Quota type used in election.  'hare' = Hare =
                      Number of ballots divided by number of seats.
                      'droop' = Droop = approximately Nballots /
                      (Nseats + 1), adjusted slightly.  [Default:
                      droop]""")))

    parser.add_option('-i',
                      '--csv-input',
                      type='string',
                      default='-',
                      help=fill(dedent("""\
                      Filename of comma-separated-variable (csv) file
                      containing ballots.  Use hyphen ('-') to take
                      input from stdin.  [Default: -]""")))

    parser.add_option('-o',
                      '--csv-output',
                      type='string',
                      default='-',
                      help=fill(dedent("""\
                      Filename of comma-separated-variable (csv) file
                      to receive table of election results.
                      '.csv' extension can be included, but it will
                      be added if not present.
                      Use hyphen ('-') to direct output to stdout.
                      [Default: -]""")))

    parser.add_option('-v',
                      '--verbose',
                      action='store_true',
                      default=False,
                      help="Turn on verbose mode printout.  [Default:  False]")

    parser.add_option('-t',
                      '--terse',
                      action='store_true',
                      default=False,
                      help="Make printout even less verbose.  [Default:  False]")

    parser.add_option('-D',
                      '--debug',
                      action='store_true',
                      default=False,
                      help="Turn on debug mode printout.  [Default:  False]")

    opts, args = parser.parse_args()

    if not re.match(r"hare|droop",opts.quota_type):
        print "\nError, argument to --quota-type can be only 'hare' or 'droop'\n"
        parser.print_help()
        sys.exit(1)

    if (opts.nseats < 1):
        print "\nError, --nseats argument must be a positive integer\n"
        parser.print_help()
        sys.exit(1)

    if (opts.csv_input == "-"):
        print "Reading CSV input from stdin\n\n"
    else:
        if not os.path.isfile(opts.csv_input):
            print "\nError, %s file does not exist\n" % opts.csv_input
            parser.print_help()
            sys.exit(1)

        ext = os.path.splitext(opts.csv_input)[1]

        if ((ext != '.csv') and (ext != '.CSV')):
            print "\nError, %s file does not have .csv or .CSV extension\n" % opts.csv_input
            parser.print_help()
            sys.exit(1)

    if (opts.csv_output == "-"):
        print "Writing CSV input to stdout\n\n"
    else:

        ext = os.path.splitext(opts.csv_output)[1]

        if not ext:
            csv_output = opts.csv_output + '.csv'

        else:

            if ((ext != '.csv') and (ext != '.CSV')):
                print "\nError, %s CSV output file does not have .csv or .CSV extension\n" % opts.csv_output
                parser.print_help()
                sys.exit(1)

            csv_output = opts.csv_output

    election = Election(nseats=opts.nseats,
                        max_score=opts.max_score,
                        csv_input=opts.csv_input,
                        csv_output=csv_output,
                        qtype=opts.quota_type)

    election.run_election(verbose=opts.verbose,
                          terse=opts.terse,
                          debug=opts.debug)
