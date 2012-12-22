#!/usr/bin/env python
"""\
Graded Approval Transferable Vote, a PR extension of
the ER-Bucklin(whole) single-winner method to multi-winner elections.
Copyright (C) 2011,  Louis G. "Ted" Stern

This code is an independently reimplemented simplification of Jameson
Quinn's PR-MCA, AKA Approval Threshold Transferable Vote (AT-TV), to
which he retains copyright.

http://www.mail-archive.com/election-methods@lists.electorama.com/msg07066.html
Copyright (C) 2011, Jameson Quinn

The main difference is that my version is simple ER-Bucklin, while
JQ selects, from among those whose rescaled Bucklin score exceeds the
quota, the candidate whose Range score (with a different weighting) is
greatest.

Other minor differences from AT-TV:

* I use a different Droop quota that is slightly larger than N/(M+1).
* I calculate the Bucklin rescaling factor using truncated vote sums
  to minimize vote loss

For more information, see the README for this project.
"""
# -------- BEGIN cut and paste line for online interpreters --------
#
# For faster reverse sorting (in 2.4+):
from operator import itemgetter
from textwrap import fill, dedent
import re, os, sys
from collections import defaultdict

# Default maximum range/score
DEFAULT_MAX_SCORE = 5

DEFAULT_N_SCORE = DEFAULT_MAX_SCORE + 1

# Default number of seats in a multi-winner election
DEFAULT_NSEATS = 7

# Utility function to sort a dictionary in reverse order of values
def reverse_sort_dict(d):
    return sorted(d.iteritems(), key=itemgetter(1), reverse=True)

qtypes = ['easy',
          'droop',
          'hare',
	  'pure-hb',
          'hagenbach-bischoff']

def droop_quota(n, m):
    """\
Traditional Droop quota of (n,m), where n = number of votes and m = number
of seats.
"""
    fn   = float(n)
    fmp1 = float(m) + 1.0
    return float(int(fn/fmp1)) + 1.0

# Set up for quotas:
def calc_quota(n,
               nseats=DEFAULT_NSEATS,
               qtype='easy'):
    """\
    Return the quota based on qtype:

    'easy'               => easy = (Nvotes + 1)/(Nseats + 1)
    'droop'              => Droop = int(Nvotes / (Nseats + 1)) + 1
    'hare'               => Hare  = Nvotes / Nseats, rounded down to nearest 0.01
    'hagenbach-bischoff' => Nvotes / (Nseats + 1), rounded up to nearest 0.01
    """

    fn = float(n)
    fnp1 = fn + 1.0
    fs = float(nseats)
    fsp1 = fs + 1.0

    # We implement a CASE switch construction using a dict:
    return {'easy':               (fnp1/fsp1),
            'droop':              (droop_quota(n,nseats)),
            'hare':               (int(fn*1000./fs-0.01)/1000.),
            'pure-hb':            (fn/fsp1),
            'hagenbach-bischoff': (droop_quota(n*1000,nseats)/1000.0)}[qtype]

class Ballot(dict):

    def __init__(self,
                 csv_string='',
                 cand_list=[],
                 weighted=False):

        # Parse the csv_string
        vals = csv_string.strip().split(',')

        # Save the weight, if present, otherwise rescale factor = 1.0.
        if weighted:
            self.rescale = float(vals[0])
            del vals[0]
        else:
            self.rescale = 1.0

        # Accumulate scores
        scores = []
        for i, v in enumerate(vals):
            if v:
                intv = int(v)
                if intv:
                    scores.append((cand_list[i],intv))

        # Now initialize with the list of 2-tuples
        dict.__init__(self,scores)

class Election(object):

    def __init__(self,
                 ballots=[],
                 candidates=set([]),
                 csv_input=None,
                 csv_output=None,
                 qtype='easy',
                 max_score=DEFAULT_MAX_SCORE,
                 nseats=DEFAULT_NSEATS,
                 range_style=0):
        "Initialize from a list of ballots or a CSV input file"

        # Number of seats to fill:
        self.nseats = nseats

        # Quota type
        self.qtype = qtype
        if qtype not in qtypes:
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


        # Count the number of votes and total approval to lowest threshold
        self.nvotes = 0
        tot_approval = defaultdict(float)
        for ballot in self.ballots:
            weight = ballot.rescale
            self.nvotes += int(weight)
            for k in ballot.keys():
                tot_approval[k] += weight

        # Calculate quota
        self.quota = calc_quota(self.nvotes,
                                self.nseats,
                                qtype=self.qtype)

        half_quota = self.quota / 2.0

        self.eliminated = set([k
                               for k in self.candidates
                               if tot_approval[k] < half_quota])

        print "Candidates with less Q/2 total approval eliminated:"
        print self.eliminated

        self.standing -= self.eliminated

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


        # Scores can be considered in three ways:
        #
        # Full range means that
        # 0 = strongly reject,
        # max_score/2 = neutral, and
        # max_score = fully approve.
        #
        # range_style == 0 means we sum up all range scores as they stand
        # range_style == 1 means we disregard the lower half of the range
        #                  when measuring approval
        # range_style == 2 means we count the entire range, but add
        #                  max_score to non-zero scores and renormalize
        #                  so that all non-zero scores are above neutral.
        #
        # self.beta is the equivalent fractional approval for each score
        # level, normalized so max_score gives approval of 1.0
        self.beta = [float(i) for i in range(self.n_score)]

        fmax = float(self.max_score)
        hmax = fmax / 2.0
        dmax = fmax * 2.0

        # Now normalize it according to range_style:
        if range_style == 0:
            for i, beta in enumerate(self.beta):
                if i == 0:
                    continue
                beta /= fmax

        elif range_style == 1:
            for i, beta in enumerate(self.beta):
                if i == 0:
                    continue
                beta /= fmax
                if beta <= hmax:
                    beta = 0.0

        elif range_style == 2:
            for i, beta in enumerate(self.beta):
                if i == 0:
                    continue
                beta = (beta + fmax)/dmax

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

        # We have a special keyword for the first field.
        # If it is 'Weight', it means the first index on each line
        # is the number of times that line should be counted repeatedly.
        if keys[0] == 'Weight':
            print "Weighted == True"
            weighted = True
            del keys[0]
        else:
            weighted = False

        self.candidates.update(set(keys))

        # Following lines are the ballots:
        for line in f:
            ballot = Ballot(line,keys,weighted=weighted)

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

If so, accumulate totals and trunc_sums at each score level for each
standing candidate, and keep track of weighted total vote.
"""

        totals = [dict([(c,0.0) for c in self.standing])]
        trunc_sums = [dict([(c,0.0) for c in self.standing])]
        total_vote = 0.0

        # Initialize dicts for each rating level.  We already
        # initialized above for score==0, but it is never used.
        for i in xrange(self.max_score):
            totals.append(dict([(c,0.0) for c in self.standing]))
            trunc_sums.append(dict([(c,0.0) for c in self.standing]))

        # In a single loop over the ballots, we
        #
        # a) Rescale the ballot using the factor from the previous winner,
        #    if applicable (i.e. if this is not the first total calculation).
        #
        # b) Accumulate totals and trunc_sums for each score level using
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
                            trunc_sums[score][c] += rescale

        return totals, trunc_sums, total_vote

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

    def bucklin_score(self, totals, trunc_sums):
        """\
Return Bucklin winner, Bucklin score and winner's trunc_sum, adjusting the
threshold if necessary."""

        # Candidates we're calculating totals for:
        standing = totals[1].keys()

        # Initial bucklin scores for each candidate:
        total = dict([(c,0.0) for c in standing])
        trunc_sum = dict([(c,0.0) for c in standing])

        threshold = self.max_score
        while self.threshold > 0:
            while threshold >= self.threshold:
                for c in standing:
                    total[c] += totals[threshold][c]
                    trunc_sum[c] += trunc_sums[threshold][c]

                ordered_scores = reverse_sort_dict(total)

                (winner, win_score) = ordered_scores[0]
                trunc_val = trunc_sum[winner]

                tied_bucklin_scores = dict([(cand,score)
                                            for cand, score in total.iteritems()
                                            if score == win_score])

                csv_line = self.print_running_total(threshold, ordered_scores)
                if ((win_score >= self.quota) or
                    ((threshold == self.threshold) and
                     (self.threshold == 1))):
                    csv_line += ",Approval Level = %d; Seating %s; Trunc_Sum = %.5g\n" % (threshold, winner, trunc_val)
                    self.csv_lines.append(csv_line)
                    return winner, win_score, trunc_val
                else:
                    csv_line += ",Approval Level = %d; Quota not reached\n" % threshold
                    self.csv_lines.append(csv_line)

                threshold -= 1

            self.threshold -= 1
            print "Dropping approval threshold level to ", self.threshold

        # Check for tied winning scores:
        if len(tied_bucklin_scores) > 1:
            print "\nUh-oh!  There is a tie!"
            print "Tied candidates:"
            for c, score in tied_bucklin_scores.iteritems():
                print "\t%s: %g" % (c, score)
            print "\nFalling back to range scoresums to resolve ties:"

            tied_cands = tied_bucklin_scores.keys()

            range_scores = defaultdict(float)

            # Range score sums are accumulated from the Bucklin
            # approval threshold up to the maximum score.
            for c in tied_cands:
                for score_level in range(self.threshold,self.n_score):
                    range_scores[c] += \
                        totals[score_level][c] * \
                        self.beta[score_level]

            ordered_range_scores = reverse_sort_dict(range_scores)

            r_winner, r_win_score = ordered_range_scores[0]

            tied_range_scores = [(c,score)
                                 for c, score in range_scores
                                 if score == r_win_score]

            if len(tied_range_scores) == 1:
                print "\nTie resolved."
                print "Winner =", r_winner, "with range scoresum =", r_win_score
                winner = r_winner
                trunc_val = trunc_sum[winner]
            else:
                print "\n*** ERROR***"
                print "Tie not resolved.  Continuing with current winner,"
                print "but algorithm is broken at this point."

        return winner, win_score, trunc_val

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

            # Calculate weighted totals and trunc_sums.
            #
            # To avoid multiple loops through the ballots,
            # the rescaling for the previous winner's
            # rescale factor is done in the same loop.
            #
            # NB: Since we're rescaling ballots from the previous
            # iteration, total_votes is returned as the total number of
            # rescaled ballots before removing the new winner.
            #
            totals, trunc_sums, total_vote = self.compute_totals(factor,
                                                                 winner=winner)
            if not terse:
                print "total_vote = ", total_vote
                print "vote_count = ", vote_count

            # Given the totals and trunc_sums for each approval level,
            # get the Bucklin winner, winner's Bucklin score and Trunc_Sum
            (winner,
             win_score,
             trunc_sum) = self.bucklin_score(totals, trunc_sums)
            used_up_fraction = \
                max(self.quota - trunc_sum, 0.0) / \
                max(max(win_score, self.quota) - trunc_sum, eps)

            factor = 1.0 - used_up_fraction

            vote_count -= min(max(trunc_sum, self.quota),win_score)

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
                    ", Trunc_Sum = %.5g" % trunc_sum, \
                    ", Rescale factor = %.5g" % factor
                print ""

        print "Winning set in order seated =",
        print "{" + ','.join([self.ordered_seated[i]
                              for i in range(self.nseats)]) + "}"

        print "Leftover vote =", vote_count

        # Write CSV output
        if self.csv_output == sys.stdout:
            print ""
            print "Begin CSV table output:"
            print "------8< cut here 8<---------"

        self.csv_output.writelines(self.csv_lines)

        if self.csv_output == sys.stdout:
            print "------8< cut here 8<---------"
            print "End CSV table output:"

        return

# -------- END cut and paste line for online interpreters --------
"""
If you don't have a python interpreter, you can run the code above
via the web, using

   http://ideone.com

Select Python from the left sidebar.

Cut and paste everything from from the "BEGIN cut and paste line" to
"END cut and paste line", and insert it into the source code textarea.

In the same textarea, following the source you've just cut and pasted
above, enter the appropriate input to run your example.  To run the
june2011.csv input, for example, you enter the following two statements:


election = Election(nseats=9,
                    max_score=9,
                    csv_input='-',
                    csv_output='-',
                    qtype='easy')

election.run_election()

Click where it says "click here to enter input (stdin) ...", and paste
in lines from the june2011.csv file.

Then click on the Submit button on the lower left.
"""

if __name__ == "__main__":
    from optparse import OptionParser

    usage="""%prog \\
            [-n|--nseats NSEATS] \\
            [-q|--quota-type QTYPE] \\
            [-i|--csv-input INPUT_FILENAME.csv] \\
            [-o|--csv-output OUTPUT_FILENAME.csv] \\
            [-v|--verbose] \\
            [-D|--debug]

%prog is a script to run Graded Approval Transferable Voting (GATV),
AKA ER-Bucklin(whole), to implement a Proportional Representation (PR)
election, using a set of tabulated ballots with ratings for each
candidate.

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
                      default='easy',
                      help=fill(dedent("""\
                      Quota type used in election.

                      'easy' = (Nballots+1) / (Nseats+1).

                      Equivalent to

                      Droop(Nballots*(Nseats+1),Nseats) / (Nseats+1)

                      Sometimes smaller than traditional Droop but
                      larger than Hagenbach-Bischoff.  Satisfies two
                      criteria: a majority bloc will capture a
                      majority of the seats; after seating Nseats
                      winners, the remaining vote is smaller than a
                      quota.

                      'droop' = Nballots /(Nseats + 1) + 1, dropping
                       fractional part.

                       Droop is traditionally used for STV.  Developed
                       before fractional transfer methods could be
                       used.

                      'hare' = Nballots / Nseats.

                      Hare is the most representational, but last seat
                      may be chosen with less than a full quota.

                      'hagenbach-bischoff'

                      = Nballots / (Nseats + 1).  This is what is
                      often called Droop.  Technically, this may allow
                      exactly 50% of the ballots to select a majority
                      of seats, or the left-out votes could meet quota
                      for an extra seat.  In this implementation, we
                      round up to the nearest thousandth of a vote, to
                      prevent the extra seat paradox.

                      [Default: 'easy']""")))

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

    if opts.quota_type not in qtypes:
        print "\nError, argument to --quota-type must be one of", \
            ', '.join(["'%s'" % q for q in qtypes])
        parser.print_help()
        sys.exit(1)

    if (opts.nseats < 1):
        print "\nError, --nseats argument must be a positive integer\n"
        parser.print_help()
        sys.exit(1)

    csv_input = opts.csv_input
    csv_output = opts.csv_output
    if (csv_input == "-"):
        print "Reading CSV input from stdin\n\n"
    else:
        if not os.path.isfile(csv_input):
            print "\nError, %s file does not exist\n" % csv_input
            parser.print_help()
            sys.exit(1)

        ext = os.path.splitext(csv_input)[1]

        if not ext:
            csv_input += '.csv'
            ext = '.csv'
        elif ((ext != '.csv') and (ext != '.CSV')):
            print "\nError, %s file does not have .csv or .CSV extension\n" % csv_input
            parser.print_help()
            sys.exit(1)

    if (csv_output == "-"):
        print "Writing CSV input to stdout\n\n"
    else:

        ext = os.path.splitext(csv_output)[1]

        if not ext:
            csv_output += '.csv'
            ext = '.csv'
        elif ((ext != '.csv') and (ext != '.CSV')):
            print "\nError, %s CSV output file does not have .csv or .CSV extension\n" % opts.csv_output
            parser.print_help()
            sys.exit(1)

    election = Election(nseats=opts.nseats,
                        max_score=opts.max_score,
                        csv_input=csv_input,
                        csv_output=csv_output,
                        qtype=opts.quota_type)

    election.run_election(verbose=opts.verbose,
                          terse=opts.terse,
                          debug=opts.debug)
