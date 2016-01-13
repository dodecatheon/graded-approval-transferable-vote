#!/usr/bin/env python
"""\
document GATV here.
"""
# -------- BEGIN cut and paste line for online interpreters --------
#
# For faster reverse sorting (in 2.4+):
import sys
import re
import os
from operator import itemgetter
from textwrap import fill, dedent
from collections import defaultdict
from pprint import pprint
from random import shuffle

# Support Python3-stle iterable range and zip in Python2
try:
    range = xrange
    import itertools
    zip = itertools.izip
except NameError:
    pass

# Default maximum range/score
DEFAULT_MAX_SCORE = 9

DEFAULT_N_SCORE = DEFAULT_MAX_SCORE + 1

# Default number of seats in a multi-winner election
DEFAULT_NSEATS = 7

# Utility function to sort a dictionary in reverse order of values
def reverse_sort_dict(d):
    return sorted(d.iteritems(), key=itemgetter(1), reverse=True)

# Utility function to enumerate backwards without storing the entire
# iterable or its index set in memory, stopping when the index reaches
# "base".
def reverse_enum(iterable, base=0):
    return zip(reversed(range(base,len(iterable))), reversed(iterable))

# Set up for quotas:
def calc_quota(n, nseats=DEFAULT_NSEATS):
    return float(n)/float(nseats + 1)

def quota_threshold(totals, v_total, quota):
    """Returns alpha, votes_above, votes_at, votes_at_plus_above, and
    the weighted score up to the quota for a given quota with totals
    and v_total
    """

    votes_above = 0.0
    votes_at_plus_above = 0.0
    weighted_score = 0.0
    for alpha, votes_at in reverse_enum(totals, base=1):
        weighted_score += float(alpha) * votes_at
        (votes_above,
         votes_at_plus_above) = (votes_at_plus_above,
                                 votes_at_plus_above + votes_at)
        if votes_at_plus_above > quota:
            weighted_score -= float(alpha) * (votes_at_plus_above - quota)
            break

    if (alpha == 1) and (votes_at_plus_above <= quota):
        votes_above, votes_at_plus_above = votes_at_plus_above, v_total
        alpha = 0
        votes_at = v_total - votes_above

    # Round the weighted score to the nearest single precision or so.
    # Since the weighted score is used as a tie-breaker, we need to
    # make sure that small differences don't skew results ... we want
    # several nearby weighted scores to round to the same value so we can
    # fall back to an alternate tie-breaker.
    scale = float(1<<30) / v_total
    weighted_score = int(weighted_score * scale + 0.5) / scale

    return alpha, votes_above, votes_at, votes_at_plus_above, weighted_score


def median_score(totals,
                 v_total,
                 quota,
                 tbs,
                 worst=False):
    "Given totals from 1 to max_score, return median score"

    (alpha,
     above,
     at,
     at_plus_above,
     alpha_score) = quota_threshold(totals, v_total, quota)

    pdiff = quota - above
    qdiff = at_plus_above - quota
    below = v_total - at_plus_above

    scores = []

    for tb in tbs:
        if tb == 'tm':
            # Truncated (or trimmed) mean:
            #
            # Find the average score between 0.5 quota and 1.5 quota
            # by subtracting the unaveraged score down to 0.5 quota from
            # the unaveraged quota down to 1.5 quota.

            (beta,
             beta_above,
             beta_at,
             beta_at_plus_above,
             beta_score) = quota_threshold(totals, v_total, quota/2.0)

            (gamma,
             gamma_above,
             gamma_at,
             gamma_at_plus_above,
             gamma_score) = quota_threshold(totals, v_total, quota*1.5)

            s = (gamma_score - beta_score) / quota

        elif tb == '2q':
            # Average score in the top two quota:
            (delta,
             delta_above,
             delta_at,
             delta_at_plus_above,
             delta_score) = quota_threshold(totals, v_total, quota*2.0)

            s = delta_score / (2.0 * quota)

        elif tb == 'mj':
            # Majority Judgment grade
            if above > 0.0 and pdiff < qdiff:
                # votes_above closer to quota than votes_{at+above}?
                # Then make the adjustment highest (+0.5)
                # when votes_above exactly equals the quota, dropping to
                # no adjustment when votes above go to zero with at+above
                # above 2*Q.
                s = (float(alpha) + 0.5 * above / quota)
            else:
                # There are no votes above, so use votes at+above,
                # or votes at+above are closer to quota than votes_above.
                # Then make the adjustment lowest (-0.5) when
                # votes below rise to the quota-complement,
                # rising to zero when there are no votes below.
                s = (float(alpha) -
                     0.5 * below / (v_total - quota))

        elif tb == 'gmj':

            # Graduated Majority Judgment:
            # Modify Jameson Quinn's formula so it works
            # when quota is not 50%.
            s = (float(alpha) + 0.5 * (qdiff - pdiff) / at)

        elif tb == 'ga':
            # Graded Approval.  This is analogous to ER-Bucklin.  We
            # quantify approval as the total weighted votes at or above
            # the quota threshold score.  In Majority Judgment terms, a
            # high votes-at-plus-above is equivalent to low votes below
            # the quota-threshold score.

            s = at_plus_above

        elif tb == 'ws':
            # Weighted score down to quota.
            s = alpha_score / quota

        elif tb == 'alpha':
            # This allows us to test a non-"median" score method.
            # In another section of the code, we choose the winner
            # by sorting on the first tb, then putting 'alpha' and 'ga'
            # as a tie-breaker combo later in the sequence of tie breakers.
            s = alpha

        if worst:

            # Invert the scores to test with the worst possible
            # ordering.
            s = -s

        scores.append(s)

    return (at_plus_above, alpha,) + tuple(scores)


class Ballot(dict):

    def __init__(self,
                 csv_string='',
                 cand_list=[],
                 weighted=False):

        # Parse the csv_string
        vals = csv_string.strip().split(',')

        # Save the weight, if present, otherwise rescale factor = 1.0.
        if weighted:
            self.rescale = max(float(vals[0]),0.0)
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
                 max_score=DEFAULT_MAX_SCORE,
                 nseats=DEFAULT_NSEATS,
                 tie_breakers=['tm', '2q','alpha','ga'],
                 worst=False,
                 alpha=1,
                 use_trunc_sum=True):
        "Initialize from a list of ballots or a CSV input file"

        # Number of seats to fill:
        self.nseats = nseats

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

        # Maximum Graded Approval score:
        self.max_score = max_score
        self.threshold = max_score
        self.n_score = self.max_score + 1

        if csv_output:
            if csv_output == '+':
                self.csv_output = None
            elif csv_output == '-':
                self.csv_output = sys.stdout
            else:
                self.csv_output = open(csv_output, 'w')
        else:
            self.csv_output = None


        # Count the number of votes and total approval to lowest threshold
        self.nvotes = 0
        tot_approval = defaultdict(float)
        for ballot in self.ballots:
            weight = ballot.rescale
            self.nvotes += int(weight)
            for k in ballot.keys():
                tot_approval[k] += weight

        # Calculate quota
        self.quota = calc_quota(self.nvotes, self.nseats)

        half_quota = self.quota / 2.0

        self.eliminated = set([k
                               for k in self.candidates
                               if tot_approval[k] < half_quota])

        if len(self.eliminated):
            print "Candidates with less Q/2 total approval eliminated:"
            print self.eliminated

            self.standing -= self.eliminated

        # Set up initial line of CSV output file:
        # Format is
        #
        # | Cand1 | Cand2 | ... | CandX | Winner name
        # +-------+-------+-----+-------+------------
        # |       |       |     |       |

        quota_string = "quota = %g out of %g\n" % \
            ( self.quota,
              self.nvotes )

        self.csv_lines = [';'.join(self.ordered_candidates + [quota_string])]

        self.tie_breakers = list(tie_breakers)

        self.worst = worst

        self.alpha = alpha

        self.use_trunc_sum = use_trunc_sum

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
        if keys[0].lower() == 'weight':
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
            if len(ballot) and ballot.rescale > 0.0:
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

        totals = dict([(c,list([0.0 for i in range(self.n_score)]))
                       for c in self.standing])
        trunc_sums = dict([(c,list([0.0 for i in range(self.n_score)]))
                           for c in self.standing])

        #$$ totals = [dict([(c,0.0) for c in self.standing])]
        #$$ trunc_sums = [dict([(c,0.0) for c in self.standing])]
        total_vote = 0.0

        # Initialize dicts for each rating level.  We already
        # initialized above for score==0, but it is never used.
        #$$ for i in range(self.max_score):
        #$$     totals.append(dict([(c,0.0) for c in self.standing]))
        #$$     trunc_sums.append(dict([(c,0.0) for c in self.standing]))

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
                        totals[c][score] += rescale
                        #$$ totals[score][c] += rescale
                        if n == 1:
                            trunc_sums[c][score] += rescale
                            #$$ trunc_sums[score][c] += rescale

        return totals, trunc_sums, total_vote

# For keeping track of running totals in a Comma Separated Variable file
# that could be imported into a spreadsheet ...
    def print_running_total(self, ordered_scores):
        """Print CSV line of ranked scores"""

        csv_line = ""

        # Create a label for each standing candidate.
        # Each label looks like
        # GA score: (rank: <sum of tb scores at this rank> > <sum at lower rank>)
        # In the lowest rank, there is no comparison.
        labels = {}
        n = len(ordered_scores)
        nm1 = n - 1
        for i in range(n):
            ip1 = i + 1

            part1 = []
            part2 = []

            tup = ordered_scores[i]

            c, ga = tup[:2]
            scores1 = tup[2:]

            label = "%15.5f (%d: " % (ga, ip1)

            if i < nm1:
                scores2 = ordered_scores[ip1][2:]

                for s1, s2 in zip(scores1, scores2):
                    part1 += [str(s1)]
                    part2 += [str(s2)]
                    if s1 > s2:
                        break

                labels[c] = (label +
                             '+'.join(part1) +
                             ' > ' +
                             '+'.join(part2) +
                             ')')
            else:

                labels[c] = (label +
                             '+'.join([str(s)
                                       for s in scores1]) +
                             ')')

        # And this prints out the appropriate label for all
        # standing candidates.

        return ';'.join([labels.get(c,'')
                         for c in self.ordered_candidates])

    def calc_win_score(self,
                       totals,
                       trunc_sums,
                       total_vote,
                       verbose=False):
        """\
Return GATV winner, votes_at_or_above_threshold, winner's trunc_sum,
winning threshold score, and tie-breaker scores."""

        # Candidates we're calculating totals for:
        standing = totals.keys()

        # Randomize order to prevent ordering bias
        shuffle(standing)

        if self.alpha:
            tbrange = range(3,3+len(self.tie_breakers))
        else:
            tbrange = range(2,3+len(self.tie_breakers))

        ranking = sorted([(c,) +
                          median_score(totals[c],
                                       total_vote,
                                       self.quota,
                                       tbs=self.tie_breakers,
                                       worst=self.worst)
                          for c in standing],
                         key=itemgetter(*tbrange),
                         reverse=True)

        winner_tuple = ranking[0]
        winner, ga_total, alpha = winner_tuple[:3]

        trunc_sum = sum(trunc_sums[winner][alpha:])

        self.threshold = alpha

        if verbose:
            print "Candidate rankings:"
            pprint(ranking)

        if self.csv_output:
            csv_line = self.print_running_total(ranking)
            csv_line += ";Alpha = %d  Seating %s  Trunc_Sum = %.5g\n" \
                % (alpha, winner, trunc_sum)
            self.csv_lines.append(csv_line)


        # Insert trunc_val into the tuple after the graded-approval total:
        return (winner, ga_total, trunc_sum, ) + winner_tuple[2:]

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
        for i in range(self.nseats):

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

                if vote_count - total_vote > 1.e-5:
                    print "Wasted vote = ", vote_count - total_vote

            # Given the totals and trunc_sums for each approval level,
            # get the Bucklin winner, winner's Bucklin score and Trunc_Sum

            winning_tuple = self.calc_win_score(totals,
                                                trunc_sums,
                                                total_vote,
                                                verbose)
            (winner,
             ga_total,
             trunc_sum,
             threshold,
             adjusted_score) = winning_tuple[:5]

            self.threshold = threshold

            if self.use_trunc_sum:
                qml = max(self.quota - trunc_sum, 0.0)
                tml = max(max(ga_total, self.quota) - trunc_sum, eps)
            else:

                if not terse:
                    print "Not using truncated ballot correction in rescale factor"
                qml = max(self.quota, 0.0)
                tml = max(max(ga_total, self.quota), eps)

            used_up_fraction = qml / tml

            factor = 1.0 - used_up_fraction

            vote_count -= min(max(trunc_sum, self.quota),ga_total)

            self.seated.add(winner)
            self.ordered_seated.append(winner)
            self.standing.remove(winner)

            n_seated += 1
            n_needed -= 1
            n_standing -= 1

            if not terse:
                print "Candidate %s seated in position %i" % ( winner,
                                                               n_seated), \
                    ", GA total = %.5g" % ga_total, \
                    ", Approval Threshold =", self.threshold, \
                    ", Adjusted score = %.5g" % adjusted_score, \
                    ", Quota = %.5g" % self.quota, \
                    ", Trunc_Sum = %.5g" % trunc_sum, \
                    ", Rescale factor = %.5g" % factor
                print ""

        print "Winning set in order seated ="
        print "\t" + '\n\t'.join(['%3d: '%(i+1) + self.ordered_seated[i]
                                    for i in range(self.nseats)])

        if not terse:
            print "Leftover vote =", vote_count

        # Write CSV output
        if self.csv_output:
            if self.csv_output == sys.stdout:
                print ""
                print "Begin CSV table output:"
                print "------8< cut here 8<---------"

            self.csv_output.writelines(self.csv_lines)

            if self.csv_output == sys.stdout:
                print "------8< cut here 8<---------"
                print "End CSV table output:"

        return

if __name__ == "__main__":
    from optparse import OptionParser

    usage="""%prog \\
            [-m|--max-score MAX_SCORE] \\
            [-n|--nseats NSEATS] \\
            [-i|--csv-input INPUT_FILENAME.csv] \\
            [-o|--csv-output OUTPUT_FILENAME.csv] \\
            [-v|--verbose] \\
            [-D|--debug]

%prog is a script to run Graded Approval Transferable Voting (GATV)
to implement a Proportional Representation (PR) election,
using a set of tabulated ballots with ratings for each candidate.

The Comma Separated Variable format is assumed to be in the form

	name1,name2,name3,...
        ,,,,,9,,,6,,7,,,2,...
        ,,9,8,7,6,1,2,0,...

with the list of candidates on the first line, and non-zero scores
for the respective candidates as ballots on following lines.

If the first candidate name is 'Weighted', the first score of each
ballot will be taken as the total weight of that ballot.
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
                      default=9,
                      help=fill(dedent("""\
                      Maximum score.  [Default: %d]""" % DEFAULT_MAX_SCORE )))

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
                      default=None,
                      help=("Filename of comma-separated-variable (csv) file "
                            "to receive table of election results.  "
                            "'.csv' extension can be included, but it will "
                            " be added if not present.  "
                            "Use hyphen ('-') to direct output to stdout.  "
                            "Use plus ('+') or leave off option to skip "
                            "output.  [Default: None]"))

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

    parser.add_option('-w',
                      '--worst',
                      action='store_true',
                      default=False,
                      help=("Switch sign of tie-breaker, so that "
                            "the worst possible ordering is chosen "
                            "for a set of candidates with the same "
                            "quota-satisfying threshold score.  This option "
                            "is used as a test to see just how much the "
                            "tie-breaker ordering affects Droop "
                            "proportionality and winning set. "
                            "[Default:  False]"))

    parser.add_option('-a',
                      '--alpha',
                      action='store',
                      type='int',
                      default=1,
                      help=("Alpha = 0 => median rating, 1 => other "
                            "tie-breaker first."
                            "Alpha functions as a switch to change from "
                            "'median'-rating to sorting based on the first "
                            "tie-breaker.  [Default:  1]"))

    parser.add_option('-b',
                      '--tie-breakers',
                      action='append',
                      default=None,
                      help=("List of tie-breakers:  "
                            "2q = Top 2-quota average weighted score; "
                            "tm = Trimmed Mean, weighted average score one "
                            "quota wide around the quota total threshold; "
                            "ws = weighted score, top quota average weighted score.  "
                            "alpha = score threshold at which total weighted "
                            "ballots at or above this score exceed the quota;"
                            "ga = Graded Approval score, total weighted votes "
                            "at or above quota-threshold score (alpha); "
                            "mj = Majority Judgment Grade, see B&L; "
                            "gmj = Graduated Majority Judgment Grade, see Quinn; "
                            "(Default:  ['tm', '2q', 'alpha', 'ga'])"
                            ))

    parser.add_option('-D',
                      '--debug',
                      action='store_true',
                      default=False,
                      help="Turn on debug mode printout.  [Default:  False]")

    parser.add_option('-u',
                      '--no-trunc-sum',
                      action='store_true',
                      default=False,
                      help="Turn off Truncated Ballots correction.  [Default:  False]")

    opts, args = parser.parse_args()

    if (opts.nseats < 1):
        print "\nError, --nseats argument must be a positive integer\n"
        parser.print_help()
        sys.exit(1)

    csv_input = opts.csv_input
    csv_output = opts.csv_output
    if (csv_input == "-"):
        if not opts.terse:
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

    if csv_output == "+":
        csv_output = None

    if csv_output:
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

    tbs = opts.tie_breakers

    alpha = opts.alpha

    use_trunc_sum = not opts.no_trunc_sum

    if not tbs:
        tbs = ['tm', '2q', 'alpha', 'ga']

    else:
        tbs = [y
               for x in tbs
               for y in x.split(',')]

        allowed_tbs = set(['tm', 'ga', '2q', 'mj', 'gmj', 'ws', 'alpha'])

        if set(tbs).difference(allowed_tbs):
            parser.print_help()
            print "Error, You entered the following tie-breakers: ", tbs
            print "Allowed tie-breakers must come from ", allowed_tbs
            sys.exit(1)

    if 'ga' not in tbs:
        # Always use 'ga' as the final tie-breaker if it is not there
        # earlier.
        tbs.append('ga')

    if alpha:
        if 'alpha' in tbs:
            alpha = tbs.index('alpha')
        else:
            # Not in the list ... put it in the right spot,
            # which would be before the first median-rating method.

            alpha = tbs.index('ga') # always present

            for m in ['gmj', 'mj']:
                if m in tbs:
                    alpha = min(alpha, tbs.index(m))

            if alpha > 0:
                tbs.insert(alpha,'alpha')

    if not opts.terse:
        print "Tie breakers = ", tbs

    election = Election(nseats=opts.nseats,
                        max_score=opts.max_score,
                        csv_input=csv_input,
                        csv_output=csv_output,
                        tie_breakers=tbs,
                        worst=opts.worst,
                        alpha=alpha,
                        use_trunc_sum=use_trunc_sum)

    election.run_election(verbose=opts.verbose,
                          terse=opts.terse,
                          debug=opts.debug)
