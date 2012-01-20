#!/usr/bin/env python
"""\
Module for ranked ballot information
"""
from operator import itemgetter
from string import lowercase

class RankedBallot(list):
    "A list of candidate sets, from highest ranked to lowest"
    # Global candidate list shared between all ballots
    candidates = []
    n_cand = 0
    max_score = 0
    def __init__(self,
                 csv_string='',
                 ranked_string='',
                 ratings_ballot=True,
                 cand_list=[],
                 ncand=0):

        # A RankedBallot is a list of sets of candidates
        list.__init__(self)

        # initial weight of the ballot is 1.0.
        self.weight = 1.0

        if not self.n_cand and ncand:
            self.n_cand = ncand

        if csv_string:          # Comma-separated variable ballot

            scores = {}

            csv_list = csv_string.rstrip().split(',')

            # Initialize candidates:
            if not self.candidates:
                if cand_list:
                    self.candidates = list(cand_list) # copy list
                    self.n_cand = len(cand_list)
                else:
                    self.n_cand = len(csv_list)
                    # Create generic alphabetic list with
                    # 'a','b',...,'z','aa','ab',...,'az','ba','bb',...
                    # I think 676 generic candidates should be ample :-).
                    for ii in xrange(self.n_cand):
                        i = ii % 26 # last letter
                        jj = (ii / 26) - 1
                        j = jj % 26

                        if jj > -1:
                            name = lowercase[j] + lowercase[i]
                        else:
                            name = lowercase[i]

                        self.candidates.append(name)
            elif not self.n_cand:
                self.n_cand = len(self.candidates)

            # Create the dict containing cand:score pairs:
            for i, v in enumerate(csv_list):
                if v:
                    intv = int(v)
                    if intv:
                        scores[self.candidates[i]] = intv

            # Process the dict into the list of sets:
            old_score = 0
            for cand, score in sorted( scores.iteritems(),
                                       key=itemgetter(1),
                                       reverse=ratings_ballot ):

                if score == old_score:
                    self[-1].add(cand)
                else:
                    # create a new set at the end of the self list
                    # and initialize it with the current candidate
                    self.append(set([cand]))

                old_score = score

        elif ranked_string:
            # with ranked strings, you pretty much have to provide
            # a cand_list with the first ballot.
            for substr in ranked_string.replace(' ', '').split('>'):
                self.append(set(substr.split('=')))

            if not self.candidates:
                if cand_list:
                    self.candidates = list(cand_list)
                    self.n_cand = len(self.candidates)
            else:
                self.n_cand = max(self.n_cand, len(self.candidates))


        else:
            print "Neither csv nor ranked string entered"

        self.max_score = max(self.max_score, len(self))

        return

    def rescale(self, factor):
        "Adjust ballot weight by rescale factor"
        self.weight *= factor
        return None

    def scores(self):
        "Returns a dict, converting ranked candidate sets back into scores"
        return dict((c, self.max_score - i)
                    for i, s in enumerate(self)
                    for c in s)

if __name__ == '__main__':

    "Simple test to see if ballot works ..."
    rb1 = RankedBallot(csv_string='1,,0,2,,,,1,,2,,2,,1,,,,,,,,,,,,,,,2,1,2,,',
                      ratings_ballot=True)

    print rb1
    print rb1.n_cand, ",", rb1.candidates

    rb2 = RankedBallot(csv_string='1,2,3,4,',
                       ratings_ballot=False)
    print rb2
    print rb2.n_cand, ",", rb2.candidates

    rb3 = RankedBallot(ranked_string='a=b=c=d>e=f=g=h')
    print rb3
