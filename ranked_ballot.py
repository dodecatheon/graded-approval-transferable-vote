#!/usr/bin/env python
"""\
Module for ranked ballot information
"""
class RankedBallot(list):
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
