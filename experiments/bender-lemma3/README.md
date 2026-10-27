# Bender et al. (ESA 2002), Lemma 3: a simulation

`sim.py` implements the tag-range relabeling algorithm of Bender, Cole, Demaine, Farach-Colton
and Zito (ESA 2002, Section 3). For every relabeling of a range of size 2^i, it records how many
insertions reached that range since it was last made uniform. It then compares the fewest such
insertions at each level with two bounds: the paper's (2 − T/2)(2/T)^i, and the corrected
(T − 1)/2 · (2/T)^i.

```
python3 sim.py 1.5 front 50000 40     # T = 1.5, insert at the front, 50,000 insertions, u = 2^40
```

The measured minimum falls below the paper's bound at every level from i = 4 to i = 37, and
stays above the corrected one. At i = 37 it is 33,707, against 52,438 for the paper's bound and
10,488 for the corrected one. The paper's appendix "Errors and Gaps Found" discusses this.
