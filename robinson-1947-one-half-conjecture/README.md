# Robinson's (1947) one-half conjecture is true

Supporting materials for the paper "Robinson's (1947) one-half conjecture is true" by Dave Goel.

## What the proof takes as given

The classical results cited in the paper: the strong Grunsky inequality, the area theorem, de Branges' coefficient theorem, Takagi's factorization, the argument principle, the open mapping theorem, the maximum and minimum principles, the Jordan curve theorem and the power series of a holomorphic function on a polydisc. The proof also rests on three computer checks, all in this repository. For each, the paper uses one program, named first below; the other programs listed check the same statements again and are not used by the paper.

- `near/`: the exact rational certificates for small angles (Section 4 of the paper): the polynomials of Lemmas 4.3 and 4.5 (`check_B8_b.py`; these runs also print a cell check at the endpoint 21/100, which the paper does not use) and the 256 cells of Lemma 4.8 (`check_B9_b.py`); their outputs are in `near/results/`. Not used by the paper: `check_B8_a.py`, and `check_B9_a.py` (320 cells);
- `far/`: the exact rational certificates for large angles (Section 6): the certificate `S135_certificate.json`, checked by `check_sector135.py`; the outputs are in `far/results/`. Not used by the paper: `S135_check_b.py`, and `audit_S135.py` (its own 207 cells in 60-digit arithmetic with outward padding and exact Sturm counts);
- `middle/`: the interval-arithmetic verification of the middle range of angles, eleven bands (Section 7): the Arb check `programB/holq_support_tree_arb.py` (bands 50.3-90 degrees, with the data `programB/HOLQ_joint_support_P55.json`) and `programB/holq_peer_tree_arb.py` (bands 90-135 degrees), which read the subdivision trees in `trees/` as data; the outputs are in `results/`. Not used by the paper: the C++ program in `programA/`, which built the trees, and the scripts `programA/*/replay_*.py`, which only recount the structure of a subdivision.

## How to verify

Install Python 3 with five packages:

```
pip install sympy mpmath python-flint numpy scipy
```

Run, in this folder:

```
./reproduce.sh
```

It runs the exact checks in about 80 seconds on one core and prints one line per check, ending with

```
RESULT: PASS - all 11 checks passed
```

`./reproduce.sh --full` also replays all eleven interval-arithmetic bands with the Arb verifier (about 4 hours on one core); `./reproduce.sh --band 90-95` replays a single band.

All rights reserved.
