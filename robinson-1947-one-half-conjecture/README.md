# Robinson's (1947) one-half conjecture is true

Supporting materials for the paper "Robinson's (1947) one-half conjecture is true" by Dave Goel:
https://doi.org/10.5281/zenodo.23953160

## What the proof takes as given

The classical results cited in the paper: the strong Grunsky inequality, the area theorem, de Branges' coefficient theorem, Takagi's factorization, the argument principle, the open mapping theorem, the Jordan curve theorem and the power series of a holomorphic function on a polydisc. The proof also rests on three computer checks, each carried out by two independently written programs, all in this repository:

- `near/`: the exact rational certificates for small angles (Section 4 of the paper): the polynomials of Lemmas 4.3 and 4.5 (first program `check_B8_b.py`, second `check_B8_a.py`; these runs also print a cell check at the endpoint 21/100, which the paper does not use) and the cells of Lemma 4.8 (first program `check_B9_b.py`, second `check_B9_a.py`); their outputs are in `near/results/`;
- `far/`: the exact rational certificates for large angles (Section 6): the certificate `S135_certificate.json` (first program `check_sector135.py`, second `S135_check_b.py`; a third check, `audit_S135.py`, which the paper does not use, covers the same range with its own 207 cells in 60-digit arithmetic with outward padding and exact Sturm counts); the outputs are in `far/results/`;
- `middle/`: the interval-arithmetic verification of the middle range of angles, eleven bands, with the subdivision trees and both programs (Section 7).

## Directions to Reproduce

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
