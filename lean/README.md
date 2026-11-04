# Robinson's (1947) one-half conjecture is true — Lean 4 proof

The paper: https://doi.org/10.5281/zenodo.23953160

This folder is a Lean 4 proof of the paper's results.

## Directions to Reproduce

Install Git, Lean (https://lean-lang.org/install/) and Python 3, then run:

```bash
git clone --branch v2.00 --single-branch https://github.com/david44hello/paper_robinson-1947-one-half-conjecture.git
cd paper_robinson-1947-one-half-conjecture/lean
./check.sh
```

Near the end it prints:

```
AUDIT: rows 141, PROVED 105, PROVED GIVEN 36, not proved yet 0, FAIL 0
FINAL GATE PASS: placeholders only as whole bodies of the 0 listed rows; statuses match the list.
```

The proof takes as given 6 published facts that Lean's library lacks and the 14 computer checks
of Lemmas 4.8, 6.2, 6.4 and 7.6; [AUDIT.md](AUDIT.md) names them, claim by claim, and
[AUDIT_NOTES.md](AUDIT_NOTES.md) explains them.

Copyright (C) Dave Goel 2026--now. All rights reserved.
