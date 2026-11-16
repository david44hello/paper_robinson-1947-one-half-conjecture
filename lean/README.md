# Robinson's (1947) one-half conjecture is true — Lean 4 formalization

The paper's link is on the [front page of this repository](https://github.com/david44hello/paper_robinson-1947-one-half-conjecture).

## How to verify

Install Git, Lean (https://lean-lang.org/install/) and Python 3, then run:

```bash
git clone --branch v3.03 --single-branch https://github.com/david44hello/paper_robinson-1947-one-half-conjecture.git
cd paper_robinson-1947-one-half-conjecture/lean
./check.sh
```

Near the end it prints:

```
AUDIT: rows 153, PROVED 117, PROVED GIVEN 36, not proved yet 0, FAIL 0
FINAL GATE PASS: placeholders only as whole bodies of the 0 listed rows; statuses match the list.
```

The proof takes as given the computer-checked Lemmas 4.8, 6.2, 6.4 and 7.6 (14 computer checks) and
6 published theorems that Lean's library lacks: the argument principle, the Jordan curve theorem,
de Branges' theorem, the area theorem, the strong Grunsky inequality, and the power series of a
holomorphic function on the bidisc. [AUDIT.md](AUDIT.md) names them, claim by claim, and
[AUDIT_NOTES.md](AUDIT_NOTES.md) states each with its source.

Copyright (C) Dave Goel 2026--now. All rights reserved.
