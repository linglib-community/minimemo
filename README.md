minimemo
========

[memo](https://github.com/kach/memo) in [Lean 4](https://lean-lang.org)

Installation:

    git clone https://github.com/linglib-community/minimemo.git
    cd minimemo
    lake exe cache get
    lake build

Run a model:

    lake env lean examples/naive.lean

Run tests:

    lake test
    pytest

Translate a memo model (requires memo):

    python scripts/examples.py
