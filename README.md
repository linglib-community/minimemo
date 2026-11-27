minimemo
========

[memo](https://github.com/kach/memo) in Lean

Installation:

    git clone https://github.com/linglib-community/minimemo.git
    cd minimemo
    lake exe cache get
    lake build

Run a model:

    lake env lean examples/naive.lean

Translate a memo model (requires memo):

    python scripts/examples.py
