"""memo and minimemo give the same array on every example model."""
import pytest

import examples
import examples_exp
import lean

MODULES = {m.__name__: m for m in (examples, examples_exp)}


@pytest.fixture(scope="module")
def verdicts():
    return {name: lean.compare(module) for name, module in MODULES.items()}


@pytest.mark.parametrize("module, model", [(name, f.__name__) for name, m in MODULES.items()
                                           for f in m.MODELS])
def test_model(verdicts, module, model):
    ok, detail = verdicts[module][model]
    assert ok, detail
