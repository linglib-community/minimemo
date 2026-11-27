"""memo and minimemo give the same array on random models, and reject the same ones."""
import importlib.util
import sys

import pytest

import fuzz
import lean


@pytest.mark.parametrize("seed", [1, 2, 3, 4])
def test_random_models(seed, tmp_path):
    name = f"fuzz_models_{seed}"
    path = tmp_path / f"{name}.py"
    fuzz.write(path, seed, 25)
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    differ = {model: detail for model, (ok, detail) in lean.compare(module).items() if not ok}
    assert not differ, f"{path.read_text()}\n{differ}"
