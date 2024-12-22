import pytest
import subprocess
import tempfile
import os
import shutil

TEST_POSITIVE_DIR = "tests/test_positive"
TEST_NEGATIVE_DIR = "tests/test_negative"
ARCHITECTURE = "x64-linux" # "arm64-apple-darwin" 

@pytest.mark.parametrize("test_file", [f for f in os.listdir(TEST_POSITIVE_DIR) if f.endswith(".bx")])
def test_positive(test_file):
    test_path = os.path.join(TEST_POSITIVE_DIR, test_file)
    expected_output_path = test_path.replace(".bx", ".out")

    with tempfile.TemporaryDirectory() as tmpdir:
        temp_test_file = os.path.join(tmpdir, test_file)
        shutil.copy(test_path, temp_test_file)
        
        result = subprocess.run(
            ["python", "bxc.py", f"--arch={ARCHITECTURE}", temp_test_file],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )
        
        assert result.returncode == 0, f"Compilation failed: {result.stderr.decode()}"
        
        exe_path = temp_test_file.replace(".bx", ".exe")
        assert os.path.exists(exe_path), "Executable not generated."
        
        run_result = subprocess.run(
            [exe_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )
        
        with open(expected_output_path, "r") as expected_file:
            expected_output = expected_file.read()
        assert run_result.stdout.decode().strip() == expected_output.strip(), \
            f"Output mismatch: {run_result.stdout.decode()}"

@pytest.mark.parametrize("test_file", [f for f in os.listdir(TEST_NEGATIVE_DIR) if f.endswith(".bx")])
def test_negative(test_file):
    test_path = os.path.join(TEST_NEGATIVE_DIR, test_file)

    with tempfile.TemporaryDirectory() as tmpdir:
        temp_test_file = os.path.join(tmpdir, test_file)
        shutil.copy(test_path, temp_test_file)
        
        result = subprocess.run(
            ["python", "bxc.py", f"--arch={ARCHITECTURE}", temp_test_file],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )
        
        assert result.returncode == 1, "Expected compilation to fail, but it succeeded."