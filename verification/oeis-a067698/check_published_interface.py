"""Check the new proof against the published, fully elaborated Robin proposition."""

import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from urllib.request import urlopen


BASE = "https://math.mit.edu/~drew/grh/"
STATEMENT_SHA256 = "fd7d5795b549201abb2b7cca916792126c34b4f4ff1dddf35d50eb4d95c1866c"


def main():
    with urlopen(BASE + "explicit-statements.out", timeout=30) as response:
        data = response.read()
    if hashlib.sha256(data).hexdigest() != STATEMENT_SHA256:
        raise SystemExit("Published statement file differs from the pinned digest.")
    statement = data.decode().split("def robinStmt : Prop :=\n", 1)[1]
    statement = statement.split("\ndef lagariasStmt : Prop :=", 1)[0]

    source = (
        "import Endpoint\n\nnamespace PublishedInterface\n"
        "def robinStmt : Prop :=\n" + statement + "\n\n"
        "theorem solve (h : robinStmt) : IsGreatest RobinExceptions.exceptions 5040 :=\n"
        "  RobinExceptions.greatest_of_robin h\n\n"
        "theorem iff_published : IsGreatest RobinExceptions.exceptions 5040 ↔ robinStmt :=\n"
        "  RobinExceptions.greatest_iff_robin\n\n"
        "#print axioms iff_published\n#print axioms solve\nend PublishedInterface\n"
    )
    lean = shutil.which("lean")
    if lean is None:
        raise SystemExit("Lean executable missing from PATH.")
    env = os.environ.copy()
    paths = [Path(__file__).resolve().parent]
    paths.extend(Path(p).resolve() for p in env.get("LEAN_PATH", "").split(os.pathsep) if p)
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    with tempfile.TemporaryDirectory() as directory:
        (Path(directory) / "InterfaceCheck.lean").write_text(source, encoding="utf-8")
        subprocess.run([lean, "-j1", "-o", "InterfaceCheck.olean", "InterfaceCheck.lean"],
                       cwd=directory, env=env, check=True)
    print("Lean accepted both directions against the pinned, fully elaborated Robin statement.")
    print("Published statement file SHA-256", STATEMENT_SHA256)


if __name__ == "__main__":
    main()
