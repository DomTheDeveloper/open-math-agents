"""Fetch and checksum the standalone Möbius module from Pandey's formalization."""
import hashlib
from pathlib import Path
from urllib.request import urlopen

URL = ("https://raw.githubusercontent.com/mayankpandey9973/squarefree-explicit-formalized/"
       "f0c7baf2d046503f49c8f220690ba1c91e42fe82/squarefree_lean/Squarefree/Mobius.lean")
DIGEST = "763c7cfac02bcca2aec955681f118f510a3ac97caa533f384012c849f45c2258"
with urlopen(URL, timeout=45) as response:
    source = response.read()
if hashlib.sha256(source).hexdigest() != DIGEST:
    raise SystemExit("The downloaded module differs from the pinned SHA-256.")
target = Path(__file__).resolve().parent / "Mobius.lean"
if target.exists() and target.read_bytes() != source:
    raise SystemExit(f"A different {target.name} already exists.")
target.write_bytes(source)
print(f"Verified {target.name} at {DIGEST}.")
