"""Reject a Lean audit log unless every reported dependency is a standard axiom."""
from pathlib import Path
import re
import sys

allowed = {'propext', 'Classical.choice', 'Quot.sound'}
log = Path(sys.argv[1]).read_text()
reports = re.findall(r"'[^']+' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
if len(reports) != int(sys.argv[2]):
    raise SystemExit(f'Expected {sys.argv[2]} axiom reports and found {len(reports)}')
for report in reports:
    unexpected = {s.strip() for s in report.split(',') if s.strip()} - allowed
    if unexpected:
        raise SystemExit(f'Unexpected axioms: {sorted(unexpected)}')
