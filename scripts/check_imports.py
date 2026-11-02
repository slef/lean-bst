"""Ensure the public entry point reaches every library source module."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^(?:public )?(?:meta )?import (?:all )?(RotationBST(?:\.\w+)*)", re.M)
modules = {".".join(path.relative_to(ROOT).with_suffix("").parts)
           for path in (ROOT / "RotationBST").rglob("*.lean")}
seen = set()
pending = ["RotationBST"]
while pending:
    module = pending.pop()
    if module in seen:
        continue
    seen.add(module)
    path = ROOT / (module.replace(".", "/") + ".lean")
    if not path.is_file():
        raise SystemExit(f"Missing local import: {module}")
    pending.extend(IMPORT.findall(path.read_text()))
missing = sorted(modules - seen)
if missing:
    raise SystemExit("Unreachable library modules:\n" + "\n".join(missing))
print(f"All {len(modules)} library modules are reachable from RotationBST.")
