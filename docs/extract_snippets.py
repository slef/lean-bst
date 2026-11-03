"""Refresh the displayed definitions from the accompanying Lean source."""
from pathlib import Path
root = Path(__file__).resolve().parent
sources = ['Models/Rotation/Abstract.lean', 'Models/Rotation/Basic.lean',
           'Models/Online/Abstract.lean', 'Bounds/WorkingSet/Abstract.lean']
lines = '\n'.join((root.parent / 'RotationBST' / path).read_text()
                  for path in sources).splitlines()
names = ['Tree', 'Tree.size', 'Rotate', 'Rotations', 'Access', 'Execution', 'Algorithm', 'Algorithm.runFrom', 'Algorithm.cost', 'DynamicallyOptimal', 'workingSetNumber', 'workingSetSum', 'HasWorkingSetBound']
for name in names:
    start = next(i for i, line in enumerate(lines)
                 if any(line.startswith(f'{kind} {name} ') or line == f'{kind} {name} where'
                        for kind in ['inductive', 'def', 'structure']))
    end = next((j for j in range(start + 1, len(lines)) if not lines[j]), len(lines))
    (root / 'lean-snippets' / f'{name}.lean').write_text('\n'.join(lines[start:end]) + '\n')
statements = [line.removesuffix(' := by') for line in lines
              if line.startswith('theorem ')]
variables = [line for line in lines if line.startswith('variable ')]
(root / 'lean-snippets' / 'Invariants.lean').write_text('\n'.join(variables + [''] + statements) + '\n')

# Keep the geometric definition directly synchronized with its public abstract.
arboral = (root.parent / 'RotationBST/Models/Geometric/Definitions/Abstract.lean').read_text().splitlines()
for name in ['Rectangle', 'ASS', 'greedySweep']:
    start = next(i for i, line in enumerate(arboral) if line.startswith(f'def {name} '))
    end = next(j for j in range(start + 1, len(arboral)) if not arboral[j])
    (root / 'lean-snippets' / f'{name}.lean').write_text('\n'.join(arboral[start:end]) + '\n')
