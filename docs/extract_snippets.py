"""Refresh the displayed definitions from the accompanying Lean source."""
from pathlib import Path
root = Path(__file__).resolve().parent
lines = (root.parent / 'RotationBST.lean').read_text().splitlines()
names = ['Tree', 'Tree.size', 'Rotate', 'Rotations', 'Access', 'Execution', 'Algorithm', 'Algorithm.runFrom', 'Algorithm.cost', 'DynamicallyOptimal', 'workingSetNumber', 'workingSetSum', 'HasWorkingSetBound']
for name in names:
    start = next(i for i, line in enumerate(lines)
                 if any(line.startswith(f'{kind} {name} ') or line == f'{kind} {name} where'
                        for kind in ['inductive', 'def', 'structure']))
    end = next((j for j in range(start + 1, len(lines)) if not lines[j]), len(lines))
    (root / 'lean-snippets' / f'{name}.lean').write_text('\n'.join(lines[start:end]) + '\n')
statements = [line.removesuffix(' := by') for line in lines
              if line.startswith('theorem ')]
(root / 'lean-snippets' / 'Invariants.lean').write_text('\n'.join(statements) + '\n')

# Explicit-state interface and research theorem statements.
state = (root.parent / 'StateElimination.lean').read_text()
start = state.index('structure StatefulAlgorithm')
end = state.index('/-- The original history', start)
(root / 'lean-snippets' / 'StatefulAlgorithm.lean').write_text(state[start:end].strip() + '\n')
unit = next(line for line in state.splitlines() if line.startswith('abbrev TreeAlgorithm '))
(root / 'lean-snippets' / 'TreeAlgorithm.lean').write_text(unit + '\n')
probe = (root.parent / 'PeriodicProbe.lean').read_text()
statements = []
for name in ['state_elimination_iff_universal', 'arbitrary_iff_linear']:
    start = probe.index('theorem ' + name)
    end = probe.index(' :=', start)
    statement = probe[start:end]
    if name == 'arbitrary_iff_linear':
        statement = statement.replace(' : ', ' :\n    ', 1)
    statements.append(statement)
(root / 'lean-snippets' / 'Equivalence.lean').write_text('\n\n'.join(statements) + '\n')
