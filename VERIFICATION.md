# Verification record

Date: 2026-07-18 (UTC)

Toolchain:

- Lean `v4.33.0-rc1`
- Mathlib `79d0395a1825a6264ad5d269e35e60537518955e`

Commands run from the repository root:

```bash
lake build
lake env lean Sq/Audit.lean
rg -n '\bsorry\b|\badmit\b|\bnative_decide\b|^\s*(axiom|opaque|unsafe)\b' --glob '*.lean' .
```

Results:

- The complete library build succeeded (`2759` Lake jobs) with no warnings.
- The source scan returned no matches.
- `#print axioms` reported exactly `propext`, `Classical.choice`, and `Quot.sound`
  for the final theorem `SquareEnergy.card_sub_one_le_min_squareEnergy`, both
  component lower bounds, the supported and unrestricted sparse-matrix
  inequalities, and the square-energy trace identity. In particular, there is
  no project-specific axiom and no native-decision axiom.

The final theorem is unconditional for finite connected simple undirected
graphs. Its square energies are the sums of the squares of the strictly
positive and strictly negative adjacency eigenvalues, counted with algebraic
multiplicity.
