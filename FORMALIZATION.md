# Formalization audit

## Certified statement

The exact certified theorem, declared in `Sq/Main.lean`, is:

```lean
theorem SquareEnergy.card_sub_one_le_min_squareEnergy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    (Fintype.card V : ℝ) - 1 ≤
      min (positiveSquareEnergy G) (negativeSquareEnergy G)
```

This is the inequality in `background.tex`, lines 172--176.  The definitions
and trace identity used to interpret it correspond to lines 108--136.

## Module layout

- `Sq/Definition.lean` contains the public definitions visible in the final
  statement: `adjacencyEigenvalues`, `positiveSquareEnergy`, and
  `negativeSquareEnergy`.
- `Sq/Spectral.lean` develops the positive and negative spectral parts and
  proves the spectral and trace identities.
- `Sq/Deduction.lean` contains the oriented-edge, Hadamard/DNN, trace,
  quadratic, upper-bound, and lower-bound helper lemmas.
- `Sq/Main.lean` contains only the two component lower bounds and the exact
  certified theorem above.

## Correspondence with the paper

- **Finite, simple, undirected graph.** `[Fintype V]` makes the vertex type
  finite. `SimpleGraph V` is mathlib's loopless symmetric graph structure, so
  it represents a simple undirected graph. Thus the paper's `G = (V,E)` has no
  directed-edge or loop generalization hidden in the Lean statement.
- **The number of vertices.** The paper's integer `n = |V|` is
  `Fintype.card V`. The theorem compares energies in `ℝ`, so its left side is
  the real expression `(Fintype.card V : ℝ) - 1`, exactly as displayed in the
  signature.
- **Adjacency spectrum and multiplicity.** In `Sq/Definition.lean`,
  `adjacencyEigenvalues G : V → ℝ` is the real eigenvalue family supplied by
  the Hermitian real adjacency matrix. Its index type has cardinality `n`.
  `roots_charpoly_adjMatrix_eq_adjacencyEigenvalues` identifies the multiset of
  characteristic-polynomial roots with this indexed family, which records
  algebraic multiplicity.
- **Sign convention and zero eigenvalues.** The literal definitions in
  `Sq/Definition.lean` make `positiveSquareEnergy G` sum `λ²` over the strict
  filter `0 < λ`, and `negativeSquareEnergy G` sum `λ²` over the strict filter
  `λ < 0`.
  Consequently zero eigenvalues contribute to neither quantity, matching
  lines 114--116.
- **Spectral parts and the trace identity.** `adjacencyPosPart G` and
  `adjacencyNegPart G` are positive semidefinite, satisfy
  `A = A₊ - A₋`, and have zero products in both orders. The compiled lemmas
  `trace_sq_adjacencyPosPart` and `trace_sq_adjacencyNegPart` identify their
  squared traces with `s⁺` and `s⁻`. The lemma
  `squareEnergies_add_eq_twice_card_edges` proves
  `s⁺ + s⁻ = 2 |E|`, matching lines 121--136.
- **Connectedness.** `G.Connected` is exactly the hypothesis in lines
  172--176. In mathlib it includes `Nonempty V`; therefore a connected graph
  in this theorem cannot have `n = 0`.
- **The one-vertex boundary case.** When `n = 1`, the target left side is
  zero. `card_sub_one_le_min_squareEnergy` proves this branch from the
  nonnegativity of both square energies. The file does not need or assert a
  separate exact-spectrum classification for that case.

## Edge normalization and final deduction

`edgeSqrtMass G M` sums over every vertex and its neighbor finset. Hence each
undirected edge is counted twice, once in each orientation. For a Hadamard
self-square it becomes

```text
edgeSqrtMass G (X ⊙ X) = ∑_{u} ∑_{v adjacent to u} |X_uv|.
```

Thus the square of this oriented sum contains the factor four appearing when
the same expression is written as an unoriented edge sum. Independently,
`trace (A^2) = 2 |E|` uses the same standard fact that an undirected edge has
two orientations. These conventions are consistent; no factor two or four is
silently discarded.

The helpers in `Sq/Deduction.lean` apply the fully proved unrestricted theorem
`SquareEnergy.sparseMatrixInequality` from `Sq.Sparse.Main` to `A₊ ⊙ A₊` and
`A₋ ⊙ A₋`. Schur's product theorem supplies positive semidefiniteness, and
entrywise squares supply nonnegativity, so both inputs are doubly nonnegative.
Trace and oriented-edge identities give

```text
(s⁺)^2 ≤ graphQ(G) s⁺,    (s⁻)^2 ≤ graphQ(G) s⁻.
```

For `n > 1`, connectedness gives strict positivity of both energies, allowing
the common positive factors to be cancelled. Finally,
`graphQ(G) = 2 |E| - n + 1` together with
`s⁺ + s⁻ = 2 |E|` converts the upper bound on either energy into the lower
bound `n - 1` on the other.

## Typeclass and computability artifacts

- `[DecidableEq V]` supports finite matrix indexing and equality decisions.
- `[DecidableRel G.Adj]` supports the adjacency matrix and neighbor finsets.
- Definitions involving spectral decomposition are `noncomputable`; this is
  an implementation choice, not an additional graph-theoretic hypothesis.
- The locally derived `[Nontrivial V]` instance is used only in the `n > 1`
  branch to invoke the strict-positivity lemmas. It is not an extra theorem
  assumption.

## Toolchain and verification

The repository pins Lean to `leanprover/lean4:v4.33.0-rc1` in
`lean-toolchain` and mathlib to revision `v4.33.0-rc1` in `lakefile.toml`.

The module verification commands are:

```sh
lake env lean Sq/Definition.lean
lake env lean Sq/Spectral.lean
lake env lean Sq/Deduction.lean
lake env lean Sq/Main.lean
lake build Sq.Main
```

These commands succeed for the code audited here. The four modules contain no
`sorry`, `admit`, or new `axiom`; the central matrix estimate is the proved
theorem imported from `Sq.Sparse.Main` by `Sq/Deduction.lean`.
