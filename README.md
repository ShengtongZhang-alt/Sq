# Positive and Negative Square Energy in Lean

This repository is a Lean 4 and Mathlib formalization of the positive/negative square-energy conjecture for finite connected simple graphs, including its spectral reduction and the graph-supported doubly-nonnegative matrix inequality.

## The theorem

Let $G$ be a finite connected simple undirected graph on $n$ vertices, and let
$\lambda_1,\ldots,\lambda_n$ be the eigenvalues of its adjacency matrix, counted
with multiplicity. Define

$$
s^+(G) := \sum_{\lambda_i>0}\lambda_i^2,
\qquad
s^-(G) := \sum_{\lambda_i<0}\lambda_i^2.
$$

Then

$$
\min(s^+(G),s^-(G)) \ge n-1.
$$

## Lean statement

```lean
theorem SquareEnergy.card_sub_one_le_min_squareEnergy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    (Fintype.card V : ℝ) - 1 ≤
      min (SquareEnergy.positiveSquareEnergy G)
        (SquareEnergy.negativeSquareEnergy G)
```

The eigenvalue and energy definitions in this statement are in
`Sq/Definition.lean`.

## Proof architecture

- **Spectral parts and trace:** decompose the adjacency matrix as
  \(A=A_+-A_-\), prove positivity and orthogonality of the two parts, and
  identify their squared traces with \(s^+(G)\) and \(s^-(G)\).
- **Graph-supported DNN inequality:** prove the key edge-mass bound for a
  doubly-nonnegative matrix whose off-diagonal support lies in \(G\).
- **Folding:** move nonedge entries onto the diagonal by positive-semidefinite
  rank-one corrections while preserving the quantities in the inequality.
- **Cut/no-cut induction:** use strong induction on the vertex count, splitting
  at a cut vertex when one exists and otherwise deleting a vertex while
  preserving connectedness.
- **Hadamard-square deduction:** apply the unrestricted DNN inequality to
  \(A_+\odot A_+\) and \(A_-\odot A_-\), then combine the resulting bounds with
  the trace identity \(s^+(G)+s^-(G)=2|E(G)|\).

## File guide

### Main Files
- `Sq/Definition.lean` — adjacency eigenvalues and the two square energies.
- `Sq/Main.lean` — the final theorem and public entry point.

### Proofs
- `Sq/Spectral.lean` — spectral parts, positivity, orthogonality, and trace
  identities.
- `Sq/Sparse/Basic.lean` and `Sq/Sparse/Scalar.lean` — definitions and scalar
  estimates for the sparse matrix inequality.
- `Sq/Sparse/Folding.lean` — reduction to graph-supported matrices.
- `Sq/Sparse/Cut.lean` and `Sq/Sparse/NoCut.lean` — the two induction branches.
- `Sq/Sparse/Main.lean` — assembly of the supported and unrestricted DNN
  inequalities.
- `Sq/Deduction.lean` — the Hadamard-square deduction from the matrix inequality.
- `Sq/Audit.lean` — kernel axiom audit for the final theorem and critical inputs.
- `FORMALIZATION.md` — detailed correspondence between the mathematics and Lean.
- `VERIFICATION.md` — reproducible build, source-scan, and axiom-audit record.

## Build

```sh
lake build
```

The repository pins the Lean toolchain to `leanprover/lean4:v4.33.0-rc1` and
Mathlib to `v4.33.0-rc1`.
