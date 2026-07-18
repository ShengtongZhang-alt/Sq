# Positive and Negative Square Energy in Lean

**Authors:** Yinchen Liu, Quanyu Tang and Shengtong Zhang

This repository is a Lean 4 and Mathlib formalization of the positive/negative
square-energy conjecture for finite connected simple graphs, including its
spectral reduction and the graph-supported doubly-nonnegative matrix
inequality.

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
\min\left(s^+(G),\,s^-(G)\right) \ge n-1.
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
[`Sq/Definition.lean`](Sq/Definition.lean).

## Proof architecture

1. **Spectral parts and trace.** Decompose the adjacency matrix as
   $A = A_+ - A_-$, prove positivity and orthogonality of the two parts, and
   identify their squared traces with $s^+(G)$ and $s^-(G)$.
2. **Graph-supported DNN inequality.** Prove the key edge-mass bound for a
   doubly-nonnegative matrix whose off-diagonal support lies in $G$.
3. **Folding.** Move nonedge entries onto the diagonal by positive-semidefinite
   rank-one corrections while preserving the quantities in the inequality.
4. **Cut/no-cut induction.** Use strong induction on the vertex count,
   splitting at a cut vertex when one exists and otherwise deleting a vertex
   while preserving connectedness.
5. **Hadamard-square deduction.** Apply the unrestricted DNN inequality to
   $A_+\circ A_+$ and $A_-\circ A_-$, then combine the resulting bounds with
   the trace identity $s^+(G)+s^-(G)=2|E(G)|$.

## File guide

### Main files

| File                                       | Contents                                           |
| ------------------------------------------ | -------------------------------------------------- |
| [`Sq/Definition.lean`](Sq/Definition.lean) | Adjacency eigenvalues and the two square energies. |
| [`Sq/Main.lean`](Sq/Main.lean)             | The final theorem and public entry point.          |

### Proofs

| File                                                                                             | Contents                                                           |
| ------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------ |
| [`Sq/Spectral.lean`](Sq/Spectral.lean)                                                           | Spectral parts, positivity, orthogonality, and trace identities.   |
| [`Sq/Sparse/Basic.lean`](Sq/Sparse/Basic.lean), [`Sq/Sparse/Scalar.lean`](Sq/Sparse/Scalar.lean) | Definitions and scalar estimates for the sparse matrix inequality. |
| [`Sq/Sparse/Folding.lean`](Sq/Sparse/Folding.lean)                                               | Reduction to graph-supported matrices.                             |
| [`Sq/Sparse/Cut.lean`](Sq/Sparse/Cut.lean), [`Sq/Sparse/NoCut.lean`](Sq/Sparse/NoCut.lean)       | The two induction branches.                                        |
| [`Sq/Sparse/Main.lean`](Sq/Sparse/Main.lean)                                                     | Assembly of the supported and unrestricted DNN inequalities.       |
| [`Sq/Deduction.lean`](Sq/Deduction.lean)                                                         | The Hadamard-square deduction from the matrix inequality.          |
| [`Sq/Audit.lean`](Sq/Audit.lean)                                                                 | Kernel axiom audit for the final theorem and critical inputs.      |

### Documentation

| File                                   | Contents                                                  |
| -------------------------------------- | --------------------------------------------------------- |
| [`FORMALIZATION.md`](FORMALIZATION.md) | Detailed correspondence between the mathematics and Lean. |
| [`VERIFICATION.md`](VERIFICATION.md)   | Reproducible build, source-scan, and axiom-audit record.  |

## Build

```sh
lake exe cache get  # download the precompiled Mathlib cache
lake build
```

The repository pins the Lean toolchain to `leanprover/lean4:v4.33.0-rc1` and
Mathlib to `v4.33.0-rc1`.
