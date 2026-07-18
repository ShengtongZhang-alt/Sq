/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Sq.Spectral
import Sq.Sparse.Main

/-!
# Square-energy deduction helpers

This file connects the spectral decomposition of a graph adjacency matrix to
the sparse doubly-nonnegative matrix inequality. It contains the matrix,
trace, quadratic, and lower-bound lemmas used by the final results in
`Sq.Main`.

All edge sums below are **oriented**: an undirected edge `{u, v}` occurs once
as `(u, v)` and once as `(v, u)`. Thus `edgeSqrtMass` already contains the
factor two whose square is the factor four in the unoriented formulation.
-/

open scoped BigOperators

namespace SquareEnergy

open Matrix

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The signed sum of matrix entries over oriented adjacent vertex pairs. -/
def orientedSignedEdgeSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Matrix V V ℝ) : ℝ :=
  ∑ u, ∑ v ∈ G.neighborFinset u, X u v

/-- The sum of absolute matrix entries over oriented adjacent vertex pairs. -/
def orientedAbsEdgeSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Matrix V V ℝ) : ℝ :=
  ∑ u, ∑ v ∈ G.neighborFinset u, |X u v|

omit [Fintype V] [DecidableEq V] in
/-- The Hadamard self-square of a positive semidefinite real matrix is doubly
nonnegative. -/
lemma hadamard_self_doublyNonnegative {X : Matrix V V ℝ}
    (hX : X.PosSemidef) :
    DoublyNonnegative (X ⊙ X) := by
  refine ⟨hX.hadamard hX, ?_⟩
  intro i j
  rw [Matrix.hadamard_apply]
  exact mul_self_nonneg (X i j)

omit [DecidableEq V] in
/-- Taking entrywise square roots of a Hadamard self-square gives absolute
values, term by term, on the oriented adjacency sum. -/
lemma edgeSqrtMass_hadamard_self_eq_orientedAbsEdgeSum
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Matrix V V ℝ) :
    edgeSqrtMass G (X ⊙ X) = orientedAbsEdgeSum G X := by
  simp only [edgeSqrtMass, orientedAbsEdgeSum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [Matrix.hadamard_apply, ← pow_two, Real.sqrt_sq_eq_abs]

/-- For a real Hermitian matrix, the total mass of its Hadamard self-square is
the trace of its ordinary square. -/
lemma totalMass_hadamard_self_eq_trace_sq {X : Matrix V V ℝ}
    (hX : X.IsHermitian) :
    totalMass (X ⊙ X) = Matrix.trace (X ^ 2) := by
  have hsymm : X.IsSymm := by
    simpa using hX
  rw [totalMass, Matrix.sum_hadamard_eq, hsymm.eq, pow_two]

omit [DecidableEq V] in
/-- Multiplication by the adjacency matrix and taking the trace extracts the
signed sum over oriented adjacent pairs. -/
lemma trace_adjMatrix_mul_eq_orientedSignedEdgeSum
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Matrix V V ℝ) :
    Matrix.trace (G.adjMatrix ℝ * X) = orientedSignedEdgeSum G X := by
  calc
    Matrix.trace (G.adjMatrix ℝ * X) =
        Matrix.trace (X * G.adjMatrix ℝ) := Matrix.trace_mul_comm _ _
    _ = orientedSignedEdgeSum G X := by
      simp [Matrix.trace, orientedSignedEdgeSum]

omit [DecidableEq V] in
/-- A signed oriented edge sum is bounded by the corresponding absolute sum. -/
lemma orientedSignedEdgeSum_le_orientedAbsEdgeSum
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Matrix V V ℝ) :
    orientedSignedEdgeSum G X ≤ orientedAbsEdgeSum G X := by
  unfold orientedSignedEdgeSum orientedAbsEdgeSum
  refine Finset.sum_le_sum fun u _ ↦ ?_
  exact Finset.sum_le_sum fun v _ ↦ le_abs_self (X u v)

omit [DecidableEq V] in
/-- The negative of a signed oriented edge sum is also bounded by the
corresponding absolute sum. -/
lemma neg_orientedSignedEdgeSum_le_orientedAbsEdgeSum
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Matrix V V ℝ) :
    -orientedSignedEdgeSum G X ≤ orientedAbsEdgeSum G X := by
  unfold orientedSignedEdgeSum orientedAbsEdgeSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun u _ ↦ ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun v _ ↦ neg_le_abs (X u v)

/-- The oriented signed edge sum of the positive spectral part is the positive
square energy. -/
lemma orientedSignedEdgeSum_adjacencyPosPart
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    orientedSignedEdgeSum G (adjacencyPosPart G) = positiveSquareEnergy G := by
  rw [← trace_adjMatrix_mul_eq_orientedSignedEdgeSum]
  rw [adjacency_eq_posPart_sub_negPart, Matrix.sub_mul,
    adjacencyNegPart_mul_posPart, sub_zero, ← pow_two,
    trace_sq_adjacencyPosPart]

/-- The oriented signed edge sum of the absolute negative spectral part is the
negative of the negative square energy. -/
lemma orientedSignedEdgeSum_adjacencyNegPart
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    orientedSignedEdgeSum G (adjacencyNegPart G) = -negativeSquareEnergy G := by
  rw [← trace_adjMatrix_mul_eq_orientedSignedEdgeSum]
  rw [adjacency_eq_posPart_sub_negPart, Matrix.sub_mul,
    adjacencyPosPart_mul_negPart, zero_sub, Matrix.trace_neg, ← pow_two,
    trace_sq_adjacencyNegPart]

/-- The total mass of the positive-part Hadamard square is the positive square
energy. -/
lemma totalMass_hadamard_self_adjacencyPosPart
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    totalMass (adjacencyPosPart G ⊙ adjacencyPosPart G) =
      positiveSquareEnergy G := by
  calc
    totalMass (adjacencyPosPart G ⊙ adjacencyPosPart G) =
        Matrix.trace (adjacencyPosPart G ^ 2) :=
      totalMass_hadamard_self_eq_trace_sq
        (adjacencyPosPart_posSemidef G).isHermitian
    _ = positiveSquareEnergy G := trace_sq_adjacencyPosPart G

/-- The total mass of the negative-part Hadamard square is the negative square
energy. -/
lemma totalMass_hadamard_self_adjacencyNegPart
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    totalMass (adjacencyNegPart G ⊙ adjacencyNegPart G) =
      negativeSquareEnergy G := by
  calc
    totalMass (adjacencyNegPart G ⊙ adjacencyNegPart G) =
        Matrix.trace (adjacencyNegPart G ^ 2) :=
      totalMass_hadamard_self_eq_trace_sq
        (adjacencyNegPart_posSemidef G).isHermitian
    _ = negativeSquareEnergy G := trace_sq_adjacencyNegPart G

/-- The positive square energy is at most the square-root edge mass of the
positive-part Hadamard square. -/
lemma positiveSquareEnergy_le_edgeSqrtMass_hadamard_posPart
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    positiveSquareEnergy G ≤
      edgeSqrtMass G (adjacencyPosPart G ⊙ adjacencyPosPart G) := by
  calc
    positiveSquareEnergy G =
        orientedSignedEdgeSum G (adjacencyPosPart G) :=
      (orientedSignedEdgeSum_adjacencyPosPart G).symm
    _ ≤ orientedAbsEdgeSum G (adjacencyPosPart G) :=
      orientedSignedEdgeSum_le_orientedAbsEdgeSum G _
    _ = edgeSqrtMass G (adjacencyPosPart G ⊙ adjacencyPosPart G) :=
      (edgeSqrtMass_hadamard_self_eq_orientedAbsEdgeSum G _).symm

/-- The negative square energy is at most the square-root edge mass of the
negative-part Hadamard square. -/
lemma negativeSquareEnergy_le_edgeSqrtMass_hadamard_negPart
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    negativeSquareEnergy G ≤
      edgeSqrtMass G (adjacencyNegPart G ⊙ adjacencyNegPart G) := by
  calc
    negativeSquareEnergy G =
        -orientedSignedEdgeSum G (adjacencyNegPart G) := by
      rw [orientedSignedEdgeSum_adjacencyNegPart]
      ring
    _ ≤ orientedAbsEdgeSum G (adjacencyNegPart G) :=
      neg_orientedSignedEdgeSum_le_orientedAbsEdgeSum G _
    _ = edgeSqrtMass G (adjacencyNegPart G ⊙ adjacencyNegPart G) :=
      (edgeSqrtMass_hadamard_self_eq_orientedAbsEdgeSum G _).symm

/-- Applying the sparse DNN theorem to the positive-part Hadamard square gives
the cancellable quadratic estimate. -/
lemma positiveSquareEnergy_sq_le_graphQ_mul
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    positiveSquareEnergy G ^ 2 ≤ graphQ G * positiveSquareEnergy G := by
  have hsparse :=
    sparseMatrixInequality G hG
      (hadamard_self_doublyNonnegative (adjacencyPosPart_posSemidef G))
  rw [totalMass_hadamard_self_adjacencyPosPart] at hsparse
  have henergy : 0 ≤ positiveSquareEnergy G :=
    positiveSquareEnergy_nonneg G
  have hedge :
      0 ≤ edgeSqrtMass G (adjacencyPosPart G ⊙ adjacencyPosPart G) :=
    edgeSqrtMass_nonneg G _
  exact
    (sq_le_sq₀ henergy hedge).mpr
      (positiveSquareEnergy_le_edgeSqrtMass_hadamard_posPart G) |>.trans hsparse

/-- Applying the sparse DNN theorem to the negative-part Hadamard square gives
the cancellable quadratic estimate. -/
lemma negativeSquareEnergy_sq_le_graphQ_mul
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    negativeSquareEnergy G ^ 2 ≤ graphQ G * negativeSquareEnergy G := by
  have hsparse :=
    sparseMatrixInequality G hG
      (hadamard_self_doublyNonnegative (adjacencyNegPart_posSemidef G))
  rw [totalMass_hadamard_self_adjacencyNegPart] at hsparse
  have henergy : 0 ≤ negativeSquareEnergy G :=
    negativeSquareEnergy_nonneg G
  have hedge :
      0 ≤ edgeSqrtMass G (adjacencyNegPart G ⊙ adjacencyNegPart G) :=
    edgeSqrtMass_nonneg G _
  exact
    (sq_le_sq₀ henergy hedge).mpr
      (negativeSquareEnergy_le_edgeSqrtMass_hadamard_negPart G) |>.trans hsparse

/-- On a nontrivial connected graph, strict positivity permits cancellation in
the positive-energy quadratic estimate. -/
lemma positiveSquareEnergy_le_graphQ
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.Connected) :
    positiveSquareEnergy G ≤ graphQ G :=
  positive_cancel_sq_le_mul
    (positiveSquareEnergy_pos_of_connected G hG)
    (positiveSquareEnergy_sq_le_graphQ_mul G hG)

/-- On a nontrivial connected graph, strict positivity permits cancellation in
the negative-energy quadratic estimate. -/
lemma negativeSquareEnergy_le_graphQ
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.Connected) :
    negativeSquareEnergy G ≤ graphQ G :=
  positive_cancel_sq_le_mul
    (negativeSquareEnergy_pos_of_connected G hG)
    (negativeSquareEnergy_sq_le_graphQ_mul G hG)

/-- The upper bound on negative energy and the trace identity give the lower
bound on positive energy by the literal formula
`graphQ G = 2 |E(G)| - |V| + 1`. -/
lemma card_sub_one_le_positiveSquareEnergy_of_negative_le_graphQ
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hneg : negativeSquareEnergy G ≤ graphQ G) :
    (Fintype.card V : ℝ) - 1 ≤ positiveSquareEnergy G := by
  have hsum := squareEnergies_add_eq_twice_card_edges G
  rw [graphQ] at hneg
  linarith

/-- The upper bound on positive energy and the trace identity give the lower
bound on negative energy by the literal formula
`graphQ G = 2 |E(G)| - |V| + 1`. -/
lemma card_sub_one_le_negativeSquareEnergy_of_positive_le_graphQ
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hpos : positiveSquareEnergy G ≤ graphQ G) :
    (Fintype.card V : ℝ) - 1 ≤ negativeSquareEnergy G := by
  have hsum := squareEnergies_add_eq_twice_card_edges G
  rw [graphQ] at hpos
  linarith

end

end SquareEnergy
