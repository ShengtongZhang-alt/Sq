import Sq.Definition

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Positive and negative square energy

This file fixes the spectral conventions used in the paper.  Eigenvalues are
the real eigenvalues of the real symmetric adjacency matrix, indexed with
algebraic multiplicity by the vertex type.
-/

open scoped BigOperators

namespace SquareEnergy

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The positive spectral part of the adjacency matrix. -/
noncomputable def adjacencyPosPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V V ℝ :=
  (G.isHermitian_adjMatrix ℝ).cfc (fun x ↦ max x 0)

/-- The absolute value of the negative spectral part of the adjacency matrix. -/
noncomputable def adjacencyNegPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V V ℝ :=
  (G.isHermitian_adjMatrix ℝ).cfc (fun x ↦ max (-x) 0)

/-- The characteristic-polynomial roots are exactly the indexed adjacency
eigenvalues.  Since `Polynomial.roots` is a multiset, this records algebraic
multiplicity. -/
lemma roots_charpoly_adjMatrix_eq_adjacencyEigenvalues
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.adjMatrix ℝ).charpoly.roots =
      Multiset.map (adjacencyEigenvalues G) Finset.univ.val := by
  simpa [adjacencyEigenvalues, Function.comp_def] using
    (G.isHermitian_adjMatrix ℝ).roots_charpoly_eq_eigenvalues

lemma positiveSquareEnergy_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] :
    0 ≤ positiveSquareEnergy G := by
  classical
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma negativeSquareEnergy_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] :
    0 ≤ negativeSquareEnergy G := by
  classical
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

omit [DecidableEq V] in
lemma sum_sq_posPart_eq_filter (f : V → ℝ) :
    (∑ i, (max (f i) 0) ^ 2) = ∑ i with 0 < f i, (f i) ^ 2 := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 < f i
  · simp [hi, hi.le]
  · have hi' : f i ≤ 0 := le_of_not_gt hi
    simp [hi, hi']

omit [DecidableEq V] in
lemma sum_sq_negPart_eq_filter (f : V → ℝ) :
    (∑ i, (max (-f i) 0) ^ 2) = ∑ i with f i < 0, (f i) ^ 2 := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : f i < 0
  · have hneg : 0 < -f i := neg_pos.mpr hi
    rw [if_pos hi, max_eq_left hneg.le]
    ring
  · have hi' : 0 ≤ f i := le_of_not_gt hi
    simp [hi, hi']

open scoped MatrixOrder

/-- The explicitly diagonalized positive part agrees with the native CFC
positive part of the adjacency matrix. -/
lemma adjacencyPosPart_eq_posPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    adjacencyPosPart G = (G.adjMatrix ℝ)⁺ := by
  rw [adjacencyPosPart, CFC.posPart_def, cfcₙ_eq_cfc,
    (G.isHermitian_adjMatrix ℝ).cfc_eq]
  congr 1

/-- The explicitly diagonalized negative part agrees with the native CFC
negative part of the adjacency matrix. -/
lemma adjacencyNegPart_eq_negPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    adjacencyNegPart G = (G.adjMatrix ℝ)⁻ := by
  rw [adjacencyNegPart, CFC.negPart_def, cfcₙ_eq_cfc,
    (G.isHermitian_adjMatrix ℝ).cfc_eq]
  congr 1

lemma adjacencyPosPart_posSemidef (G : SimpleGraph V) [DecidableRel G.Adj] :
    (adjacencyPosPart G).PosSemidef := by
  rw [adjacencyPosPart_eq_posPart]
  exact (CFC.posPart_nonneg (G.adjMatrix ℝ)).posSemidef

lemma adjacencyNegPart_posSemidef (G : SimpleGraph V) [DecidableRel G.Adj] :
    (adjacencyNegPart G).PosSemidef := by
  rw [adjacencyNegPart_eq_negPart]
  exact (CFC.negPart_nonneg (G.adjMatrix ℝ)).posSemidef

lemma adjacency_eq_posPart_sub_negPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.adjMatrix ℝ = adjacencyPosPart G - adjacencyNegPart G := by
  rw [adjacencyPosPart_eq_posPart, adjacencyNegPart_eq_negPart]
  exact (CFC.posPart_sub_negPart (G.adjMatrix ℝ)
    (G.isHermitian_adjMatrix ℝ).isSelfAdjoint).symm

lemma adjacencyPosPart_mul_negPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    adjacencyPosPart G * adjacencyNegPart G = 0 := by
  rw [adjacencyPosPart_eq_posPart, adjacencyNegPart_eq_negPart]
  exact CFC.posPart_mul_negPart (G.adjMatrix ℝ)

lemma adjacencyNegPart_mul_posPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    adjacencyNegPart G * adjacencyPosPart G = 0 := by
  rw [adjacencyPosPart_eq_posPart, adjacencyNegPart_eq_negPart]
  exact CFC.negPart_mul_posPart (G.adjMatrix ℝ)

/-- Trace of the finite-dimensional Hermitian functional calculus. -/
lemma trace_hermitianCfc {A : Matrix V V ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (hA.cfc f) = ∑ i, f (hA.eigenvalues i) := by
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.trace_diagonal]
  simp

/-- The trace of the square of a Hermitian CFC value is the sum of the
corresponding squared scalar values. -/
lemma trace_sq_hermitianCfc {A : Matrix V V ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (hA.cfc f ^ 2) = ∑ i, (f (hA.eigenvalues i)) ^ 2 := by
  have hf : ContinuousOn f (spectrum ℝ A) := by
    rw [continuousOn_iff_continuous_restrict]
    fun_prop
  calc
    Matrix.trace (hA.cfc f ^ 2) =
        Matrix.trace (hA.cfc (fun x ↦ f x * f x)) := by
      rw [pow_two, ← hA.cfc_eq f, ← cfc_mul f f A hf hf, hA.cfc_eq]
    _ = ∑ i, f (hA.eigenvalues i) * f (hA.eigenvalues i) :=
      trace_hermitianCfc hA _
    _ = ∑ i, (f (hA.eigenvalues i)) ^ 2 := by
      simp only [pow_two]

lemma trace_sq_adjacencyPosPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix.trace (adjacencyPosPart G ^ 2) = positiveSquareEnergy G := by
  rw [adjacencyPosPart, trace_sq_hermitianCfc, sum_sq_posPart_eq_filter]
  rfl

lemma trace_sq_adjacencyNegPart (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix.trace (adjacencyNegPart G ^ 2) = negativeSquareEnergy G := by
  rw [adjacencyNegPart, trace_sq_hermitianCfc, sum_sq_negPart_eq_filter]
  rfl

lemma sq_adjacency_eq_sq_posPart_add_sq_negPart
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.adjMatrix ℝ ^ 2 = adjacencyPosPart G ^ 2 + adjacencyNegPart G ^ 2 := by
  simp only [pow_two]
  rw [adjacency_eq_posPart_sub_negPart, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_sub, adjacencyPosPart_mul_negPart, adjacencyNegPart_mul_posPart]
  simp

lemma squareEnergies_add_eq_trace_sq_adjacency
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    positiveSquareEnergy G + negativeSquareEnergy G =
      Matrix.trace (G.adjMatrix ℝ ^ 2) := by
  rw [sq_adjacency_eq_sq_posPart_add_sq_negPart, Matrix.trace_add,
    trace_sq_adjacencyPosPart, trace_sq_adjacencyNegPart]

lemma trace_sq_adjacency_eq_twice_card_edges
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix.trace (G.adjMatrix ℝ ^ 2) = (2 : ℝ) * G.edgeFinset.card := by
  simp only [pow_two, Matrix.trace, Matrix.diag_apply,
    G.adjMatrix_mul_self_apply_self]
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

lemma squareEnergies_add_eq_twice_card_edges
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    positiveSquareEnergy G + negativeSquareEnergy G =
      (2 : ℝ) * G.edgeFinset.card :=
  (squareEnergies_add_eq_trace_sq_adjacency G).trans
    (trace_sq_adjacency_eq_twice_card_edges G)

omit [DecidableEq V] in
lemma exists_pos_of_sum_eq_zero_of_ne_zero (f : V → ℝ)
    (hsum : ∑ i, f i = 0) (hf : f ≠ 0) :
    ∃ i, 0 < f i := by
  classical
  by_contra hpos
  apply hf
  funext i
  have hnonpos : ∀ j, f j ≤ 0 := fun j ↦
    le_of_not_gt fun hj ↦ hpos ⟨j, hj⟩
  exact (Finset.sum_eq_zero_iff_of_nonpos fun j _ ↦ hnonpos j).mp hsum
    i (Finset.mem_univ i)

omit [DecidableEq V] in
lemma exists_neg_of_sum_eq_zero_of_ne_zero (f : V → ℝ)
    (hsum : ∑ i, f i = 0) (hf : f ≠ 0) :
    ∃ i, f i < 0 := by
  classical
  by_contra hneg
  apply hf
  funext i
  have hnonneg : ∀ j, 0 ≤ f j := fun j ↦
    le_of_not_gt fun hj ↦ hneg ⟨j, hj⟩
  exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hnonneg j).mp hsum
    i (Finset.mem_univ i)

omit [DecidableEq V] in
lemma sum_sq_pos_filter_pos_of_exists_pos (f : V → ℝ)
    (h : ∃ i, 0 < f i) :
    0 < ∑ i with 0 < f i, (f i) ^ 2 := by
  classical
  apply Finset.sum_pos'
  · intro i _
    exact sq_nonneg (f i)
  · obtain ⟨i, hi⟩ := h
    exact ⟨i, by simp [hi], sq_pos_of_pos hi⟩

omit [DecidableEq V] in
lemma sum_sq_neg_filter_pos_of_exists_neg (f : V → ℝ)
    (h : ∃ i, f i < 0) :
    0 < ∑ i with f i < 0, (f i) ^ 2 := by
  classical
  apply Finset.sum_pos'
  · intro i _
    exact sq_nonneg (f i)
  · obtain ⟨i, hi⟩ := h
    exact ⟨i, by simp [hi], sq_pos_of_neg hi⟩

omit [Fintype V] [DecidableEq V] in
lemma exists_adj_of_connected_nontrivial
    (G : SimpleGraph V) [Nontrivial V]
    (hG : G.Connected) :
    ∃ u v, G.Adj u v := by
  let v : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨u, hu⟩ := hG.preconnected.exists_adj_of_nontrivial v
  exact ⟨v, u, hu⟩

omit [Fintype V] [DecidableEq V] in
lemma adjacencyMatrix_ne_zero_of_exists_adj
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∃ u v, G.Adj u v) :
    G.adjMatrix ℝ ≠ 0 := by
  obtain ⟨u, v, huv⟩ := h
  intro hzero
  have huv_entry := congr_fun (congr_fun hzero u) v
  simp [huv] at huv_entry

omit [Fintype V] [DecidableEq V] in
lemma adjacencyMatrix_ne_zero_of_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.Connected) :
    G.adjMatrix ℝ ≠ 0 :=
  adjacencyMatrix_ne_zero_of_exists_adj G
    (exists_adj_of_connected_nontrivial G hG)

lemma adjacencyEigenvalues_ne_zero_of_adjacencyMatrix_ne_zero
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hA : G.adjMatrix ℝ ≠ 0) :
    adjacencyEigenvalues G ≠ 0 := by
  intro hzero
  apply hA
  apply (G.isHermitian_adjMatrix ℝ).eigenvalues_eq_zero_iff.mp
  simpa only [adjacencyEigenvalues] using hzero

lemma adjacencyEigenvalues_ne_zero_of_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.Connected) :
    adjacencyEigenvalues G ≠ 0 :=
  adjacencyEigenvalues_ne_zero_of_adjacencyMatrix_ne_zero G
    (adjacencyMatrix_ne_zero_of_connected G hG)

lemma sum_adjacencyEigenvalues_eq_zero
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ i, adjacencyEigenvalues G i = 0 := by
  calc
    ∑ i, adjacencyEigenvalues G i = Matrix.trace (G.adjMatrix ℝ) := by
      simpa [adjacencyEigenvalues] using
        (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
    _ = 0 := G.trace_adjMatrix ℝ

lemma exists_pos_adjacencyEigenvalue_of_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.Connected) :
    ∃ i, 0 < adjacencyEigenvalues G i :=
  exists_pos_of_sum_eq_zero_of_ne_zero (adjacencyEigenvalues G)
    (sum_adjacencyEigenvalues_eq_zero G)
    (adjacencyEigenvalues_ne_zero_of_connected G hG)

lemma exists_neg_adjacencyEigenvalue_of_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.Connected) :
    ∃ i, adjacencyEigenvalues G i < 0 :=
  exists_neg_of_sum_eq_zero_of_ne_zero (adjacencyEigenvalues G)
    (sum_adjacencyEigenvalues_eq_zero G)
    (adjacencyEigenvalues_ne_zero_of_connected G hG)

lemma positiveSquareEnergy_pos_of_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.Connected) :
    0 < positiveSquareEnergy G := by
  exact sum_sq_pos_filter_pos_of_exists_pos (adjacencyEigenvalues G)
    (exists_pos_adjacencyEigenvalue_of_connected G hG)

lemma negativeSquareEnergy_pos_of_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.Connected) :
    0 < negativeSquareEnergy G := by
  exact sum_sq_neg_filter_pos_of_exists_neg (adjacencyEigenvalues G)
    (exists_neg_adjacencyEigenvalue_of_connected G hG)

end SquareEnergy
