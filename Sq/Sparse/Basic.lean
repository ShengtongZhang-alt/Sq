import Mathlib.Analysis.Real.Sqrt
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Basic definitions for the sparse matrix inequality

This file fixes the conventions used by the sparse-matrix part of the
square-energy argument.  In particular, `EntrywiseNonnegative` is an
entrywise condition; it is deliberately not notation from `MatrixOrder`.

The edge sums below are oriented: an undirected edge contributes once from
each endpoint.  Thus the paper's
`4 * (∑ uv ∈ E(G), √(M uv)) ^ 2` is represented by
`edgeSqrtMass G M ^ 2`.
-/

open scoped BigOperators

namespace SquareEnergy

open Matrix

noncomputable section

variable {V : Type*}

/-- Every entry of `M` is nonnegative.  This is not the Loewner order. -/
def EntrywiseNonnegative (M : Matrix V V ℝ) : Prop :=
  ∀ i j, 0 ≤ M i j

/-- A real matrix which is both positive semidefinite and entrywise nonnegative. -/
def DoublyNonnegative (M : Matrix V V ℝ) : Prop :=
  M.PosSemidef ∧ EntrywiseNonnegative M

/-- The off-diagonal support of `M` is contained in the edge set of `G`. -/
def SupportedOn (G : SimpleGraph V) (M : Matrix V V ℝ) : Prop :=
  ∀ ⦃u v⦄, u ≠ v → ¬G.Adj u v → M u v = 0

namespace EntrywiseNonnegative

lemma add {M N : Matrix V V ℝ} (hM : EntrywiseNonnegative M)
    (hN : EntrywiseNonnegative N) : EntrywiseNonnegative (M + N) :=
  fun i j ↦ add_nonneg (hM i j) (hN i j)

lemma zero : EntrywiseNonnegative (0 : Matrix V V ℝ) := by
  intro i j
  simp

lemma smul {M : Matrix V V ℝ} (hM : EntrywiseNonnegative M) {c : ℝ}
    (hc : 0 ≤ c) : EntrywiseNonnegative (c • M) := by
  intro i j
  exact mul_nonneg hc (hM i j)

end EntrywiseNonnegative

namespace DoublyNonnegative

lemma posSemidef {M : Matrix V V ℝ} (hM : DoublyNonnegative M) :
    M.PosSemidef :=
  hM.1

lemma entrywise {M : Matrix V V ℝ} (hM : DoublyNonnegative M) :
    EntrywiseNonnegative M :=
  hM.2

lemma entry_nonneg {M : Matrix V V ℝ} (hM : DoublyNonnegative M) (i j : V) :
    0 ≤ M i j :=
  hM.2 i j

lemma isHermitian {M : Matrix V V ℝ} (hM : DoublyNonnegative M) :
    M.IsHermitian :=
  hM.1.isHermitian

lemma isSymm {M : Matrix V V ℝ} (hM : DoublyNonnegative M) :
    M.IsSymm := by
  simpa using hM.isHermitian

lemma apply_symm {M : Matrix V V ℝ} (hM : DoublyNonnegative M) (i j : V) :
    M i j = M j i := by
  simpa using (hM.isSymm.apply j i)

end DoublyNonnegative

section Finite

variable [Fintype V]

/-- The graph parameter `2 |E(G)| - |V(G)| + 1`, with no truncation. -/
def graphQ (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  2 * (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) + 1

@[simp]
lemma graphQ_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    graphQ G =
      2 * (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) + 1 :=
  rfl

/-- A useful separation of `graphQ` into edge count and connected excess. -/
lemma graphQ_eq_card_edges_add_excess (G : SimpleGraph V) [DecidableRel G.Adj] :
    graphQ G =
      (G.edgeFinset.card : ℝ) +
        ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) + 1) := by
  simp only [graphQ]
  ring

lemma connected_card_vertices_le_card_edges_add_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    (Fintype.card V : ℝ) ≤ (G.edgeFinset.card : ℝ) + 1 := by
  have hNat : Fintype.card V ≤ G.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, ← G.edgeFinset_card] using
      hG.card_vert_le_card_edgeSet_add_one
  exact_mod_cast hNat

/-- For a connected graph, its edge count is at most `graphQ`. -/
lemma card_edges_le_graphQ (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) :
    (G.edgeFinset.card : ℝ) ≤ graphQ G := by
  have h := connected_card_vertices_le_card_edges_add_one G hG
  simp only [graphQ]
  linarith

/-- The literal (nontruncated) `graphQ` is nonnegative on connected graphs. -/
lemma graphQ_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) :
    0 ≤ graphQ G :=
  (Nat.cast_nonneg G.edgeFinset.card).trans (card_edges_le_graphQ G hG)

/-- The sum of all entries of a matrix. -/
def totalMass (M : Matrix V V ℝ) : ℝ :=
  ∑ i, ∑ j, M i j

lemma totalMass_eq_one_dotProduct_mulVec_one (M : Matrix V V ℝ) :
    totalMass M = (1 : V → ℝ) ⬝ᵥ (M *ᵥ (1 : V → ℝ)) := by
  simp [totalMass, dotProduct, mulVec]

lemma totalMass_add (M N : Matrix V V ℝ) :
    totalMass (M + N) = totalMass M + totalMass N := by
  simp [totalMass, Finset.sum_add_distrib]

lemma totalMass_smul (c : ℝ) (M : Matrix V V ℝ) :
    totalMass (c • M) = c * totalMass M := by
  simp [totalMass, Finset.mul_sum]

lemma totalMass_finset_sum {ι : Type*} (s : Finset ι)
    (M : ι → Matrix V V ℝ) :
    totalMass (∑ k ∈ s, M k) = ∑ k ∈ s, totalMass (M k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [totalMass]
  | @insert a s ha ih =>
      simp [ha, totalMass_add, ih]

/-- Positive semidefiniteness makes the total entry mass nonnegative. -/
lemma totalMass_nonneg_of_posSemidef {M : Matrix V V ℝ}
    (hM : M.PosSemidef) : 0 ≤ totalMass M := by
  rw [totalMass_eq_one_dotProduct_mulVec_one]
  simpa using hM.dotProduct_mulVec_nonneg (1 : V → ℝ)

lemma DoublyNonnegative.totalMass_nonneg {M : Matrix V V ℝ}
    (hM : DoublyNonnegative M) : 0 ≤ totalMass M :=
  totalMass_nonneg_of_posSemidef hM.posSemidef

/-- The oriented edge-entry mass.  Every undirected edge is counted twice. -/
def edgeMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Matrix V V ℝ) : ℝ :=
  ∑ u, ∑ v ∈ G.neighborFinset u, M u v

/--
The oriented square-root edge mass.  Every undirected edge is counted twice,
so the sparse theorem has the normalization
`edgeSqrtMass G M ^ 2 ≤ graphQ G * totalMass M`.
-/
def edgeSqrtMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Matrix V V ℝ) : ℝ :=
  ∑ u, ∑ v ∈ G.neighborFinset u, Real.sqrt (M u v)

lemma edgeMass_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Matrix V V ℝ} (hM : EntrywiseNonnegative M) :
    0 ≤ edgeMass G M := by
  exact Finset.sum_nonneg fun u _ ↦
    Finset.sum_nonneg fun v _ ↦ hM u v

lemma edgeSqrtMass_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Matrix V V ℝ) :
    0 ≤ edgeSqrtMass G M := by
  exact Finset.sum_nonneg fun u _ ↦
    Finset.sum_nonneg fun v _ ↦ Real.sqrt_nonneg _

lemma edgeMass_congr (G : SimpleGraph V) [DecidableRel G.Adj]
    {M N : Matrix V V ℝ}
    (h : ∀ ⦃u v⦄, G.Adj u v → M u v = N u v) :
    edgeMass G M = edgeMass G N := by
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v hv
  exact h ((G.mem_neighborFinset u v).mp hv)

lemma edgeSqrtMass_congr (G : SimpleGraph V) [DecidableRel G.Adj]
    {M N : Matrix V V ℝ}
    (h : ∀ ⦃u v⦄, G.Adj u v → M u v = N u v) :
    edgeSqrtMass G M = edgeSqrtMass G N := by
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v hv
  rw [h ((G.mem_neighborFinset u v).mp hv)]

end Finite

end

end SquareEnergy
