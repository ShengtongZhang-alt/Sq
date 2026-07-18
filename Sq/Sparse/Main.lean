import Sq.Sparse.Folding
import Sq.Sparse.NoCut

/-!
# Sparse matrix induction

This file closes the induction for the graph-supported sparse matrix
inequality and then removes the support hypothesis by folding nonedges onto
the diagonal.

The edge sum is oriented: every undirected edge occurs twice in
`edgeSqrtMass`.  Consequently its square is exactly the paper's factor
`4 * (∑ uv ∈ E(G), √(M uv)) ^ 2`.
-/

open scoped BigOperators

namespace SquareEnergy

open Matrix

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

section CardinalityFacts

omit [DecidableEq V] in
/-- A two-element fintype can be enumerated by two distinct vertices. -/
lemma exists_pair_of_card_eq_two (hcard : Fintype.card V = 2) :
    ∃ u v : V, u ≠ v ∧ ∀ x : V, x = u ∨ x = v := by
  rw [← Nat.card_eq_fintype_card] at hcard
  obtain ⟨u, v, huv, huv_univ⟩ := Nat.card_eq_two_iff.mp hcard
  refine ⟨u, v, huv, fun x ↦ ?_⟩
  have hx : x ∈ ({u, v} : Set V) := by
    rw [huv_univ]
    exact Set.mem_univ x
  simpa [eq_comm] using hx

/-- The universal finset of a two-element type is its chosen pair. -/
lemma univ_eq_pair_of_card_eq_two
    (hcard : Fintype.card V = 2) {u v : V} (huv : u ≠ v) :
    (Finset.univ : Finset V) = {u, v} := by
  symm
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simp [hcard, huv]

omit [DecidableEq V] in
/-- Every vertex of a two-element type is one of a fixed distinct pair. -/
lemma eq_left_or_right_of_card_eq_two
    (hcard : Fintype.card V = 2) {u v : V} (huv : u ≠ v) (x : V) :
    x = u ∨ x = v := by
  classical
  have hx : x ∈ ({u, v} : Finset V) := by
    rw [← univ_eq_pair_of_card_eq_two hcard huv]
    exact Finset.mem_univ x
  simpa [eq_comm] using hx

omit [DecidableEq V] in
/-- In a connected graph on two vertices, the two vertices are adjacent. -/
lemma adj_of_connected_card_two
    (G : SimpleGraph V) (hG : G.Connected)
    (hcard : Fintype.card V = 2) {u v : V} (huv : u ≠ v) :
    G.Adj u v := by
  letI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨w, huw⟩ := hG.preconnected.exists_adj_of_nontrivial u
  rcases eq_left_or_right_of_card_eq_two hcard huv w with rfl | rfl
  · exact (huw.ne rfl).elim
  · exact huw

omit [DecidableEq V] in
/-- A connected simple graph on two vertices is the complete graph. -/
lemma eq_top_of_connected_card_two
    (G : SimpleGraph V) (hG : G.Connected)
    (hcard : Fintype.card V = 2) :
    G = ⊤ := by
  ext u v
  simp only [SimpleGraph.top_adj]
  exact ⟨SimpleGraph.Adj.ne, adj_of_connected_card_two G hG hcard⟩

omit [DecidableEq V] in
/-- A connected graph on two vertices has graph parameter exactly one. -/
lemma graphQ_eq_one_of_connected_card_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hcard : Fintype.card V = 2) :
    graphQ G = 1 := by
  have hlower : Fintype.card V ≤ G.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, ← G.edgeFinset_card] using
      hG.card_vert_le_card_edgeSet_add_one
  have hupper := G.card_edgeFinset_le_card_choose_two
  have hedge : G.edgeFinset.card = 1 := by
    norm_num [hcard] at hlower hupper
    omega
  simp [graphQ, hcard, hedge]

omit [DecidableEq V] in
/-- A simple graph on one vertex has no edges. -/
lemma eq_bot_of_card_eq_one
    (G : SimpleGraph V) (hcard : Fintype.card V = 1) :
    G = ⊥ := by
  haveI : Subsingleton V :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  exact Subsingleton.elim G ⊥

omit [DecidableEq V] in
/-- The graph parameter is exactly zero on a one-vertex graph. -/
lemma graphQ_eq_zero_of_card_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 1) :
    graphQ G = 0 := by
  have hupper := G.card_edgeFinset_le_card_choose_two
  have hedge : G.edgeFinset.card = 0 := by
    have hz : G.edgeFinset.card ≤ 0 := by
      simpa [hcard] using hupper
    exact Nat.eq_zero_of_le_zero hz
  simp [graphQ, hcard, hedge]

omit [DecidableEq V] in
/--
The oriented square-root edge mass is zero on a connected one-vertex graph.
Connectedness supplies its unique vertex, and simplicity rules out its only
possible edge.
-/
lemma edgeSqrtMass_eq_zero_of_card_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hcard : Fintype.card V = 1)
    (M : Matrix V V ℝ) :
    edgeSqrtMass G M = 0 := by
  classical
  let u : V := Classical.choice hG.nonempty
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hcard
  have hall (x : V) : x = u := (ha x).trans (ha u).symm
  have huniv : (Finset.univ : Finset V) = {u} := by
    ext x
    simp [hall x]
  have hneighbor : G.neighborFinset u = ∅ := by
    ext x
    rw [hall x]
    simp
  simp [edgeSqrtMass, huniv, hneighbor]

end CardinalityFacts

section TwoVertexFormulas

variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- The two neighbor finsets in a connected two-vertex graph are singletons. -/
lemma neighborFinsets_of_connected_card_two
    (hG : G.Connected) (hcard : Fintype.card V = 2)
    {u v : V} (huv : u ≠ v)
    (hcover : ∀ x : V, x = u ∨ x = v) :
    G.neighborFinset u = {v} ∧ G.neighborFinset v = {u} := by
  classical
  have hadj := adj_of_connected_card_two G hG hcard huv
  constructor <;> ext x
  · simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    rcases hcover x with rfl | rfl
    · simp [huv]
    · simp [hadj]
  · simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    rcases hcover x with rfl | rfl
    · simp [hadj.symm]
    · simp [huv.symm]

omit [DecidableEq V] in
/-- Explicit oriented square-root edge sum on two connected vertices. -/
lemma edgeSqrtMass_eq_card_two
    (hG : G.Connected) (hcard : Fintype.card V = 2)
    {u v : V} (huv : u ≠ v)
    (hcover : ∀ x : V, x = u ∨ x = v)
    (M : Matrix V V ℝ) :
    edgeSqrtMass G M = Real.sqrt (M u v) + Real.sqrt (M v u) := by
  classical
  have huniv := univ_eq_pair_of_card_eq_two hcard huv
  obtain ⟨hnu, hnv⟩ :=
    neighborFinsets_of_connected_card_two G hG hcard huv hcover
  simp [edgeSqrtMass, huniv, hnu, hnv, huv]

omit [DecidableEq V] in
/-- For a symmetric nonnegative matrix, oriented edge mass squared is `4 M_uv`. -/
lemma edgeSqrtMass_sq_eq_four_mul_of_card_two
    (hG : G.Connected) (hcard : Fintype.card V = 2)
    {u v : V} (huv : u ≠ v)
    (hcover : ∀ x : V, x = u ∨ x = v)
    {M : Matrix V V ℝ} (hM : DoublyNonnegative M) :
    edgeSqrtMass G M ^ 2 = 4 * M u v := by
  rw [edgeSqrtMass_eq_card_two G hG hcard huv hcover M]
  rw [← hM.apply_symm u v]
  rw [show (Real.sqrt (M u v) + Real.sqrt (M u v)) ^ 2 =
      4 * Real.sqrt (M u v) ^ 2 by ring]
  rw [Real.sq_sqrt (hM.entry_nonneg u v)]

omit [DecidableEq V] in
/-- Explicit total matrix mass after enumerating a two-element type. -/
lemma totalMass_eq_card_two
    (hcard : Fintype.card V = 2)
    {u v : V} (huv : u ≠ v)
    {M : Matrix V V ℝ} (hM : M.IsHermitian) :
    totalMass M = M u u + M v v + 2 * M u v := by
  classical
  have huniv := univ_eq_pair_of_card_eq_two hcard huv
  simp only [totalMass, huniv, Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_singleton, huv, not_false_eq_true]
  have hsymm : M v u = M u v := by
    simpa using hM.apply u v
  rw [hsymm]
  ring

omit [DecidableEq V] in
/-- PSD evaluated at `e_u - e_v` gives the two-vertex diagonal bound. -/
lemma two_mul_offdiag_le_diag_sum_of_card_two
    (hcard : Fintype.card V = 2)
    {u v : V} (huv : u ≠ v)
    {M : Matrix V V ℝ} (hM : M.PosSemidef) :
    2 * M u v ≤ M u u + M v v := by
  classical
  have huniv := univ_eq_pair_of_card_eq_two hcard huv
  have hquad :=
    hM.dotProduct_mulVec_nonneg (basisDiff u v)
  simp only [dotProduct, Matrix.mulVec, huniv, Finset.sum_insert,
    Finset.sum_singleton, Finset.mem_singleton, huv, not_false_eq_true,
    basisDiff_apply_left huv, basisDiff_apply_right huv, star_trivial,
    one_mul, neg_mul, mul_one, mul_neg] at hquad
  have hsymm : M v u = M u v := by
    simpa using hM.isHermitian.apply u v
  rw [hsymm] at hquad
  linarith

end TwoVertexFormulas

section BaseCases

omit [DecidableEq V] in
/-- The exact one-vertex base of the sparse induction. -/
lemma supportedSparseMatrixInequality_card_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hcard : Fintype.card V = 1)
    {M : Matrix V V ℝ} (_hM : DoublyNonnegative M)
    (_hSupport : SupportedOn G M) :
    edgeSqrtMass G M ^ 2 ≤ graphQ G * totalMass M := by
  rw [edgeSqrtMass_eq_zero_of_card_one G hG hcard M,
    graphQ_eq_zero_of_card_one G hcard]
  norm_num

omit [DecidableEq V] in
/-- The paper's exact two-vertex base of the sparse induction. -/
lemma supportedSparseMatrixInequality_card_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hcard : Fintype.card V = 2)
    {M : Matrix V V ℝ} (hM : DoublyNonnegative M)
    (_hSupport : SupportedOn G M) :
    edgeSqrtMass G M ^ 2 ≤ graphQ G * totalMass M := by
  obtain ⟨u, v, huv, hcover⟩ := exists_pair_of_card_eq_two hcard
  rw [edgeSqrtMass_sq_eq_four_mul_of_card_two G hG hcard huv hcover hM]
  rw [graphQ_eq_one_of_connected_card_two G hG hcard]
  rw [totalMass_eq_card_two hcard huv hM.isHermitian]
  have hdiag :=
    two_mul_offdiag_le_diag_sum_of_card_two hcard huv hM.posSemidef
  linarith

end BaseCases

section Induction

omit [DecidableEq V] in
/--
The supported sparse-matrix inequality for every finite connected simple
graph.  Since `edgeSqrtMass` is oriented, its square includes the paper's
factor `4`.
-/
theorem supportedSparseMatrixInequality
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected)
    {M : Matrix V V ℝ} (hM : DoublyNonnegative M)
    (hSupport : SupportedOn G M) :
    edgeSqrtMass G M ^ 2 ≤ graphQ G * totalMass M := by
  classical
  let P : Nat → Prop := fun n ↦
    ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card W = n →
      H.Connected →
      ∀ {N : Matrix W W ℝ},
        DoublyNonnegative N →
        SupportedOn H N →
        edgeSqrtMass H N ^ 2 ≤ graphQ H * totalMass N
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp only [P]
        intro W _ _ H _ hcard hH N hN hNSupport
        have hnpos : 0 < n := by
          rw [← hcard]
          exact Fintype.card_pos_iff.mpr hH.nonempty
        by_cases hn1 : n = 1
        · exact supportedSparseMatrixInequality_card_one
            H hH (hcard.trans hn1) hN hNSupport
        by_cases hn2 : n = 2
        · exact supportedSparseMatrixInequality_card_two
            H hH (hcard.trans hn2) hN hNSupport
        have hn3 : 3 ≤ Fintype.card W := by omega
        by_cases hcut : ∃ v, ¬(deleteVertex H v).Connected
        · obtain ⟨v, hv⟩ := hcut
          have hne : Nonempty {x : W // x ≠ v} := by
            obtain ⟨w, hw⟩ :=
              Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card W) v
            exact ⟨⟨w, hw⟩⟩
          apply supported_sparse_bound_of_not_connected_delete
            H v hH hne hv hN hNSupport
          intro X _ _ K _ hK hlt L hL hLSupport
          exact ih (Fintype.card X) (by omega)
            K rfl hK hL hLSupport
        · have hdelete : ∀ v, (deleteVertex H v).Connected := by
            simpa only [not_exists, not_not] using hcut
          apply noCutVertex_step H hH hn3 hdelete hN hNSupport
          intro v
          have hlt : Fintype.card (DeletedVertex v) < n := by
            have := card_deletedVertex_lt v
            omega
          exact ih (Fintype.card (DeletedVertex v)) hlt
            (deleteVertex H v) rfl (hdelete v)
            (deleteMatrix_doublyNonnegative hN v)
            (deleteMatrix_supportedOn H hNSupport v)
  exact hP (Fintype.card V) G rfl hG hM hSupport

omit [DecidableEq V] in
/--
The sparse-matrix inequality for an arbitrary doubly nonnegative matrix.
Nonedge entries are folded onto the diagonal before applying the supported
theorem.  The oriented edge mass encodes the paper's factor `4`.
-/
theorem sparseMatrixInequality
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected)
    {M : Matrix V V ℝ} (hM : DoublyNonnegative M) :
    edgeSqrtMass G M ^ 2 ≤ graphQ G * totalMass M := by
  classical
  exact supported_sparse_inequality_implies_unrestricted G
    (fun N hN hNSupport ↦
      supportedSparseMatrixInequality G hG hN hNSupport)
    hM

end Induction

end

end SquareEnergy
