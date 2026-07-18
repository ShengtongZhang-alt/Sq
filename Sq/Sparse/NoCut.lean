import Sq.Sparse.Cut
import Mathlib.Data.Nat.Choose.Cast

/-!
# The no-cut-vertex induction step

This file proves the vertex-deletion branch of the sparse square-energy
induction.  All edge sums use the oriented convention from `Sq.Sparse.Basic`:
every undirected edge occurs in both directions.
-/

open scoped BigOperators

namespace SquareEnergy

open Matrix

noncomputable section

variable {V : Type*}

/-- The type of vertices left after deleting `v`. -/
abbrev DeletedVertex (v : V) := {u : V // u ≠ v}

instance (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    DecidableRel (deleteVertex G v).Adj := by
  intro i j
  change Decidable (G.Adj i.1 j.1)
  infer_instance

/-- The principal submatrix obtained by deleting one row and column. -/
def deleteMatrix (M : Matrix V V ℝ) (v : V) :
    Matrix (DeletedVertex v) (DeletedVertex v) ℝ :=
  M.submatrix Subtype.val Subtype.val

section BasicDeletion

variable [Fintype V] [DecidableEq V]

@[simp]
lemma card_deletedVertex (v : V) :
    Fintype.card (DeletedVertex v) = Fintype.card V - 1 := by
  change Fintype.card ({v}ᶜ : Set V) = Fintype.card V - 1
  rw [Fintype.card_compl_set]
  simp

lemma card_deletedVertex_lt (v : V) :
    Fintype.card (DeletedVertex v) < Fintype.card V := by
  rw [card_deletedVertex]
  exact Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨v⟩) Nat.zero_lt_one

omit [Fintype V] [DecidableEq V] in
lemma deleteMatrix_posSemidef {M : Matrix V V ℝ}
    (hM : M.PosSemidef) (v : V) :
    (deleteMatrix M v).PosSemidef := by
  exact hM.submatrix Subtype.val

omit [Fintype V] [DecidableEq V] in
lemma deleteMatrix_entrywiseNonnegative {M : Matrix V V ℝ}
    (hM : EntrywiseNonnegative M) (v : V) :
    EntrywiseNonnegative (deleteMatrix M v) := by
  intro i j
  exact hM i.1 j.1

omit [Fintype V] [DecidableEq V] in
lemma deleteMatrix_doublyNonnegative {M : Matrix V V ℝ}
    (hM : DoublyNonnegative M) (v : V) :
    DoublyNonnegative (deleteMatrix M v) :=
  ⟨deleteMatrix_posSemidef hM.posSemidef v,
    deleteMatrix_entrywiseNonnegative hM.entrywise v⟩

omit [Fintype V] [DecidableEq V] in
lemma deleteMatrix_supportedOn (G : SimpleGraph V)
    {M : Matrix V V ℝ} (hM : SupportedOn G M) (v : V) :
    SupportedOn (deleteVertex G v) (deleteMatrix M v) := by
  intro i j hij hnonedge
  apply hM
  · intro h
    apply hij
    exact Subtype.ext h
  · simpa [deleteVertex, SimpleGraph.induce_adj] using hnonedge

end BasicDeletion

section FiniteSumDeletion

variable [Fintype V] [DecidableEq V]

/--
Deleting row and column `v`, then adding back that row and column, counts the
diagonal entry twice.
-/
private lemma sum_delete_add_row_add_column (a : V → V → ℝ) (v : V) :
    (∑ i : DeletedVertex v, ∑ j : DeletedVertex v, a i.1 j.1) +
        (∑ j, a v j) + (∑ i, a i v) =
      (∑ i, ∑ j, a i j) + a v v := by
  have houter :
      (∑ i, ∑ j, a i j) =
        (∑ j, a v j) + ∑ i : DeletedVertex v, ∑ j, a i.1 j := by
    exact Fintype.sum_eq_add_sum_subtype_ne (fun i ↦ ∑ j, a i j) v
  have hinner :
      (∑ i : DeletedVertex v, ∑ j, a i.1 j) =
        (∑ i : DeletedVertex v, a i.1 v) +
          ∑ i : DeletedVertex v, ∑ j : DeletedVertex v, a i.1 j.1 := by
    simp_rw [Fintype.sum_eq_add_sum_subtype_ne (fun j ↦ a _ j) v]
    rw [Finset.sum_add_distrib]
  have hcolumn :
      (∑ i, a i v) =
        a v v + ∑ i : DeletedVertex v, a i.1 v := by
    exact Fintype.sum_eq_add_sum_subtype_ne (fun i ↦ a i v) v
  rw [houter, hinner, hcolumn]
  ring

/-- Generic summed principal-submatrix deletion identity. -/
private lemma sum_delete_submatrices (a : V → V → ℝ) :
    (∑ v, ∑ i : DeletedVertex v, ∑ j : DeletedVertex v, a i.1 j.1) =
      ((Fintype.card V : ℝ) - 2) * (∑ i, ∑ j, a i j) +
        ∑ i, a i i := by
  let D : V → ℝ :=
    fun v ↦ ∑ i : DeletedVertex v, ∑ j : DeletedVertex v, a i.1 j.1
  let R : V → ℝ := fun v ↦ ∑ j, a v j
  let C : V → ℝ := fun v ↦ ∑ i, a i v
  let T : ℝ := ∑ i, ∑ j, a i j
  have hsum :
      (∑ v, D v) + (∑ v, R v) + (∑ v, C v) =
        (∑ _v : V, T) + ∑ v, a v v := by
    calc
      (∑ v, D v) + (∑ v, R v) + (∑ v, C v) =
          ∑ v, (D v + R v + C v) := by
            simp only [Finset.sum_add_distrib]
      _ = ∑ v, (T + a v v) := by
            apply Finset.sum_congr rfl
            intro v _
            exact sum_delete_add_row_add_column a v
      _ = (∑ _v : V, T) + ∑ v, a v v := by
            rw [Finset.sum_add_distrib]
  have hrow : (∑ v, R v) = T := rfl
  have hcolumn : (∑ v, C v) = T := by
    dsimp [C, T]
    rw [Finset.sum_comm]
  have hconstant : (∑ _v : V, T) = (Fintype.card V : ℝ) * T := by
    simp
  rw [hrow, hcolumn, hconstant] at hsum
  dsimp only [D, T] at hsum ⊢
  ring_nf at hsum ⊢
  linarith

end FiniteSumDeletion

section EdgeDeletion

variable [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
private lemma edgeSqrtMass_eq_sum_if (M : Matrix V V ℝ) :
    edgeSqrtMass G M =
      ∑ u, ∑ w, if G.Adj u w then Real.sqrt (M u w) else 0 := by
  simp [edgeSqrtMass, SimpleGraph.neighborFinset_eq_filter,
    Finset.sum_filter]

omit [DecidableEq V] in
private lemma edgeMass_eq_sum_if (M : Matrix V V ℝ) :
    edgeMass G M =
      ∑ u, ∑ w, if G.Adj u w then M u w else 0 := by
  simp [edgeMass, SimpleGraph.neighborFinset_eq_filter,
    Finset.sum_filter]

/--
Deleting `v` removes both oriented copies of every incident edge: the copy
leaving `v` and the copy entering `v`.
-/
lemma edgeSqrtMass_deleteVertex_add_incident (M : Matrix V V ℝ) (v : V) :
    edgeSqrtMass (deleteVertex G v) (deleteMatrix M v) +
        (∑ w ∈ G.neighborFinset v, Real.sqrt (M v w)) +
        (∑ u ∈ G.neighborFinset v, Real.sqrt (M u v)) =
      edgeSqrtMass G M := by
  let a : V → V → ℝ :=
    fun u w ↦ if G.Adj u w then Real.sqrt (M u w) else 0
  have h := sum_delete_add_row_add_column a v
  have hdiag : a v v = 0 := by simp [a]
  rw [hdiag, add_zero] at h
  rw [edgeSqrtMass_eq_sum_if (G := deleteVertex G v),
    edgeSqrtMass_eq_sum_if (G := G)]
  simpa [a, deleteVertex, deleteMatrix,
    SimpleGraph.induce_adj, SimpleGraph.neighborFinset_eq_filter,
    Finset.sum_filter, SimpleGraph.adj_comm] using h

/-- Every oriented edge survives all vertex deletions except its two ends. -/
lemma sum_edgeSqrtMass_deleteVertex (M : Matrix V V ℝ) :
    (∑ v, edgeSqrtMass (deleteVertex G v) (deleteMatrix M v)) =
      ((Fintype.card V : ℝ) - 2) * edgeSqrtMass G M := by
  let a : V → V → ℝ :=
    fun u w ↦ if G.Adj u w then Real.sqrt (M u w) else 0
  have h := sum_delete_submatrices a
  have hdiag : (∑ v, a v v) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    simp [a]
  rw [hdiag, add_zero] at h
  calc
    (∑ v, edgeSqrtMass (deleteVertex G v) (deleteMatrix M v)) =
        ∑ v, ∑ u : DeletedVertex v, ∑ w : DeletedVertex v,
          a u.1 w.1 := by
            apply Finset.sum_congr rfl
            intro v _
            rw [edgeSqrtMass_eq_sum_if (G := deleteVertex G v)]
            simp [a, deleteVertex, deleteMatrix]
    _ = ((Fintype.card V : ℝ) - 2) * (∑ u, ∑ w, a u w) := h
    _ = ((Fintype.card V : ℝ) - 2) * edgeSqrtMass G M := by
      rw [edgeSqrtMass_eq_sum_if (G := G)]

omit [DecidableEq V] in
private lemma edgeSqrtMass_eq_dart_sum (M : Matrix V V ℝ) :
    edgeSqrtMass G M =
      ∑ p ∈ (Finset.univ.filter fun p : V × V ↦ G.Adj p.1 p.2),
        Real.sqrt (M p.1 p.2) := by
  rw [edgeSqrtMass_eq_sum_if]
  rw [Finset.sum_filter]
  exact (Finset.sum_product' Finset.univ Finset.univ
    (fun u w ↦ if G.Adj u w then Real.sqrt (M u w) else 0)).symm

omit [DecidableEq V] in
private lemma edgeMass_eq_dart_sum (M : Matrix V V ℝ) :
    edgeMass G M =
      ∑ p ∈ (Finset.univ.filter fun p : V × V ↦ G.Adj p.1 p.2),
        M p.1 p.2 := by
  rw [edgeMass_eq_sum_if]
  rw [Finset.sum_filter]
  exact (Finset.sum_product' Finset.univ Finset.univ
    (fun u w ↦ if G.Adj u w then M u w else 0)).symm

omit [DecidableEq V] in
/--
Flat Cauchy--Schwarz in oriented normalization.  The indexing finset has
`2 * |E(G)|` elements.
-/
lemma edgeSqrtMass_sq_le_two_mul_card_edges_mul_edgeMass
    {M : Matrix V V ℝ} (hM : EntrywiseNonnegative M) :
    edgeSqrtMass G M ^ 2 ≤
      2 * (G.edgeFinset.card : ℝ) * edgeMass G M := by
  let s := Finset.univ.filter fun p : V × V ↦ G.Adj p.1 p.2
  have hflat :=
    sq_sum_sqrt_le_card_mul_sum s (fun p : V × V ↦ M p.1 p.2)
      (fun p _ ↦ hM p.1 p.2)
  have hcardNat : s.card = 2 * G.edgeFinset.card := by
    dsimp [s]
    exact G.two_mul_card_edgeFinset.symm
  have hcardReal : (s.card : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hcardNat
  rw [edgeSqrtMass_eq_dart_sum, edgeMass_eq_dart_sum]
  rw [hcardReal] at hflat
  exact hflat

end EdgeDeletion

section GraphDeletion

variable [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma card_edges_deleteVertex (v : V) :
    (deleteVertex G v).edgeFinset.card =
      G.edgeFinset.card - G.degree v := by
  let e : DeletedVertex v ≃ ({v}ᶜ : Set V) :=
    { toFun := fun u ↦ ⟨u.1, by
          change u.1 ∉ ({v} : Set V)
          simpa using u.2⟩
      invFun := fun u ↦ ⟨u.1, by
          intro h
          apply u.2
          simp [h]⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let f : deleteVertex G v ≃g G.induce ({v}ᶜ : Set V) :=
    { toEquiv := e
      map_rel_iff' := by
        intro u w
        rfl }
  calc
    (deleteVertex G v).edgeFinset.card =
        (G.induce ({v}ᶜ : Set V)).edgeFinset.card :=
      f.card_edgeFinset_eq
    _ = G.edgeFinset.card - G.degree v :=
      (G.card_edgeFinset_induce_compl_singleton v).trans
        (G.card_edgeFinset_deleteIncidenceSet v)

/-- Vertex deletion changes `q = 2m - n + 1` by `1 - 2 deg(v)`. -/
lemma graphQ_deleteVertex (v : V) :
    graphQ (deleteVertex G v) =
      graphQ G + 1 - 2 * (G.degree v : ℝ) := by
  have hdegree : G.degree v ≤ G.edgeFinset.card :=
    by
      rw [← G.card_incidenceFinset_eq_degree]
      exact Finset.card_le_card (G.incidenceFinset_subset v)
  have hvertex : 1 ≤ Fintype.card V :=
    Fintype.card_pos_iff.mpr ⟨v⟩
  simp only [graphQ_eq, card_edges_deleteVertex, card_deletedVertex]
  rw [Nat.cast_sub hdegree, Nat.cast_sub hvertex]
  ring

/-- Summed deletion identity for the graph parameter. -/
lemma sum_graphQ_deleteVertex :
    (∑ v, graphQ (deleteVertex G v)) =
      ((Fintype.card V : ℝ) - 2) * (graphQ G - 1) := by
  have hdegree :
      (∑ v, (G.degree v : ℝ)) =
        2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  calc
    (∑ v, graphQ (deleteVertex G v)) =
        ∑ v, (graphQ G + 1 - 2 * (G.degree v : ℝ)) := by
          apply Finset.sum_congr rfl
          intro v _
          exact graphQ_deleteVertex G v
    _ = (Fintype.card V : ℝ) * (graphQ G + 1) -
        2 * ∑ v, (G.degree v : ℝ) := by
          simp [Finset.sum_sub_distrib, Finset.mul_sum]
          ring
    _ = ((Fintype.card V : ℝ) - 2) * (graphQ G - 1) := by
          rw [hdegree]
          simp only [graphQ]
          ring

end GraphDeletion

section MatrixDeletion

variable [Fintype V] [DecidableEq V]

/-- Summing all principal vertex deletions counts off-diagonal entries
`n - 2` times and diagonal entries `n - 1` times. -/
lemma sum_totalMass_deleteMatrix (M : Matrix V V ℝ) :
    (∑ v, totalMass (deleteMatrix M v)) =
      ((Fintype.card V : ℝ) - 2) * totalMass M + M.trace := by
  simpa [totalMass, deleteMatrix, Matrix.trace, Matrix.diag] using
    (sum_delete_submatrices (fun i j ↦ M i j))

end MatrixDeletion

section SupportedMass

variable [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- For a graph-supported matrix, total mass is diagonal mass plus oriented
edge mass.  Symmetry is not needed for this stronger statement. -/
lemma totalMass_eq_trace_add_edgeMass_of_supported
    {M : Matrix V V ℝ} (hM : SupportedOn G M) :
    totalMass M = M.trace + edgeMass G M := by
  classical
  have hentry (i j : V) :
      M i j =
        (if i = j then M i j else 0) +
          (if G.Adj i j then M i j else 0) := by
    by_cases hij : i = j
    · subst j
      simp
    · by_cases hadj : G.Adj i j
      · simp [hij, hadj]
      · simp [hij, hadj, hM hij hadj]
  calc
    totalMass M = ∑ i, ∑ j,
        ((if i = j then M i j else 0) +
          (if G.Adj i j then M i j else 0)) := by
            unfold totalMass
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            exact hentry i j
    _ = (∑ i, ∑ j, if i = j then M i j else 0) +
        (∑ i, ∑ j, if G.Adj i j then M i j else 0) := by
          simp only [Finset.sum_add_distrib]
    _ = M.trace + edgeMass G M := by
          rw [edgeMass_eq_sum_if]
          simp [Matrix.trace, Matrix.diag]

end SupportedMass

section GraphCardinality

variable [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The real-valued cycle rank `m - n + 1`. -/
def graphCycleRank : ℝ :=
  (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) + 1

omit [DecidableEq V] in
lemma graphQ_edge_count_identity :
    4 * (G.edgeFinset.card : ℝ) =
      2 * graphQ G + 2 * ((Fintype.card V : ℝ) - 1) := by
  simp only [graphQ]
  ring

omit [DecidableEq V] in
lemma graphQ_sub_one_eq_card_sub_two_add_two_mul_cycleRank :
    graphQ G - 1 =
      ((Fintype.card V : ℝ) - 2) + 2 * graphCycleRank G := by
  simp only [graphQ, graphCycleRank]
  ring

omit [DecidableEq V] in
/-- The complete-graph edge bound in the cycle-rank normalization used in
Case 2. -/
lemma two_mul_graphCycleRank_le :
    2 * graphCycleRank G ≤
      ((Fintype.card V : ℝ) - 1) *
        ((Fintype.card V : ℝ) - 2) := by
  have hsimpleNat :
      G.edgeFinset.card ≤ (Fintype.card V).choose 2 :=
    G.card_edgeFinset_le_card_choose_two
  have hsimple :
      2 * (G.edgeFinset.card : ℝ) ≤
        (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
    have hcast :
        (G.edgeFinset.card : ℝ) ≤
          ((Fintype.card V).choose 2 : ℝ) := by
      exact_mod_cast hsimpleNat
    rw [Nat.cast_choose_two] at hcast
    linarith
  dsimp [graphCycleRank]
  linarith

omit [DecidableEq V] in
lemma one_le_graphQ_of_connected_of_three_le
    (hG : G.Connected) (hcard : 3 ≤ Fintype.card V) :
    1 ≤ graphQ G := by
  have hedges := connected_card_vertices_le_card_edges_add_one G hG
  have hn : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast hcard
  simp only [graphQ]
  linarith

end GraphCardinality

section ScalarOriented

/-- `averaged_estimate_of_sqrt_bound` in the oriented normalization. -/
lemma oriented_averaged_estimate_of_sqrt_bound
    {n q S T d₀ : ℝ}
    (hn : 2 < n) (hq : 1 ≤ q) (hS : 0 ≤ S)
    (hT : 0 ≤ T) (hd₀ : 0 ≤ d₀)
    (hbound :
      (n - 2) * S ≤
        √(((n - 2) * (q - 1)) * ((n - 2) * T + d₀))) :
    S ^ 2 ≤ (q - 1) * T + (q - 1) / (n - 2) * d₀ := by
  have hbound' :
      2 * (n - 2) * (S / 2) ≤
        √(((n - 2) * (q - 1)) * ((n - 2) * T + d₀)) := by
    convert hbound using 1
    ring
  have h :=
    averaged_estimate_of_sqrt_bound
      (S := S / 2) hn hq (by positivity) hT hd₀ hbound'
  convert h using 1
  ring

/-- Paper Case 1 with oriented edge and square-root masses. -/
lemma oriented_paper_case_one
    {m n q S d₀ w : ℝ}
    (hcount : 4 * m = 2 * q + 2 * (n - 1))
    (hflat : S ^ 2 ≤ 2 * m * w)
    (hthreshold : (n - 1) * w ≤ q * d₀) :
    S ^ 2 ≤ q * (d₀ + w) := by
  have h :=
    paper_case_one
      (S := S / 2) (w := w / 2) hcount
      (by convert hflat using 1 <;> ring)
      (by
        convert hthreshold using 1
        ring)
  convert h using 1 <;> ring

/-- Paper Case 2 with oriented edge and square-root masses. -/
lemma oriented_paper_case_two
    {n q β S d₀ w : ℝ}
    (hn : 2 < n) (hd₀ : 0 ≤ d₀)
    (hqβ : q - 1 = (n - 2) + 2 * β)
    (hsimple : 2 * β ≤ (n - 1) * (n - 2))
    (hthreshold : q * d₀ < (n - 1) * w)
    (haverage :
      S ^ 2 ≤
        (q - 1) * (d₀ + w) + (q - 1) / (n - 2) * d₀) :
    S ^ 2 ≤ q * (d₀ + w) := by
  have h :=
    paper_case_two
      (S := S / 2) (w := w / 2)
      hn hd₀ hqβ hsimple
      (by
        convert hthreshold using 1
        ring)
      (by convert haverage using 1 <;> ring)
  convert h using 1 <;> ring

end ScalarOriented

section AveragedInduction

variable [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/--
The oriented averaged estimate obtained by summing all vertex-deletion
induction hypotheses.
-/
lemma averaged_estimate_of_deleteVertex_IH
    (hG : G.Connected)
    (hcard : 3 ≤ Fintype.card V)
    (hdelete : ∀ v, (deleteVertex G v).Connected)
    {M : Matrix V V ℝ} (hM : DoublyNonnegative M)
    (hIH : ∀ v,
      edgeSqrtMass (deleteVertex G v) (deleteMatrix M v) ^ 2 ≤
        graphQ (deleteVertex G v) * totalMass (deleteMatrix M v)) :
    edgeSqrtMass G M ^ 2 ≤
      (graphQ G - 1) * totalMass M +
        (graphQ G - 1) / ((Fintype.card V : ℝ) - 2) * M.trace := by
  let qv : V → ℝ := fun v ↦ graphQ (deleteVertex G v)
  let Tv : V → ℝ := fun v ↦ totalMass (deleteMatrix M v)
  let Sv : V → ℝ :=
    fun v ↦ edgeSqrtMass (deleteVertex G v) (deleteMatrix M v)
  have hqv (v : V) : 0 ≤ qv v :=
    graphQ_nonneg (deleteVertex G v) (hdelete v)
  have hTv (v : V) : 0 ≤ Tv v :=
    (deleteMatrix_doublyNonnegative hM v).totalMass_nonneg
  have hSv (v : V) : 0 ≤ Sv v :=
    edgeSqrtMass_nonneg (deleteVertex G v) (deleteMatrix M v)
  have hroot (v : V) : Sv v ≤ √(qv v * Tv v) := by
    exact (sq_le_mul_iff_le_sqrt_mul (hSv v)
      (mul_nonneg (hqv v) (hTv v))).mp (hIH v)
  have hsumroot :
      (∑ v, Sv v) ≤
        √((∑ v, qv v) * (∑ v, Tv v)) := by
    calc
      (∑ v, Sv v) ≤ ∑ v, √(qv v * Tv v) :=
        Finset.sum_le_sum fun v _ ↦ hroot v
      _ ≤ √((∑ v, qv v) * (∑ v, Tv v)) :=
        sum_sqrt_mul_le_sqrt_sum_mul_sum Finset.univ qv Tv hqv hTv
  have hbound :
      ((Fintype.card V : ℝ) - 2) * edgeSqrtMass G M ≤
        √((((Fintype.card V : ℝ) - 2) * (graphQ G - 1)) *
          (((Fintype.card V : ℝ) - 2) * totalMass M + M.trace)) := by
    rw [← sum_edgeSqrtMass_deleteVertex G M,
      ← sum_graphQ_deleteVertex G,
      ← sum_totalMass_deleteMatrix M]
    exact hsumroot
  have hn : (2 : ℝ) < Fintype.card V := by
    exact_mod_cast (show 2 < Fintype.card V from lt_of_lt_of_le (by decide) hcard)
  exact oriented_averaged_estimate_of_sqrt_bound
    hn (one_le_graphQ_of_connected_of_three_le G hG hcard)
    (edgeSqrtMass_nonneg G M) hM.totalMass_nonneg
    hM.posSemidef.trace_nonneg hbound

end AveragedInduction

section NoCutStep

variable [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/--
The no-cut-vertex induction step for graph-supported doubly nonnegative
matrices.
-/
theorem noCutVertex_step
    (hG : G.Connected)
    (hcard : 3 ≤ Fintype.card V)
    (hdelete : ∀ v, (deleteVertex G v).Connected)
    {M : Matrix V V ℝ}
    (hM : DoublyNonnegative M)
    (hSupported : SupportedOn G M)
    (hIH : ∀ v,
      edgeSqrtMass (deleteVertex G v) (deleteMatrix M v) ^ 2 ≤
        graphQ (deleteVertex G v) * totalMass (deleteMatrix M v)) :
    edgeSqrtMass G M ^ 2 ≤ graphQ G * totalMass M := by
  let n : ℝ := Fintype.card V
  let m : ℝ := G.edgeFinset.card
  let q : ℝ := graphQ G
  let S : ℝ := edgeSqrtMass G M
  let d₀ : ℝ := M.trace
  let w : ℝ := edgeMass G M
  have htotal : totalMass M = d₀ + w := by
    exact totalMass_eq_trace_add_edgeMass_of_supported G hSupported
  have hn : 2 < n := by
    dsimp [n]
    exact_mod_cast (show 2 < Fintype.card V from lt_of_lt_of_le (by decide) hcard)
  have hd₀ : 0 ≤ d₀ := hM.posSemidef.trace_nonneg
  have hflat : S ^ 2 ≤ 2 * m * w := by
    exact edgeSqrtMass_sq_le_two_mul_card_edges_mul_edgeMass G hM.entrywise
  by_cases hcase : (n - 1) * w ≤ q * d₀
  · have hcaseOne : S ^ 2 ≤ q * (d₀ + w) :=
      oriented_paper_case_one
        (by
          dsimp [m, n, q]
          exact graphQ_edge_count_identity G)
        hflat hcase
    simpa [S, q, ← htotal] using hcaseOne
  · have hthreshold : q * d₀ < (n - 1) * w := lt_of_not_ge hcase
    have haverage :
        S ^ 2 ≤
          (q - 1) * (d₀ + w) + (q - 1) / (n - 2) * d₀ := by
      have havg :=
        averaged_estimate_of_deleteVertex_IH G hG hcard hdelete hM hIH
      simpa [S, q, n, d₀, htotal] using havg
    have hcaseTwo : S ^ 2 ≤ q * (d₀ + w) :=
      oriented_paper_case_two
        hn hd₀
        (by
          dsimp [q, n]
          exact graphQ_sub_one_eq_card_sub_two_add_two_mul_cycleRank G)
        (by
          dsimp [n]
          exact two_mul_graphCycleRank_le G)
        hthreshold haverage
    simpa [S, q, ← htotal] using hcaseTwo

end NoCutStep

end

end SquareEnergy
