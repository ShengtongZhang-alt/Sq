import Mathlib.Algebra.Order.Star.Real
import Sq.Sparse.Basic

/-!
# Folding off-diagonal nonedges onto the diagonal

For every unordered nonedge `{u, v}`, the folding operation adds

`M u v • (e_u - e_v) (e_u - e_v)ᵀ`.

The use of `Sym2 V` makes the sum genuinely unordered.  The Hermitian
hypothesis makes the displayed summand independent of which endpoint is
named first.
-/

open scoped BigOperators

namespace SquareEnergy

open Matrix

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- The vector `e_u - e_v`. -/
def basisDiff (u v : V) : V → ℝ :=
  Pi.single u 1 - Pi.single v 1

@[simp]
lemma basisDiff_self (u : V) : basisDiff u u = 0 := by
  ext i
  simp [basisDiff]

lemma basisDiff_swap (u v : V) : basisDiff v u = -basisDiff u v := by
  ext i
  simp [basisDiff]

@[simp]
lemma basisDiff_apply_left {u v : V} (huv : u ≠ v) :
    basisDiff u v u = 1 := by
  simp [basisDiff, huv]

@[simp]
lemma basisDiff_apply_right {u v : V} (huv : u ≠ v) :
    basisDiff u v v = -1 := by
  simp [basisDiff, huv]

lemma basisDiff_apply_of_ne {u v i : V} (hiu : i ≠ u) (hiv : i ≠ v) :
    basisDiff u v i = 0 := by
  simp [basisDiff, hiu, hiv]

@[simp]
lemma sum_basisDiff [Fintype V] (u v : V) : ∑ i, basisDiff u v i = 0 := by
  simp [basisDiff, Pi.single_apply, Finset.sum_sub_distrib]

/--
The positive-semidefinite rank-one correction belonging to an unordered
pair.  For a Hermitian real matrix, the coefficient `M u v` is independent
of the orientation of the pair.
-/
def rankOneCorrection (M : Matrix V V ℝ) (hM : M.IsHermitian) :
    Sym2 V → Matrix V V ℝ :=
  Sym2.lift
    ⟨fun u v ↦
        M u v • Matrix.vecMulVec (basisDiff u v) (star (basisDiff u v)),
      by
        intro u v
        have huv : M u v = M v u := by
          simpa using hM.apply v u
        change
          M u v • Matrix.vecMulVec (basisDiff u v) (star (basisDiff u v)) =
            M v u • Matrix.vecMulVec (basisDiff v u) (star (basisDiff v u))
        have hOuter :
            Matrix.vecMulVec (basisDiff u v) (star (basisDiff u v)) =
              Matrix.vecMulVec (basisDiff v u) (star (basisDiff v u)) := by
          rw [basisDiff_swap u v]
          ext i j
          simp [Matrix.vecMulVec_apply]
        rw [huv, hOuter]⟩

@[simp]
lemma rankOneCorrection_mk (M : Matrix V V ℝ) (hM : M.IsHermitian)
    (u v : V) :
    rankOneCorrection M hM s(u, v) =
      M u v • Matrix.vecMulVec (basisDiff u v) (star (basisDiff u v)) :=
  rfl

section Finite

variable [Fintype V]

/-- The finite set of unordered pairs of distinct, nonadjacent vertices. -/
def nonedgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Sym2 V) :=
  Finset.univ.filter fun e ↦ ¬e.IsDiag ∧ e ∉ G.edgeFinset

@[simp]
lemma mk_mem_nonedgeFinset_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) :
    s(u, v) ∈ nonedgeFinset G ↔ u ≠ v ∧ ¬G.Adj u v := by
  simp [nonedgeFinset, SimpleGraph.mem_edgeFinset]

/-- The sum of all unordered nonedge rank-one corrections. -/
def foldingCorrection (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Matrix V V ℝ) (hM : M.IsHermitian) : Matrix V V ℝ :=
  ∑ e ∈ nonedgeFinset G, rankOneCorrection M hM e

/-- Fold every off-diagonal nonedge entry of `M` onto the diagonal. -/
def foldNonedges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Matrix V V ℝ) (hM : M.IsHermitian) : Matrix V V ℝ :=
  M + foldingCorrection G M hM

omit [Fintype V] in
lemma rankOneCorrection_posSemidef [Finite V] {M : Matrix V V ℝ}
    (hM : M.IsHermitian) (hEntry : EntrywiseNonnegative M) (e : Sym2 V) :
    (rankOneCorrection M hM e).PosSemidef := by
  induction e using Sym2.inductionOn with | hf u v
  rw [rankOneCorrection_mk]
  exact (Matrix.posSemidef_vecMulVec_self_star (basisDiff u v)).smul
    (hEntry u v)

lemma foldingCorrection_posSemidef (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Matrix V V ℝ} (hM : M.IsHermitian)
    (hEntry : EntrywiseNonnegative M) :
    (foldingCorrection G M hM).PosSemidef := by
  exact Matrix.posSemidef_sum (nonedgeFinset G) fun e _ ↦
    rankOneCorrection_posSemidef hM hEntry e

lemma foldNonedges_posSemidef (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Matrix V V ℝ} (hPSD : M.PosSemidef)
    (hEntry : EntrywiseNonnegative M) :
    (foldNonedges G M hPSD.isHermitian).PosSemidef :=
  hPSD.add (foldingCorrection_posSemidef G hPSD.isHermitian hEntry)

omit [Fintype V] in
/--
Away from the diagonal, one rank-one correction is nonzero only at the
ordered entries belonging to its own unordered pair.
-/
lemma rankOneCorrection_apply_offdiag {M : Matrix V V ℝ}
    (hM : M.IsHermitian) (e : Sym2 V) {i j : V} (hij : i ≠ j) :
    rankOneCorrection M hM e i j =
      if e = s(i, j) then -M i j else 0 := by
  induction e using Sym2.inductionOn with | hf u v
  have huv : M u v = M v u := by
    simpa using hM.apply v u
  by_cases heq : s(u, v) = s(i, j)
  · rw [if_pos heq]
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [basisDiff, Matrix.vecMulVec_apply, hij]
    · simp [basisDiff, Matrix.vecMulVec_apply, hij, huv]
  · rw [if_neg heq]
    have hz :
        (i ≠ u ∧ i ≠ v) ∨ (j ≠ u ∧ j ≠ v) := by
      by_cases hi : i = u ∨ i = v
      · by_cases hj : j = u ∨ j = v
        · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
          · exact (hij rfl).elim
          · exact (heq rfl).elim
          · exact (heq Sym2.eq_swap).elim
          · exact (hij rfl).elim
        · exact Or.inr ⟨fun h ↦ hj (Or.inl h), fun h ↦ hj (Or.inr h)⟩
      · exact Or.inl ⟨fun h ↦ hi (Or.inl h), fun h ↦ hi (Or.inr h)⟩
    rcases hz with hi | hj
    · simp [rankOneCorrection_mk, Matrix.vecMulVec_apply,
        basisDiff_apply_of_ne hi.1 hi.2]
    · simp [rankOneCorrection_mk, Matrix.vecMulVec_apply,
        basisDiff_apply_of_ne hj.1 hj.2]

/-- Entry formula for the whole correction sum away from the diagonal. -/
lemma foldingCorrection_apply_offdiag (G : SimpleGraph V)
    [DecidableRel G.Adj] {M : Matrix V V ℝ} (hM : M.IsHermitian)
    {i j : V} (hij : i ≠ j) :
    foldingCorrection G M hM i j =
      if G.Adj i j then 0 else -M i j := by
  classical
  by_cases hadj : G.Adj i j
  · have hnot : s(i, j) ∉ nonedgeFinset G := by
      simp [hij, hadj]
    rw [foldingCorrection, Matrix.sum_apply]
    simp_rw [rankOneCorrection_apply_offdiag hM _ hij]
    simp [hnot, hadj]
  · have hmem : s(i, j) ∈ nonedgeFinset G := by
      simp [hij, hadj]
    rw [foldingCorrection, Matrix.sum_apply]
    simp_rw [rankOneCorrection_apply_offdiag hM _ hij]
    simp [hmem, hadj]

/-- Complete off-diagonal entry formula for the folded matrix. -/
lemma foldNonedges_apply_offdiag (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Matrix V V ℝ} (hM : M.IsHermitian) {i j : V} (hij : i ≠ j) :
    foldNonedges G M hM i j =
      if G.Adj i j then M i j else 0 := by
  rw [foldNonedges, Matrix.add_apply,
    foldingCorrection_apply_offdiag G hM hij]
  by_cases hadj : G.Adj i j <;> simp [hadj]

/-- Folding preserves every edge entry. -/
lemma foldNonedges_apply_of_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Matrix V V ℝ} (hM : M.IsHermitian) {i j : V}
    (hij : G.Adj i j) :
    foldNonedges G M hM i j = M i j := by
  rw [foldNonedges_apply_offdiag G hM hij.ne]
  simp [hij]

/-- Folding zeros every off-diagonal nonedge entry. -/
lemma foldNonedges_apply_of_nonedge (G : SimpleGraph V)
    [DecidableRel G.Adj] {M : Matrix V V ℝ} (hM : M.IsHermitian)
    {i j : V} (hne : i ≠ j) (hij : ¬G.Adj i j) :
    foldNonedges G M hM i j = 0 := by
  rw [foldNonedges_apply_offdiag G hM hne]
  simp [hij]

omit [Fintype V] in
lemma rankOneCorrection_apply_diag_nonneg {M : Matrix V V ℝ}
    (hM : M.IsHermitian) (hEntry : EntrywiseNonnegative M)
    (e : Sym2 V) (i : V) :
    0 ≤ rankOneCorrection M hM e i i := by
  induction e using Sym2.inductionOn with | hf u v
  rw [rankOneCorrection_mk]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    star_trivial]
  exact mul_nonneg (hEntry u v) (mul_self_nonneg (basisDiff u v i))

lemma foldingCorrection_apply_diag_nonneg (G : SimpleGraph V)
    [DecidableRel G.Adj] {M : Matrix V V ℝ} (hM : M.IsHermitian)
    (hEntry : EntrywiseNonnegative M) (i : V) :
    0 ≤ foldingCorrection G M hM i i := by
  rw [foldingCorrection, Matrix.sum_apply]
  exact Finset.sum_nonneg fun e _ ↦
    rankOneCorrection_apply_diag_nonneg hM hEntry e i

/-- Folding preserves entrywise nonnegativity. -/
lemma foldNonedges_entrywiseNonnegative (G : SimpleGraph V)
    [DecidableRel G.Adj] {M : Matrix V V ℝ} (hM : M.IsHermitian)
    (hEntry : EntrywiseNonnegative M) :
    EntrywiseNonnegative (foldNonedges G M hM) := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [foldNonedges, Matrix.add_apply]
    exact add_nonneg (hEntry i i)
      (foldingCorrection_apply_diag_nonneg G hM hEntry i)
  · rw [foldNonedges_apply_offdiag G hM hij]
    by_cases hadj : G.Adj i j
    · simp [hadj, hEntry i j]
    · simp [hadj]

/-- The folded matrix is supported on the graph. -/
lemma foldNonedges_supportedOn (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Matrix V V ℝ} (hM : M.IsHermitian) :
    SupportedOn G (foldNonedges G M hM) := by
  intro i j hij hnonedge
  exact foldNonedges_apply_of_nonedge G hM hij hnonedge

/-- Folding a DNN matrix produces a graph-supported DNN matrix. -/
lemma foldNonedges_doublyNonnegative (G : SimpleGraph V)
    [DecidableRel G.Adj] {M : Matrix V V ℝ}
    (hM : DoublyNonnegative M) :
    DoublyNonnegative (foldNonedges G M hM.isHermitian) :=
  ⟨foldNonedges_posSemidef G hM.posSemidef hM.entrywise,
    foldNonedges_entrywiseNonnegative G hM.isHermitian hM.entrywise⟩

/-- Each rank-one correction has zero total mass. -/
lemma totalMass_rankOneCorrection {M : Matrix V V ℝ}
    (hM : M.IsHermitian) (e : Sym2 V) :
    totalMass (rankOneCorrection M hM e) = 0 := by
  induction e using Sym2.inductionOn with | hf u v
  rw [rankOneCorrection_mk, totalMass_smul]
  change
    M u v *
      totalMass (Matrix.vecMulVec (basisDiff u v) (basisDiff u v)) = 0
  unfold totalMass
  simp only [Matrix.vecMulVec_apply]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_basisDiff]
  simp

lemma totalMass_foldingCorrection (G : SimpleGraph V)
    [DecidableRel G.Adj] {M : Matrix V V ℝ} (hM : M.IsHermitian) :
    totalMass (foldingCorrection G M hM) = 0 := by
  rw [foldingCorrection, totalMass_finset_sum]
  simp [totalMass_rankOneCorrection hM]

/-- Folding preserves the sum of all matrix entries. -/
lemma totalMass_foldNonedges (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Matrix V V ℝ} (hM : M.IsHermitian) :
    totalMass (foldNonedges G M hM) = totalMass M := by
  rw [foldNonedges, totalMass_add, totalMass_foldingCorrection]
  simp

/-- Folding preserves the oriented edge-entry mass. -/
lemma edgeMass_foldNonedges (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Matrix V V ℝ} (hM : M.IsHermitian) :
    edgeMass G (foldNonedges G M hM) = edgeMass G M := by
  apply edgeMass_congr G
  intro i j hij
  exact foldNonedges_apply_of_adj G hM hij

/-- Folding preserves the oriented square-root edge mass. -/
lemma edgeSqrtMass_foldNonedges (G : SimpleGraph V)
    [DecidableRel G.Adj] {M : Matrix V V ℝ} (hM : M.IsHermitian) :
    edgeSqrtMass G (foldNonedges G M hM) = edgeSqrtMass G M := by
  apply edgeSqrtMass_congr G
  intro i j hij
  exact foldNonedges_apply_of_adj G hM hij

omit [DecidableEq V] in
/--
Reduction from the graph-supported sparse inequality to the same inequality
for arbitrary DNN matrices.  The sparse theorem itself is supplied as a
higher-order hypothesis, so this statement is independent of its eventual
name and proof.
-/
theorem supported_sparse_inequality_implies_unrestricted
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hSupported :
      ∀ (N : Matrix V V ℝ),
        DoublyNonnegative N →
        SupportedOn G N →
        edgeSqrtMass G N ^ 2 ≤ graphQ G * totalMass N)
    {M : Matrix V V ℝ} (hM : DoublyNonnegative M) :
    edgeSqrtMass G M ^ 2 ≤ graphQ G * totalMass M := by
  classical
  have hFold :=
    hSupported (foldNonedges G M hM.isHermitian)
      (foldNonedges_doublyNonnegative G hM)
      (foldNonedges_supportedOn G hM.isHermitian)
  rwa [edgeSqrtMass_foldNonedges G hM.isHermitian,
    totalMass_foldNonedges G hM.isHermitian] at hFold

end Finite

end

end SquareEnergy
