import Sq.Sparse.Basic
import Sq.Sparse.Scalar
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The cut-vertex induction step

This file proves the cut-vertex branch of the induction for the supported
sparse square-energy inequality.  The convention from `Sq.Sparse.Basic` is
used throughout: `edgeSqrtMass` is an oriented sum, so every unoriented edge
is counted twice.
-/

open scoped BigOperators

namespace SquareEnergy

open Matrix

noncomputable section

universe u

variable {V : Type u}

/-- The graph obtained by deleting `v`.  Its vertices remember that they are
different from `v`. -/
def deleteVertex (G : SimpleGraph V) (v : V) :
    SimpleGraph {x : V // x ≠ v} :=
  G.induce {x | x ≠ v}

@[simp]
lemma deleteVertex_adj (G : SimpleGraph V) (v : V)
    (x y : {x : V // x ≠ v}) :
    (deleteVertex G v).Adj x y ↔ G.Adj x.1 y.1 :=
  Iff.rfl

/-- The vertices of a component of `G - v`, viewed back in `V`. -/
def deletionComponentVertices (G : SimpleGraph V) (v : V)
    (C : (deleteVertex G v).ConnectedComponent) : Set V :=
  {x | ∃ hx : x ≠ v, (⟨x, hx⟩ : {x : V // x ≠ v}) ∈ C.supp}

@[simp]
lemma mem_deletionComponentVertices_iff (G : SimpleGraph V) (v x : V)
    (C : (deleteVertex G v).ConnectedComponent) :
    x ∈ deletionComponentVertices G v C ↔
      ∃ hx : x ≠ v, (⟨x, hx⟩ : {x : V // x ≠ v}) ∈ C.supp :=
  Iff.rfl

lemma deletionComponentVertices_nonempty (G : SimpleGraph V) (v : V)
    (C : (deleteVertex G v).ConnectedComponent) :
    (deletionComponentVertices G v C).Nonempty := by
  obtain ⟨x, hx⟩ := C.nonempty_supp
  exact ⟨x.1, x.2, hx⟩

lemma vertex_not_mem_deletionComponentVertices (G : SimpleGraph V) (v : V)
    (C : (deleteVertex G v).ConnectedComponent) :
    v ∉ deletionComponentVertices G v C := by
  rintro ⟨h, -⟩
  exact h rfl

/-- A component of the deletion, lifted to the original vertex type, still
induces a connected graph. -/
lemma connected_induce_deletionComponentVertices (G : SimpleGraph V) (v : V)
    (C : (deleteVertex G v).ConnectedComponent) :
    (G.induce (deletionComponentVertices G v C)).Connected := by
  let f :
      C.toSimpleGraph →g G.induce (deletionComponentVertices G v C) := {
    toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
    map_rel' := by
      intro x y hxy
      exact hxy
  }
  apply C.connected_toSimpleGraph.map f
  intro x
  rcases x with ⟨x, hx, hC⟩
  exact ⟨⟨⟨x, hx⟩, hC⟩, rfl⟩

/-- In a connected graph, every component left after deleting `v` has a
neighbor of `v`. -/
lemma deletionComponent_has_vertex_neighbor (G : SimpleGraph V) (v : V)
    (hG : G.Connected) (C : (deleteVertex G v).ConnectedComponent) :
    ∃ x ∈ deletionComponentVertices G v C, G.Adj v x := by
  obtain ⟨c, hc⟩ := C.nonempty_supp
  obtain ⟨p, hp⟩ := hG.exists_isPath v c.1
  obtain ⟨w, hvw, q, rfl⟩ := p.exists_eq_cons_of_ne c.2.symm
  have hvq : v ∉ q.support := by
    exact (List.nodup_cons.mp hp.support_nodup).1
  have hall : ∀ x ∈ q.support, x ∈ ({x : V | x ≠ v} : Set V) := by
    intro x hx hxv
    exact hvq (hxv ▸ hx)
  have hreach :
      (deleteVertex G v).Reachable
        (⟨w, hvw.ne.symm⟩ : {x : V // x ≠ v}) c := by
    refine ⟨?_⟩
    simpa [deleteVertex] using q.induce ({x : V | x ≠ v}) hall
  have hwC :
      (⟨w, hvw.ne.symm⟩ : {x : V // x ≠ v}) ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    calc
      (deleteVertex G v).connectedComponentMk
            (⟨w, hvw.ne.symm⟩ : {x : V // x ≠ v}) =
          (deleteVertex G v).connectedComponentMk c :=
        SimpleGraph.ConnectedComponent.sound hreach
      _ = C := (SimpleGraph.ConnectedComponent.mem_supp_iff C c).mp hc
  exact ⟨w, ⟨hvw.ne.symm, hwC⟩, hvw⟩

/-- Adding the deleted vertex back to one deletion component gives a
connected induced graph. -/
lemma connected_induce_component_insert_vertex (G : SimpleGraph V) (v : V)
    (hG : G.Connected) (C : (deleteVertex G v).ConnectedComponent) :
    (G.induce (deletionComponentVertices G v C ∪ {v})).Connected := by
  obtain ⟨x, hxC, hvx⟩ := deletionComponent_has_vertex_neighbor G v hG C
  have hsingle : (G.induce ({v} : Set V)).Preconnected := by
    intro a b
    have hab : a = b := Subtype.ext (by simpa using a.2.trans b.2.symm)
    subst b
    exact SimpleGraph.Reachable.rfl
  exact G.connected_induce_union
    (connected_induce_deletionComponentVertices G v C).preconnected
    hsingle hxC (by simp) hvx.symm

section FiniteGraph

variable [Fintype V] [DecidableEq V]

/-- Data of the two sides of a cut vertex.  `U` and `W` partition all
vertices other than `v`; the two side graphs overlap only at `v`. -/
structure CutPartition (G : SimpleGraph V) (v : V) where
  U : Finset V
  W : Finset V
  v_not_mem_U : v ∉ U
  v_not_mem_W : v ∉ W
  disjoint : Disjoint U W
  union_eq : U ∪ W = Finset.univ.erase v
  U_nonempty : U.Nonempty
  W_nonempty : W.Nonempty
  no_cross : ∀ ⦃u w⦄, u ∈ U → w ∈ W → ¬G.Adj u w
  left_connected :
    (G.induce (↑(insert v U) : Set V)).Connected
  right_connected :
    (G.induce (↑(insert v W) : Set V)).Connected
  left_card_lt : (insert v U).card < Fintype.card V
  right_card_lt : (insert v W).card < Fintype.card V

namespace CutPartition

variable {G : SimpleGraph V} {v : V}

/-- The vertices of the left side graph. -/
def leftVertices (P : CutPartition G v) : Finset V :=
  insert v P.U

/-- The vertices of the right side graph. -/
def rightVertices (P : CutPartition G v) : Finset V :=
  insert v P.W

/-- The graph induced by the left side and the separator. -/
def leftGraph (P : CutPartition G v) : SimpleGraph {x // x ∈ P.leftVertices} :=
  G.induce (↑P.leftVertices : Set V)

/-- The graph induced by the right side and the separator. -/
def rightGraph (P : CutPartition G v) : SimpleGraph {x // x ∈ P.rightVertices} :=
  G.induce (↑P.rightVertices : Set V)

instance instDecidableRelLeftGraph (P : CutPartition G v)
    [DecidableRel G.Adj] : DecidableRel P.leftGraph.Adj := by
  intro x y
  change Decidable (G.Adj x.1 y.1)
  infer_instance

instance instDecidableRelRightGraph (P : CutPartition G v)
    [DecidableRel G.Adj] : DecidableRel P.rightGraph.Adj := by
  intro x y
  change Decidable (G.Adj x.1 y.1)
  infer_instance

@[simp]
lemma leftVertices_eq (P : CutPartition G v) :
    P.leftVertices = insert v P.U :=
  rfl

@[simp]
lemma rightVertices_eq (P : CutPartition G v) :
    P.rightVertices = insert v P.W :=
  rfl

@[simp]
lemma mem_leftVertices (P : CutPartition G v) (x : V) :
    x ∈ P.leftVertices ↔ x = v ∨ x ∈ P.U := by
  simp [leftVertices]

@[simp]
lemma mem_rightVertices (P : CutPartition G v) (x : V) :
    x ∈ P.rightVertices ↔ x = v ∨ x ∈ P.W := by
  simp [rightVertices]

@[simp]
lemma separator_mem_leftVertices (P : CutPartition G v) :
    v ∈ P.leftVertices := by
  simp

@[simp]
lemma separator_mem_rightVertices (P : CutPartition G v) :
    v ∈ P.rightVertices := by
  simp

lemma leftGraph_connected (P : CutPartition G v) :
    P.leftGraph.Connected :=
  P.left_connected

lemma rightGraph_connected (P : CutPartition G v) :
    P.rightGraph.Connected :=
  P.right_connected

lemma card_left_lt (P : CutPartition G v) :
    Fintype.card {x // x ∈ P.leftVertices} < Fintype.card V := by
  rw [Fintype.card_coe]
  exact P.left_card_lt

lemma card_right_lt (P : CutPartition G v) :
    Fintype.card {x // x ∈ P.rightVertices} < Fintype.card V := by
  rw [Fintype.card_coe]
  exact P.right_card_lt

lemma vertex_mem_left_or_right (P : CutPartition G v) (x : V) :
    x ∈ P.leftVertices ∨ x ∈ P.rightVertices := by
  by_cases hx : x = v
  · simp [hx]
  have hxErase : x ∈ Finset.univ.erase v := by simp [hx]
  rw [← P.union_eq] at hxErase
  rcases Finset.mem_union.mp hxErase with hxU | hxW
  · exact Or.inl (by simp [leftVertices, hxU])
  · exact Or.inr (by simp [rightVertices, hxW])

lemma left_right_inter (P : CutPartition G v) :
    P.leftVertices ∩ P.rightVertices = {v} := by
  ext x
  constructor
  · simp only [Finset.mem_inter, mem_leftVertices, mem_rightVertices,
      Finset.mem_singleton]
    rintro ⟨hxv | hxU, hyv | hxW⟩
    · exact hxv
    · exact hxv
    · exact hyv
    · exact (Finset.disjoint_left.mp P.disjoint hxU hxW).elim
  · intro hx
    have hxv : x = v := Finset.mem_singleton.mp hx
    subst x
    simp

lemma adj_side (P : CutPartition G v) {x y : V} (hxy : G.Adj x y) :
    (x ∈ P.leftVertices ∧ y ∈ P.leftVertices) ∨
      (x ∈ P.rightVertices ∧ y ∈ P.rightVertices) := by
  by_cases hxv : x = v
  · subst x
    rcases P.vertex_mem_left_or_right y with hyL | hyR
    · exact Or.inl ⟨separator_mem_leftVertices P, hyL⟩
    · exact Or.inr ⟨separator_mem_rightVertices P, hyR⟩
  by_cases hyv : y = v
  · subst y
    rcases P.vertex_mem_left_or_right x with hxL | hxR
    · exact Or.inl ⟨hxL, separator_mem_leftVertices P⟩
    · exact Or.inr ⟨hxR, separator_mem_rightVertices P⟩
  have hxErase : x ∈ Finset.univ.erase v := by simp [hxv]
  have hyErase : y ∈ Finset.univ.erase v := by simp [hyv]
  rw [← P.union_eq] at hxErase hyErase
  rcases Finset.mem_union.mp hxErase with hxU | hxW
  · rcases Finset.mem_union.mp hyErase with hyU | hyW
    · exact Or.inl ⟨by simp [leftVertices, hxU], by simp [leftVertices, hyU]⟩
    · exact (P.no_cross hxU hyW hxy).elim
  · rcases Finset.mem_union.mp hyErase with hyU | hyW
    · exact (P.no_cross hyU hxW hxy.symm).elim
    · exact Or.inr ⟨by simp [rightVertices, hxW], by simp [rightVertices, hyW]⟩

end CutPartition

/-- A connected graph whose deletion at `v` is not preconnected admits a
two-sided cut partition. -/
theorem exists_cutPartition_of_not_preconnected_delete
    (G : SimpleGraph V) (v : V) (hG : G.Connected)
    (hdelete : ¬(deleteVertex G v).Preconnected) :
    Nonempty (CutPartition G v) := by
  classical
  change ¬(∀ x y, (deleteVertex G v).Reachable x y) at hdelete
  obtain ⟨a, ha⟩ := not_forall.mp hdelete
  obtain ⟨b, hab⟩ := not_forall.mp ha
  let C : (deleteVertex G v).ConnectedComponent :=
    (deleteVertex G v).connectedComponentMk a
  let U : Finset V := (deletionComponentVertices G v C).toFinset
  let W : Finset V := (Finset.univ.erase v) \ U
  have hvU : v ∉ U := by
    simp [U]
  have hUsub : U ⊆ Finset.univ.erase v := by
    intro x hx
    have hxC : x ∈ deletionComponentVertices G v C := by
      simpa [U] using hx
    exact Finset.mem_erase.mpr
      ⟨(fun hxv ↦ vertex_not_mem_deletionComponentVertices G v C (hxv ▸ hxC)),
        Finset.mem_univ x⟩
  have haU : a.1 ∈ U := by
    simp only [U, Set.mem_toFinset, mem_deletionComponentVertices_iff]
    exact ⟨a.2, by simp [C]⟩
  have hbU : b.1 ∉ U := by
    intro hbU
    have hbC : b ∈ C.supp := by
      have hbC' : b.1 ∈ deletionComponentVertices G v C := by
        simpa [U] using hbU
      rcases hbC' with ⟨hbv, hbC'⟩
      simpa only [Subtype.ext_iff] using hbC'
    have hba : (deleteVertex G v).Reachable b a := by
      apply SimpleGraph.ConnectedComponent.exact
      simpa [C] using
        (SimpleGraph.ConnectedComponent.mem_supp_iff C b).mp hbC
    exact hab hba.symm
  have hbW : b.1 ∈ W := by
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_erase.mpr ⟨b.2, Finset.mem_univ _⟩, hbU⟩
  have hUW : U ∪ W = Finset.univ.erase v := by
    exact Finset.union_sdiff_of_subset hUsub
  have hdisj : Disjoint U W := by
    exact Finset.disjoint_sdiff
  have hcross : ∀ ⦃u w⦄, u ∈ U → w ∈ W → ¬G.Adj u w := by
    intro u w hu hw huw
    have huC' : u ∈ deletionComponentVertices G v C := by
      simpa [U] using hu
    rcases huC' with ⟨huv, huC⟩
    have hwv : w ≠ v := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hw).1).1
    have hadj :
        (deleteVertex G v).Adj
          (⟨u, huv⟩ : {x : V // x ≠ v}) ⟨w, hwv⟩ := by
      exact huw
    have hwC :
        (⟨w, hwv⟩ : {x : V // x ≠ v}) ∈ C.supp :=
      (C.mem_supp_congr_adj hadj).mp huC
    have hwU : w ∈ U := by
      simp only [U, Set.mem_toFinset, mem_deletionComponentVertices_iff]
      exact ⟨hwv, hwC⟩
    exact (Finset.mem_sdiff.mp hw).2 hwU
  have hleft :
      (G.induce (↑(insert v U) : Set V)).Connected := by
    have hc := connected_induce_component_insert_vertex G v hG C
    have hset :
        (↑(insert v U) : Set V) =
          deletionComponentVertices G v C ∪ {v} := by
      ext x
      simp [U]
    rw [hset]
    exact hc
  have hright :
      (G.induce (↑(insert v W) : Set V)).Connected := by
    apply G.induce_connected_of_patches v (by simp)
    intro x hx
    by_cases hxv : x = v
    · subst x
      refine ⟨{v}, ?_, by simp, by simp, ?_⟩
      · intro y hy
        have hyv : y = v := by simpa using hy
        subst y
        simp
      · exact SimpleGraph.Reachable.rfl
    · have hxW : x ∈ W := by simpa [hxv] using hx
      let x' : {x : V // x ≠ v} := ⟨x, hxv⟩
      let D : (deleteVertex G v).ConnectedComponent :=
        (deleteVertex G v).connectedComponentMk x'
      have hDne : D ≠ C := by
        intro hDC
        have hxC :
            x ∈ deletionComponentVertices G v C := by
          refine ⟨hxv, ?_⟩
          have hxD : x' ∈ D.supp := by
            exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
          have hxC' : x' ∈ C.supp := hDC ▸ hxD
          simpa [x'] using hxC'
        have hxU : x ∈ U := by simpa [U] using hxC
        exact (Finset.mem_sdiff.mp hxW).2 hxU
      let s : Set V := deletionComponentVertices G v D ∪ {v}
      have hsv : v ∈ s := by simp [s]
      have hsx : x ∈ s := by
        left
        exact ⟨hxv, by simp [D, x']⟩
      refine ⟨s, ?_, hsv, hsx, ?_⟩
      · intro y hy
        rcases hy with hyD | hyv
        · rcases hyD with ⟨hyv, hyDmem⟩
          have hyNotU : y ∉ U := by
            intro hyU
            have hyC' : y ∈ deletionComponentVertices G v C := by
              simpa [U] using hyU
            rcases hyC' with ⟨hyv', hyCmem⟩
            have hDC : D = C := by
              apply SimpleGraph.ConnectedComponent.eq_of_common_vertex
                (v := (⟨y, hyv⟩ : {x : V // x ≠ v}))
              · exact hyDmem
              · simpa only [Subtype.ext_iff] using hyCmem
            exact hDne hDC
          simp only [Finset.mem_coe, Finset.mem_insert]
          exact Or.inr (Finset.mem_sdiff.mpr
            ⟨Finset.mem_erase.mpr ⟨hyv, Finset.mem_univ _⟩, hyNotU⟩)
        · have : y = v := by simpa using hyv
          simp [this]
      · exact (connected_induce_component_insert_vertex G v hG D).preconnected
          ⟨v, hsv⟩ ⟨x, hsx⟩
  have hVdisj : Disjoint (insert v U) W := by
    rw [Finset.disjoint_left]
    intro x hx hW
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp hW).1).1 rfl
    · exact (Finset.mem_sdiff.mp hW).2 hxU
  have hVunion : insert v U ∪ W = Finset.univ := by
    ext x
    by_cases hxv : x = v
    · simp [hxv]
    · have hxErase : x ∈ Finset.univ.erase v := by simp [hxv]
      rw [← hUW] at hxErase
      simpa [hxv] using hxErase
  have hcard :
      (insert v U).card + W.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hVdisj, hVunion,
      Finset.card_univ]
  have hWpos : 0 < W.card := Finset.card_pos.mpr ⟨b.1, hbW⟩
  have hleftCard : (insert v U).card < Fintype.card V := by
    omega
  have hrightDisj : Disjoint (insert v W) U := by
    rw [Finset.disjoint_left]
    intro x hx hU
    rcases Finset.mem_insert.mp hx with rfl | hxW
    · exact hvU hU
    · exact (Finset.mem_sdiff.mp hxW).2 hU
  have hrightUnion : insert v W ∪ U = Finset.univ := by
    rw [Finset.union_comm]
    simpa [Finset.union_assoc, Finset.union_left_comm,
      Finset.union_comm] using hVunion
  have hcardRight :
      (insert v W).card + U.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hrightDisj, hrightUnion,
      Finset.card_univ]
  have hUpos : 0 < U.card := Finset.card_pos.mpr ⟨a.1, haU⟩
  have hrightCard : (insert v W).card < Fintype.card V := by
    omega
  exact ⟨{
    U := U
    W := W
    v_not_mem_U := hvU
    v_not_mem_W := by
      intro hvW
      exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp hvW).1).1 rfl
    disjoint := hdisj
    union_eq := hUW
    U_nonempty := ⟨a.1, haU⟩
    W_nonempty := ⟨b.1, hbW⟩
    no_cross := hcross
    left_connected := hleft
    right_connected := hright
    left_card_lt := hleftCard
    right_card_lt := hrightCard
  }⟩

namespace CutPartition

variable {G : SimpleGraph V} {v : V} (P : CutPartition G v)

lemma left_right_edge_intersections_disjoint [DecidableRel G.Adj] :
    Disjoint
      (G.edgeFinset ∩ P.leftVertices.sym2)
      (G.edgeFinset ∩ P.rightVertices.sym2) := by
  classical
  rw [Finset.disjoint_left]
  intro e heL heR
  induction e using Sym2.inductionOn with
  | _ x y =>
      have heL' := Finset.mem_inter.mp heL
      have heR' := Finset.mem_inter.mp heR
      have hxy : G.Adj x y := by
        simpa [SimpleGraph.mem_edgeFinset] using heL'.1
      have hxL : x ∈ P.leftVertices := (Finset.mk_mem_sym2_iff.mp heL'.2).1
      have hyL : y ∈ P.leftVertices := (Finset.mk_mem_sym2_iff.mp heL'.2).2
      have hxR : x ∈ P.rightVertices := (Finset.mk_mem_sym2_iff.mp heR'.2).1
      have hyR : y ∈ P.rightVertices := (Finset.mk_mem_sym2_iff.mp heR'.2).2
      have hxv : x = v := by
        apply Finset.mem_singleton.mp
        rw [← P.left_right_inter]
        exact Finset.mem_inter.mpr ⟨hxL, hxR⟩
      have hyv : y = v := by
        apply Finset.mem_singleton.mp
        rw [← P.left_right_inter]
        exact Finset.mem_inter.mpr ⟨hyL, hyR⟩
      exact hxy.ne (hxv.trans hyv.symm)

lemma left_right_edge_intersections_union [DecidableRel G.Adj] :
    (G.edgeFinset ∩ P.leftVertices.sym2) ∪
        (G.edgeFinset ∩ P.rightVertices.sym2) =
      G.edgeFinset := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [Finset.mem_union, Finset.mem_inter,
        Finset.mk_mem_sym2_iff]
      constructor
      · rintro (⟨he, -⟩ | ⟨he, -⟩)
        · exact he
        · exact he
      · intro he
        have hxy : G.Adj x y := by
          simpa [SimpleGraph.mem_edgeFinset] using he
        rcases P.adj_side hxy with hL | hR
        · exact Or.inl ⟨he, hL⟩
        · exact Or.inr ⟨he, hR⟩

/-- The side edge sets partition the edge set of `G`. -/
lemma card_edges_left_add_right [DecidableRel G.Adj] :
    P.leftGraph.edgeFinset.card + P.rightGraph.edgeFinset.card =
      G.edgeFinset.card := by
  classical
  have hleft :
      P.leftGraph.edgeFinset.card =
        (G.edgeFinset ∩ P.leftVertices.sym2).card := by
    have hmap :
        P.leftGraph.edgeFinset.map
            (Function.Embedding.subtype (· ∈ P.leftVertices)).sym2Map =
          G.edgeFinset ∩ P.leftVertices.sym2 := by
      ext e
      induction e using Sym2.inductionOn with
      | _ x y =>
          constructor
          · intro he
            rw [Finset.mem_map] at he
            obtain ⟨a, ha, heq⟩ := he
            induction a using Sym2.inductionOn with
            | _ p q =>
                have hpqEdge : s(p, q) ∈ P.leftGraph.edgeSet :=
                  (P.leftGraph.mem_edgeFinset).mp ha
                have hpqSide : P.leftGraph.Adj p q :=
                  (P.leftGraph.mem_edgeSet).mp hpqEdge
                have hpq : G.Adj p.1 q.1 := by
                  exact hpqSide
                change s(p.1, q.1) = s(x, y) at heq
                rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact Finset.mem_inter.mpr
                    ⟨by simpa [SimpleGraph.mem_edgeFinset] using hpq,
                      Finset.mk_mem_sym2_iff.mpr ⟨p.2, q.2⟩⟩
                · exact Finset.mem_inter.mpr
                    ⟨by simpa [SimpleGraph.mem_edgeFinset] using hpq.symm,
                      Finset.mk_mem_sym2_iff.mpr ⟨q.2, p.2⟩⟩
          · intro he
            have he' := Finset.mem_inter.mp he
            have hxy : G.Adj x y := by
              simpa [SimpleGraph.mem_edgeFinset] using he'.1
            obtain ⟨hx, hy⟩ := Finset.mk_mem_sym2_iff.mp he'.2
            rw [Finset.mem_map]
            refine ⟨s((⟨x, hx⟩ : {z // z ∈ P.leftVertices}),
                (⟨y, hy⟩ : {z // z ∈ P.leftVertices})), ?_, rfl⟩
            apply (P.leftGraph.mem_edgeFinset).mpr
            apply (P.leftGraph.mem_edgeSet).mpr
            exact hxy
    rw [← hmap, Finset.card_map]
  have hright :
      P.rightGraph.edgeFinset.card =
        (G.edgeFinset ∩ P.rightVertices.sym2).card := by
    have hmap :
        P.rightGraph.edgeFinset.map
            (Function.Embedding.subtype (· ∈ P.rightVertices)).sym2Map =
          G.edgeFinset ∩ P.rightVertices.sym2 := by
      ext e
      induction e using Sym2.inductionOn with
      | _ x y =>
          constructor
          · intro he
            rw [Finset.mem_map] at he
            obtain ⟨a, ha, heq⟩ := he
            induction a using Sym2.inductionOn with
            | _ p q =>
                have hpqEdge : s(p, q) ∈ P.rightGraph.edgeSet :=
                  (P.rightGraph.mem_edgeFinset).mp ha
                have hpqSide : P.rightGraph.Adj p q :=
                  (P.rightGraph.mem_edgeSet).mp hpqEdge
                have hpq : G.Adj p.1 q.1 := by
                  exact hpqSide
                change s(p.1, q.1) = s(x, y) at heq
                rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact Finset.mem_inter.mpr
                    ⟨by simpa [SimpleGraph.mem_edgeFinset] using hpq,
                      Finset.mk_mem_sym2_iff.mpr ⟨p.2, q.2⟩⟩
                · exact Finset.mem_inter.mpr
                    ⟨by simpa [SimpleGraph.mem_edgeFinset] using hpq.symm,
                      Finset.mk_mem_sym2_iff.mpr ⟨q.2, p.2⟩⟩
          · intro he
            have he' := Finset.mem_inter.mp he
            have hxy : G.Adj x y := by
              simpa [SimpleGraph.mem_edgeFinset] using he'.1
            obtain ⟨hx, hy⟩ := Finset.mk_mem_sym2_iff.mp he'.2
            rw [Finset.mem_map]
            refine ⟨s((⟨x, hx⟩ : {z // z ∈ P.rightVertices}),
                (⟨y, hy⟩ : {z // z ∈ P.rightVertices})), ?_, rfl⟩
            apply (P.rightGraph.mem_edgeFinset).mpr
            apply (P.rightGraph.mem_edgeSet).mpr
            exact hxy
    rw [← hmap, Finset.card_map]
  rw [hleft, hright, ← Finset.card_union_of_disjoint
    P.left_right_edge_intersections_disjoint,
    P.left_right_edge_intersections_union]

lemma card_vertices_left_add_right :
    Fintype.card {x // x ∈ P.leftVertices} +
        Fintype.card {x // x ∈ P.rightVertices} =
      Fintype.card V + 1 := by
  classical
  rw [Fintype.card_coe, Fintype.card_coe]
  have hparts :
      P.U.card + P.W.card = (Finset.univ.erase v).card := by
    rw [← Finset.card_union_of_disjoint P.disjoint, P.union_eq]
  have herase :
      (Finset.univ.erase v).card = Fintype.card V - 1 :=
    Finset.card_erase_of_mem (Finset.mem_univ v)
  have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  simp only [leftVertices, rightVertices,
    Finset.card_insert_of_notMem P.v_not_mem_U,
    Finset.card_insert_of_notMem P.v_not_mem_W]
  omega

/-- The graph parameters of the two sides add to the graph parameter of the
original graph. -/
lemma graphQ_left_add_right [DecidableRel G.Adj] :
    graphQ P.leftGraph + graphQ P.rightGraph = graphQ G := by
  have hE := P.card_edges_left_add_right
  have hV := P.card_vertices_left_add_right
  have hEr :
      (P.leftGraph.edgeFinset.card : ℝ) +
          (P.rightGraph.edgeFinset.card : ℝ) =
        (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hE
  have hVr :
      (Fintype.card {x // x ∈ P.leftVertices} : ℝ) +
          (Fintype.card {x // x ∈ P.rightVertices} : ℝ) =
        (Fintype.card V : ℝ) + 1 := by
    exact_mod_cast hV
  simp only [graphQ]
  linarith

end CutPartition

/-- The finite set of oriented edges. -/
def orientedEdgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset ((_u : V) × V) :=
  Finset.univ.sigma fun u ↦ G.neighborFinset u

omit [DecidableEq V] in
@[simp]
lemma mem_orientedEdgeFinset_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (u w : V) :
    Sigma.mk u w ∈ orientedEdgeFinset G ↔ G.Adj u w := by
  simp [orientedEdgeFinset]

omit [DecidableEq V] in
lemma edgeSqrtMass_eq_sum_orientedEdgeFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : Matrix V V ℝ) :
    edgeSqrtMass G M =
      (orientedEdgeFinset G).sum fun e ↦ √(M e.1 e.2) := by
  exact Finset.sum_sigma' Finset.univ (fun u ↦ G.neighborFinset u)
    (fun u w ↦ √(M u w))

/-- The embedding of ordered pairs of vertices in a finite set back into the
ambient ordered-pair type. -/
def orientedSubtypeEmbedding (s : Finset V) :
    (((_u : {x // x ∈ s}) × {x // x ∈ s}) ↪ ((_u : V) × V)) where
  toFun e := Sigma.mk e.1.1 e.2.1
  inj' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    change
      (@Sigma.mk V (fun _ : V ↦ V) x.1 y.1) =
        (@Sigma.mk V (fun _ : V ↦ V) x'.1 y'.1) at h
    have hx : x = x' := Subtype.ext (congrArg Sigma.fst h)
    subst x'
    have hy : y = y' := Subtype.ext (by
      exact congrArg (fun e ↦ e.2) h)
    subst y'
    rfl

lemma map_orientedEdgeFinset_induce (G : SimpleGraph V)
    [DecidableRel G.Adj] (s : Finset V) :
    (orientedEdgeFinset (G.induce (↑s : Set V))).map
        (orientedSubtypeEmbedding s) =
      (orientedEdgeFinset G).filter
        (fun e ↦ e.1 ∈ s ∧ e.2 ∈ s) := by
  classical
  ext e
  rcases e with ⟨x, y⟩
  constructor
  · intro he
    rw [Finset.mem_map] at he
    obtain ⟨⟨x', y'⟩, hxy', heq⟩ := he
    change
      (@Sigma.mk V (fun _ : V ↦ V) x'.1 y'.1) =
        (@Sigma.mk V (fun _ : V ↦ V) x y) at heq
    have hx : x'.1 = x := congrArg Sigma.fst heq
    subst x
    have hy : y'.1 = y := by
      exact congrArg (fun e ↦ e.2) heq
    subst y
    simp only [Finset.mem_filter, mem_orientedEdgeFinset_iff]
    exact ⟨by simpa using hxy', x'.2, y'.2⟩
  · simp only [Finset.mem_filter, mem_orientedEdgeFinset_iff]
    rintro ⟨hxy, hx, hy⟩
    rw [Finset.mem_map]
    refine ⟨Sigma.mk (⟨x, hx⟩ : {z // z ∈ s}) (⟨y, hy⟩ : {z // z ∈ s}), ?_, rfl⟩
    simpa using hxy

/-- Oriented edge sums on an induced graph can be evaluated in the ambient
graph when all induced-edge entries are preserved. -/
lemma edgeSqrtMass_induce_eq_filtered_oriented_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V)
    (N : Matrix {x // x ∈ s} {x // x ∈ s} ℝ) (M : Matrix V V ℝ)
    (hentry : ∀ ⦃x y : {x // x ∈ s}⦄,
      (G.induce (↑s : Set V)).Adj x y → N x y = M x.1 y.1) :
    edgeSqrtMass (G.induce (↑s : Set V)) N =
      ((orientedEdgeFinset G).filter
          (fun e ↦ e.1 ∈ s ∧ e.2 ∈ s)).sum
        (fun e ↦ √(M e.1 e.2)) := by
  classical
  rw [edgeSqrtMass_eq_sum_orientedEdgeFinset]
  rw [← map_orientedEdgeFinset_induce G s]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e he
  rw [hentry (by simpa [orientedEdgeFinset] using he)]
  rfl

namespace CutPartition

variable {G : SimpleGraph V} {v : V} (P : CutPartition G v)

lemma filtered_oriented_edges_disjoint [DecidableRel G.Adj] :
    Disjoint
      ((orientedEdgeFinset G).filter
        (fun e ↦ e.1 ∈ P.leftVertices ∧ e.2 ∈ P.leftVertices))
      ((orientedEdgeFinset G).filter
        (fun e ↦ e.1 ∈ P.rightVertices ∧ e.2 ∈ P.rightVertices)) := by
  classical
  rw [Finset.disjoint_left]
  rintro ⟨x, y⟩ hx hy
  simp only [Finset.mem_filter, mem_orientedEdgeFinset_iff] at hx hy
  have hxv : x = v := by
    apply Finset.mem_singleton.mp
    rw [← P.left_right_inter]
    exact Finset.mem_inter.mpr ⟨hx.2.1, hy.2.1⟩
  have hyv : y = v := by
    apply Finset.mem_singleton.mp
    rw [← P.left_right_inter]
    exact Finset.mem_inter.mpr ⟨hx.2.2, hy.2.2⟩
  exact hx.1.ne (hxv.trans hyv.symm)

lemma filtered_oriented_edges_union [DecidableRel G.Adj] :
    ((orientedEdgeFinset G).filter
        (fun e ↦ e.1 ∈ P.leftVertices ∧ e.2 ∈ P.leftVertices)) ∪
      ((orientedEdgeFinset G).filter
        (fun e ↦ e.1 ∈ P.rightVertices ∧ e.2 ∈ P.rightVertices)) =
      orientedEdgeFinset G := by
  classical
  ext e
  rcases e with ⟨x, y⟩
  simp only [Finset.mem_union, Finset.mem_filter,
    mem_orientedEdgeFinset_iff]
  constructor
  · rintro (⟨hxy, -⟩ | ⟨hxy, -⟩)
    · exact hxy
    · exact hxy
  · intro hxy
    rcases P.adj_side hxy with hL | hR
    · exact Or.inl ⟨hxy, hL⟩
    · exact Or.inr ⟨hxy, hR⟩

/-- The two induced oriented edge sums add to the oriented edge sum of the
original graph, provided their edge entries agree with the original matrix. -/
lemma edgeSqrtMass_left_add_right
    [DecidableRel G.Adj]
    (M₁ : Matrix {x // x ∈ P.leftVertices} {x // x ∈ P.leftVertices} ℝ)
    (M₂ : Matrix {x // x ∈ P.rightVertices} {x // x ∈ P.rightVertices} ℝ)
    (M : Matrix V V ℝ)
    (h₁ : ∀ ⦃x y⦄, P.leftGraph.Adj x y → M₁ x y = M x.1 y.1)
    (h₂ : ∀ ⦃x y⦄, P.rightGraph.Adj x y → M₂ x y = M x.1 y.1) :
    edgeSqrtMass P.leftGraph M₁ + edgeSqrtMass P.rightGraph M₂ =
      edgeSqrtMass G M := by
  change
    edgeSqrtMass (G.induce (↑P.leftVertices : Set V)) M₁ +
        edgeSqrtMass (G.induce (↑P.rightVertices : Set V)) M₂ =
      edgeSqrtMass G M
  rw [edgeSqrtMass_induce_eq_filtered_oriented_sum G P.leftVertices M₁ M h₁,
    edgeSqrtMass_induce_eq_filtered_oriented_sum G P.rightVertices M₂ M h₂,
    edgeSqrtMass_eq_sum_orientedEdgeFinset]
  rw [← Finset.sum_union P.filtered_oriented_edges_disjoint,
    P.filtered_oriented_edges_union]

end CutPartition

/-- A positive semidefinite real matrix is a Gram matrix in a finite
Euclidean space. -/
lemma exists_eq_gram_of_posSemidef {I : Type*} [Finite I]
    {M : Matrix I I ℝ} (hM : M.PosSemidef) :
    ∃ (m : ℕ) (z : I → EuclideanSpace ℝ (Fin m)),
      M = Matrix.gram ℝ z := by
  obtain ⟨m, a, ha⟩ :=
    Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hM
  refine ⟨m, fun u ↦ WithLp.toLp 2 (fun k ↦ a k u), ?_⟩
  rw [ha]
  ext u w
  simp [Matrix.sum_apply, Matrix.gram_apply, Matrix.vecMulVec_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

/-- The total entry mass of a Gram matrix is the squared norm of the sum of
its representing vectors. -/
lemma totalMass_gram {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (z : I → E) :
    totalMass (Matrix.gram ℝ z) = ‖∑ i, z i‖ ^ 2 := by
  unfold totalMass
  simp only [Matrix.gram_apply]
  calc
    (∑ i, ∑ j, inner ℝ (z i) (z j)) =
        ∑ i, inner ℝ (z i) (∑ j, z j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (inner_sum Finset.univ z (z i)).symm
    _ = inner ℝ (∑ i, z i) (∑ j, z j) :=
      (sum_inner Finset.univ z _).symm
    _ = ‖∑ i, z i‖ ^ 2 := real_inner_self_eq_norm_sq _

namespace CutPartition

variable {G : SimpleGraph V} {v : V} (P : CutPartition G v)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Span of the Gram vectors on the open left side. -/
def leftSpan (z : V → E) : Submodule ℝ E :=
  Submodule.span ℝ (z '' (↑P.U : Set V))

/-- Span of the Gram vectors on the open right side. -/
def rightSpan (z : V → E) : Submodule ℝ E :=
  Submodule.span ℝ (z '' (↑P.W : Set V))

lemma mem_leftSpan (z : V → E) {u : V} (hu : u ∈ P.U) :
    z u ∈ P.leftSpan z := by
  apply Submodule.subset_span
  exact ⟨u, hu, rfl⟩

lemma mem_rightSpan (z : V → E) {w : V} (hw : w ∈ P.W) :
    z w ∈ P.rightSpan z := by
  apply Submodule.subset_span
  exact ⟨w, hw, rfl⟩

/-- Support on `G` makes the spans generated by the two open sides
orthogonal. -/
lemma rightSpan_le_leftSpan_orthogonal
    {M : Matrix V V ℝ} (hSupport : SupportedOn G M)
    (z : V → E) (hgram : M = Matrix.gram ℝ z) :
    P.rightSpan z ≤ (P.leftSpan z)ᗮ := by
  rw [rightSpan, Submodule.span_le]
  rintro y ⟨w, hw, rfl⟩
  apply (Submodule.mem_orthogonal (P.leftSpan z) (z w)).2
  intro x hx
  refine Submodule.span_induction ?_ (by simp) ?_ ?_ hx
  · rintro _ ⟨u, hu, rfl⟩
    have huw : u ≠ w := by
      intro huw
      subst w
      exact (Finset.disjoint_left.mp P.disjoint hu hw)
    have hnon : ¬G.Adj u w := P.no_cross hu hw
    have hzero : M u w = 0 := hSupport huw hnon
    simpa [hgram, Matrix.gram_apply] using hzero
  · intro x y hx hy hix hiy
    simp [inner_add_left, hix, hiy]
  · intro a x hx hix
    simp [inner_smul_left, hix]

/-- The sequential orthogonal-projection decomposition of the separator
Gram vector. -/
structure SeparatorProjection (z : V → E) where
  pU : E
  pW : E
  p0 : E
  separator_eq : z v = pU + pW + p0
  pU_mem_left : pU ∈ P.leftSpan z
  pW_mem_right : pW ∈ P.rightSpan z
  pW_mem_leftOrth : pW ∈ (P.leftSpan z)ᗮ
  pU_mem_rightOrth : pU ∈ (P.rightSpan z)ᗮ
  p0_mem_leftOrth : p0 ∈ (P.leftSpan z)ᗮ
  p0_mem_rightOrth : p0 ∈ (P.rightSpan z)ᗮ
  rightSpan_le_leftOrth : P.rightSpan z ≤ (P.leftSpan z)ᗮ

/-- Construct the separator decomposition by first projecting onto the left
span and then projecting the residual onto the right span. -/
def separatorProjection [FiniteDimensional ℝ E]
    {M : Matrix V V ℝ} (hSupport : SupportedOn G M)
    (z : V → E) (hgram : M = Matrix.gram ℝ z) :
    P.SeparatorProjection z := by
  let L : Submodule ℝ E := P.leftSpan z
  let R : Submodule ℝ E := P.rightSpan z
  let pU : E := L.starProjection (z v)
  let r : E := z v - pU
  let pW : E := R.starProjection r
  let p0 : E := r - pW
  have hpU : pU ∈ L := L.starProjection_apply_mem _
  have hrL : r ∈ Lᗮ := Submodule.sub_starProjection_mem_orthogonal _
  have hpW : pW ∈ R := R.starProjection_apply_mem _
  have hRL : R ≤ Lᗮ :=
    P.rightSpan_le_leftSpan_orthogonal hSupport z hgram
  have hpWL : pW ∈ Lᗮ := by
    exact hRL hpW
  have hp0R : p0 ∈ Rᗮ := Submodule.sub_starProjection_mem_orthogonal _
  have hp0L : p0 ∈ Lᗮ := by
    exact Submodule.sub_mem _ hrL hpWL
  have hpUR : pU ∈ Rᗮ := by
    apply (Submodule.mem_orthogonal R pU).2
    intro y hy
    have hyL : y ∈ Lᗮ := hRL hy
    have hzero : inner ℝ pU y = 0 :=
      (Submodule.mem_orthogonal L y).1 hyL pU hpU
    simpa [real_inner_comm] using hzero
  refine {
    pU := pU
    pW := pW
    p0 := p0
    separator_eq := ?_
    pU_mem_left := hpU
    pW_mem_right := hpW
    pW_mem_leftOrth := hpWL
    pU_mem_rightOrth := hpUR
    p0_mem_leftOrth := hp0L
    p0_mem_rightOrth := hp0R
    rightSpan_le_leftOrth := hRL
  }
  dsimp [p0, r]
  abel

namespace SeparatorProjection

variable {P : CutPartition G v} {z : V → E}

/-- The separator vector assigned to the left side. -/
def leftSeparator (S : P.SeparatorProjection z) : E :=
  S.pU + S.p0

/-- The separator vector assigned to the right side. -/
def rightSeparator (S : P.SeparatorProjection z) : E :=
  S.pW

lemma leftSeparator_add_rightSeparator (S : P.SeparatorProjection z) :
    S.leftSeparator + S.rightSeparator = z v := by
  rw [S.separator_eq]
  simp only [leftSeparator, rightSeparator]
  abel

lemma leftSeparator_inner_eq (S : P.SeparatorProjection z)
    {u : V} (hu : u ∈ P.U) :
    inner ℝ S.leftSeparator (z u) = inner ℝ (z v) (z u) := by
  have hzu : z u ∈ P.leftSpan z := P.mem_leftSpan z hu
  have hpWzero : inner ℝ S.pW (z u) = 0 :=
    (Submodule.mem_orthogonal' (P.leftSpan z) S.pW).1
      S.pW_mem_leftOrth (z u) hzu
  have hsep : S.leftSeparator = z v - S.pW := by
    rw [S.separator_eq]
    simp only [leftSeparator]
    abel
  rw [hsep, inner_sub_left, hpWzero, sub_zero]

lemma inner_leftSeparator_eq (S : P.SeparatorProjection z)
    {u : V} (hu : u ∈ P.U) :
    inner ℝ (z u) S.leftSeparator = inner ℝ (z u) (z v) := by
  simpa [real_inner_comm] using S.leftSeparator_inner_eq hu

lemma rightSeparator_inner_eq (S : P.SeparatorProjection z)
    {w : V} (hw : w ∈ P.W) :
    inner ℝ S.rightSeparator (z w) = inner ℝ (z v) (z w) := by
  have hzw : z w ∈ P.rightSpan z := P.mem_rightSpan z hw
  have hpUzero : inner ℝ S.pU (z w) = 0 :=
    (Submodule.mem_orthogonal' (P.rightSpan z) S.pU).1
      S.pU_mem_rightOrth (z w) hzw
  have hp0zero : inner ℝ S.p0 (z w) = 0 :=
    (Submodule.mem_orthogonal' (P.rightSpan z) S.p0).1
      S.p0_mem_rightOrth (z w) hzw
  rw [S.separator_eq]
  simp only [rightSeparator, inner_add_left, hpUzero, hp0zero,
    zero_add, add_zero]

lemma inner_rightSeparator_eq (S : P.SeparatorProjection z)
    {w : V} (hw : w ∈ P.W) :
    inner ℝ (z w) S.rightSeparator = inner ℝ (z w) (z v) := by
  simpa [real_inner_comm] using S.rightSeparator_inner_eq hw

/-- Gram vectors for the left side. -/
def leftVector (S : P.SeparatorProjection z) :
    {x // x ∈ P.leftVertices} → E :=
  fun x ↦ if x.1 = v then S.leftSeparator else z x.1

/-- Gram vectors for the right side. -/
def rightVector (S : P.SeparatorProjection z) :
    {x // x ∈ P.rightVertices} → E :=
  fun x ↦ if x.1 = v then S.rightSeparator else z x.1

@[simp]
lemma leftVector_separator (S : P.SeparatorProjection z) :
    S.leftVector ⟨v, P.separator_mem_leftVertices⟩ = S.leftSeparator := by
  simp [leftVector]

@[simp]
lemma rightVector_separator (S : P.SeparatorProjection z) :
    S.rightVector ⟨v, P.separator_mem_rightVertices⟩ = S.rightSeparator := by
  simp [rightVector]

lemma leftVector_of_mem_U (S : P.SeparatorProjection z)
    {u : V} (hu : u ∈ P.U) :
    S.leftVector ⟨u, by simp [CutPartition.leftVertices, hu]⟩ = z u := by
  have huv : u ≠ v := by
    intro huv
    subst u
    exact P.v_not_mem_U hu
  simp [leftVector, huv]

lemma rightVector_of_mem_W (S : P.SeparatorProjection z)
    {w : V} (hw : w ∈ P.W) :
    S.rightVector ⟨w, by simp [CutPartition.rightVertices, hw]⟩ = z w := by
  have hwv : w ≠ v := by
    intro hwv
    subst w
    exact P.v_not_mem_W hw
  simp [rightVector, hwv]

/-- Left side Gram matrix. -/
def leftMatrix (S : P.SeparatorProjection z) :
    Matrix {x // x ∈ P.leftVertices} {x // x ∈ P.leftVertices} ℝ :=
  Matrix.gram ℝ S.leftVector

/-- Right side Gram matrix. -/
def rightMatrix (S : P.SeparatorProjection z) :
    Matrix {x // x ∈ P.rightVertices} {x // x ∈ P.rightVertices} ℝ :=
  Matrix.gram ℝ S.rightVector

/-- Every off-diagonal left-side entry is inherited from the original Gram
matrix. -/
lemma leftMatrix_apply_of_ne (S : P.SeparatorProjection z)
    {M : Matrix V V ℝ} (hgram : M = Matrix.gram ℝ z)
    {x y : {x // x ∈ P.leftVertices}} (hxy : x ≠ y) :
    S.leftMatrix x y = M x.1 y.1 := by
  rw [leftMatrix, Matrix.gram_apply]
  by_cases hx : x.1 = v
  · by_cases hy : y.1 = v
    · exact (hxy (Subtype.ext (hx.trans hy.symm))).elim
    · have hyU : y.1 ∈ P.U :=
        (P.mem_leftVertices y.1).mp y.2 |>.resolve_left hy
      rw [leftVector, if_pos hx, leftVector, if_neg hy,
        S.leftSeparator_inner_eq hyU, hgram, Matrix.gram_apply]
      simp [hx]
  · by_cases hy : y.1 = v
    · have hxU : x.1 ∈ P.U :=
        (P.mem_leftVertices x.1).mp x.2 |>.resolve_left hx
      rw [leftVector, if_neg hx, leftVector, if_pos hy,
        S.inner_leftSeparator_eq hxU, hgram, Matrix.gram_apply]
      simp [hy]
    · rw [leftVector, if_neg hx, leftVector, if_neg hy,
        hgram, Matrix.gram_apply]

/-- Every off-diagonal right-side entry is inherited from the original Gram
matrix. -/
lemma rightMatrix_apply_of_ne (S : P.SeparatorProjection z)
    {M : Matrix V V ℝ} (hgram : M = Matrix.gram ℝ z)
    {x y : {x // x ∈ P.rightVertices}} (hxy : x ≠ y) :
    S.rightMatrix x y = M x.1 y.1 := by
  rw [rightMatrix, Matrix.gram_apply]
  by_cases hx : x.1 = v
  · by_cases hy : y.1 = v
    · exact (hxy (Subtype.ext (hx.trans hy.symm))).elim
    · have hyW : y.1 ∈ P.W :=
        (P.mem_rightVertices y.1).mp y.2 |>.resolve_left hy
      rw [rightVector, if_pos hx, rightVector, if_neg hy,
        S.rightSeparator_inner_eq hyW, hgram, Matrix.gram_apply]
      simp [hx]
  · by_cases hy : y.1 = v
    · have hxW : x.1 ∈ P.W :=
        (P.mem_rightVertices x.1).mp x.2 |>.resolve_left hx
      rw [rightVector, if_neg hx, rightVector, if_pos hy,
        S.inner_rightSeparator_eq hxW, hgram, Matrix.gram_apply]
      simp [hy]
    · rw [rightVector, if_neg hx, rightVector, if_neg hy,
        hgram, Matrix.gram_apply]

lemma leftMatrix_doublyNonnegative (S : P.SeparatorProjection z)
    {M : Matrix V V ℝ} (hM : DoublyNonnegative M)
    (hgram : M = Matrix.gram ℝ z) :
    DoublyNonnegative S.leftMatrix := by
  refine ⟨Matrix.posSemidef_gram ℝ S.leftVector, ?_⟩
  intro x y
  by_cases hxy : x = y
  · subst y
    exact real_inner_self_nonneg
  · rw [S.leftMatrix_apply_of_ne hgram hxy]
    exact hM.entry_nonneg x.1 y.1

lemma rightMatrix_doublyNonnegative (S : P.SeparatorProjection z)
    {M : Matrix V V ℝ} (hM : DoublyNonnegative M)
    (hgram : M = Matrix.gram ℝ z) :
    DoublyNonnegative S.rightMatrix := by
  refine ⟨Matrix.posSemidef_gram ℝ S.rightVector, ?_⟩
  intro x y
  by_cases hxy : x = y
  · subst y
    exact real_inner_self_nonneg
  · rw [S.rightMatrix_apply_of_ne hgram hxy]
    exact hM.entry_nonneg x.1 y.1

lemma leftMatrix_supportedOn (S : P.SeparatorProjection z) {M : Matrix V V ℝ}
    (hSupport : SupportedOn G M) (hgram : M = Matrix.gram ℝ z) :
    SupportedOn P.leftGraph S.leftMatrix := by
  intro x y hxy hnon
  rw [S.leftMatrix_apply_of_ne hgram hxy]
  apply hSupport
  · intro hval
    exact hxy (Subtype.ext hval)
  · exact hnon

lemma rightMatrix_supportedOn (S : P.SeparatorProjection z) {M : Matrix V V ℝ}
    (hSupport : SupportedOn G M) (hgram : M = Matrix.gram ℝ z) :
    SupportedOn P.rightGraph S.rightMatrix := by
  intro x y hxy hnon
  rw [S.rightMatrix_apply_of_ne hgram hxy]
  apply hSupport
  · intro hval
    exact hxy (Subtype.ext hval)
  · exact hnon

lemma leftMatrix_apply_of_adj (S : P.SeparatorProjection z)
    {M : Matrix V V ℝ} (hgram : M = Matrix.gram ℝ z)
    {x y : {x // x ∈ P.leftVertices}} (hxy : P.leftGraph.Adj x y) :
    S.leftMatrix x y = M x.1 y.1 :=
  S.leftMatrix_apply_of_ne hgram hxy.ne

lemma rightMatrix_apply_of_adj (S : P.SeparatorProjection z)
    {M : Matrix V V ℝ} (hgram : M = Matrix.gram ℝ z)
    {x y : {x // x ∈ P.rightVertices}} (hxy : P.rightGraph.Adj x y) :
    S.rightMatrix x y = M x.1 y.1 :=
  S.rightMatrix_apply_of_ne hgram hxy.ne

lemma sum_leftVector (S : P.SeparatorProjection z) :
    ∑ x, S.leftVector x = S.leftSeparator + ∑ u ∈ P.U, z u := by
  let f : V → E := fun x ↦ if x = v then S.leftSeparator else z x
  change (∑ x : {x // x ∈ P.leftVertices}, f x.1) =
    S.leftSeparator + ∑ u ∈ P.U, z u
  rw [← Finset.sum_subtype P.leftVertices (fun _ ↦ Iff.rfl) f]
  rw [leftVertices, Finset.sum_insert P.v_not_mem_U]
  simp only [f, if_pos]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  have huv : u ≠ v := by
    intro huv
    subst u
    exact P.v_not_mem_U hu
  simp [huv]

lemma sum_rightVector (S : P.SeparatorProjection z) :
    ∑ x, S.rightVector x = S.rightSeparator + ∑ w ∈ P.W, z w := by
  let f : V → E := fun x ↦ if x = v then S.rightSeparator else z x
  change (∑ x : {x // x ∈ P.rightVertices}, f x.1) =
    S.rightSeparator + ∑ w ∈ P.W, z w
  rw [← Finset.sum_subtype P.rightVertices (fun _ ↦ Iff.rfl) f]
  rw [rightVertices, Finset.sum_insert P.v_not_mem_W]
  simp only [f, if_pos]
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  have hwv : w ≠ v := by
    intro hwv
    subst w
    exact P.v_not_mem_W hw
  simp [hwv]

lemma sum_original_eq (_S : P.SeparatorProjection z) :
    ∑ x, z x =
      z v + (∑ u ∈ P.U, z u) + ∑ w ∈ P.W, z w := by
  calc
    (∑ x, z x) = z v + ∑ x ∈ Finset.univ.erase v, z x :=
      (Finset.add_sum_erase Finset.univ z (Finset.mem_univ v)).symm
    _ = z v + ∑ x ∈ P.U ∪ P.W, z x := by rw [P.union_eq]
    _ = z v + ((∑ u ∈ P.U, z u) + ∑ w ∈ P.W, z w) := by
      rw [Finset.sum_union P.disjoint]
    _ = _ := by abel

lemma sum_leftVector_add_sum_rightVector (S : P.SeparatorProjection z) :
    (∑ x, S.leftVector x) + (∑ x, S.rightVector x) = ∑ x, z x := by
  rw [S.sum_leftVector, S.sum_rightVector, S.sum_original_eq]
  rw [← S.leftSeparator_add_rightSeparator]
  abel

lemma inner_sum_leftVector_sum_rightVector (S : P.SeparatorProjection z) :
    inner ℝ (∑ x, S.leftVector x) (∑ x, S.rightVector x) = 0 := by
  have hsumU : (∑ u ∈ P.U, z u) ∈ P.leftSpan z :=
    (P.leftSpan z).sum_mem fun u hu ↦ P.mem_leftSpan z hu
  have hsumW : (∑ w ∈ P.W, z w) ∈ P.rightSpan z :=
    (P.rightSpan z).sum_mem fun w hw ↦ P.mem_rightSpan z hw
  have hright :
      S.rightSeparator + (∑ w ∈ P.W, z w) ∈ P.rightSpan z :=
    (P.rightSpan z).add_mem S.pW_mem_right hsumW
  have hpUzero :
      inner ℝ S.pU (S.rightSeparator + ∑ w ∈ P.W, z w) = 0 :=
    (Submodule.mem_orthogonal' (P.rightSpan z) S.pU).1
      S.pU_mem_rightOrth _ hright
  have hp0zero :
      inner ℝ S.p0 (S.rightSeparator + ∑ w ∈ P.W, z w) = 0 :=
    (Submodule.mem_orthogonal' (P.rightSpan z) S.p0).1
      S.p0_mem_rightOrth _ hright
  have hrightLeftOrth :
      S.rightSeparator + (∑ w ∈ P.W, z w) ∈ (P.leftSpan z)ᗮ := by
    exact (P.leftSpan z)ᗮ.add_mem S.pW_mem_leftOrth
      (S.rightSpan_le_leftOrth hsumW)
  have hsumUzero :
      inner ℝ (∑ u ∈ P.U, z u)
        (S.rightSeparator + ∑ w ∈ P.W, z w) = 0 :=
    (Submodule.mem_orthogonal (P.leftSpan z) _).1
      hrightLeftOrth _ hsumU
  rw [S.sum_leftVector, S.sum_rightVector]
  simp only [leftSeparator, inner_add_left, hpUzero, hp0zero,
    hsumUzero, zero_add]

lemma totalMass_left_add_right (S : P.SeparatorProjection z)
    {M : Matrix V V ℝ} (hgram : M = Matrix.gram ℝ z) :
    totalMass M = totalMass S.leftMatrix + totalMass S.rightMatrix := by
  rw [hgram, leftMatrix, rightMatrix, totalMass_gram, totalMass_gram,
    totalMass_gram]
  calc
    ‖∑ x, z x‖ ^ 2 =
        ‖(∑ x, S.leftVector x) + ∑ x, S.rightVector x‖ ^ 2 := by
      rw [S.sum_leftVector_add_sum_rightVector]
    _ = ‖∑ x, S.leftVector x‖ ^ 2 +
        ‖∑ x, S.rightVector x‖ ^ 2 := by
      simpa [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
          (∑ x, S.leftVector x) (∑ x, S.rightVector x)
          S.inner_sum_leftVector_sum_rightVector

lemma edgeSqrtMass_leftMatrix_add_rightMatrix
    [DecidableRel G.Adj] (S : P.SeparatorProjection z)
    {M : Matrix V V ℝ} (hgram : M = Matrix.gram ℝ z) :
    edgeSqrtMass P.leftGraph S.leftMatrix +
        edgeSqrtMass P.rightGraph S.rightMatrix =
      edgeSqrtMass G M := by
  exact P.edgeSqrtMass_left_add_right S.leftMatrix S.rightMatrix M
    (fun {_ _} hxy ↦ S.leftMatrix_apply_of_adj hgram hxy)
    (fun {_ _} hxy ↦ S.rightMatrix_apply_of_adj hgram hxy)

end SeparatorProjection

/-- The two side matrices supplied by the separator geometry, together with
all properties needed by the induction step. -/
structure OneSeparatorSplit [DecidableRel G.Adj] (M : Matrix V V ℝ) where
  leftMatrix :
    Matrix {x // x ∈ P.leftVertices} {x // x ∈ P.leftVertices} ℝ
  rightMatrix :
    Matrix {x // x ∈ P.rightVertices} {x // x ∈ P.rightVertices} ℝ
  left_dnn : DoublyNonnegative leftMatrix
  right_dnn : DoublyNonnegative rightMatrix
  left_supported : SupportedOn P.leftGraph leftMatrix
  right_supported : SupportedOn P.rightGraph rightMatrix
  left_edge_entry :
    ∀ ⦃x y⦄, P.leftGraph.Adj x y → leftMatrix x y = M x.1 y.1
  right_edge_entry :
    ∀ ⦃x y⦄, P.rightGraph.Adj x y → rightMatrix x y = M x.1 y.1
  edgeSqrtMass_eq :
    edgeSqrtMass P.leftGraph leftMatrix +
        edgeSqrtMass P.rightGraph rightMatrix =
      edgeSqrtMass G M
  totalMass_eq :
    totalMass M = totalMass leftMatrix + totalMass rightMatrix

/-- Package the Gram/projection construction into the reusable two-block
split used by the cut-vertex induction branch. -/
theorem oneSeparatorSplit [DecidableRel G.Adj]
    {M : Matrix V V ℝ} (hM : DoublyNonnegative M)
    (hSupport : SupportedOn G M) :
    Nonempty (P.OneSeparatorSplit M) := by
  obtain ⟨m, z, hgram⟩ := exists_eq_gram_of_posSemidef hM.posSemidef
  let S : P.SeparatorProjection z :=
    P.separatorProjection hSupport z hgram
  exact ⟨{
    leftMatrix := S.leftMatrix
    rightMatrix := S.rightMatrix
    left_dnn := S.leftMatrix_doublyNonnegative hM hgram
    right_dnn := S.rightMatrix_doublyNonnegative hM hgram
    left_supported := S.leftMatrix_supportedOn hSupport hgram
    right_supported := S.rightMatrix_supportedOn hSupport hgram
    left_edge_entry := fun {_ _} hxy ↦ S.leftMatrix_apply_of_adj hgram hxy
    right_edge_entry := fun {_ _} hxy ↦ S.rightMatrix_apply_of_adj hgram hxy
    edgeSqrtMass_eq := S.edgeSqrtMass_leftMatrix_add_rightMatrix hgram
    totalMass_eq := S.totalMass_left_add_right hgram
  }⟩

end CutPartition

/-- Scalar Cauchy--Schwarz in the normalization of the oriented sparse
inequality. -/
lemma sq_add_le_of_two_blocks {S₁ S₂ q₁ q₂ T₁ T₂ : ℝ}
    (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂)
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (h₁ : S₁ ^ 2 ≤ q₁ * T₁) (h₂ : S₂ ^ 2 ≤ q₂ * T₂) :
    (S₁ + S₂) ^ 2 ≤ (q₁ + q₂) * (T₁ + T₂) := by
  have hroot₁ : S₁ ≤ √(q₁ * T₁) :=
    (sq_le_mul_iff_le_sqrt_mul hS₁ (mul_nonneg hq₁ hT₁)).mp h₁
  have hroot₂ : S₂ ≤ √(q₂ * T₂) :=
    (sq_le_mul_iff_le_sqrt_mul hS₂ (mul_nonneg hq₂ hT₂)).mp h₂
  apply (sq_le_mul_iff_le_sqrt_mul
    (add_nonneg hS₁ hS₂)
    (mul_nonneg (add_nonneg hq₁ hq₂) (add_nonneg hT₁ hT₂))).mpr
  calc
    S₁ + S₂ ≤ √(q₁ * T₁) + √(q₂ * T₂) :=
      add_le_add hroot₁ hroot₂
    _ ≤ √((q₁ + q₂) * (T₁ + T₂)) :=
      sqrt_mul_add_sqrt_mul_le hq₁ hq₂ hT₁ hT₂

/-- Cut-vertex step with hypotheses stated directly for the two side graphs. -/
theorem supported_sparse_bound_of_cutPartition
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V}
    (P : CutPartition G v) {M : Matrix V V ℝ}
    (hM : DoublyNonnegative M) (hSupport : SupportedOn G M)
    (hleft :
      ∀ (N : Matrix {x // x ∈ P.leftVertices}
          {x // x ∈ P.leftVertices} ℝ),
        DoublyNonnegative N →
        SupportedOn P.leftGraph N →
        edgeSqrtMass P.leftGraph N ^ 2 ≤
          graphQ P.leftGraph * totalMass N)
    (hright :
      ∀ (N : Matrix {x // x ∈ P.rightVertices}
          {x // x ∈ P.rightVertices} ℝ),
        DoublyNonnegative N →
        SupportedOn P.rightGraph N →
        edgeSqrtMass P.rightGraph N ^ 2 ≤
          graphQ P.rightGraph * totalMass N) :
    edgeSqrtMass G M ^ 2 ≤ graphQ G * totalMass M := by
  classical
  let S := Classical.choice (P.oneSeparatorSplit hM hSupport)
  have h₁ := hleft S.leftMatrix S.left_dnn S.left_supported
  have h₂ := hright S.rightMatrix S.right_dnn S.right_supported
  have hcombine :
      (edgeSqrtMass P.leftGraph S.leftMatrix +
          edgeSqrtMass P.rightGraph S.rightMatrix) ^ 2 ≤
        (graphQ P.leftGraph + graphQ P.rightGraph) *
          (totalMass S.leftMatrix + totalMass S.rightMatrix) :=
    sq_add_le_of_two_blocks
      (edgeSqrtMass_nonneg P.leftGraph S.leftMatrix)
      (edgeSqrtMass_nonneg P.rightGraph S.rightMatrix)
      (graphQ_nonneg P.leftGraph P.leftGraph_connected)
      (graphQ_nonneg P.rightGraph P.rightGraph_connected)
      S.left_dnn.totalMass_nonneg S.right_dnn.totalMass_nonneg h₁ h₂
  rw [S.edgeSqrtMass_eq, P.graphQ_left_add_right,
    ← S.totalMass_eq] at hcombine
  exact hcombine

omit [DecidableEq V] in
/-- Induction-facing cut-vertex branch.  The induction hypothesis is supplied
for every strictly smaller connected finite graph. -/
theorem supported_sparse_bound_of_disconnected_delete
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hG : G.Connected) (hdelete : ¬(deleteVertex G v).Preconnected)
    {M : Matrix V V ℝ} (hM : DoublyNonnegative M)
    (hSupport : SupportedOn G M)
    (hsmaller :
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj],
        H.Connected →
        Fintype.card W < Fintype.card V →
        ∀ (N : Matrix W W ℝ),
          DoublyNonnegative N →
          SupportedOn H N →
          edgeSqrtMass H N ^ 2 ≤ graphQ H * totalMass N) :
    edgeSqrtMass G M ^ 2 ≤ graphQ G * totalMass M := by
  classical
  let P := Classical.choice
    (exists_cutPartition_of_not_preconnected_delete G v hG hdelete)
  apply supported_sparse_bound_of_cutPartition P hM hSupport
  · intro N hN hSupp
    exact hsmaller P.leftGraph P.leftGraph_connected P.card_left_lt
      N hN hSupp
  · intro N hN hSupp
    exact hsmaller P.rightGraph P.rightGraph_connected P.card_right_lt
      N hN hSupp

omit [Fintype V] [DecidableEq V] in
/-- A non-connected deletion with a nonempty vertex type is not
preconnected.  The nonemptiness assumption excludes the one-vertex
degeneracy in mathlib's definition of `Connected`. -/
lemma not_preconnected_delete_of_not_connected
    (G : SimpleGraph V) (v : V)
    (hne : Nonempty {x : V // x ≠ v})
    (hdelete : ¬(deleteVertex G v).Connected) :
    ¬(deleteVertex G v).Preconnected := by
  intro hpre
  letI : Nonempty {x : V // x ≠ v} := hne
  exact hdelete ⟨hpre⟩

omit [DecidableEq V] in
/-- Variant of the induction-facing theorem using mathlib's `¬ Connected`
form of disconnectedness. -/
theorem supported_sparse_bound_of_not_connected_delete
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hG : G.Connected)
    (hne : Nonempty {x : V // x ≠ v})
    (hdelete : ¬(deleteVertex G v).Connected)
    {M : Matrix V V ℝ} (hM : DoublyNonnegative M)
    (hSupport : SupportedOn G M)
    (hsmaller :
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj],
        H.Connected →
        Fintype.card W < Fintype.card V →
        ∀ (N : Matrix W W ℝ),
          DoublyNonnegative N →
          SupportedOn H N →
          edgeSqrtMass H N ^ 2 ≤ graphQ H * totalMass N) :
    edgeSqrtMass G M ^ 2 ≤ graphQ G * totalMass M :=
  supported_sparse_bound_of_disconnected_delete G v hG
    (not_preconnected_delete_of_not_connected G v hne hdelete)
    hM hSupport hsmaller

end FiniteGraph

end

end SquareEnergy
