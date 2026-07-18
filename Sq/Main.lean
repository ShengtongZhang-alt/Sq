/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Sq.Deduction

/-!
# The square-energy theorem

This file exposes the two component lower bounds and their combined final
form. The square energies use strict positive and strict negative filters, so
zero adjacency eigenvalues contribute to neither energy.
-/

namespace SquareEnergy

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The positive square energy of a nontrivial connected graph is at least
`|V| - 1`. -/
lemma card_sub_one_le_positiveSquareEnergy
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.Connected) :
    (Fintype.card V : ℝ) - 1 ≤ positiveSquareEnergy G :=
  card_sub_one_le_positiveSquareEnergy_of_negative_le_graphQ G
    (negativeSquareEnergy_le_graphQ G hG)

/-- The negative square energy of a nontrivial connected graph is at least
`|V| - 1`. -/
lemma card_sub_one_le_negativeSquareEnergy
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.Connected) :
    (Fintype.card V : ℝ) - 1 ≤ negativeSquareEnergy G :=
  card_sub_one_le_negativeSquareEnergy_of_positive_le_graphQ G
    (positiveSquareEnergy_le_graphQ G hG)

/--
Every finite connected simple undirected graph has both positive and negative
square energy at least `|V| - 1`. Adjacency eigenvalues are the real
eigenvalues counted with algebraic multiplicity; the strict sign filters omit
zero eigenvalues. The one-vertex graph is handled separately, while
connectedness excludes the zero-vertex case.
-/
theorem card_sub_one_le_min_squareEnergy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    (Fintype.card V : ℝ) - 1 ≤
      min (positiveSquareEnergy G) (negativeSquareEnergy G) := by
  by_cases hcard : Fintype.card V = 1
  · have hleft : (Fintype.card V : ℝ) - 1 = 0 := by
      norm_num [hcard]
    rw [hleft]
    exact le_min (positiveSquareEnergy_nonneg G) (negativeSquareEnergy_nonneg G)
  · have hcard_pos : 0 < Fintype.card V :=
      Fintype.card_pos_iff.mpr hG.nonempty
    have hcard_gt : 1 < Fintype.card V := by
      omega
    letI : Nontrivial V :=
      Fintype.one_lt_card_iff_nontrivial.mp hcard_gt
    exact le_min
      (card_sub_one_le_positiveSquareEnergy G hG)
      (card_sub_one_le_negativeSquareEnergy G hG)

end

end SquareEnergy
