/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Square-energy definitions

This file defines the adjacency eigenvalues of a finite simple graph and its
positive and negative square energies. Eigenvalues are indexed by the vertex
type and therefore counted with algebraic multiplicity; the strict sign
filters exclude zero eigenvalues from both energies.
-/

open scoped BigOperators

namespace SquareEnergy

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The adjacency eigenvalues of a finite simple graph, indexed with algebraic
multiplicity by its vertex type. -/
noncomputable def adjacencyEigenvalues
    (G : SimpleGraph V) [DecidableRel G.Adj] : V → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues

/-- The sum of the squares of the strictly positive adjacency eigenvalues. -/
noncomputable def positiveSquareEnergy
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ i with 0 < adjacencyEigenvalues G i, (adjacencyEigenvalues G i) ^ 2

/-- The sum of the squares of the strictly negative adjacency eigenvalues. -/
noncomputable def negativeSquareEnergy
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ i with adjacencyEigenvalues G i < 0, (adjacencyEigenvalues G i) ^ 2

end SquareEnergy
