/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplementLink

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem restrict_eq_of_subcomplex (K A : Geometry.SimplicialComplex ℝ E)
    (hAK : A.faces ⊆ K.faces) : restrict K A.space = A := by
  ext s
  rw [mem_restrict_faces_iff_of_faces_subset K K A subset_rfl hAK]
  exact ⟨And.right, fun h => ⟨hAK h, h⟩⟩

theorem restrict_convexHull_eq_simplexComplex (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) :
    restrict K (convexHull ℝ (s : Set E)) = simplexComplex s (K.indep hs) := by
  rw [← simplexComplex_space s (K.indep hs) (K.nonempty_of_mem_faces hs)]
  exact restrict_eq_of_subcomplex K _ (fun t ht => K.down_closed hs ht.2 ht.1)

theorem mem_restrict_convexHull_faces_iff (K : Geometry.SimplicialComplex ℝ E)
    {s e : Finset E} (hs : s ∈ K.faces) :
    e ∈ (restrict K (convexHull ℝ (s : Set E))).faces ↔ e.Nonempty ∧ e ⊆ s := by
  rw [restrict_convexHull_eq_simplexComplex K hs]
  rfl

end DifferentialGeometry.Topology.PiecewiseLinear
