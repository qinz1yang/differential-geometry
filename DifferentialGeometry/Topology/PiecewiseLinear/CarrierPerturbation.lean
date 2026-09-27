/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem carrierFace_eq_singleton {K : Geometry.SimplicialComplex ℝ E} {v : E}
    (hv : v ∈ K.vertices) : carrierFace K v = {v} := by
  have hx := K.vertices_subset_space hv
  have hsingle : v ∈ convexHull ℝ (({v} : Finset E) : Set E) := by simp
  apply Finset.Subset.antisymm (carrierFace_subset hx hv hsingle)
  exact face_subset_of_mem_openSimplex_of_mem_convexHull K hv (carrierFace_mem hx)
    (mem_openSimplex_singleton v) (mem_convexHull_carrierFace hx)

theorem eq_of_mem_affineSpan_carrierFace_of_mem_vertices
    {K : Geometry.SimplicialComplex ℝ E} {v w : E} (hv : v ∈ K.vertices)
    (hw : w ∈ affineSpan ℝ (carrierFace K v : Set E)) : w = v := by
  rw [carrierFace_eq_singleton hv, Finset.coe_singleton] at hw
  exact (AffineSubspace.mem_affineSpan_singleton ℝ E).mp hw

theorem eqOn_vertices_of_mem_affineSpan_carrierFace
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    {φ ψ : E → F} (hφ : MapsTo φ K.vertices L.vertices)
    (hψ : ∀ v ∈ K.vertices, ψ v ∈ affineSpan ℝ (carrierFace L (φ v) : Set F)) :
    EqOn ψ φ K.vertices :=
  fun _ hv => eq_of_mem_affineSpan_carrierFace_of_mem_vertices (hφ hv) (hψ _ hv)

theorem simplicialMap_eqOn_of_mem_affineSpan_carrierFace
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    {φ ψ : E → F} (hφ : MapsTo φ K.vertices L.vertices)
    (hψ : ∀ v ∈ K.vertices, ψ v ∈ affineSpan ℝ (carrierFace L (φ v) : Set F)) :
    EqOn (simplicialMap K ψ) (simplicialMap K φ) K.space :=
  simplicialMap_eqOn_of_eqOn_vertices K (eqOn_vertices_of_mem_affineSpan_carrierFace K L hφ hψ)

theorem doublePointSet_simplicialMap_eq_of_mem_affineSpan_carrierFace
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    {φ ψ : E → F} (hφ : MapsTo φ K.vertices L.vertices)
    (hψ : ∀ v ∈ K.vertices, ψ v ∈ affineSpan ℝ (carrierFace L (φ v) : Set F)) :
    doublePointSet (simplicialMap K ψ) K.space = doublePointSet (simplicialMap K φ) K.space := by
  have heq := simplicialMap_eqOn_of_mem_affineSpan_carrierFace K L hφ hψ
  ext y
  constructor
  · rintro ⟨a, ha, b, hb, hab, hay, hby⟩
    exact ⟨a, ha, b, hb, hab, (heq ha).symm.trans hay, (heq hb).symm.trans hby⟩
  · rintro ⟨a, ha, b, hb, hab, hay, hby⟩
    exact ⟨a, ha, b, hb, hab, (heq ha).trans hay, (heq hb).trans hby⟩

theorem not_disjoint_doublePointSet_vertices_of_mem_affineSpan_carrierFace
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    {φ ψ : E → F} (hφ : MapsTo φ K.vertices L.vertices)
    (hψ : ∀ v ∈ K.vertices, ψ v ∈ affineSpan ℝ (carrierFace L (φ v) : Set F))
    {a b : E} (ha : a ∈ K.vertices) (hb : b ∈ K.vertices) (hab : a ≠ b) (heq : φ a = φ b) :
    ¬ Disjoint (doublePointSet (simplicialMap K ψ) K.space) L.vertices := by
  rw [doublePointSet_simplicialMap_eq_of_mem_affineSpan_carrierFace K L hφ hψ]
  intro hd
  apply Set.disjoint_left.mp hd _ (hφ ha)
  exact ⟨a, K.vertices_subset_space ha, b, K.vertices_subset_space hb, hab,
    simplicialMap_vertex K φ ha, (simplicialMap_vertex K φ hb).trans heq.symm⟩

end DifferentialGeometry.Topology.PiecewiseLinear
