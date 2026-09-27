/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphereInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Carrier

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem mapsTo_convexHull_of_mem_carrierFace
    (K L : Geometry.SimplicialComplex ℝ V) (hLK : IsSubdivision L K) {f : V → V}
    (hf : ∀ s ∈ L.faces, ∃ a : V →ᵃ[ℝ] V, EqOn f a (convexHull ℝ (s : Set V)))
    (hcarrier : ∀ v ∈ L.vertices, f v ∈ convexHull ℝ (carrierFace K v : Set V))
    {t : Finset V} (ht : t ∈ K.faces) :
    MapsTo f (convexHull ℝ (t : Set V)) (convexHull ℝ (t : Set V)) := by
  intro x hx
  obtain ⟨s, hs, hxs, hst⟩ := hLK.exists_face_subset_of_mem ht hx
  obtain ⟨a, ha⟩ := hf s hs
  have hverts : ∀ v ∈ s, a v ∈ convexHull ℝ (t : Set V) := by
    intro v hv
    have hvL : v ∈ L.vertices :=
      L.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hvK : v ∈ K.space := hLK.space_eq.subset (L.vertices_subset_space hvL)
    have hvt := hst (subset_convexHull ℝ (s : Set V) hv)
    rw [← ha (subset_convexHull ℝ (s : Set V) hv)]
    exact convexHull_mono (Finset.coe_subset.mpr (carrierFace_subset hvK ht hvt)) (hcarrier v hvL)
  rw [ha hxs]
  exact convexHull_min hverts ((convex_convexHull ℝ (t : Set V)).affine_preimage a) hxs

theorem mapsTo_space_of_mem_carrierFace
    (K L : Geometry.SimplicialComplex ℝ V) (hLK : IsSubdivision L K) {f : V → V}
    (hf : ∀ s ∈ L.faces, ∃ a : V →ᵃ[ℝ] V, EqOn f a (convexHull ℝ (s : Set V)))
    (hcarrier : ∀ v ∈ L.vertices, f v ∈ convexHull ℝ (carrierFace K v : Set V)) :
    MapsTo f K.space K.space := by
  intro x hx
  obtain ⟨t, ht, hxt⟩ := K.mem_space_iff.mp hx
  exact K.convexHull_subset_space ht (mapsTo_convexHull_of_mem_carrierFace K L hLK hf hcarrier ht
      hxt)

end Carrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem image_space_eq_of_mem_carrierFace {n : ℕ}
    (K L : Geometry.SimplicialComplex ℝ E) (hK : IsPLSphere (n + 1) K.space)
    (hLK : IsSubdivision L K) {f : E → E} (hfcont : ContinuousOn f K.space) (hfinj : InjOn f
        K.space)
    (hf : ∀ s ∈ L.faces, ∃ a : E →ᵃ[ℝ] E, EqOn f a (convexHull ℝ (s : Set E)))
    (hcarrier : ∀ v ∈ L.vertices, f v ∈ convexHull ℝ (carrierFace K v : Set E)) :
    f '' K.space = K.space :=
  hK.image_eq_of_mapsTo hfcont hfinj (mapsTo_space_of_mem_carrierFace K L hLK hf hcarrier)

end DifferentialGeometry.Topology.PiecewiseLinear
