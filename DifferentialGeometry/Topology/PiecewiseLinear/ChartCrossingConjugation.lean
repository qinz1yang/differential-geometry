/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallUpdate
import DifferentialGeometry.Topology.PiecewiseLinear.SlabWedgeConjugation

open Set Topology

namespace OpenPartialHomeomorph

theorem image_conjugateMap_inter_source {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (c : OpenPartialHomeomorph X Y)
    {f : Y → Y} (hmap : MapsTo f c.target c.target) (A : Set X) :
    c '' (c.conjugateMap f '' A ∩ c.source) = f '' (c '' (A ∩ c.source)) := by
  have hsrc : ∀ x, c.conjugateMap f x ∈ c.source ↔ x ∈ c.source := fun x =>
    c.conjugateMap_mem_iff hmap (fun _ hx => iff_of_true hx (c.map_source hx))
      (fun _ hy => iff_of_true (hmap hy) hy) x
  have hcoord : ∀ x ∈ c.source, c (c.conjugateMap f x) = f (c x) := by
    intro x hx
    rw [c.conjugateMap_of_mem f hx, c.right_inv (hmap (c.map_source hx))]
  ext y
  constructor
  · rintro ⟨x, ⟨⟨a, ha, rfl⟩, has⟩, rfl⟩
    have hac := (hsrc a).mp has
    exact ⟨c a, ⟨a, ⟨ha, hac⟩, rfl⟩, (hcoord a hac).symm⟩
  · rintro ⟨x, ⟨a, ⟨ha, has⟩, rfl⟩, rfl⟩
    exact ⟨c.conjugateMap f a, ⟨⟨a, ha, rfl⟩, (hsrc a).mpr has⟩, hcoord a has⟩

end OpenPartialHomeomorph

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_chart_hasPLCrossingAt_conjugate_image
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) {B Sf : Set M} (hBc : B ⊆ c.source)
    (Φ : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3))
    (hΦ : IsPLHomeomorphOn Φ univ univ) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ c.target) (hfix : EqOn Φ id Kᶜ)
    (hSf : (c.conjugateHomeomorph Φ hK hKc hfix) '' Sf = Sf)
    (hcross : ∀ y ∈ B ∩ Sf, ∃ d ∈ (plGroupoid 3).maximalAtlas M, y ∈ d.source ∧
      HasPLCrossingAt (d '' (B ∩ d.source)) (d '' (Sf ∩ d.source)) (d y)) :
    ∀ y ∈ (c.conjugateHomeomorph Φ hK hKc hfix) '' B ∩ Sf,
      ∃ d ∈ (plGroupoid 3).maximalAtlas M, y ∈ d.source ∧
        HasPLCrossingAt
          (d '' ((c.conjugateHomeomorph Φ hK hKc hfix) '' B ∩ d.source))
          (d '' (Sf ∩ d.source)) (d y) := by
  let Ψ := c.conjugateHomeomorph Φ hK hKc hfix
  have hmap : MapsTo Φ c.target c.target := mapsTo_of_injective_eqOn_compl Φ.injective
    (hfix.mono (compl_subset_compl.mpr hKc))
  have hcoord : ∀ x ∈ c.source, c (Ψ x) = Φ (c x) := by
    intro x hx
    change c (c.conjugateMap Φ x) = Φ (c x)
    rw [c.conjugateMap_of_mem Φ hx, c.right_inv (hmap (c.map_source hx))]
  have himg : ∀ A : Set M,
      c '' (Ψ '' A ∩ c.source) = Φ '' (c '' (A ∩ c.source)) :=
    c.image_conjugateMap_inter_source hmap
  rintro y ⟨⟨x, hxB, rfl⟩, hxSf⟩
  have hxs : x ∈ c.source := hBc hxB
  have hxSf' : x ∈ Sf := by
    obtain ⟨z, hzSf, hzx⟩ := hSf.symm ▸ hxSf
    exact Ψ.injective hzx ▸ hzSf
  obtain ⟨d, hd, hxd, hxdCross⟩ := hcross x ⟨hxB, hxSf'⟩
  have hcCross := hxdCross.image_chart_of_mem_maximalAtlas hc hd hxs hxd
  have hnew := hcCross.image_openPartialHomeomorph Φ.toOpenPartialHomeomorph
    hΦ.isPiecewiseAffineOn (mem_univ _)
  change HasPLCrossingAt (Φ '' (univ ∩ c '' (B ∩ c.source)))
    (Φ '' (univ ∩ c '' (Sf ∩ c.source))) (Φ (c x)) at hnew
  rw [univ_inter, univ_inter, ← himg B, ← himg Sf, hSf, ← hcoord x hxs] at hnew
  refine ⟨c, hc, ?_, hnew⟩
  change c.conjugateMap Φ x ∈ c.source
  rw [c.conjugateMap_of_mem Φ hxs]
  exact c.map_target (hmap (c.map_source hxs))

end DifferentialGeometry.Topology.PiecewiseLinear
