/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedWeights
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionTransport

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section

variable [DecidableEq E] [DecidableEq F]
  {K : Geometry.SimplicialComplex ℝ E} {K' : Geometry.SimplicialComplex ℝ F}
  {L : Geometry.SimplicialComplex ℝ E} {L' : Geometry.SimplicialComplex ℝ F}
  {φ : E → F} {ψ : F → E}

theorem IsGlueIso.simplicialMap_centroid (h : IsGlueIso K K' φ ψ) {s : Finset E}
    (hs : s ∈ K.faces) :
    simplicialMap K φ (s.centroid ℝ id) = (s.image φ).centroid ℝ id := by
  have hsne : s.Nonempty := K.nonempty_of_mem_faces hs
  have hinj : Set.InjOn φ (s : Set E) := by
    intro v hv w hw hvw
    calc
      v = ψ (φ v) := (h.left s hs v (Finset.mem_coe.mp hv)).symm
      _ = ψ (φ w) := congrArg ψ hvw
      _ = w := h.left s hs w (Finset.mem_coe.mp hw)
  rw [simplicialMap_eq_of_mem K φ hs
      (openSimplex_subset_convexHull s (centroid_mem_openSimplex hsne)),
    centroid_eq_sum (s.image φ) (hsne.image φ), Finset.sum_image hinj,
    Finset.card_image_of_injOn hinj]
  exact Finset.sum_congr rfl fun v hv => by
    rw [weights_centroid (K.indep hs) (Finset.Subset.refl s) hsne hv, ite_eq_left hv]

theorem IsGlueIso.image_isFlag (h : IsGlueIso K K' φ ψ)
    {D : Finset (Finset E)} (hD : IsFlag K D) :
    IsFlag K' (D.image fun s => s.image φ) := by
  constructor
  · rintro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact h.image₁ s (hD.mem_faces hs)
  · rintro s hs t ht
    obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
    rcases hD.subset_or_subset hs₀ ht₀ with hst | hts
    · exact Or.inl (Finset.image_mono φ hst)
    · exact Or.inr (Finset.image_mono φ hts)

theorem IsGlueIso.barycentricSubdivision (h : IsGlueIso K K' φ ψ) :
    IsGlueIso
      (DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K)
      (DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K')
      (simplicialMap K φ) (simplicialMap K' ψ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro u ⟨D, hD, hDne, rfl⟩
    let D' : Finset (Finset F) := D.image fun s => s.image φ
    refine ⟨D', h.image_isFlag hD, hDne.image _, ?_⟩
    simp only [D', Finset.image_image]
    exact Finset.image_congr fun s hs => h.simplicialMap_centroid (hD.mem_faces hs)
  · rintro u ⟨D, hD, hDne, rfl⟩
    let D' : Finset (Finset E) := D.image fun s => s.image ψ
    refine ⟨D', h.symm.image_isFlag hD, hDne.image _, ?_⟩
    simp only [D', Finset.image_image]
    exact Finset.image_congr fun s hs => h.symm.simplicialMap_centroid (hD.mem_faces hs)
  · intro u hu v hv
    let BK := DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K
    have hvBK : v ∈ BK.space :=
      BK.convexHull_subset_space hu (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))
    exact h.simplicialMap_simplicialMap_left
      ((barycentricSubdivision_isSubdivision K).space_eq.subset hvBK)
  · intro u hu v hv
    let BK' := DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K'
    have hvBK' : v ∈ BK'.space :=
      BK'.convexHull_subset_space hu (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))
    exact h.simplicialMap_simplicialMap_right
      ((barycentricSubdivision_isSubdivision K').space_eq.subset hvBK')

theorem IsGlueIso.secondDerived (h : IsGlueIso K K' φ ψ) :
    IsGlueIso (secondDerived K) (secondDerived K')
      (simplicialMap
        (DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K)
        (simplicialMap K φ))
      (simplicialMap
        (DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K')
        (simplicialMap K' ψ)) :=
  h.barycentricSubdivision.barycentricSubdivision

omit [DecidableEq E] [DecidableEq F] in
open Classical in
theorem IsSubdivision.simplicialMap_simplicialMap_eq [FiniteDimensional ℝ E]
    {R : Geometry.SimplicialComplex ℝ E} (hR : IsSubdivision R K) (f : E → F) :
    EqOn (simplicialMap R (simplicialMap K f)) (simplicialMap K f) R.space := by
  apply simplicialMap_eq_of_forall_affineOn
  intro u hu
  obtain ⟨s, hs, hus⟩ := hR.exists_face_subset hu
  obtain ⟨A, hA⟩ := exists_affineMap_eqOn_simplicialMap K f hs
  exact ⟨A, hA.mono hus⟩

omit [DecidableEq F] in
theorem simplicialMap_derivedNeighborhood_eq [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (f : E → F) :
    EqOn
      (simplicialMap
        (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood K L)
        (simplicialMap
          (DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K) f))
      (simplicialMap
        (DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K) f)
      (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood K L).space := by
  apply simplicialMap_eq_of_forall_affineOn
  intro u hu
  let BK := DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K
  have hsub := barycentricSubdivision_isSubdivision BK
  obtain ⟨e, he, hue⟩ :=
    hsub.exists_face_subset (derivedNeighborhood_faces_subset K L hu)
  obtain ⟨A, hA⟩ := exists_affineMap_eqOn_simplicialMap
    (DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K) f he
  exact ⟨A, hA.mono hue⟩

theorem IsGlueIso.derivedNeighborhood (hK : IsGlueIso K K' φ ψ)
    (hL : IsGlueIso L L' φ ψ) (hLK : L.faces ⊆ K.faces)
    (hL'K' : L'.faces ⊆ K'.faces) :
    IsGlueIso
      (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood K L)
      (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood K' L')
      (simplicialMap
        (DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K)
        (simplicialMap K φ))
      (simplicialMap
        (DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K')
        (simplicialMap K' ψ)) := by
  let Φ := simplicialMap
    (DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K)
    (simplicialMap K φ)
  let Ψ := simplicialMap
    (DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K')
    (simplicialMap K' ψ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro u ⟨D, hD, hDne, hmeet, rfl⟩
    let D' : Finset (Finset F) := D.image fun e => e.image (simplicialMap K φ)
    refine ⟨D', hK.barycentricSubdivision.image_isFlag hD, hDne.image _, ?_, ?_⟩
    · rintro e he
      obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨s, hs, hse⟩ := hmeet e₀ he₀
      refine ⟨s.image φ, hL.image₁ s hs, ?_⟩
      rw [← hK.simplicialMap_centroid (hLK hs)]
      exact Finset.mem_image_of_mem _ hse
    · simp only [D', Finset.image_image]
      exact Finset.image_congr fun e he =>
        hK.barycentricSubdivision.simplicialMap_centroid (hD.mem_faces he)
  · rintro u ⟨D, hD, hDne, hmeet, rfl⟩
    let D' : Finset (Finset E) := D.image fun e => e.image (simplicialMap K' ψ)
    refine ⟨D', hK.symm.barycentricSubdivision.image_isFlag hD, hDne.image _, ?_, ?_⟩
    · rintro e he
      obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨s, hs, hse⟩ := hmeet e₀ he₀
      refine ⟨s.image ψ, hL.image₂ s hs, ?_⟩
      rw [← hK.symm.simplicialMap_centroid (hL'K' hs)]
      exact Finset.mem_image_of_mem _ hse
    · simp only [D', Finset.image_image]
      exact Finset.image_congr fun e he =>
        hK.symm.barycentricSubdivision.simplicialMap_centroid (hD.mem_faces he)
  · intro u hu
    exact hK.secondDerived.left u (derivedNeighborhood_faces_subset K L hu)
  · intro u hu
    exact hK.secondDerived.right u (derivedNeighborhood_faces_subset K' L' hu)

theorem IsGlueIso.image_derivedNeighborhood [FiniteDimensional ℝ E]
    (hK : IsGlueIso K K' φ ψ)
    (hL : IsGlueIso L L' φ ψ) (hLK : L.faces ⊆ K.faces)
    (hL'K' : L'.faces ⊆ K'.faces) :
    simplicialMap
        (DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K)
        (simplicialMap K φ) ''
        (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood K L).space =
      (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood K' L').space := by
  let Φ := simplicialMap
    (DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K)
    (simplicialMap K φ)
  calc
    Φ '' (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood K L).space =
        simplicialMap
            (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood K L) Φ ''
          (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood K L).space :=
      (simplicialMap_derivedNeighborhood_eq K L (simplicialMap K φ)).image_eq.symm
    _ = (DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood K' L').space :=
      (hK.derivedNeighborhood hL hLK hL'K').image_left

end

end DifferentialGeometry.Topology.PiecewiseLinear
