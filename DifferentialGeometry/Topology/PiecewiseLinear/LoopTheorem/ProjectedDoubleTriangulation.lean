/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedDoubleInvolution
import DifferentialGeometry.Topology.PiecewiseLinear.InvolutionTriangulation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsPiecewiseAffineOn.exists_simplicialComplex_doublePointInvolution_relative
    {f : E → F} {P : Set E} (hf : IsPiecewiseAffineOn f P) (hP : IsPolyhedron P)
    (hloc : IsLocallyInjective (P.domRestrict f))
    (hcard : ∀ y, (P ∩ f ⁻¹' {y}).encard ≤ 2)
    {J : Type*} [Finite J] (C : J → Set E) (hC : ∀ j, IsPolyhedron (C j)) :
    ∃ (K : Geometry.SimplicialComplex ℝ E) (τ : E → E),
      K.faces.Finite ∧ K.space = doublePointPreimage f P ∧
      IsPLHomeomorphOn τ K.space K.space ∧ EqOn (simplicialMap K τ) τ K.space ∧
      (∀ x ∈ K.space, τ (τ x) = x ∧ τ x ≠ x ∧ f (τ x) = f x) ∧
      (∀ s ∈ K.faces, s.image τ ∈ K.faces ∧
        Disjoint (convexHull ℝ (s : Set E)) (convexHull ℝ (↑(s.image τ) : Set E))) ∧
      ∀ j, (restrict K (doublePointPreimage f P ∩ C j)).space =
        doublePointPreimage f P ∩ C j := by
  let Q := doublePointRelation f P
  let A : E × E →ᵃ[ℝ] E × E :=
    ((LinearMap.snd ℝ E E).prod (LinearMap.fst ℝ E E)).toAffineMap
  have hA : Function.Involutive A := fun _ => rfl
  have hAQ : MapsTo A Q Q := fun _ hz =>
    ⟨hz.2.1, hz.1, hz.2.2.1.symm, hz.2.2.2.symm⟩
  have hfree : ∀ z ∈ Q, A z ≠ z := by
    intro z hz h
    exact hz.2.2.1 (congrArg Prod.fst h).symm
  let B (j : J) := Q ∩ (C j ×ˢ P)
  have hQ : IsPolyhedron Q := hf.isPolyhedron_doublePointRelation hP hloc
  obtain ⟨L, hLfin, hLQ, hLA, hLB⟩ :=
    hQ.exists_simplicialComplex_affineInvolution_relative A hA hAQ B
      (fun j => hQ.inter ((hC j).prod hP)) (fun _ => inter_subset_left)
  have hLA' (s : Finset (E × E)) (hs : s ∈ L.faces) : s.image A ∈ L.faces := by
    convert hLA s hs using 2
  let _ : Finite L.faces := hLfin.to_subtype
  have hπ := bijOn_fst_doublePointRelation hcard
  have hπL : InjOn Prod.fst L.space := hLQ.symm ▸ hπ.injOn
  let p : E × E →ᵃ[ℝ] E := (LinearMap.fst ℝ E E).toAffineMap
  obtain ⟨K, hKfin, hKL, hKfaces, -⟩ :=
    exists_simplicialComplex_image_of_affineOn_faces L (f := Prod.fst)
      (fun _ _ => ⟨p, fun _ _ => rfl⟩) hπL
  have hKP : K.space = doublePointPreimage f P := by
    rw [hKL, hLQ]
    exact image_fst_doublePointRelation f P
  obtain ⟨τ, hτ, hτspec⟩ :=
    hf.exists_isPLHomeomorphOn_doublePointPreimage_involution hP hloc hcard
  have hpair (z : E × E) (hz : z ∈ Q) : τ z.1 = z.2 := by
    have hx := hπ.mapsTo hz
    have ht := hτspec z.1 hx
    have hz' : (z.1, τ z.1) ∈ Q :=
      ⟨hz.1, (hτ.bijOn.mapsTo hx).1, ht.2.1.symm, ht.2.2.symm⟩
    exact congrArg Prod.snd (hπ.injOn hz' hz rfl)
  have hHull (s : Finset (E × E)) :
      convexHull ℝ (↑(s.image Prod.fst) : Set E) =
        Prod.fst '' convexHull ℝ (s : Set (E × E)) := by
    rw [Finset.coe_image]
    exact (p.image_convexHull (s : Set (E × E))).symm
  have hfaceImage (s : Finset (E × E)) (hs : s ∈ L.faces) :
      (s.image Prod.fst).image τ = (s.image A).image Prod.fst := by
    rw [Finset.image_image, Finset.image_image]
    exact Finset.image_congr fun z hz => hpair z
      (hLQ ▸ L.convexHull_subset_space hs (subset_convexHull ℝ _ hz))
  have hsimp : EqOn (simplicialMap K τ) τ K.space := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := K.mem_space_iff.mp hx
    obtain ⟨s, hs, rfl⟩ := (hKfaces t).mp ht
    let t := s.image Prod.fst
    have hvertex : ∀ v ∈ t, (v, τ v) ∈ convexHull ℝ (s : Set (E × E)) := by
      intro v hv
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
      have hzQ : z ∈ Q := hLQ ▸ L.convexHull_subset_space hs (subset_convexHull ℝ _ hz)
      rw [hpair z hzQ]
      exact subset_convexHull ℝ _ hz
    let z : E × E := ∑ v ∈ t, weights t x v • (v, τ v)
    have hz : z ∈ convexHull ℝ (s : Set (E × E)) :=
      (convex_convexHull ℝ _).sum_mem (fun _ hv => weights_nonneg hxt hv)
        (sum_weights hxt) hvertex
    have hz₁ : z.1 = x := by
      change (LinearMap.fst ℝ E E) z = x
      simp only [z, map_sum, map_smul, LinearMap.fst_apply]
      exact sum_weights_smul hxt
    have hz₂ : z.2 = ∑ v ∈ t, weights t x v • τ v := by
      change (LinearMap.snd ℝ E E) z = _
      simp only [z, map_sum, map_smul, LinearMap.snd_apply]
    rw [simplicialMap_eq_of_mem K τ ht hxt]
    exact hz₂.symm.trans ((hpair z (hLQ ▸ L.convexHull_subset_space hs hz)).symm.trans
      (congrArg τ hz₁))
  refine ⟨K, τ, hKfin, hKP, hKP.symm ▸ hτ, hsimp,
    fun x hx => hτspec x (hKP ▸ hx), ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := (hKfaces t).mp ht
    rw [hfaceImage s hs]
    refine ⟨(hKfaces _).mpr ⟨s.image A, hLA' s hs, rfl⟩, ?_⟩
    have hdisj := Convex.disjoint_image_affineInvolution
      (convex_convexHull ℝ (s : Set (E × E))) A hA
      (fun z hz => hfree z (hLQ ▸ L.convexHull_subset_space hs hz))
    rw [hHull, hHull, Finset.coe_image, ← A.image_convexHull]
    rw [Set.disjoint_left] at hdisj ⊢
    rintro x ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    have hzL := L.convexHull_subset_space hs hz
    have hwL : w ∈ L.space := by
      rw [hLQ]
      obtain ⟨u, hu, rfl⟩ := hw
      exact hAQ (hLQ ▸ L.convexHull_subset_space hs hu)
    exact hdisj hz ((hπL hwL hzL hwz) ▸ hw)
  · intro j
    apply Subset.antisymm (restrict_space_subset _ _)
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hπ.surjOn hx.1
    have hzB : z ∈ B j := ⟨hz, hzx.symm ▸ hx.2, hz.2.1⟩
    have hzR : z ∈ (restrict L (B j)).space := (hLB j).symm ▸ hzB
    obtain ⟨s, hs, hzs⟩ := (restrict L (B j)).mem_space_iff.mp hzR
    apply (restrict K (doublePointPreimage f P ∩ C j)).convexHull_subset_space
      (s := s.image Prod.fst)
    · refine ⟨(hKfaces _).mpr ⟨s, hs.1, rfl⟩, ?_⟩
      rw [hHull]
      rintro y ⟨w, hw, rfl⟩
      have hwB := hs.2 hw
      exact ⟨hπ.mapsTo hwB.1, hwB.2.1⟩
    · rw [hHull]
      exact ⟨z, hzs, hzx⟩

namespace NormalSystem

open Classical in
theorem DoubleCoverDiagram.exists_projected_doublePointTriangulation
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T)
    (D : EmbeddedDisk T) :
    ∃ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
      K.faces.Finite ∧ K.space = doublePointPreimage (R.projection ∘ D.map) D.domain ∧
      IsPLHomeomorphOn τ K.space K.space ∧ EqOn (simplicialMap K τ) τ K.space ∧
      (∀ x ∈ K.space, τ (τ x) = x ∧ τ x ≠ x ∧
        R.projection (D.map (τ x)) = R.projection (D.map x) ∧
        (τ x ∈ frontier D.domain ↔ x ∈ frontier D.domain)) ∧
      (∀ s ∈ K.faces, s.image τ ∈ K.faces ∧
        Disjoint (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2))))
          (convexHull ℝ (↑(s.image τ) : Set (EuclideanSpace ℝ (Fin 2))))) ∧
      (restrict K (K.space ∩ frontier D.domain)).space = K.space ∩ frontier D.domain := by
  obtain ⟨f, γ, q, rfl, -, hf, -, hloc, hcard, hpre, -, -, -, -, -⟩ :=
    R.exists_projected_map_of_embeddedDisk D
  obtain ⟨K, τ, hfin, hspace, hτ, hsimp, hspec, hfaces, hfront⟩ :=
    hf.exists_simplicialComplex_doublePointInvolution_relative
      D.isPLBall_domain.isPolyhedron hloc hcard (fun _ : Unit => frontier D.domain)
      (fun _ => D.isPLBall_domain.isPLSphere_frontier.isPolyhedron)
  refine ⟨K, τ, hfin, hspace, hτ, hsimp, fun x hx => ?_, ?_, ?_⟩
  · have hs := hspec x hx
    have hxP : x ∈ D.domain := (hspace ▸ hx).1
    have hτP : τ x ∈ D.domain := (hspace ▸ hτ.bijOn.mapsTo hx).1
    refine ⟨hs.1, hs.2.1, hs.2.2, ?_⟩
    constructor
    · intro hb
      apply hpre.subset
      refine ⟨hxP, ?_⟩
      change (R.projection ∘ D.map) x ∈ S.boundaryComplex.space
      rw [← hs.2.2]
      exact (hpre.superset hb).2
    · intro hb
      apply hpre.subset
      refine ⟨hτP, ?_⟩
      change (R.projection ∘ D.map) (τ x) ∈ S.boundaryComplex.space
      rw [hs.2.2]
      exact (hpre.superset hb).2
  · intro s hs
    convert hfaces s hs using 2
    · ext v
      simp only [Finset.mem_image]
    · simp only [Finset.coe_image]
  · rw [hspace]
    exact hfront ()

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
