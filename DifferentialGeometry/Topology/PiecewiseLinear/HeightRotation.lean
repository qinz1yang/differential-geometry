import DifferentialGeometry.Topology.PiecewiseLinear.HeightStability
import DifferentialGeometry.Topology.PiecewiseLinear.HeightChange

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem eventually_mem_heightSingularPoints_iff_and_encard_levelPolygons_eq {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere (n + 1) K.space)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ K.vertices) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
      (p ∈ heightSingularPoints K.space f ↔ p ∈ heightSingularPoints K.space ℓ) ∧
      (levelPolygons K.space f (f p)).encard = (levelPolygons K.space ℓ (ℓ p)).encard := by
  filter_upwards [eventually_exists_homeomorph_preserving_sphere_image_fiber
    K hK ℓ hℓ hinj hp isOpen_univ (subset_univ _) zero_lt_one] with f hf
  obtain ⟨h, hh, -, -, hfix, himage, hfiber, hplane⟩ := hf
  have hhp : h p = p := hfix hp
  have hcross : HasPLCrossingAt K.space {x | ℓ x = ℓ p} p ↔
      HasPLCrossingAt K.space {x | f x = f p} p := by
    have htransport := hasPLCrossingAt_image_homeomorph_iff
      (A := K.space) (B := {x | ℓ x = ℓ p}) (x := p) h hh
    rw [himage, hhp] at htransport
    refine htransport.symm.trans ⟨fun hc => ?_, fun hc => ?_⟩
    · exact hc.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) hplane
    · exact hc.congr (Filter.Eventually.of_forall fun _ => Iff.rfl)
        (hplane.mono fun _ hy => hy.symm)
  have hisolated : {p} ∈ 𝓝[K.space ∩ {x | f x = f p}] p ↔
      {p} ∈ 𝓝[K.space ∩ {x | ℓ x = ℓ p}] p := by
    have htransport : {h p} ∈ 𝓝[h '' (K.space ∩ {x | ℓ x = ℓ p})] (h p) ↔
        {p} ∈ 𝓝[K.space ∩ {x | ℓ x = ℓ p}] p := by
      rw [← h.isEmbedding.map_nhdsWithin_eq]
      change h ⁻¹' {h p} ∈ 𝓝[K.space ∩ {x | ℓ x = ℓ p}] p ↔ _
      have hpre : h ⁻¹' {h p} = {p} := by
        ext x
        exact h.injective.eq_iff
      rw [hpre]
    simpa only [hfiber, hhp] using htransport
  refine ⟨?_, encard_levelPolygons_eq_of_image_fiber h hh hfiber⟩
  change (p ∈ K.space ∧ ¬ HasPLCrossingAt K.space {x | f x = f p} p ∧ _) ↔
    (p ∈ K.space ∧ ¬ HasPLCrossingAt K.space {x | ℓ x = ℓ p} p ∧ _)
  rw [← hcross, hisolated]

theorem eventually_heightSingularPoints_eq_and_levelPolygons_encard_eq
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere 2 K.space)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, heightSingularPoints K.space f = heightSingularPoints K.space ℓ ∧
      ∀ p ∈ K.vertices,
        (levelPolygons K.space f (f p)).encard = (levelPolygons K.space ℓ (ℓ p)).encard := by
  have hV : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  have hvertices : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∀ p ∈ K.vertices,
      (p ∈ heightSingularPoints K.space f ↔ p ∈ heightSingularPoints K.space ℓ) ∧
      (levelPolygons K.space f (f p)).encard = (levelPolygons K.space ℓ (ℓ p)).encard := by
    rw [hV.eventually_all]
    exact fun p hp => eventually_mem_heightSingularPoints_iff_and_encard_levelPolygons_eq K hK ℓ hℓ hinj hp
  have hne : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f ≠ 0 := isOpen_compl_singleton.mem_nhds hℓ
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  have hKman := hK.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
  have hsing := heightSingularPoints_subset_vertices K hKman hdimE ℓ.toLinearMap hlinear hinj
  filter_upwards [hvertices, hne, eventually_preserves_strict_order hV ℓ] with f hf hfne horder
  have hfinj : InjOn f K.vertices := by
    intro x hx y hy hxy
    rcases lt_trichotomy (ℓ x) (ℓ y) with hlt | heq | hgt
    · exact ((horder x hx y hy hlt).ne hxy).elim
    · exact hinj hx hy heq
    · exact ((horder y hy x hx hgt).ne hxy.symm).elim
  have hflinear : f.toLinearMap ≠ 0 := by
    intro hz
    apply hfne
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  have hfsing := heightSingularPoints_subset_vertices K hKman hdimE f.toLinearMap hflinear hfinj
  refine ⟨?_, fun p hp => (hf p hp).2⟩
  ext p
  by_cases hp : p ∈ K.vertices
  · exact (hf p hp).1
  · exact iff_of_false (fun hs => hp (hfsing hs)) (fun hs => hp (hsing hs))

theorem eventually_heightIndex_eq (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, heightIndex K.space f = heightIndex K.space ℓ := by
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  have hsing := heightSingularPoints_subset_vertices K
    hK.isCombinatorialManifold.isCombinatorialManifoldWithBoundary hdimE ℓ.toLinearMap hlinear hinj
  filter_upwards [eventually_heightSingularPoints_eq_and_levelPolygons_encard_eq K hK hdimE ℓ hℓ hinj]
    with f hf
  let e : heightSingularPoints K.space ℓ ≃ heightSingularPoints K.space f := Equiv.setCongr hf.1.symm
  unfold heightIndex
  rw [← e.tsum_eq]
  apply tsum_congr
  intro p
  change (levelPolygons K.space f (f p)).encard - 1 = (levelPolygons K.space ℓ (ℓ p)).encard - 1
  rw [hf.2 p (hsing p.property)]

end DifferentialGeometry.Topology.PiecewiseLinear
