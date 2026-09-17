import DifferentialGeometry.Analysis.InnerProductSpace.SphereDerivative
import DifferentialGeometry.Analysis.Calculus.BallBoundary
import DifferentialGeometry.Analysis.Calculus.Inverse.CoordinateDerivativeEquiv
import DifferentialGeometry.Topology.Manifold.RelativeCollarIsotopy
import DifferentialGeometry.Topology.Homeomorph.LevelIsotopy

open Set Metric Filter
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace Diffeomorph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem injective_convex_combination_fderiv_of_eventuallyEq_sphere
    {F : E → E} {c x : E} {r : ℝ} (hr : 0 < r) (hx : x ∈ sphere c r)
    (hF : DifferentiableAt ℝ F x) (hfixed : F =ᶠ[𝓝[sphere c r] x] id)
    (hpos : 0 < ⟪x - c, fderiv ℝ F x (x - c)⟫)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Function.Injective ((1 - t) • ContinuousLinearMap.id ℝ E + t • fderiv ℝ F x) := by
  have hn : ‖x - c‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hx
  let l : E →ₗ[ℝ] ℝ := (r ^ 2)⁻¹ • (innerSL ℝ (x - c)).toLinearMap
  have hl (v : E) : l v = (r ^ 2)⁻¹ * ⟪x - c, v⟫ := rfl
  have hln : l (x - c) = 1 := by
    rw [hl, real_inner_self_eq_norm_sq, hn, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne')]
  apply (fderiv ℝ F x).toLinearMap.injective_convex_combination_of_eqOn_ker_id l hln
  · intro v hv
    have hv' : ⟪x - c, v⟫ = 0 := (mul_eq_zero.mp hv).resolve_left
      (inv_ne_zero (pow_ne_zero 2 hr.ne'))
    change (fderiv ℝ F x) v = v
    simpa only [fderiv_id, ContinuousLinearMap.id_apply] using
      fderiv_apply_eq_of_eventuallyEq_sphere hr hx hF differentiableAt_id hfixed hv'
  · exact mul_pos (inv_pos.mpr (sq_pos_of_pos hr)) hpos
  · exact ht

theorem injective_convex_combination_fderiv_of_eqOn_sphere
    {F : E → E} {c x : E} {r : ℝ} (hr : 0 < r) (hx : x ∈ sphere c r)
    (hF : DifferentiableAt ℝ F x) (hfixed : EqOn F id (sphere c r))
    (hpos : 0 < ⟪x - c, fderiv ℝ F x (x - c)⟫)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Function.Injective ((1 - t) • ContinuousLinearMap.id ℝ E + t • fderiv ℝ F x) := by
  apply injective_convex_combination_fderiv_of_eventuallyEq_sphere hr hx hF ?_ hpos ht
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hfixed hy

theorem exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere
    [FiniteDimensional ℝ E] {F : E → E} {W : Set E}
    (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W)
    {c : E} {r : ℝ} (hr : 0 < r)
    (hfixed : EqOn F id (sphere c r ∩ W))
    {K : Set E} (hK : IsCompact K) (hKS : K ⊆ sphere c r ∩ W)
    (hpos : ∀ x ∈ K, 0 < ⟪x - c, fderiv ℝ F x (x - c)⟫)
    {O : Set E} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ W ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ V, Φ t p = (1 - t) • p + t • F p) ∧
        (∀ t, EqOn (Φ t) id (sphere c r) ∧ EqOn (Φ t).symm id (sphere c r)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, Φ t '' closedBall c r = closedBall c r) ∧
        ∃ L : Set E, IsCompact L ∧ L ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Lᶜ ∧ EqOn (Φ t).symm id Lᶜ := by
  obtain ⟨V, hV, hSV, hVW, Φ, hΦ, hΦi, hΦ0, htrack, hfix, hsupport⟩ :=
    exists_contDiff_compact_isotopy_eqOn_of_injective_convex_combination hW hF
      hfixed hK hKS
      (fun x hx t ht => injective_convex_combination_fderiv_of_eventuallyEq_sphere hr (hKS hx).1
        ((hF.contDiffAt (hW.mem_nhds (hKS hx).2)).differentiableAt (by simp))
        (by
          filter_upwards [self_mem_nhdsWithin,
            eventually_nhdsWithin_of_eventually_nhds (hW.mem_nhds (hKS hx).2)] with y hy hyW
          exact hfixed ⟨hy, hyW⟩)
        (hpos x hx) ht) hO hKO
  refine ⟨V, hV, hSV, hVW, Φ, hΦ, hΦi, hΦ0, htrack, hfix, ?_, hsupport⟩
  intro t ht
  change (Φ t).toHomeomorph '' closedBall c r = closedBall c r
  have hlevel (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      (Φ u).toHomeomorph '' {x : E | dist x c = r} = {x : E | dist x c = r} := by
    change Φ u '' sphere c r = sphere c r
    rw [(hfix u).1.image_eq, image_id]
  exact Homeomorph.image_sublevel_eq_of_image_level_eq (fun u => (Φ u).toHomeomorph)
    (continuous_id.dist continuous_const) (fun x => (hΦ.continuous.comp
      (continuous_id.prodMk continuous_const)).continuousOn)
    (by rw [hΦ0]; rfl) hlevel t ht

theorem exists_contDiff_compact_isotopy_eqOn_of_eqOn_sphere
    [FiniteDimensional ℝ E] {F : E → E} {W : Set E}
    (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W)
    {c : E} {r : ℝ} (hr : 0 < r) (hSW : sphere c r ⊆ W)
    (hfixed : EqOn F id (sphere c r))
    (hpos : ∀ x ∈ sphere c r, 0 < ⟪x - c, fderiv ℝ F x (x - c)⟫)
    {O : Set E} (hO : IsOpen O) (hSO : sphere c r ⊆ O) :
    ∃ V : Set E, IsOpen V ∧ sphere c r ⊆ V ∧ V ⊆ W ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ V, Φ t p = (1 - t) • p + t • F p) ∧
        (∀ t, EqOn (Φ t) id (sphere c r) ∧ EqOn (Φ t).symm id (sphere c r)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, Φ t '' closedBall c r = closedBall c r) ∧
        ∃ L : Set E, IsCompact L ∧ L ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Lᶜ ∧ EqOn (Φ t).symm id Lᶜ := by
  exact exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere hW hF hr
    (hfixed.mono inter_subset_left) (isCompact_sphere c r) (fun x hx => ⟨hx, hSW hx⟩)
    hpos hO hSO

end Diffeomorph

namespace PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_fderiv_pos_of_mapsTo_closedBall
    (F : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {c x : E} {r : ℝ} (hr : 0 < r) (hx : x ∈ sphere c r)
    (hxF : x ∈ F.source) (hfixed : F x = x)
    (hmap : MapsTo F (closedBall c r ∩ F.source) (closedBall c r)) :
    0 < ⟪x - c, fderiv ℝ F x (x - c)⟫ := by
  have hn : ‖x - c‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hx
  have hd := ((F.contMDiffOn.contDiffOn.contDiffAt
    (F.open_source.mem_nhds hxF)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨a, ha, heq⟩ := hd.exists_pos_inner_eq_mul_inner_of_eventually_mem_closedBall
    (DifferentialGeometry.Analysis.bijective_fderiv_of_partialDiffeomorph F hxF).surjective
    hr hr hn (by rw [hfixed]; exact hn) (by
      filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (F.open_source.mem_nhds hxF)] with y hy hyF
      exact hmap ⟨hy, hyF⟩)
  have h := heq (x - c)
  rw [hfixed, real_inner_self_eq_norm_sq, hn] at h
  rw [h]
  exact mul_pos ha (sq_pos_of_pos hr)

theorem exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere
    [FiniteDimensional ℝ E]
    (F : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {c : E} {r : ℝ} (hr : 0 < r)
    (hfixed : EqOn F id (sphere c r ∩ F.source))
    {K : Set E} (hK : IsCompact K) (hKS : K ⊆ sphere c r ∩ F.source)
    (hmap : MapsTo F (closedBall c r ∩ F.source) (closedBall c r))
    {O : Set E} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ F.source ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        EqOn (Φ 1) F V ∧
        (∀ t, EqOn (Φ t) id (sphere c r) ∧ EqOn (Φ t).symm id (sphere c r)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, Φ t '' closedBall c r = closedBall c r) ∧
        ∃ L : Set E, IsCompact L ∧ L ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Lᶜ ∧ EqOn (Φ t).symm id Lᶜ := by
  obtain ⟨V, hV, hSV, hVF, Φ, hΦ, hΦi, hΦ0, htrack, hfix, hball, hsupport⟩ :=
    Diffeomorph.exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere
      F.open_source F.contMDiffOn.contDiffOn hr hfixed hK hKS
      (fun x hx => F.inner_fderiv_pos_of_mapsTo_closedBall hr (hKS hx).1
        (hKS hx).2 (hfixed (hKS hx)) hmap) hO hKO
  refine ⟨V, hV, hSV, hVF, Φ, hΦ, hΦi, hΦ0, ?_, hfix, hball, hsupport⟩
  intro x hx
  simpa only [sub_self, zero_smul, one_smul, zero_add] using htrack 1 ⟨zero_le_one, le_rfl⟩ x hx

theorem exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood
    [FiniteDimensional ℝ E]
    (F : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {c : E} {r : ℝ} (hr : 0 < r) (hSF : sphere c r ⊆ F.source)
    (hfixed : EqOn F id (sphere c r))
    (hmap : MapsTo F (closedBall c r ∩ F.source) (closedBall c r))
    {O : Set E} (hO : IsOpen O) (hSO : sphere c r ⊆ O) :
    ∃ V : Set E, IsOpen V ∧ sphere c r ⊆ V ∧ V ⊆ F.source ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        EqOn (Φ 1) F V ∧
        (∀ t, EqOn (Φ t) id (sphere c r) ∧ EqOn (Φ t).symm id (sphere c r)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, Φ t '' closedBall c r = closedBall c r) ∧
        ∃ L : Set E, IsCompact L ∧ L ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Lᶜ ∧ EqOn (Φ t).symm id Lᶜ := by
  exact F.exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere hr
    (hfixed.mono inter_subset_left) (isCompact_sphere c r) (fun x hx => ⟨hx, hSF hx⟩)
    hmap hO hSO

end PartialDiffeomorph
