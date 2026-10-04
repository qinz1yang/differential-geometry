import DifferentialGeometry.Geometry.Collapse.SublevelCore.GradientBand
import DifferentialGeometry.Geometry.Collapse.SublevelCore.DistanceCrossing

/-!
# LC34: distance-sublevel homeomorphism with small tracks (binding)

Blueprint LC34 (master207A:21486) for the LC30 radial function `η` on a complete Riemannian
manifold (PC setting), with the LC32 constants `a = 1/8`, `b = 3`, `0 ≤ ε < 1/2`, `e < 1/40`
and `ρ ∈ [1/5, 2]`.

* `radial_distance_crossing_height`: the crossing height `h_ρ` on the band (unique `u ∈ (1/8, 3)`
  with `d_p(Φ (u - η y) y) = ρ`), constant on flow lines, continuous on the band, `|h_ρ - ρ| < e`.
* `radial_distance_sublevel_isotopy`: a continuous isotopy `H_λ` of homeomorphisms of `M`,
  `H_0 = id`, equal to the identity where `η ∉ (1/8, 3)` (in particular off the band `K`), with
  tracks `d(H_λ q, q) < e / (1 - ε)`, and `H_1` maps `A_ρ`, `η⁻¹(ρ)`, `{η < ρ}` onto the closed
  distance ball, the distance sphere and the open distance ball of radius `ρ`.

The flow is the LC33 gradient product flow; the slope is LC33's `c_ε = (1 - 2ε)/(1 - ε)`.
Neither the distance sphere nor the isotopy is asserted to be smooth.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- The flow data used by LC34: the LC33 product flow, the band value property, the slope of the
distance along coordinate curves, and the Lipschitz bound of short flow segments in the band. -/
private theorem radial_flow_data (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M} {η : M → ℝ} {ε : ℝ≥0} {e : ℝ}
    (hε1 : (ε : ℝ) < 1) (he : e < 1 / 40) (hclose : ∀ x, |η x - dist p x| < e)
    (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x)) :
    ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      Continuous (fun q : ℝ × M => Φ q.1 q.2) ∧
      (∀ s t x, Φ (s + t) x = Φ t (Φ s x)) ∧ (∀ x, Φ 0 x = x) ∧
      (∀ y, η y ∈ Icc (1 / 8 : ℝ) 3 → ∀ s ∈ Icc (1 / 8 : ℝ) 3, η (Φ (s - η y) y) = s) ∧
      (∀ y, η y ∈ Icc (1 / 8 : ℝ) 3 → ∀ s t, 1 / 8 ≤ s → s ≤ t → t ≤ 3 →
        (1 - 2 * (ε : ℝ)) / (1 - ε) * (t - s) ≤
          dist p (Φ (t - η y) y) - dist p (Φ (s - η y) y)) ∧
      (∀ y, η y ∈ Icc (1 / 8 : ℝ) 3 → ∀ s, η y + s ∈ Icc (1 / 8 : ℝ) 3 →
        dist (Φ s y) y ≤ (1 - (ε : ℝ))⁻¹ * |s|) := by
  have hm : 0 < 1 - (ε : ℝ) := by linarith
  obtain ⟨Φ, hΦ0, hΦc, -, hΦadd, hval, -, hvel, hspeed, htrack, -⟩ :=
    radialBand_gradient_product g hEnorm hε1 he hclose hlip hW hCW hηW hgrad
  have hΦ0' : ∀ x, Φ 0 x = x := fun x => by rw [hΦ0]; rfl
  have hR : ∀ y, η y ∈ Icc (1 / 8 : ℝ) 3 → η (Φ (1 - η y) y) = 1 := fun y hy =>
    hval y hy 1 ⟨by norm_num, by norm_num⟩
  have hcomp : ∀ y u, Φ (u - 1) (Φ (1 - η y) y) = Φ (u - η y) y := by
    intro y u
    rw [← hΦadd, show 1 - η y + (u - 1) = u - η y by ring]
  refine ⟨Φ, hΦc.continuous, hΦadd, hΦ0', hval, ?_, ?_⟩
  · intro y hy s t hs hst ht
    have h := htrack (Φ (1 - η y) y) (hR y hy) s t hs hst ht
    rwa [hcomp, hcomp] at h
  · intro y hy s hs
    -- the flow line `u ↦ Φ (u - η y) y` between `η y` and `η y + s`
    have hsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun u => Φ u y) :=
      hΦc.comp (contMDiff_id.prodMk contMDiff_const)
    have hlev : ∀ u, η y + u ∈ Icc (1 / 8 : ℝ) 3 → η (Φ u y) = η y + u := by
      intro u hu
      have h1 := hval y hy (η y + u) hu
      rwa [add_sub_cancel_left] at h1
    have hspeed' : ∀ u, η y + u ∈ Icc (1 / 8 : ℝ) 3 →
        √(g.inner (Φ u y) (mfderiv 𝓘(ℝ, ℝ) I (fun s => Φ s y) u 1)
          (mfderiv 𝓘(ℝ, ℝ) I (fun s => Φ s y) u 1)) ≤ (1 - (ε : ℝ))⁻¹ := by
      intro u hu
      have hin : η (Φ u y) ∈ Icc (1 / 8 : ℝ) 3 := by rw [hlev u hu]; exact hu
      have hd := (hvel y u hin).mfderiv
      erw [hd]
      convert hspeed _ hin using 4 <;> exact one_smul ℝ _
    have hseg : ∀ s₁ s₂, s₁ ≤ s₂ → η y + s₁ ∈ Icc (1 / 8 : ℝ) 3 →
        η y + s₂ ∈ Icc (1 / 8 : ℝ) 3 →
        dist (Φ s₁ y) (Φ s₂ y) ≤ (1 - (ε : ℝ))⁻¹ * (s₂ - s₁) := by
      intro s₁ s₂ h12 h1 h2
      have hb := DifferentialGeometry.Geometry.riemannianEDistOf_le_of_curve_speed_bound g h12
        (hsm.contMDiffOn.of_le (by norm_num)) (C := (1 - (ε : ℝ))⁻¹) (by
          intro u hu
          exact hspeed' u ⟨by linarith [h1.1, hu.1], by linarith [h2.2, hu.2]⟩)
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hm.le),
        riemannianEDistOf_eq_riemannianEDist g hEnorm, ← IsRiemannianManifold.out (I := I),
        edist_dist] at hb
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (inv_nonneg.mpr hm.le)
        (sub_nonneg.mpr h12))).mp hb
    have hy0 : η y + 0 ∈ Icc (1 / 8 : ℝ) 3 := by rw [add_zero]; exact hy
    rcases le_total 0 s with h | h
    · have := hseg 0 s h hy0 hs
      rw [hΦ0', sub_zero, dist_comm] at this
      rwa [abs_of_nonneg h]
    · have := hseg s 0 h hs hy0
      rw [hΦ0', zero_sub] at this
      rwa [abs_of_nonpos h]

/-- LC34, crossing height `h_ρ` for the LC30 radial function. -/
theorem radial_distance_crossing_height (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M} {η : M → ℝ} {ε : ℝ≥0} {e : ℝ}
    (hε : (ε : ℝ) < 1 / 2) (he : e < 1 / 40) (hclose : ∀ x, |η x - dist p x| < e)
    (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x))
    {ρ : ℝ} (hρ : ρ ∈ Icc (1 / 5 : ℝ) 2) :
    ∃ Φ : ℝ → Diffeomorph I I M M ∞, (∀ y, η y ∈ Icc (1 / 8 : ℝ) 3 →
        ∀ s ∈ Icc (1 / 8 : ℝ) 3, η (Φ (s - η y) y) = s) ∧
      ∃ hρ : M → ℝ, ContinuousOn hρ (η ⁻¹' Icc (1 / 8) 3) ∧
        (∀ y, η y ∈ Icc (1 / 8 : ℝ) 3 → ∀ s, η y + s ∈ Icc (1 / 8 : ℝ) 3 →
          hρ (Φ s y) = hρ y) ∧
        ∀ y, η y ∈ Icc (1 / 8 : ℝ) 3 →
          hρ y ∈ Ioo (1 / 8) 3 ∧ |hρ y - ρ| < e ∧ dist p (Φ (hρ y - η y) y) = ρ ∧
          ∀ u ∈ Icc (1 / 8 : ℝ) 3, (dist p (Φ (u - η y) y) ≤ ρ ↔ u ≤ hρ y) ∧
            (dist p (Φ (u - η y) y) < ρ ↔ u < hρ y) ∧
            (dist p (Φ (u - η y) y) = ρ ↔ u = hρ y) := by
  have hη : Continuous η :=
    (hlip.continuous.add (continuous_const.dist continuous_id)).congr
      (fun x => sub_add_cancel (η x) (dist p x))
  obtain ⟨Φ, hΦc, hΦadd, -, hval, hslope, -⟩ :=
    radial_flow_data g hEnorm (by linarith) he hclose hlip hW hCW hηW hgrad
  refine ⟨Φ, hval, ?_⟩
  exact exists_distance_crossing_height (a := 1 / 8) (b := 3)
    (c := (1 - 2 * (ε : ℝ)) / (1 - ε)) (ρ := ρ) hη (continuous_const.dist continuous_id) hΦc
    hΦadd hval (div_pos (by linarith) (by linarith)) hslope hclose (by linarith [hρ.1])
    (by linarith [hρ.2])

/-- LC34: the radial sublevel `A_ρ` is carried onto the closed distance ball by a continuous
isotopy of homeomorphisms with small tracks. -/
theorem radial_distance_sublevel_isotopy (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M} {η : M → ℝ} {ε : ℝ≥0} {e : ℝ}
    (hε : (ε : ℝ) < 1 / 2) (he : e < 1 / 40) (hclose : ∀ x, |η x - dist p x| < e)
    (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x))
    {ρ : ℝ} (hρ : ρ ∈ Icc (1 / 5 : ℝ) 2) :
    ∃ Hs : ℝ → M ≃ₜ M,
      Continuous (fun q : ℝ × M => Hs q.1 q.2) ∧
      Continuous (fun q : ℝ × M => (Hs q.1).symm q.2) ∧
      (∀ x, Hs 0 x = x) ∧ (∀ t x, η x ∉ Ioo (1 / 8 : ℝ) 3 → Hs t x = x) ∧
      (∀ t x, dist (Hs t x) x < e / (1 - ε)) ∧
      Hs 1 '' {x | η x ≤ ρ} = Metric.closedBall p ρ ∧
      Hs 1 '' {x | η x = ρ} = Metric.sphere p ρ ∧
      Hs 1 '' {x | η x < ρ} = Metric.ball p ρ := by
  have hη : Continuous η :=
    (hlip.continuous.add (continuous_const.dist continuous_id)).congr
      (fun x => sub_add_cancel (η x) (dist p x))
  have hm : 0 < 1 - (ε : ℝ) := by linarith
  obtain ⟨Φ, hΦc, hΦadd, hΦ0, hval, hslope, hlipΦ⟩ :=
    radial_flow_data g hEnorm (by linarith) he hclose hlip hW hCW hηW hgrad
  obtain ⟨Hs, hHc, hHsc, hH0, hHfix, htrack, h1, h2, h3⟩ :=
    exists_distance_sublevel_isotopy (a := 1 / 8) (b := 3) (c := (1 - 2 * (ε : ℝ)) / (1 - ε))
      (ρ := ρ) (d := fun x => dist p x) (Φ := fun t x => Φ t x) hη
      (continuous_const.dist continuous_id) hΦc hΦadd hΦ0
      hval (div_pos (by linarith) (by linarith)) hslope hclose
      (by linarith [hρ.1]) (by linarith [hρ.2])
  have hball : {x | dist p x ≤ ρ} = Metric.closedBall p ρ := by
    ext x; rw [mem_ofPred_eq, Metric.mem_closedBall, dist_comm]
  have hsph : {x | dist p x = ρ} = Metric.sphere p ρ := by
    ext x; rw [mem_ofPred_eq, Metric.mem_sphere, dist_comm]
  have hob : {x | dist p x < ρ} = Metric.ball p ρ := by
    ext x; rw [mem_ofPred_eq, Metric.mem_ball, dist_comm]
  refine ⟨Hs, hHc, hHsc, hH0, hHfix, ?_, hball ▸ h1, hsph ▸ h2, hob ▸ h3⟩
  intro t x
  obtain ⟨s, hs, hx, hband⟩ := htrack t x
  rw [hx]
  by_cases hxb : η x ∈ Icc (1 / 8 : ℝ) 3
  · calc dist (Φ s x) x ≤ (1 - (ε : ℝ))⁻¹ * |s| := hlipΦ x hxb s (hband hxb)
      _ < (1 - (ε : ℝ))⁻¹ * e := mul_lt_mul_of_pos_left hs (inv_pos.mpr hm)
      _ = e / (1 - ε) := by rw [inv_mul_eq_div]
  · have hs0 : Φ s x = x := by
      rw [← hx]
      exact hHfix t x (fun h => hxb (Ioo_subset_Icc_self h))
    rw [hs0, dist_self]
    have := lt_of_le_of_lt (abs_nonneg _) hs
    exact div_pos this hm

end DifferentialGeometry.Geometry.Collapse
