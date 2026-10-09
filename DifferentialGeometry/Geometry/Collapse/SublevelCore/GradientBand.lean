import DifferentialGeometry.Geometry.Collapse.SublevelCore.FieldBand
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ProperSublevel
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Geometry.Metric.CurveSpeed

/-!
# LC33: normalized gradient product on the band

Blueprint LC33 (master207A:21422), constants `a = 1/8`, `b = 3`, base level `Σ = η⁻¹(1)`.

* Kernel (metric spaces), `le_sub_dist_of_lipschitz_level_curve`: if `η - d_p` is
  `ε`-Lipschitz and a curve `γ` with `η (γ u) = u` moves at most `L (t - s)` between times
  `s ≤ t`, then `d_p(γ t) - d_p(γ s) ≥ (1 - ε L)(t - s)`. With `L = (1-ε)⁻¹` this is the blueprint
  track estimate with `c_ε = (1 - 2ε)/(1 - ε)`.
* Binding (PC Riemannian setting), `radialBand_gradient_product`: LC46 applied to `Y = ∇η`
  gives the product `η⁻¹(1) × [1/8, 3] ≃ K` along the flow of `X = ∇η / |∇η|²`, with speed
  `|X| ≤ (1-ε)⁻¹` on the band and the track estimate along every coordinate curve.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

/-- LC33 kernel: the track estimate along a curve transverse to the levels. -/
theorem le_sub_dist_of_lipschitz_level_curve {X : Type*} [PseudoMetricSpace X] {p : X}
    {η : X → ℝ} {ε : ℝ≥0} (hlip : LipschitzWith ε (fun x => η x - dist p x)) {γ : ℝ → X}
    {L s t : ℝ} (hγ : dist (γ s) (γ t) ≤ L * (t - s)) (hs : η (γ s) = s)
    (ht : η (γ t) = t) :
    (1 - ε * L) * (t - s) ≤ dist p (γ t) - dist p (γ s) := by
  have h := hlip.dist_le_mul (γ t) (γ s)
  rw [Real.dist_eq, ht, hs, dist_comm (γ t) (γ s)] at h
  have h2 := (abs_le.mp (h.trans (mul_le_mul_of_nonneg_left hγ ε.2))).2
  nlinarith

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

/-- LC33, binding form. The flow `Φ` of a compactly supported extension of
`X = ∇η / |∇η|²` gives product coordinates `η⁻¹(1) × [1/8, 3] ≃ η⁻¹[1/8, 3]`,
`(x, u) ↦ Φ (u - 1) x`; along the band its velocity is `X`, of `g`-length at most `(1-ε)⁻¹`,
and the distance from `p` grows at least at rate `(1 - 2ε)/(1 - ε)` along each coordinate curve. -/
theorem radialBand_gradient_product (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M} {η : M → ℝ} {ε : ℝ≥0} {e : ℝ}
    (hε1 : (ε : ℝ) < 1) (he : e < 1 / 40) (hclose : ∀ x, |η x - dist p x| < e)
    (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x)) :
    ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      Φ 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (Φ q.1).symm q.2) ∧
      (∀ s t x, Φ (s + t) x = Φ t (Φ s x)) ∧
      (∀ x, η x ∈ Icc (1 / 8 : ℝ) 3 → ∀ s ∈ Icc (1 / 8 : ℝ) 3, η (Φ (s - η x) x) = s) ∧
      (∃ S : Set M, IsCompact S ∧ S ⊆ W ∧ ∀ t x, x ∉ S → Φ t x = x ∧ (Φ t).symm x = x) ∧
      (∀ x t, η (Φ t x) ∈ Icc (1 / 8 : ℝ) 3 →
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t ((1 : ℝ →L[ℝ] ℝ).smulRight
          ((g.inner (Φ t x) (gradientFun (I := I) g η (Φ t x))
            (gradientFun (I := I) g η (Φ t x)))⁻¹ • gradientFun (I := I) g η (Φ t x)))) ∧
      (∀ y, η y ∈ Icc (1 / 8 : ℝ) 3 →
        √(g.inner y ((g.inner y (gradientFun (I := I) g η y) (gradientFun (I := I) g η y))⁻¹ •
            gradientFun (I := I) g η y)
          ((g.inner y (gradientFun (I := I) g η y) (gradientFun (I := I) g η y))⁻¹ •
            gradientFun (I := I) g η y)) ≤ (1 - (ε : ℝ))⁻¹) ∧
      (∀ x, η x = 1 → ∀ s t, 1 / 8 ≤ s → s ≤ t → t ≤ 3 →
        (1 - 2 * (ε : ℝ)) / (1 - ε) * (t - s) ≤
          dist p (Φ (t - 1) x) - dist p (Φ (s - 1) x)) ∧
      ∃ e : ({x : M // η x = 1} × Icc (1 / 8 : ℝ) 3) ≃ₜ {x : M // η x ∈ Icc (1 / 8 : ℝ) 3},
        (∀ q, (e q : M) = Φ (q.2 - 1) q.1) ∧
        (∀ y, ((e.symm y).1 : M) = Φ (1 - η y) y) ∧
        (∀ y, ((e.symm y).2 : ℝ) = η y) ∧
        (∀ q, η (e q) = q.2) ∧
        ∀ x : {x : M // η x = 1}, (e (x, ⟨1, by norm_num, by norm_num⟩) : M) = x := by
  have hη : Continuous η := by
    have h2 : Continuous (fun x : M => dist p x) := continuous_const.dist continuous_id
    exact (hlip.continuous.add h2).congr (fun x => sub_add_cancel (η x) (dist p x))
  have : ProperSpace M :=
    ⟨fun x r => DifferentialGeometry.Geometry.Topology.soul_isCompact_closedBall
      (I := I) g hEnorm x r⟩
  set K := η ⁻¹' Icc (1 / 8 : ℝ) 3 with hKdef
  have hK : IsCompact K := isCompact_preimage_of_abs_sub_dist_lt hη hclose isCompact_Icc
  have hKann := radialBand_subset_annulus hclose he
  have hKC : ∀ x ∈ K, 1 / 10 ≤ dist p x ∧ dist p x ≤ 10 := fun x hx =>
    ⟨(hKann hx).1.le, (hKann hx).2.le⟩
  have hKW : K ⊆ W := fun x hx => hCW x (hKC x hx).1 (hKC x hx).2
  have hm : 0 < 1 - (ε : ℝ) := by linarith
  have hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, gradientFun (I := I) g η x⟩ : TangentBundle I M)) W := fun x hx =>
    (gradientFun_contMDiffAt (I := I) g (hηW.contMDiffAt (hW.mem_nhds hx))).contMDiffWithinAt
  have hnorm : ∀ x ∈ K, (1 - (ε : ℝ)) ^ 2 ≤
      g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x) := fun x hx =>
    hgrad x (hKC x hx).1 (hKC x hx).2
  have hdY : ∀ x, mvfderiv (I := I) η x (gradientFun (I := I) g η x) =
      g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x) := fun x =>
    (inner_gradientFun (I := I) g η x _).symm
  have hpos : ∀ x ∈ K, 0 < mvfderiv (I := I) η x (gradientFun (I := I) g η x) := by
    intro x hx
    rw [hdY]
    exact lt_of_lt_of_le (by positivity) (hnorm x hx)
  obtain ⟨Φ, hΦ0, hΦc, hΦs, hΦadd, hval, hsupp, hvel, e, he1, he2, he3, he4, he5⟩ :=
    exists_field_band_product_of_contMDiffOn hη hW hηW (by norm_num : (1 / 8 : ℝ) < 3)
      (⟨by norm_num, by norm_num⟩ : (1 : ℝ) ∈ Icc (1 / 8 : ℝ) 3) hK hKW
      (gradientFun (I := I) g η) hY hpos
  have hvel' : ∀ x t, η (Φ t x) ∈ Icc (1 / 8 : ℝ) 3 →
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t ((1 : ℝ →L[ℝ] ℝ).smulRight
        ((g.inner (Φ t x) (gradientFun (I := I) g η (Φ t x))
          (gradientFun (I := I) g η (Φ t x)))⁻¹ • gradientFun (I := I) g η (Φ t x))) := by
    intro x t ht
    have h := hvel x t ht
    rwa [hdY] at h
  have hspeed : ∀ y, η y ∈ Icc (1 / 8 : ℝ) 3 →
      √(g.inner y ((g.inner y (gradientFun (I := I) g η y) (gradientFun (I := I) g η y))⁻¹ •
          gradientFun (I := I) g η y)
        ((g.inner y (gradientFun (I := I) g η y) (gradientFun (I := I) g η y))⁻¹ •
          gradientFun (I := I) g η y)) ≤ (1 - (ε : ℝ))⁻¹ := by
    intro y hy
    set G := gradientFun (I := I) g η y
    set q := g.inner y G G with hq
    have hqpos : (1 - (ε : ℝ)) ^ 2 ≤ q := hnorm y hy
    have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hqpos
    have hval' : g.inner y (q⁻¹ • G) (q⁻¹ • G) = q⁻¹ := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      rw [← hq]
      field_simp
    rw [hval']
    rw [show (1 - (ε : ℝ))⁻¹ = √(((1 - ε) ^ 2)⁻¹) by
      rw [Real.sqrt_inv, Real.sqrt_sq hm.le]]
    exact Real.sqrt_le_sqrt (inv_anti₀ (by positivity) hqpos)
  refine ⟨Φ, hΦ0, hΦc, hΦs, hΦadd, hval, hsupp, hvel', hspeed, ?_, e, he1, he2, he3, he4, he5⟩
  intro x hx s t hs hst ht
  set x' := Φ (-1) x with hx'
  have hγ : ∀ u, Φ (u - 1) x = Φ u x' := by
    intro u
    rw [hx', ← hΦadd]
    ring_nf
  have hlev : ∀ u ∈ Icc (1 / 8 : ℝ) 3, η (Φ u x') = u := by
    intro u hu
    rw [← hγ]
    have h := hval x (by rw [hx]; norm_num) u hu
    rwa [hx] at h
  have hsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun u => Φ u x') :=
    hΦc.comp (contMDiff_id.prodMk contMDiff_const)
  have hdist : dist (Φ s x') (Φ t x') ≤ (1 - (ε : ℝ))⁻¹ * (t - s) := by
    have hb := DifferentialGeometry.Geometry.riemannianEDistOf_le_of_curve_speed_bound g hst
      (hsm.contMDiffOn.of_le (by norm_num)) (C := (1 - (ε : ℝ))⁻¹) (by
        intro u hu
        have huI : u ∈ Icc (1 / 8 : ℝ) 3 := ⟨hs.trans hu.1.le, hu.2.le.trans ht⟩
        have hin : η (Φ u x') ∈ Icc (1 / 8 : ℝ) 3 := by rw [hlev u huI]; exact huI
        have hd := (hvel' x' u hin).mfderiv
        erw [hd]
        convert hspeed _ hin using 4 <;> exact one_smul ℝ _)
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hm.le),
      riemannianEDistOf_eq_riemannianEDist g hEnorm, ← IsRiemannianManifold.out (I := I),
      edist_dist] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (inv_nonneg.mpr hm.le)
      (sub_nonneg.mpr hst))).mp hb
  have hk := le_sub_dist_of_lipschitz_level_curve hlip (γ := fun u => Φ u x') hdist
    (hlev s ⟨hs, hst.trans ht⟩) (hlev t ⟨hs.trans hst, ht⟩)
  rw [hγ, hγ]
  have hc : (1 - 2 * (ε : ℝ)) / (1 - ε) = 1 - ε * (1 - (ε : ℝ))⁻¹ := by
    field_simp
    ring
  rw [hc]
  exact hk

end DifferentialGeometry.Geometry.Collapse
