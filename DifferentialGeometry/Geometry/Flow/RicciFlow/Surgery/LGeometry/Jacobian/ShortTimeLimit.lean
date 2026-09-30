import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Jacobian.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Truncation
import DifferentialGeometry.Analysis.Integration.Measure.ParamDensityComposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShortTime.ReducedJacobianLimit

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature (metricScalarAt)
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Integral.Measure (paramDensity)
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)

universe u

variable {H : ObservedHistory.{u}}

private theorem continuousWithinAt_stageMetric_inner {j : Fin (H.eventCount + 1)} {t : ℝ}
    (ht : t ∈ H.stageDomain j) (hjt : H.time j < t) (y : (H.stage j).Carrier)
    (u w : TangentSpace ThreeModel y) :
    ContinuousWithinAt (fun r => (H.stageMetric j r).inner y u w) (Ioo (H.time j) t) t := by
  cases j using Fin.lastCases with
  | last =>
    have ht' : t ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon := by
      simpa [stageDomain] using ht
    have hh : H.time (Fin.last H.eventCount) < H.horizon := hjt.trans_le ht'.2
    have hc := (H.finalSlab hh).equation.smoothMetric.coeff_cont y u w t ht'
    simp only [stageMetric, Fin.lastCases_last, dite_eq_left hh]
    exact hc.mono fun r hr => ⟨hr.1.le, hr.2.le.trans ht'.2⟩
  | cast i =>
    have ht' : t ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
      simpa [stageDomain] using ht
    have hc := (H.event i).incoming.equation.smoothMetric.coeff_cont y u w t ht'
    simp only [stageMetric, Fin.lastCases_castSucc]
    exact hc.mono fun r hr => ⟨hr.1.le, hr.2.trans ht'.2⟩

private theorem lt_regularizedStageEnd_of_lt {j : Fin (H.eventCount + 1)} {T b s : ℝ}
    (hs0 : 0 ≤ s) (hsb : s < b) (hst : s ^ 2 < T - H.time j) :
    s < H.regularizedStageEnd T b j := by
  unfold regularizedStageEnd
  rw [Real.lt_sqrt hs0]
  have hsb2 : s ^ 2 < b ^ 2 := pow_lt_pow_left₀ hsb hs0 two_ne_zero
  rcases le_total (T - b ^ 2) (H.time j) with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

private theorem sqrt_det_inner_comp {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] (g : SmoothRiemannianMetric ThreeModel X) (y : X)
    (A : ThreeSpace →L[ℝ] ThreeSpace) :
    Real.sqrt (Matrix.of fun i k : Fin (Module.finrank ℝ ThreeSpace) =>
      g.inner y (A (chartModelBasis ThreeSpace i)) (A (chartModelBasis ThreeSpace k))).det =
      |LinearMap.det (A : ThreeSpace →ₗ[ℝ] ThreeSpace)| *
        Real.sqrt (Matrix.of fun i k : Fin (Module.finrank ℝ ThreeSpace) =>
          g.inner y (chartModelBasis ThreeSpace i) (chartModelBasis ThreeSpace k)).det := by
  let B : LinearMap.BilinForm ℝ ThreeSpace := (g.inner y).toLinearMap₁₂
  have h1 : (Matrix.of fun i k : Fin (Module.finrank ℝ ThreeSpace) =>
      g.inner y (A (chartModelBasis ThreeSpace i)) (A (chartModelBasis ThreeSpace k))) =
      (B.comp (A : ThreeSpace →ₗ[ℝ] ThreeSpace) A).toMatrix (chartModelBasis ThreeSpace) := by
    ext i k
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  have h2 : (Matrix.of fun i k : Fin (Module.finrank ℝ ThreeSpace) =>
      g.inner y (chartModelBasis ThreeSpace i) (chartModelBasis ThreeSpace k)) =
      B.toMatrix (chartModelBasis ThreeSpace) := by
    ext i k
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  rw [h1, h2, LinearMap.BilinForm.toMatrix_comp (chartModelBasis ThreeSpace)
    (chartModelBasis ThreeSpace), Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix, show ∀ d G : ℝ, d * G * d = d ^ 2 * G from fun d G => by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

private theorem exists_contMDiff_eqOn_Icc {X : Type*} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] {γ : ℝ → X} {K : Set ℝ} (hK : IsOpen K)
    (hKc : IsPreconnected K)
    {c b : ℝ} (hc : 0 < c) (hcb : c < b) (hKsub : Icc 0 b ⊆ K)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ γ K) :
    ∃ α : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ α ∧ EqOn α γ (Icc 0 c) := by
  have h0K : (0 : ℝ) ∈ K := hKsub ⟨le_rfl, hc.le.trans hcb.le⟩
  obtain ⟨η₁, hη₁, hball⟩ := Metric.isOpen_iff.1 hK 0 h0K
  have hneg : -(η₁ / 2) ∈ K := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hη₁)]
    linarith)
  set η := min (η₁ / 2) (b - c) with hηdef
  have hη : 0 < η := lt_min (half_pos hη₁) (by linarith)
  have hη1 : η ≤ η₁ / 2 := min_le_left _ _
  have hη2 : η ≤ b - c := min_le_right _ _
  have hsub : Ioo (-η) (c + η) ⊆ K := fun t ht =>
    hKc.Icc_subset hneg (hKsub ⟨hc.le.trans hcb.le, le_rfl⟩)
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let ψ : ContDiffBump (c / 2 : ℝ) := ⟨c / 2, c / 2 + η, half_pos hc, by linarith⟩
  let φ : ℝ → ℝ := fun t => ψ t * t
  have hφ : ContDiff ℝ ∞ φ := ψ.contDiff.mul contDiff_id
  have hφK : ∀ t, φ t ∈ K := by
    intro t
    by_cases ht : t ∈ Ioo (-η) (c + η)
    · have h0 : 0 ≤ ψ t := ψ.nonneg
      have h1 : ψ t ≤ 1 := ψ.le_one
      apply hsub
      rcases le_total 0 t with htt | htt
      · exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
      · exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    · have hz : ψ t = 0 := by
        apply ψ.zero_of_le_dist
        change c / 2 + η ≤ dist t (c / 2)
        rw [Real.dist_eq]
        by_contra hlt
        exact ht ⟨by linarith [(abs_lt.1 (not_le.1 hlt)).1],
          by linarith [(abs_lt.1 (not_le.1 hlt)).2]⟩
      change ψ t * t ∈ K
      rw [hz, zero_mul]
      exact h0K
  refine ⟨γ ∘ φ, hγ.comp_contMDiff hφ.contMDiff hφK, fun t ht => ?_⟩
  have h1 : ψ t = 1 := ψ.one_of_mem_closedBall (by
    change dist t (c / 2) ≤ c / 2
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [ht.1, ht.2])
  change γ (ψ t * t) = γ t
  rw [h1, one_mul]

section BaseWindow

variable {last : Fin (H.eventCount + 1)} {T : ℝ} (W : H.LWindow last last T)

private theorem mem_stageDomain_of_a_eq_zero (ha : W.a = 0) : T ∈ H.stageDomain last := by
  have h := W.upper
  rw [ha] at h
  simpa using h

private theorem sub_sq_mem_stageDomain (ha : W.a = 0) {v : ℝ} (hv : 0 < v)
    (hvT : v ^ 2 < T - H.time last) : T - v ^ 2 ∈ H.stageDomain last :=
  H.mem_stageDomain_of_mem_Ioo ⟨by linarith, lt_of_lt_of_le (by linarith [pow_pos hv 2])
    (H.le_stageEndTime_of_mem_stageDomain (mem_stageDomain_of_a_eq_zero W ha))⟩

private theorem metric_eq_localPullMetric_of_a_eq_zero (ha : W.a = 0) (hT : H.time last < T) :
    W.S.base.metric T = localPullMetric (H.stageMetric last T) (W.f ⟨last, le_rfl, le_rfl⟩)
      (W.localDiffeomorph _) := by
  ext y u w
  rw [localPullMetric_inner]
  have hb : 0 < W.b := ha ▸ W.lt
  set c := min W.b (Real.sqrt (T - H.time last)) with hcdef
  have hc0 : 0 < c := lt_min hb (Real.sqrt_pos.2 (by linarith))
  have hcb : c ^ 2 ≤ W.b ^ 2 := pow_le_pow_left₀ hc0.le (min_le_left _ _) 2
  have hcT : c ^ 2 ≤ T - H.time last := by
    calc c ^ 2 ≤ Real.sqrt (T - H.time last) ^ 2 := pow_le_pow_left₀ hc0.le (min_le_right _ _) 2
      _ = T - H.time last := Real.sq_sqrt (by linarith)
  have hstart : H.regularizedStageStart T W.a last = 0 := by
    rw [H.regularizedStageStart_eq_of_mem_Icc W.nonneg W.upper_mem_Icc, ha]
  have hsq : ∀ t ∈ Ioo (T - c ^ 2) T, 0 < Real.sqrt (T - t) ∧
      Real.sqrt (T - t) ^ 2 < c ^ 2 ∧ T - Real.sqrt (T - t) ^ 2 = t := by
    intro t ht
    have h1 : Real.sqrt (T - t) ^ 2 = T - t := Real.sq_sqrt (by linarith [ht.2])
    exact ⟨Real.sqrt_pos.2 (by linarith [ht.2]), by rw [h1]; linarith [ht.1], by rw [h1]; ring⟩
  have hsb : ∀ t ∈ Ioo (T - c ^ 2) T, Real.sqrt (T - t) < W.b := fun t ht => by
    obtain ⟨h0, h1, -⟩ := hsq t ht
    nlinarith
  have key : ∀ t ∈ Ioo (T - c ^ 2) T, (W.S.base.metric t).inner y u w =
      (H.stageMetric last t).inner (W.f ⟨last, le_rfl, le_rfl⟩ y)
        (mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) y u)
        (mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) y w) := by
    intro t ht
    obtain ⟨h0, h1, h2⟩ := hsq t ht
    have hm := W.metric ⟨last, le_rfl, le_rfl⟩ (Real.sqrt (T - t))
      ⟨by rw [hstart]; exact h0, lt_regularizedStageEnd_of_lt h0.le (hsb t ht) (by linarith)⟩
    rw [h2] at hm
    rw [hm, localPullMetric_inner]
  have hTc : T ∈ W.D.carrier := by
    have h := W.mem_carrier (s := 0) ⟨ha.le, hb.le⟩
    simpa using h
  have hsub : Ioo (T - c ^ 2) T ⊆ W.D.carrier := fun t ht => by
    obtain ⟨h0, -, h2⟩ := hsq t ht
    have h := W.mem_carrier (s := Real.sqrt (T - t)) ⟨ha ▸ h0.le, (hsb t ht).le⟩
    rwa [h2] at h
  have hL : ContinuousWithinAt (fun t => (W.S.base.metric t).inner y u w) (Ioo (T - c ^ 2) T) T :=
    (W.solution.smoothMetric.coeff_cont y u w T hTc).mono hsub
  have hR := (continuousWithinAt_stageMetric_inner (mem_stageDomain_of_a_eq_zero W ha) hT
    (W.f ⟨last, le_rfl, le_rfl⟩ y)
    (mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) y u)
    (mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) y w)).mono
    (show Ioo (T - c ^ 2) T ⊆ Ioo (H.time last) T from fun t ht => ⟨by linarith [ht.1], ht.2⟩)
  have := right_nhdsWithin_Ioo_neBot (show T - c ^ 2 < T by linarith [pow_pos hc0 2])
  exact tendsto_nhds_unique_of_eventuallyEq hL.tendsto hR.tendsto
    (eventually_nhdsWithin_of_forall key)

variable (ha : W.a = 0) {x : W.X} {Zx : TangentSpace ThreeModel x}
  (hdom : W.b ∈ lRegularizedDomain W.S T x Zx)

include ha hdom in
private theorem isHistoryLGeodesicOn_comp_lRegularizedCurve {v : ℝ} (hv : 0 < v) (hvb : v < W.b)
    (hvT : v ^ 2 < T - H.time last) :
    H.IsHistoryLGeodesicOn (le_refl last) T v
      (fun j => W.f j ∘ lRegularizedCurve W.S T x Zx) := by
  have hgeo := isLRegularizedGeodesicOn_lRegularizedCurve W.S W.solution T x Zx
  have hsub : Icc 0 W.b ⊆ lRegularizedDomain W.S T x Zx := fun s hs =>
    lRegularizedDomain_segment W.S T x Zx hdom hs.1 hs.2
  have hup : T - (0 : ℝ) ^ 2 ∈ H.stageDomain last := by
    simpa using mem_stageDomain_of_a_eq_zero W ha
  have hdown := sub_sq_mem_stageDomain W ha hv hvT
  let W' := W.restrict (a' := 0) (b' := v) le_rfl le_rfl le_rfl ha.le hv hvb.le hup hdown
  refine ⟨hdown, fun i hf hl => absurd (hf.trans_lt (i.castSucc_lt_succ.trans_le hl))
    (lt_irrefl _), fun s hs => ⟨last, last, le_rfl, le_rfl, W', hs, le_rfl, ?_⟩, ?_⟩
  · have hg1 : IsLRegularizedGeodesicOn W.S T (lRegularizedCurve W.S T x Zx) (Ioo 0 v) :=
      fun r hr => hgeo r (hsub ⟨hr.1.le, hr.2.le.trans hvb.le⟩)
    exact ⟨(lRegularizedCurve W.S T x Zx : ℝ → W.X), hg1, fun j r _ => rfl⟩
  have hd := (hgeo v (hsub ⟨hv.le, hvb.le⟩)).2.1
  exact ((W.localDiffeomorph _).contMDiff.continuous.continuousAt.comp
    hd.continuousAt).continuousWithinAt

include ha hdom in
private theorem hasHistoryLInitialVector_comp_lRegularizedCurve {p : (H.stage last).Carrier}
    (hx : W.f ⟨last, le_rfl, le_rfl⟩ x = p) {Z : TangentSpace ThreeModel p}
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) x Zx = Z) :
    H.HasHistoryLInitialVector T (fun j => W.f j ∘ lRegularizedCurve W.S T x Zx) p Z :=
  ⟨last, le_rfl, W, x, Zx, ha, hx, hZ, hdom, fun _ _ _ => rfl⟩

include ha hdom in
private theorem mem_historyLExpDomain_of_window {p : (H.stage last).Carrier}
    (hx : W.f ⟨last, le_rfl, le_rfl⟩ x = p) {Z : TangentSpace ThreeModel p}
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) x Zx = Z) {v : ℝ}
    (hv : 0 < v) (hvb : v < W.b) (hvT : v ^ 2 < T - H.time last) :
    Z ∈ H.historyLExpDomain (le_refl last) T v p :=
  ⟨_, isHistoryLGeodesicOn_comp_lRegularizedCurve W ha hdom hv hvb hvT,
    hasHistoryLInitialVector_comp_lRegularizedCurve W ha hdom hx hZ⟩

include ha hdom in
private theorem historyLCurve_eqOn_window {p : (H.stage last).Carrier}
    (hx : W.f ⟨last, le_rfl, le_rfl⟩ x = p) {v : ℝ} (hv : 0 < v) (hvb : v < W.b)
    (hvT : v ^ 2 < T - H.time last) (Z : H.historyLExpDomain (le_refl last) T v p)
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) x Zx = Z.1) :
    EqOn (H.historyLCurve (le_refl last) T v p Z ⟨last, le_rfl, le_rfl⟩)
      (W.f ⟨last, le_rfl, le_rfl⟩ ∘ lRegularizedCurve W.S T x Zx) (Icc 0 v) := by
  have h := eqOn_historyLCurve hv Z (isHistoryLGeodesicOn_comp_lRegularizedCurve W ha hdom hv
    hvb hvT) (hasHistoryLInitialVector_comp_lRegularizedCurve W ha hdom hx hZ)
    ⟨last, le_rfl, le_rfl⟩
  have hup : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    have h0 := mem_stageDomain_of_a_eq_zero W ha
    simpa using
      And.intro (H.time_le_of_mem_stageDomain h0) (H.le_stageEndTime_of_mem_stageDomain h0)
  rwa [H.regularizedStageStart_eq_of_mem_Icc le_rfl hup,
    H.regularizedStageEnd_eq_of_mem_stageDomain hv.le (sub_sq_mem_stageDomain W ha hv hvT)] at h

include hdom in
private theorem exists_nhds_lRegularizedDomain :
    ∃ V : Set ThreeSpace, IsOpen V ∧ (Zx : ThreeSpace) ∈ V ∧
      (∀ Z ∈ V, W.b ∈ lRegularizedDomain W.S T x Z) ∧
      ∀ s ∈ Icc 0 W.b, MDifferentiableAt 𝓘(ℝ, ThreeSpace) ThreeModel
        (fun Z : ThreeSpace => lRegularizedCurve W.S T x (Z : TangentSpace ThreeModel x) s)
        (Zx : ThreeSpace) := by
  obtain ⟨α, J, hJo, hJc, h0J, hbJ, hcurve⟩ := hdom
  obtain ⟨V, hV, hZV, K, hK, hKc, h0K, hbK, fam, hfam, hfamc⟩ :=
    lRegularizedFamily_extend W.S W.solution T hJo hJc h0J hbJ hcurve
  refine ⟨V, hV, hZV, fun Z hZ => ⟨_, K, hK, hKc, h0K, hbK, hfamc Z hZ⟩, fun s hs => ?_⟩
  have hsK : s ∈ K := hKc.Icc_subset h0K hbK hs
  let z : ThreeSpace := Zx
  have hzV : z ∈ V := hZV
  have hsmooth : MDifferentiableAt 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => fam (Z, s)) z :=
    (((hfam (z, s) ⟨hzV, hsK⟩).contMDiffAt ((hV.prod hK).mem_nhds ⟨hzV, hsK⟩)).comp z
      (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp)
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards [hV.mem_nhds hzV] with Z hZ
  exact lRegularizedCurve_eqOn W.S W.solution T hK hKc h0K (hfamc Z hZ) hsK

include ha hdom in
private theorem historyLAction_eq_window {p : (H.stage last).Carrier}
    (hx : W.f ⟨last, le_rfl, le_rfl⟩ x = p) {v : ℝ} (hv : 0 < v) (hvb : v < W.b)
    (hvT : v ^ 2 < T - H.time last) (Z : H.historyLExpDomain (le_refl last) T v p)
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) x Zx = Z.1) :
    H.historyLAction (le_refl last) T v p Z =
      lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 v := by
  have heq := historyLCurve_eqOn_window W ha hdom hx hv hvb hvT Z hZ
  have hgeo := isLRegularizedGeodesicOn_lRegularizedCurve W.S W.solution T x Zx
  have hup : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    have h0 := mem_stageDomain_of_a_eq_zero W ha
    simpa using
      And.intro (H.time_le_of_mem_stageDomain h0) (H.le_stageEndTime_of_mem_stageDomain h0)
  have hstart : H.regularizedStageStart T W.a last = 0 := by
    rw [H.regularizedStageStart_eq_of_mem_Icc W.nonneg W.upper_mem_Icc, ha]
  unfold historyLAction
  rw [Fintype.sum_eq_single ⟨last, le_rfl, le_rfl⟩
    (fun j hj => absurd (Subtype.ext (le_antisymm j.2.2 j.2.1)) hj),
    H.regularizedStageStart_eq_of_mem_Icc le_rfl hup,
    H.regularizedStageEnd_eq_of_mem_stageDomain hv.le (sub_sq_mem_stageDomain W ha hv hvT)]
  unfold stageRegularizedAction lRegularizedAction
  rw [intervalIntegral.integral_of_le hv.le, intervalIntegral.integral_of_le hv.le,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hev : H.historyLCurve (le_refl last) T v p Z ⟨last, le_rfl, le_rfl⟩ =ᶠ[𝓝 t]
      W.f ⟨last, le_rfl, le_rfl⟩ ∘ lRegularizedCurve W.S T x Zx := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact heq (Ioo_subset_Icc_self hr)
  have hvel : lVelocity (I := ThreeModel) (H.historyLCurve (le_refl last) T v p Z
      ⟨last, le_rfl, le_rfl⟩) t =
      lVelocity (I := ThreeModel)
        (W.f ⟨last, le_rfl, le_rfl⟩ ∘ lRegularizedCurve W.S T x Zx) t := by
    have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) hev
    with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf
  have hval := hev.self_of_nhds
  have htb : t < W.b := ht.2.trans hvb
  have hm := W.metric ⟨last, le_rfl, le_rfl⟩ t ⟨by rw [hstart]; exact ht.1,
    lt_regularizedStageEnd_of_lt ht.1.le htb (by nlinarith [ht.1, ht.2])⟩
  have hdiff := (hgeo t (lRegularizedDomain_segment W.S T x Zx hdom ht.1.le htb.le)).2.1
  rw [← H.stageRegularizedLagrangian_comp_eq_of_localPullMetric last W.S _
    (W.localDiffeomorph ⟨last, le_rfl, le_rfl⟩) T hdiff hm]
  unfold stageRegularizedLagrangian
  rw [hval, hvel]

include ha hdom in
private theorem historyLJacobianDensity_div_eq (hT : H.time last < T) {p : (H.stage last).Carrier}
    (hx : W.f ⟨last, le_rfl, le_rfl⟩ x = p) {v : ℝ} (hv : 0 < v) (hvb : v < W.b)
    (hvT : v ^ 2 < T - H.time last) (Z₀ : H.historyLExpDomain (le_refl last) T v p)
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) x Zx = Z₀.1) :
    H.historyLJacobianDensity (le_refl last) T v p Z₀ ⟨last, le_rfl, le_rfl⟩ v /
      H.historyLSourceDensity T p =
      paramDensity (W.S.base.metric (T - v ^ 2))
        (fun Z : ThreeSpace => lRegularizedCurve W.S T x Z v) Zx /
      Real.sqrt (Matrix.of fun i k : Fin (Module.finrank ℝ ThreeSpace) =>
        (W.S.base.metric T).inner x (chartModelBasis ThreeSpace i)
          (chartModelBasis ThreeSpace k)).det := by
  obtain ⟨V, hV, hZxV, hVdom, hMD⟩ := exists_nhds_lRegularizedDomain W hdom
  let e :=
    (W.localDiffeomorph ⟨last, le_rfl, le_rfl⟩).mfderivToContinuousLinearEquiv (by simp) x
  let L : ThreeSpace →L[ℝ] ThreeSpace :=
    (e.symm : TangentSpace ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩ x) →L[ℝ]
      TangentSpace ThreeModel x)
  let A : ThreeSpace →L[ℝ] ThreeSpace :=
    (e : TangentSpace ThreeModel x →L[ℝ]
      TangentSpace ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩ x))
  have hLe : ∀ Z : ThreeSpace,
      mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) x (L Z) = Z :=
    fun Z => e.apply_symm_apply Z
  have hLZ : L Z₀.1 = Zx := by
    have h : e Zx = Z₀.1 := hZ
    rw [← h]
    exact e.symm_apply_apply Zx
  have hLA : LinearMap.det (L : ThreeSpace →ₗ[ℝ] ThreeSpace) *
      LinearMap.det (A : ThreeSpace →ₗ[ℝ] ThreeSpace) = 1 := by
    rw [← LinearMap.det_comp]
    have hid :
        (L : ThreeSpace →ₗ[ℝ] ThreeSpace).comp (A : ThreeSpace →ₗ[ℝ] ThreeSpace) =
        LinearMap.id := LinearMap.ext fun Z => e.symm_apply_apply Z
    rw [hid, LinearMap.det_id]
  let Φ : ThreeSpace → W.X := fun Z => lRegularizedCurve W.S T x Z v
  let z : ThreeSpace := Zx
  have hΦ : MDifferentiableAt 𝓘(ℝ, ThreeSpace) ThreeModel Φ z := hMD v ⟨hv.le, hvb.le⟩
  have hfd : MDifferentiableAt ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) (Φ z) :=
    (W.localDiffeomorph _ _).mdifferentiableAt (by simp)
  have hev : ((W.f ⟨last, le_rfl, le_rfl⟩ ∘ Φ) ∘ L) =ᶠ[𝓝 Z₀.1]
      H.historyLCurveMap (le_refl last) T v p Z₀ ⟨last, le_rfl, le_rfl⟩ v := by
    have hmem : L ⁻¹' V ∈ 𝓝 Z₀.1 :=
      L.continuous.continuousAt.preimage_mem_nhds (by rw [hLZ]; exact hV.mem_nhds hZxV)
    filter_upwards [hmem] with Z hZV
    have hdomZ := hVdom (L Z) hZV
    have hmemZ := mem_historyLExpDomain_of_window W ha hdomZ hx (hLe Z) hv hvb hvT
    rw [historyLCurveMap_of_mem _ _ hmemZ]
    exact (historyLCurve_eqOn_window W ha hdomZ hx hv hvb hvT ⟨Z, hmemZ⟩ (hLe Z)
      ⟨hv.le, le_rfl⟩).symm
  have h1 :=
    paramDensity_eq_historyLJacobianDensity_of_eventuallyEq ⟨last, le_rfl, le_rfl⟩ v hev
  have hstart : H.regularizedStageStart T W.a last = 0 := by
    rw [H.regularizedStageStart_eq_of_mem_Icc W.nonneg W.upper_mem_Icc, ha]
  have hm := W.metric ⟨last, le_rfl, le_rfl⟩ v ⟨by rw [hstart]; exact hv,
    lt_regularizedStageEnd_of_lt hv.le hvb hvT⟩
  have h3 := DifferentialGeometry.Integral.Measure.paramDensity_comp_of_inner_eq
    (W.S.base.metric (T - v ^ 2)) (H.stageMetric last (T - v ^ 2)) hfd hΦ
    (fun u u' => by rw [hm, localPullMetric_inner])
  have h2 := DifferentialGeometry.Integral.Measure.paramDensity_comp
    (H.stageMetric last (T - v ^ 2)) (Φ := W.f ⟨last, le_rfl, le_rfl⟩ ∘ Φ) (ψ := L)
    (x := Z₀.1)
    (by rw [hLZ]; exact hfd.comp z hΦ) L.differentiableAt
  have hLf : fderiv ℝ (⇑L) Z₀.1 = L := L.fderiv
  rw [hLf, hLZ, h3] at h2
  have hsrc : Real.sqrt (Matrix.of fun i k : Fin (Module.finrank ℝ ThreeSpace) =>
      (W.S.base.metric T).inner x (chartModelBasis ThreeSpace i)
        (chartModelBasis ThreeSpace k)).det =
      |LinearMap.det (A : ThreeSpace →ₗ[ℝ] ThreeSpace)| * H.historyLSourceDensity T p := by
    have hmat : (Matrix.of fun i k : Fin (Module.finrank ℝ ThreeSpace) =>
        (W.S.base.metric T).inner x (chartModelBasis ThreeSpace i)
          (chartModelBasis ThreeSpace k)) =
        Matrix.of fun i k : Fin (Module.finrank ℝ ThreeSpace) =>
        (H.stageMetric last T).inner (W.f ⟨last, le_rfl, le_rfl⟩ x)
          (A (chartModelBasis ThreeSpace i)) (A (chartModelBasis ThreeSpace k)) := by
      ext i k
      simp only [Matrix.of_apply]
      rw [metric_eq_localPullMetric_of_a_eq_zero W ha hT]
      exact localPullMetric_inner (H.stageMetric last T) _ _ x _ _
    rw [hmat]
    subst hx
    exact sqrt_det_inner_comp (H.stageMetric last T) (W.f ⟨last, le_rfl, le_rfl⟩ x) A
  have hA : LinearMap.det (A : ThreeSpace →ₗ[ℝ] ThreeSpace) ≠ 0 := fun h => by
    rw [h, mul_zero] at hLA
    exact zero_ne_one hLA
  rw [← h1]
  erw [h2]
  rw [hsrc, mul_comm |LinearMap.det (A : ThreeSpace →ₗ[ℝ] ThreeSpace)|,
    ← mul_div_mul_right _ _ (abs_ne_zero.2 hA)]
  change |LinearMap.det (L : ThreeSpace →ₗ[ℝ] ThreeSpace)| * _ *
    |LinearMap.det (A : ThreeSpace →ₗ[ℝ] ThreeSpace)| / _ = _
  rw [mul_right_comm, ← abs_mul, hLA, abs_one, one_mul]

include hdom in
private theorem exists_contMDiffOn_lRegularizedCurve :
    ∃ K : Set ℝ, IsOpen K ∧ IsPreconnected K ∧ Icc 0 W.b ⊆ K ∧
      ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (lRegularizedCurve W.S T x Zx) K := by
  obtain ⟨α, J, hJo, hJc, h0J, hbJ, hcurve⟩ := hdom
  obtain ⟨V, hV, hZV, K, hK, hKc, h0K, hbK, fam, hfam, hfamc⟩ :=
    lRegularizedFamily_extend W.S W.solution T hJo hJc h0J hbJ hcurve
  let z : ThreeSpace := Zx
  have hzV : z ∈ V := hZV
  refine ⟨K, hK, hKc, hKc.Icc_subset h0K hbK, ?_⟩
  have hs : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (fun s => fam (z, s)) K :=
    hfam.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn fun s hs => ⟨hzV, hs⟩
  exact hs.congr fun s hsK => lRegularizedCurve_eqOn W.S W.solution T hK hKc h0K
    (hfamc z hzV) hsK

variable {B : ℝ} (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ y : (H.stage j).Carrier,
  -B ≤ metricScalarAt (H.stageMetric j t) y)

include ha hdom hfloor in
private theorem lRegularizedAction_le_of_mem_historyMinDomain {p : (H.stage last).Carrier}
    (hx : W.f ⟨last, le_rfl, le_rfl⟩ x = p) {Z : TangentSpace ThreeModel p}
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) x Zx = Z) {c : ℝ}
    (hc : 0 < c) (hcb : c < W.b) (hcT : c ^ 2 < T - H.time last)
    (hmin : Z ∈ H.historyMinDomain (le_refl last) T B c p) (δ : ℝ → W.X)
    (hδ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ) (hδ0 : δ 0 = x)
    (hδc : δ c = lRegularizedCurve W.S T x Zx c) :
    lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 c ≤
      lRegularizedAction W.S T δ 0 c := by
  obtain ⟨α, hgeo, hinit, hac, hp, hmin', hfin⟩ := hmin
  have huniq := IsHistoryLGeodesicOn.eqOn_of_hasHistoryLInitialVector hc hgeo
    (isHistoryLGeodesicOn_comp_lRegularizedCurve W ha hdom hc hcb hcT) hinit
    (hasHistoryLInitialVector_comp_lRegularizedCurve W ha hdom hx hZ)
  have hup0 : T - (0 : ℝ) ^ 2 ∈ H.stageDomain last := by
    simpa using mem_stageDomain_of_a_eq_zero W ha
  have hupIcc : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hup0, H.le_stageEndTime_of_mem_stageDomain hup0⟩
  have hdown := sub_sq_mem_stageDomain W ha hc hcT
  obtain ⟨K, -, -, hKsub, hsm⟩ := exists_contMDiffOn_lRegularizedCurve W hdom
  have hγac : Manifold.absolutelyContinuousOnInterval ThreeModel
      (lRegularizedCurve W.S T x Zx) 0 c :=
    Manifold.absolutelyContinuousOnInterval_of_contMDiffOn ((hsm.mono (by
      rw [uIcc_of_le hc.le]
      exact (Icc_subset_Icc le_rfl hcb.le).trans hKsub)).of_le (by norm_num))
  rw [← hp] at hmin'
  let W' := W.restrict (a' := 0) (b' := c) le_rfl le_rfl le_rfl ha.le hc hcb.le hup0 hdown
  exact W'.lRegularizedAction_le_of_regularizedCost_eq (le_refl last) le_rfl le_rfl
    (u := 0) (v := c) le_rfl le_rfl le_rfl hupIcc hdown hfloor α hac
    (fun i hf hl => absurd (hf.trans_lt (i.castSucc_lt_succ.trans_le hl)) (lt_irrefl _))
    hmin' hfin (lRegularizedCurve W.S T x Zx : ℝ → W.X) hγac
    (fun j => (huniq ⟨j.val, j.2.1, j.2.2⟩).symm) δ hδ
    (hδ0.trans (lRegularizedCurve_zero W.S T x Zx).symm) hδc

include ha hdom hfloor in
private theorem mem_lMinDomain_of_mem_historyMinDomain {p : (H.stage last).Carrier}
    (hx : W.f ⟨last, le_rfl, le_rfl⟩ x = p) {Z : TangentSpace ThreeModel p}
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) x Zx = Z) {c : ℝ}
    (hc : 0 < c) (hcb : c < W.b) (hcT : c ^ 2 < T - H.time last)
    (hmin : Z ∈ H.historyMinDomain (le_refl last) T B c p) :
    (Zx, c ^ 2) ∈ lMinDomain W.S T x ∧
      BddBelow {r : ℝ | ∃ α : ℝ → W.X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α ∧
        α 0 = x ∧
        α (Real.sqrt (c ^ 2)) = lExp W.S T x Zx (c ^ 2) ∧
        lRegularizedAction W.S T α 0 (Real.sqrt (c ^ 2)) = r} := by
  have hsq : Real.sqrt (c ^ 2) = c := Real.sqrt_sq hc.le
  have hlow := lRegularizedAction_le_of_mem_historyMinDomain W ha hdom hfloor hx hZ hc hcb hcT hmin
  obtain ⟨K, hK, hKc, hKsub, hsm⟩ := exists_contMDiffOn_lRegularizedCurve W hdom
  obtain ⟨αe, hαe, heqe⟩ := exists_contMDiff_eqOn_Icc hK hKc hc hcb hKsub hsm
  have hαe1 : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 αe := hαe.of_le (by norm_num)
  have hαe0 : αe 0 = x := (heqe ⟨le_rfl, hc.le⟩).trans (lRegularizedCurve_zero W.S T x Zx)
  have hαec : αe c = lRegularizedCurve W.S T x Zx c := heqe ⟨hc.le, le_rfl⟩
  have hαeA : lRegularizedAction W.S T αe 0 c =
      lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 c :=
    lRegularizedAction_congr W.S T _ _ 0 c fun t ht => heqe (by
      rw [uIoo_of_le hc.le] at ht
      exact Ioo_subset_Icc_self ht)
  have hExp : lExp W.S T x Zx (c ^ 2) = lRegularizedCurve W.S T x Zx c := by
    change lRegularizedCurve W.S T x Zx (Real.sqrt (c ^ 2)) = _
    rw [hsq]
  have hLen : ∀ α : ℝ → W.X, lLength W.S T (squareRootReparametrization α) 0 (c ^ 2) =
      lRegularizedAction W.S T α 0 c := fun α => by
    rw [lLength_squareRootReparametrization_eq_lRegularizedAction W.S T α (c ^ 2) (sq_nonneg c),
      hsq]
  refine ⟨⟨⟨pow_pos hc 2, ?_⟩, ?_⟩,
    ⟨lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 c, ?_⟩⟩
  · change Real.sqrt (c ^ 2) ∈ lRegularizedDomain W.S T x Zx
    rw [hsq]
    exact lRegularizedDomain_segment W.S T x Zx hdom hc.le hcb.le
  · change lLength W.S T (squareRootReparametrization (lRegularizedCurve W.S T x Zx)) 0 (c ^ 2) =
      lCost W.S T x (lExp W.S T x Zx (c ^ 2)) (c ^ 2)
    rw [hLen, lCost]
    refine le_antisymm (le_csInf ⟨_, αe, hαe1, hαe0, by rw [hsq, hExp, hαec], rfl⟩ ?_)
      (csInf_le ⟨lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 c, ?_⟩
        ⟨αe, hαe1, hαe0, by rw [hsq, hExp, hαec], by rw [hLen, hαeA]⟩)
    · rintro r ⟨α, hα, h0, h1, rfl⟩
      rw [hLen]
      rw [hsq, hExp] at h1
      exact hlow α hα h0 h1
    · rintro r ⟨α, hα, h0, h1, rfl⟩
      rw [hLen]
      rw [hsq, hExp] at h1
      exact hlow α hα h0 h1
  · rintro r ⟨α, hα, h0, h1, rfl⟩
    rw [hsq] at h1 ⊢
    rw [hExp] at h1
    exact hlow α hα h0 h1

include ha hdom in
private theorem historyReducedJacobian_eq_of_window (hT : H.time last < T)
    {p : (H.stage last).Carrier} (hx : W.f ⟨last, le_rfl, le_rfl⟩ x = p)
    {Z : TangentSpace ThreeModel p}
    (hZ : mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) x Zx = Z) {v : ℝ}
    (hv : 0 < v) (hvb : v < W.b) (hvT : v ^ 2 < T - H.time last)
    (hZv : Z ∈ H.historyLExpDomain (le_refl last) T v p) :
    H.historyReducedJacobian (le_refl last) T v p ⟨Z, hZv⟩ =
      paramDensity (W.S.base.metric (T - v ^ 2))
          (fun Z : ThreeSpace => lRegularizedCurve W.S T x Z v) Zx /
        Real.sqrt (Matrix.of fun i k : Fin (Module.finrank ℝ ThreeSpace) =>
          (W.S.base.metric T).inner x (chartModelBasis ThreeSpace i)
            (chartModelBasis ThreeSpace k)).det *
      Real.exp (-lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 v / (2 * v) -
        (3 / 2 : ℝ) * Real.log (v ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi)) := by
  rw [historyReducedJacobian,
    historyLJacobianDensity_div_eq W ha hdom hT hx hv hvb hvT ⟨Z, hZv⟩ hZ,
    historyLAction_eq_window W ha hdom hx hv hvb hvT ⟨Z, hZv⟩ hZ]

end BaseWindow

private theorem exp_sub_log_normalization {v : ℝ} (hv : 0 < v) (a : ℝ) :
    Real.exp (a - (3 / 2 : ℝ) * Real.log (v ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi)) =
      Real.exp a / ((2 * v) ^ 3 * Real.pi ^ ((3 : ℝ) / 2)) := by
  have h1 : Real.exp ((3 / 2 : ℝ) * Real.log (v ^ 2)) = v ^ 3 := by
    rw [mul_comm, ← Real.rpow_def_of_pos (pow_pos hv 2), ← Real.rpow_natCast v 2,
      ← Real.rpow_mul hv.le, show ((2 : ℕ) : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have h2 : Real.exp ((3 / 2 : ℝ) * Real.log (4 * Real.pi)) = 8 * Real.pi ^ ((3 : ℝ) / 2) := by
    rw [mul_comm, ← Real.rpow_def_of_pos (by positivity),
      Real.mul_rpow (by norm_num) Real.pi_pos.le,
      show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
      show (2 : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [Real.exp_sub, Real.exp_sub, h1, h2]
  ring

section Limit

variable {last : Fin (H.eventCount + 1)} {T : ℝ} {p : (H.stage last).Carrier}

private theorem exists_base_window {v₀ : ℝ}
    (Z₀ : H.historyLExpDomain (le_refl last) T v₀ p) :
    ∃ (W : H.LWindow last last T) (x : W.X) (Zx : TangentSpace ThreeModel x), W.a = 0 ∧
      W.f ⟨last, le_rfl, le_rfl⟩ x = p ∧
      mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) x Zx = Z₀.1 ∧
      W.b ∈ lRegularizedDomain W.S T x Zx := by
  obtain ⟨lo, hlo, W, x, Zx, ha, hx, hZ, hdom, -⟩ := hasHistoryLInitialVector_historyLCurve Z₀
  obtain rfl : last = lo := le_antisymm hlo W.le
  exact ⟨W, x, Zx, ha, hx, hZ, hdom⟩

theorem exists_lWindow_historyReducedJacobian_eq (hT : H.time last < T) {v₀ : ℝ}
    (Z₀ : H.historyLExpDomain (le_refl last) T v₀ p) :
    ∃ (W : H.LWindow last last T) (x : W.X) (Zx : TangentSpace ThreeModel x),
      W.a = 0 ∧ W.f ⟨last, le_rfl, le_rfl⟩ x = p ∧
      mfderiv ThreeModel ThreeModel (W.f ⟨last, le_rfl, le_rfl⟩) x Zx = Z₀.1 ∧
      W.S.base.metric T = localPullMetric (H.stageMetric last T) (W.f ⟨last, le_rfl, le_rfl⟩)
        (W.localDiffeomorph _) ∧
      ∃ δ > 0, ∀ v ∈ Ioo 0 δ,
        ∃ hZ : (Z₀.1 : TangentSpace ThreeModel p) ∈ H.historyLExpDomain (le_refl last) T v p,
          H.historyReducedJacobian (le_refl last) T v p ⟨Z₀.1, hZ⟩ =
            paramDensity (W.S.base.metric (T - v ^ 2))
                (fun Z : ThreeSpace => lRegularizedCurve W.S T x Z v) Zx /
              Real.sqrt (Matrix.of fun i k : Fin (Module.finrank ℝ ThreeSpace) =>
                (W.S.base.metric T).inner x (chartModelBasis ThreeSpace i)
                  (chartModelBasis ThreeSpace k)).det *
            Real.exp (-lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 v / (2 * v) -
              (3 / 2 : ℝ) * Real.log (v ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi)) := by
  obtain ⟨W, x, Zx, ha, hx, hZ, hdom⟩ := exists_base_window Z₀
  have hb : 0 < W.b := ha ▸ W.lt
  refine ⟨W, x, Zx, ha, hx, hZ, metric_eq_localPullMetric_of_a_eq_zero W ha hT,
    min W.b (Real.sqrt (T - H.time last)), lt_min hb (Real.sqrt_pos.2 (by linarith)),
    fun v hv => ?_⟩
  have hvb : v < W.b := hv.2.trans_le (min_le_left _ _)
  have hvT : v ^ 2 < T - H.time last :=
    (Real.lt_sqrt hv.1.le).1 (hv.2.trans_le (min_le_right _ _))
  have hZv := mem_historyLExpDomain_of_window W ha hdom hx hZ hv.1 hvb hvT
  exact ⟨hZv, historyReducedJacobian_eq_of_window W ha hdom hT hx hZ hv.1 hvb hvT hZv⟩

open Classical in
theorem tendsto_historyReducedJacobian_nhdsGT_zero (hT : H.time last < T) {v₀ : ℝ}
    (Z₀ : H.historyLExpDomain (le_refl last) T v₀ p) :
    Tendsto (fun v => if hZ : (Z₀.1 : TangentSpace ThreeModel p) ∈
        H.historyLExpDomain (le_refl last) T v p then
        H.historyReducedJacobian (le_refl last) T v p ⟨Z₀.1, hZ⟩ else 0) (𝓝[>] 0)
      (𝓝 ((Real.pi ^ ((3 : ℝ) / 2))⁻¹ *
        Real.exp (-(H.stageMetric last T).inner p Z₀.1 Z₀.1))) := by
  obtain ⟨W, x, Zx, ha, hx, hZ, hmet, δ, hδ, hid⟩ :=
    exists_lWindow_historyReducedJacobian_eq hT Z₀
  let _ : TopologicalSpace.MetrizableSpace W.X := Manifold.metrizableSpace ThreeModel W.X
  let _ : MetricSpace W.X := TopologicalSpace.metrizableSpaceMetric W.X
  have hTreg : T ∈ W.D.regular := by
    have h := W.regular 0 ⟨ha.le, (ha ▸ W.lt).le⟩
    simpa using h
  have hden := tendsto_normalized_lExpDensity_at_zero W.S W.solution T x Zx hTreg
  rw [finrank_euclideanSpace_fin] at hden
  have hact : Tendsto (fun s => -lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 s /
      (2 * s)) (𝓝[>] 0) (𝓝 (-(W.S.base.metric T).inner x Zx Zx)) := by
    simpa only [neg_div] using
      (tendsto_lRegularizedAction_div_at_zero W.S W.solution T x Zx hTreg).neg
  have hsrc : 0 < lSourceDensity W.S T x := lSourceDensity_pos W.S T x
  have hG := ((hden.div_const (lSourceDensity W.S T x)).mul_const
    (Real.pi ^ ((3 : ℝ) / 2))⁻¹).mul (Real.continuous_exp.continuousAt.tendsto.comp hact)
  have hgauss : (W.S.base.metric T).inner x Zx Zx =
      (H.stageMetric last T).inner p Z₀.1 Z₀.1 := by
    rw [hmet, localPullMetric_inner, hZ]
    subst hx
    rfl
  rw [div_self hsrc.ne', one_mul, hgauss] at hG
  refine hG.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with v hv
  obtain ⟨hZv, hval⟩ := hid v hv
  have hfun : (fun Z : ThreeSpace => lExp W.S T x Z (v ^ 2)) =
      fun Z : ThreeSpace => lRegularizedCurve W.S T x Z v :=
    funext fun Z => by
      change lRegularizedCurve W.S T x Z (Real.sqrt (v ^ 2)) = _
      rw [Real.sqrt_sq hv.1.le]
  have hPE : lExpDensity W.S T x Zx (v ^ 2) = paramDensity (W.S.base.metric (T - v ^ 2))
      (fun Z : ThreeSpace => lExp W.S T x Z (v ^ 2)) Zx := rfl
  rw [hfun] at hPE
  simp only [Function.comp_apply]
  rw [dite_eq_left hZv, hval, exp_sub_log_normalization hv.1, ← hPE]
  change _ = lExpDensity W.S T x Zx (v ^ 2) / lSourceDensity W.S T x * _
  field_simp

theorem le_gaussian_of_antitoneOn_of_eventuallyEq_historyReducedJacobian
    (hT : H.time last < T) {v₀ : ℝ}
    (Z₀ : H.historyLExpDomain (le_refl last) T v₀ p) {F : ℝ → ℝ} {v₂ : ℝ}
    (hF : AntitoneOn F (Ioc 0 v₂))
    (hbase : ∀ᶠ v in 𝓝[>] 0, ∀ hZ : (Z₀.1 : TangentSpace ThreeModel p) ∈
      H.historyLExpDomain (le_refl last) T v p,
        F v = H.historyReducedJacobian (le_refl last) T v p ⟨Z₀.1, hZ⟩)
    {v : ℝ} (hv : v ∈ Ioc 0 v₂) :
    F v ≤ (Real.pi ^ ((3 : ℝ) / 2))⁻¹ *
      Real.exp (-(H.stageMetric last T).inner p Z₀.1 Z₀.1) := by
  classical
  obtain ⟨W, x, Zx, -, -, -, -, δ, hδ, hid⟩ :=
    exists_lWindow_historyReducedJacobian_eq hT Z₀
  have hlim : Tendsto F (𝓝[>] 0) (𝓝 ((Real.pi ^ ((3 : ℝ) / 2))⁻¹ *
      Real.exp (-(H.stageMetric last T).inner p Z₀.1 Z₀.1))) := by
    refine (tendsto_historyReducedJacobian_nhdsGT_zero hT Z₀).congr' ?_
    filter_upwards [hbase, Ioo_mem_nhdsGT hδ] with w hw hwδ
    obtain ⟨hZw, -⟩ := hid w hwδ
    rw [dite_eq_left hZw, hw hZw]
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hv.1] with w hw
  exact hF ⟨hw.1, hw.2.le.trans hv.2⟩ hv hw.2.le

open Classical in
theorem historyReducedJacobian_le_gaussian_of_antitoneOn (hT : H.time last < T) {v₀ : ℝ}
    (Z₀ : H.historyLExpDomain (le_refl last) T v₀ p) {v₂ : ℝ}
    (hanti : AntitoneOn (fun v => if hZ : (Z₀.1 : TangentSpace ThreeModel p) ∈
        H.historyLExpDomain (le_refl last) T v p then
        H.historyReducedJacobian (le_refl last) T v p ⟨Z₀.1, hZ⟩ else 0) (Ioc 0 v₂))
    {v : ℝ} (hv : v ∈ Ioc 0 v₂)
    (hZ : (Z₀.1 : TangentSpace ThreeModel p) ∈ H.historyLExpDomain (le_refl last) T v p) :
    H.historyReducedJacobian (le_refl last) T v p ⟨Z₀.1, hZ⟩ ≤
      (Real.pi ^ ((3 : ℝ) / 2))⁻¹ *
        Real.exp (-(H.stageMetric last T).inner p Z₀.1 Z₀.1) := by
  have h := le_gaussian_of_antitoneOn_of_eventuallyEq_historyReducedJacobian hT Z₀ hanti
    (Eventually.of_forall fun w hw => dite_eq_left hw) hv
  rwa [dite_eq_left hZ] at h

theorem exists_pos_historyReducedJacobian_le_gaussian (hT : H.time last < T) {B v₂ : ℝ}
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ y : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) y)
    (hv₂ : 0 < v₂) {Z₀ : TangentSpace ThreeModel p}
    (hZ₀ : Z₀ ∈ H.historyMinDomain (le_refl last) T B v₂ p) :
    ∃ δ > 0, ∀ v ∈ Ioo 0 δ, ∀ hZ : Z₀ ∈ H.historyLExpDomain (le_refl last) T v p,
      H.historyReducedJacobian (le_refl last) T v p ⟨Z₀, hZ⟩ ≤
        (Real.pi ^ ((3 : ℝ) / 2))⁻¹ *
          Real.exp (-(H.stageMetric last T).inner p Z₀ Z₀) := by
  obtain ⟨W, x, Zx, ha, hx, hZ, hdom⟩ := exists_base_window
    (⟨Z₀, historyMinDomain_subset_historyLExpDomain hZ₀⟩ :
      H.historyLExpDomain (le_refl last) T v₂ p)
  have hb : 0 < W.b := ha ▸ W.lt
  have hm0 : 0 < min (min W.b (Real.sqrt (T - H.time last))) v₂ :=
    lt_min (lt_min hb (Real.sqrt_pos.2 (by linarith))) hv₂
  set c := min (min W.b (Real.sqrt (T - H.time last))) v₂ / 2 with hcdef
  have hc : 0 < c := half_pos hm0
  have hcm : c < min (min W.b (Real.sqrt (T - H.time last))) v₂ := half_lt_self hm0
  have hcb : c < W.b := hcm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hcv : c ≤ v₂ := (hcm.trans_le (min_le_right _ _)).le
  have hcT : c ^ 2 < T - H.time last :=
    (Real.lt_sqrt hc.le).1 (hcm.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hminc := mem_historyMinDomain_of_le hfloor (le_refl last) hc hcv
    (sub_sq_mem_stageDomain W ha hc hcT) hZ₀
  obtain ⟨hmin, hbdd⟩ := mem_lMinDomain_of_mem_historyMinDomain W ha hdom hfloor hx hZ hc hcb
    hcT hminc
  refine ⟨c, hc, fun v hv hZv => ?_⟩
  have hvb : v < W.b := hv.2.trans hcb
  have hvc2 : v ^ 2 < c ^ 2 := pow_lt_pow_left₀ hv.2 hv.1.le two_ne_zero
  have hvT : v ^ 2 < T - H.time last := hvc2.trans hcT
  rw [historyReducedJacobian_eq_of_window W ha hdom hT hx hZ hv.1 hvb hvT hZv]
  let _ : TopologicalSpace.MetrizableSpace W.X := Manifold.metrizableSpace ThreeModel W.X
  let _ : MetricSpace W.X := TopologicalSpace.metrizableSpaceMetric W.X
  have hv2 : 0 < v ^ 2 := pow_pos hv.1 2
  have hsq : Real.sqrt (v ^ 2) = v := Real.sqrt_sq hv.1.le
  have hle := lReducedJacobian_le_gaussian_of_bdd W.S W.solution T x hmin hv2 hvc2 hbdd
  have hdomv : (Zx, v ^ 2) ∈ lExpPosDom W.S T x := ⟨hv2, by
    change Real.sqrt (v ^ 2) ∈ lRegularizedDomain W.S T x Zx
    rw [hsq]
    exact lRegularizedDomain_segment W.S T x Zx hdom hv.1.le hvb.le⟩
  have hnc := lMinVec_nconj_lt_of_bdd W.S W.solution T x hmin hvc2 hbdd
  have hmv := lMinDomain_down_of_bdd W.S W.solution T x Zx hmin hv2 hvc2.le
    (lRegularizedCosts_prefix_bdd_of_min W.S W.solution T x Zx hmin hv2 hvc2.le hbdd) hbdd
  have hA : lCost W.S T x (lExp W.S T x Zx (v ^ 2)) (v ^ 2) =
      lRegularizedAction W.S T (lRegularizedCurve W.S T x Zx) 0 v := by
    rw [← ((mem_lMinDomain W.S T x Zx (v ^ 2)).1 hmv).2]
    change lLength W.S T (squareRootReparametrization (lRegularizedCurve W.S T x Zx)) 0 (v ^ 2) = _
    rw [lLength_squareRootReparametrization_eq_lRegularizedAction W.S T _ (v ^ 2) hv2.le, hsq]
  have hsrc : 0 < lSourceDensity W.S T x := lSourceDensity_pos W.S T x
  have hfun : (fun Z : ThreeSpace => lExp W.S T x Z (v ^ 2)) =
      fun Z : ThreeSpace => lRegularizedCurve W.S T x Z v :=
    funext fun Z => by
      change lRegularizedCurve W.S T x Z (Real.sqrt (v ^ 2)) = _
      rw [hsq]
  have hPE : lExpDensity W.S T x Zx (v ^ 2) = paramDensity (W.S.base.metric (T - v ^ 2))
      (fun Z : ThreeSpace => lExp W.S T x Z (v ^ 2)) Zx := rfl
  rw [hfun] at hPE
  have hRJ := lRedJac_mul_src_of_nonconj W.S T x Zx (v ^ 2) hdomv hnc
  rw [← eq_div_iff hsrc.ne'] at hRJ
  unfold redDensity redLength at hRJ
  rw [hA, hsq, hPE, finrank_euclideanSpace_fin] at hRJ
  have hgauss : (W.S.base.metric T).inner x Zx Zx = (H.stageMetric last T).inner p Z₀ Z₀ := by
    rw [metric_eq_localPullMetric_of_a_eq_zero W ha hT, localPullMetric_inner, hZ]
    subst hx
    rfl
  have h3 : ((3 : ℕ) : ℝ) / 2 = 3 / 2 := by norm_num
  rw [hRJ, finrank_euclideanSpace_fin, hgauss, h3, ← neg_div] at hle
  change _ / lSourceDensity W.S T x * _ ≤ _
  rwa [div_mul_eq_mul_div]

end Limit

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
