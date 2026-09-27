import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReferenceSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.ReferenceFieldSecondDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReferenceSpeed
import DifferentialGeometry.Geometry.Geodesic.Local
import Mathlib.Topology.Order.Compact

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance supportBoundTopology : TopologicalSpace F.M := F.topology
private local instance supportBoundCharted : ChartedSpace H F.M := F.charted
private local instance supportBoundSmooth : IsManifold I ∞ F.M := F.smooth
private local instance supportBoundT2 : T2Space F.M := F.t2
private local instance supportBoundSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_uniform_redLength_upper_support_second_derivative_bound_on_final_tails
    {δ T a₀ μ Λ A B K₀ C N U : ℝ} (hδ : 0 < δ)
    (ha₀ : a₀ < Real.sqrt δ)
    (hμ : 0 ≤ μ) (hΛ : 0 ≤ Λ) (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ tau ∈ Icc δ T,
      ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
      {I : ModelWithCorners ℝ E H} [I.Boundaryless]
      (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
      {kappa : ℝ}, IsAncientKappaSolution kappa F →
      ∀ (g : SmoothRiemannianMetric I F.M) (p : F.M) (K L : Set F.M),
    ( ∀ (y : F.M), y ∈ K → ∀ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha →
      IsLRegularizedGeodesicOn F.S 0 alpha (Ioc 0 (Real.sqrt tau)) → alpha 0 = p →
      alpha (Real.sqrt tau) = y →
      lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) = lCost F.S 0 p y tau →
      alpha '' Icc (max a₀ (Real.sqrt tau / 2)) (Real.sqrt tau) ⊆ L) →
    ( ∀ y ∈ K, redLength F.S 0 p y tau ≤ U) →
    ( ∀ s ∈ Icc (max a₀ (Real.sqrt tau / 2)) (Real.sqrt tau),
      ∀ x ∈ L, ∀ z : TangentSpace I x,
      g.inner x z z ≤ μ * (F.S.base.metric (0 - s ^ 2)).inner x z z) →
    ( ∀ s ∈ Icc (max a₀ (Real.sqrt tau / 2)) (Real.sqrt tau),
      ∀ x ∈ L, ∀ z : TangentSpace I x,
      (F.S.base.metric (0 - s ^ 2)).inner x z z ≤
        Λ * g.inner x z z) →
    ( ∀ s ∈ Icc (max a₀ (Real.sqrt tau / 2)) (Real.sqrt tau),
      ∀ x ∈ L, ∀ u w : TangentSpace I x,
      Real.sqrt (g.inner x
        (CovariantDerivative.difference (metricCov (F.S.base.metric (0 - s ^ 2)))
          (metricCov g) x u w)
        (CovariantDerivative.difference (metricCov (F.S.base.metric (0 - s ^ 2)))
          (metricCov g) x u w)) ≤
        A * Real.sqrt (g.inner x u u) *
          Real.sqrt (g.inner x w w)) →
    ( ∀ s ∈ Icc (max a₀ (Real.sqrt tau / 2)) (Real.sqrt tau), ∀ x ∈ L,
      Real.sqrt (normSq0S (F.S.base.metric (0 - s ^ 2)) x 4
        (F.S.base.rm04 (0 - s ^ 2) x)) ≤ K₀) →
    ( ∀ s ∈ Icc (max a₀ (Real.sqrt tau / 2)) (Real.sqrt tau), ∀ x ∈ L,
      Real.sqrt (normSq0S (F.S.base.metric (0 - s ^ 2)) x 2
        (hessianSec (I := I) (F.S.base.connection (0 - s ^ 2))
          (metricCov_smooth (I := I) (F.S.base.metric (0 - s ^ 2)))
          (F.S.scalar (0 - s ^ 2)) (scalarSmoothOfSolution F.S (0 - s ^ 2)) x)) ≤ C) →
    ( ∀ s ∈ Icc (max a₀ (Real.sqrt tau / 2)) (Real.sqrt tau), ∀ x ∈ L,
      Real.sqrt (normSq0S (F.S.base.metric (0 - s ^ 2)) x 3
        (totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (F.S.base.connection (0 - s ^ 2))
          (F.S.ricci (0 - s ^ 2)) x)) ≤ N) →
    ∀ beta : ℝ → F.M,
      IsGeodesicAt (I := I) g beta 0 → beta 0 ∈ K →
      Real.sqrt (g.inner (beta 0)
        (lVelocity (I := I) beta 0) (lVelocity (I := I) beta 0)) ≤ B →
      ∃ phi : ℝ → ℝ, ContDiff ℝ 2 phi ∧
        phi 0 = redLength F.S 0 p (beta 0) tau ∧
        (fun r ↦ redLength F.S 0 p (beta r) tau) ≤ᶠ[𝓝 (0 : ℝ)] phi ∧
        deriv (deriv phi) 0 ≤ D := by
  obtain ⟨C₀, hC₀, hproducer⟩ :=
    exists_uniform_redLength_upper_support_norm_bounds_of_ancient
  let V := Real.sqrt μ * Real.sqrt (24 * U)
  let W : ℝ → ℝ := fun tau ↦ C₀ / (Real.sqrt tau - max a₀ (Real.sqrt tau / 2)) * B
  let Vh := Real.sqrt Λ * V
  let Qh := Real.sqrt Λ * B
  let Wh : ℝ → ℝ := fun tau ↦ Real.sqrt Λ * (W tau + A * B * V)
  let D₀ : ℝ → ℝ := fun tau ↦ ((Real.sqrt tau - max a₀ (Real.sqrt tau / 2)) *
    ((1 / 2 : ℝ) * ((Wh tau) ^ 2 + K₀ * Qh ^ 2 * Vh ^ 2) +
      (Real.sqrt tau) ^ 2 * C * Qh ^ 2 + 3 * Real.sqrt tau * N * Vh * Qh ^ 2)) /
      Real.sqrt tau + (Real.sqrt Λ * (0 + A * B ^ 2) * Vh) / (2 * Real.sqrt tau)
  have hsqrt : ContinuousOn Real.sqrt (Icc δ T) := Real.continuous_sqrt.continuousOn
  have hsqrt_ne : ∀ tau ∈ Icc δ T, Real.sqrt tau ≠ 0 := by
    intro tau htau
    exact (Real.sqrt_pos.mpr (hδ.trans_le htau.1)).ne'
  have hcut : ContinuousOn (fun tau ↦ max a₀ (Real.sqrt tau / 2)) (Icc δ T) :=
    (continuous_const.max (Real.continuous_sqrt.div_const 2)).continuousOn
  have hgap_ne : ∀ tau ∈ Icc δ T, Real.sqrt tau - max a₀ (Real.sqrt tau / 2) ≠ 0 := by
    intro tau htau
    have hpos : 0 < Real.sqrt tau := Real.sqrt_pos.mpr (hδ.trans_le htau.1)
    have hleft : a₀ < Real.sqrt tau := ha₀.trans_le (Real.sqrt_le_sqrt htau.1)
    have hright : Real.sqrt tau / 2 < Real.sqrt tau := by linarith
    have hgap : 0 < Real.sqrt tau - max a₀ (Real.sqrt tau / 2) :=
      sub_pos.mpr (max_lt hleft hright)
    exact hgap.ne'
  have hW : ContinuousOn W (Icc δ T) :=
    (continuousOn_const.div (hsqrt.sub hcut) hgap_ne).mul
      continuousOn_const
  have hWh : ContinuousOn Wh (Icc δ T) :=
    continuousOn_const.mul (hW.add continuousOn_const)
  have hcore : ContinuousOn
      (fun tau ↦ (1 / 2 : ℝ) * ((Wh tau) ^ 2 + K₀ * Qh ^ 2 * Vh ^ 2) +
        (Real.sqrt tau) ^ 2 * C * Qh ^ 2 + 3 * Real.sqrt tau * N * Vh * Qh ^ 2)
      (Icc δ T) :=
    ((continuousOn_const.mul ((hWh.pow 2).add continuousOn_const)).add
      (((hsqrt.pow 2).mul continuousOn_const).mul continuousOn_const)).add
        ((((continuousOn_const.mul hsqrt).mul continuousOn_const).mul
          continuousOn_const).mul continuousOn_const)
  have hD₀ : ContinuousOn D₀ (Icc δ T) :=
    (((hsqrt.sub hcut).mul hcore).div hsqrt hsqrt_ne).add
      (continuousOn_const.div (continuousOn_const.mul hsqrt) (by
        intro tau htau
        exact mul_ne_zero (by norm_num) (hsqrt_ne tau htau)))
  obtain ⟨D, hD⟩ := (isCompact_Icc : IsCompact (Icc δ T)).bddAbove_image hD₀
  refine ⟨max D 0, le_max_right _ _, ?_⟩
  intro tau htauInterval E _ _ _ H _ I _ F kappa hF g p K L hcapture hcost
    hreference hmetric hconnection hRm hHess hRic beta hbeta hbetaK hB
  have htau : 0 < tau := hδ.trans_le htauInterval.1
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hc : 0 < max a₀ (Real.sqrt tau / 2) :=
    (half_pos hb).trans_le (le_max_right _ _)
  have hcb : max a₀ (Real.sqrt tau / 2) < Real.sqrt tau :=
    max_lt (ha₀.trans_le (Real.sqrt_le_sqrt htauInterval.1)) (by linarith)
  obtain ⟨alpha, halpha, hstart, hend, hgeo, haction, f, hf, hcenter,
      hcenterGeo, hfixed, hterminal, _hvelocity, hY, hDY, hC2, htouch,
      hupper, _hsecond⟩ :=
    hproducer F hF g p tau (max a₀ (Real.sqrt tau / 2)) htau hc hcb beta hbeta
  have hL (s : ℝ) (hs : s ∈ Icc (max a₀ (Real.sqrt tau / 2)) (Real.sqrt tau)) :
      f 0 s ∈ L := by
    rw [hcenter hs]
    exact hcapture (beta 0) hbetaK alpha halpha hgeo hstart hend
      (by simpa only [hend] using haction) ⟨s, hs, rfl⟩
  have hAvel : ∀ s ∈ Icc (max a₀ (Real.sqrt tau / 2)) (Real.sqrt tau),
      Real.sqrt (g.inner (f 0 s)
        (lVelocity (I := I) (f 0) s) (lVelocity (I := I) (f 0) s)) ≤ V := by
    have hcentral : ContMDiff 𝓘(ℝ, ℝ) I 8 (f 0) :=
      hf.comp (contMDiff_const.prodMk contMDiff_id)
    intro s hs
    have hu := (uniqueDiffOn_Icc hcb s hs).uniqueMDiffWithinAt
    have hderiv := mfderivWithin_congr_of_mem
      (I := 𝓘(ℝ, ℝ)) (I' := I) hcenter hs
    rw [mfderivWithin_eq_mfderiv hu (hcentral.mdifferentiableAt (by norm_num)),
      mfderivWithin_eq_mfderiv hu (halpha.mdifferentiableAt (by norm_num))] at hderiv
    have hvel : lVelocity (I := I) (f 0) s = lVelocity (I := I) alpha s :=
      congrArg (fun D ↦ D (1 : ℝ)) hderiv
    have hbound := lVelocity_norm_le_on_half_tail_of_ancient
      F hF g alpha halpha p htau
      ⟨(le_max_right _ _).trans hs.1, hs.2⟩
      (fun r hr ↦ hgeo r ⟨hr.1, hr.2.le⟩) haction hμ
      (fun z ↦ by
        have hαL : alpha s ∈ L := by rw [← hcenter hs]; exact hL s hs
        simpa only [zero_sub] using hreference s hs (alpha s) hαL z)
      (by simpa only [hend] using hcost (beta 0) hbetaK)
    rw [hcenter hs, hvel]
    exact hbound
  have hbetaC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 beta 0 :=
    (DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt hbeta).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hacc := covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
    g beta 0 hbetaC2
      (IsGeodesicAt.hasGeodesicEquationAt (I := I) g hbeta)
  have haccBound : Real.sqrt (g.inner (beta 0)
      (covDerivAlong g beta
        (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) 0)
      (covDerivAlong g beta
        (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) 0)) ≤ 0 := by
    rw [hacc]
    simp
  have hcoeff : 0 ≤ C₀ / (Real.sqrt tau - max a₀ (Real.sqrt tau / 2)) :=
    div_nonneg hC₀.le (sub_nonneg.mpr hcb.le)
  have hbound := deriv_deriv_lRegularizedAction_div_le_of_reference_field_norm_bounds
    F.S F.isSolution 0 f hf (max a₀ (Real.sqrt tau / 2)) (Real.sqrt tau) hcb.le
    (by simpa only [uIcc_of_le hcb.le] using hcenterGeo)
    (Filter.Eventually.of_forall fun r ↦ (hfixed r).self_of_nhds)
    hterminal (lRegularizedAction F.S 0 alpha 0 (max a₀ (Real.sqrt tau / 2)))
    g hb hΛ hA
    (fun s hs z ↦ hmetric s hs (f 0 s) (hL s hs) z)
    (fun s hs u w ↦ hconnection s hs (f 0 s) (hL s hs) u w)
    hB haccBound
    (fun s hs ↦ hRm s hs (f 0 s) (hL s hs))
    (fun s hs ↦ hHess s hs (f 0 s) (hL s hs))
    (fun s hs ↦ hRic s hs (f 0 s) (hL s hs)) hAvel
    (fun s hs ↦ (hY s hs).trans hB)
    (fun s hs ↦ (hDY s hs).trans (mul_le_mul_of_nonneg_left hB hcoeff))
    (fun s hs ↦ by rw [abs_of_nonneg (hc.le.trans hs.1)]; exact hs.2)
  refine ⟨_, hC2, htouch, hupper, ?_⟩
  exact hbound.trans ((hD ⟨tau, htauInterval, rfl⟩).trans (le_max_left D 0))

theorem exists_uniform_redLength_upper_support_second_derivative_bound_on_time_interval
    {δ T μ Λ A B K₀ C N U : ℝ} (hδ : 0 < δ)
    (hμ : 0 ≤ μ) (hΛ : 0 ≤ Λ) (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ tau ∈ Icc δ T,
      ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
      {I : ModelWithCorners ℝ E H} [I.Boundaryless]
      (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
      {kappa : ℝ}, IsAncientKappaSolution kappa F →
      ∀ (g : SmoothRiemannianMetric I F.M) (p : F.M) (K L : Set F.M),
    ( ∀ (y : F.M), y ∈ K → ∀ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha →
      IsLRegularizedGeodesicOn F.S 0 alpha (Ioc 0 (Real.sqrt tau)) → alpha 0 = p →
      alpha (Real.sqrt tau) = y →
      lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) = lCost F.S 0 p y tau →
      alpha '' Icc (Real.sqrt tau / 2) (Real.sqrt tau) ⊆ L) →
    ( ∀ y ∈ K, redLength F.S 0 p y tau ≤ U) →
    ( ∀ s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau),
      ∀ x ∈ L, ∀ z : TangentSpace I x,
      g.inner x z z ≤ μ * (F.S.base.metric (0 - s ^ 2)).inner x z z) →
    ( ∀ s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau),
      ∀ x ∈ L, ∀ z : TangentSpace I x,
      (F.S.base.metric (0 - s ^ 2)).inner x z z ≤
        Λ * g.inner x z z) →
    ( ∀ s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau),
      ∀ x ∈ L, ∀ u w : TangentSpace I x,
      Real.sqrt (g.inner x
        (CovariantDerivative.difference (metricCov (F.S.base.metric (0 - s ^ 2)))
          (metricCov g) x u w)
        (CovariantDerivative.difference (metricCov (F.S.base.metric (0 - s ^ 2)))
          (metricCov g) x u w)) ≤
        A * Real.sqrt (g.inner x u u) *
          Real.sqrt (g.inner x w w)) →
    ( ∀ s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau), ∀ x ∈ L,
      Real.sqrt (normSq0S (F.S.base.metric (0 - s ^ 2)) x 4
        (F.S.base.rm04 (0 - s ^ 2) x)) ≤ K₀) →
    ( ∀ s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau), ∀ x ∈ L,
      Real.sqrt (normSq0S (F.S.base.metric (0 - s ^ 2)) x 2
        (hessianSec (I := I) (F.S.base.connection (0 - s ^ 2))
          (metricCov_smooth (I := I) (F.S.base.metric (0 - s ^ 2)))
          (F.S.scalar (0 - s ^ 2)) (scalarSmoothOfSolution F.S (0 - s ^ 2)) x)) ≤ C) →
    ( ∀ s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau), ∀ x ∈ L,
      Real.sqrt (normSq0S (F.S.base.metric (0 - s ^ 2)) x 3
        (totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (F.S.base.connection (0 - s ^ 2))
          (F.S.ricci (0 - s ^ 2)) x)) ≤ N) →
    ∀ beta : ℝ → F.M,
      IsGeodesicAt (I := I) g beta 0 → beta 0 ∈ K →
      Real.sqrt (g.inner (beta 0)
        (lVelocity (I := I) beta 0) (lVelocity (I := I) beta 0)) ≤ B →
      ∃ phi : ℝ → ℝ, ContDiff ℝ 2 phi ∧
        phi 0 = redLength F.S 0 p (beta 0) tau ∧
        (fun r ↦ redLength F.S 0 p (beta r) tau) ≤ᶠ[𝓝 (0 : ℝ)] phi ∧
        deriv (deriv phi) 0 ≤ D := by
  obtain ⟨D, hD, hsupport⟩ :=
    exists_uniform_redLength_upper_support_second_derivative_bound_on_final_tails
      (δ := δ) (T := T) (a₀ := 0) (B := B) (K₀ := K₀) (C := C) (N := N) (U := U)
      hδ (Real.sqrt_pos.mpr hδ) hμ hΛ hA
  refine ⟨D, hD, ?_⟩
  intro tau htau E _ _ _ H _ I _ F kappa hF g p K L
  have hhalf : 0 ≤ Real.sqrt tau / 2 := by positivity
  simpa only [max_eq_right hhalf] using
    hsupport tau htau F hF g p K L

theorem exists_uniform_redLength_upper_support_second_derivative_bound_of_reference_norm_bounds
    {tau μ Λ A B K₀ C N U : ℝ} (htau : 0 < tau)
    (hμ : 0 ≤ μ) (hΛ : 0 ≤ Λ) (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
      {I : ModelWithCorners ℝ E H} [I.Boundaryless]
      (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
      {kappa : ℝ}, IsAncientKappaSolution kappa F →
      ∀ (g : SmoothRiemannianMetric I F.M) (p : F.M) (K L : Set F.M),
    ( ∀ (y : F.M), y ∈ K → ∀ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha →
      IsLRegularizedGeodesicOn F.S 0 alpha (Ioc 0 (Real.sqrt tau)) → alpha 0 = p →
      alpha (Real.sqrt tau) = y →
      lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) = lCost F.S 0 p y tau →
      alpha '' Icc (Real.sqrt tau / 2) (Real.sqrt tau) ⊆ L) →
    ( ∀ y ∈ K, redLength F.S 0 p y tau ≤ U) →
    ( ∀ s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau),
      ∀ x ∈ L, ∀ z : TangentSpace I x,
      g.inner x z z ≤ μ * (F.S.base.metric (0 - s ^ 2)).inner x z z) →
    ( ∀ s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau),
      ∀ x ∈ L, ∀ z : TangentSpace I x,
      (F.S.base.metric (0 - s ^ 2)).inner x z z ≤
        Λ * g.inner x z z) →
    ( ∀ s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau),
      ∀ x ∈ L, ∀ u w : TangentSpace I x,
      Real.sqrt (g.inner x
        (CovariantDerivative.difference (metricCov (F.S.base.metric (0 - s ^ 2)))
          (metricCov g) x u w)
        (CovariantDerivative.difference (metricCov (F.S.base.metric (0 - s ^ 2)))
          (metricCov g) x u w)) ≤
        A * Real.sqrt (g.inner x u u) *
          Real.sqrt (g.inner x w w)) →
    ( ∀ s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau), ∀ x ∈ L,
      Real.sqrt (normSq0S (F.S.base.metric (0 - s ^ 2)) x 4
        (F.S.base.rm04 (0 - s ^ 2) x)) ≤ K₀) →
    ( ∀ s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau), ∀ x ∈ L,
      Real.sqrt (normSq0S (F.S.base.metric (0 - s ^ 2)) x 2
        (hessianSec (I := I) (F.S.base.connection (0 - s ^ 2))
          (metricCov_smooth (I := I) (F.S.base.metric (0 - s ^ 2)))
          (F.S.scalar (0 - s ^ 2)) (scalarSmoothOfSolution F.S (0 - s ^ 2)) x)) ≤ C) →
    ( ∀ s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau), ∀ x ∈ L,
      Real.sqrt (normSq0S (F.S.base.metric (0 - s ^ 2)) x 3
        (totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (F.S.base.connection (0 - s ^ 2))
          (F.S.ricci (0 - s ^ 2)) x)) ≤ N) →
    ∀ beta : ℝ → F.M,
      IsGeodesicAt (I := I) g beta 0 → beta 0 ∈ K →
      Real.sqrt (g.inner (beta 0)
        (lVelocity (I := I) beta 0) (lVelocity (I := I) beta 0)) ≤ B →
      ∃ phi : ℝ → ℝ, ContDiff ℝ 2 phi ∧
        phi 0 = redLength F.S 0 p (beta 0) tau ∧
        (fun r ↦ redLength F.S 0 p (beta r) tau) ≤ᶠ[𝓝 (0 : ℝ)] phi ∧
        deriv (deriv phi) 0 ≤ D := by
  obtain ⟨D, hD, hsupport⟩ :=
    exists_uniform_redLength_upper_support_second_derivative_bound_on_time_interval
      (δ := tau) (T := tau) (B := B) (K₀ := K₀) (C := C) (N := N) (U := U)
      htau hμ hΛ hA
  exact ⟨D, hD, hsupport tau ⟨le_rfl, le_rfl⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
