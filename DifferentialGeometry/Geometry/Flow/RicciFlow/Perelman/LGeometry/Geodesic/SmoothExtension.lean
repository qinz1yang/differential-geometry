import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Family
import DifferentialGeometry.Topology.Manifold.SmoothInterval
import DifferentialGeometry.Analysis.ODE.Uniqueness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Congruence

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold _root_.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem continuousAt_lPhaseState_of_contMDiffAt_one
    {alpha : ℝ → M} {b : ℝ}
    (hC1 : ContMDiffAt 𝓘(ℝ, ℝ) I 1 alpha b) :
    ContinuousAt (fun r : ℝ =>
      (chartCurve (I := I) (alpha b) alpha r,
        chartRepAtBase (I := I) (alpha b) alpha
          (fun t => lVelocity (I := I) alpha t) r)) b := by
  have hchart : ContDiffAt ℝ 1 (chartCurve (I := I) (alpha b) alpha) b := by
    exact contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt (I := I) (x := alpha b)).comp b hC1)
  have hsrc : ∀ᶠ r in 𝓝 b, alpha r ∈ (chartAt H (alpha b)).source :=
    hC1.continuousAt.eventually
      ((chartAt H (alpha b)).open_source.mem_nhds (mem_chart_source H (alpha b)))
  have hC1' : ∀ᶠ r in 𝓝 b, ContMDiffAt 𝓘(ℝ, ℝ) I 1 alpha r :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by decide)).mp hC1
  have heq : chartRepAtBase (I := I) (alpha b) alpha
      (fun t => lVelocity (I := I) alpha t) =ᶠ[𝓝 b]
        (fun r => fderiv ℝ (chartCurve (I := I) (alpha b) alpha) r (1 : ℝ)) := by
    filter_upwards [hsrc, hC1'] with r hr hCr
    exact DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (hCr.mdifferentiableAt (by norm_num)) (alpha b) hr
  have hderiv : ContinuousAt
      (fun r => fderiv ℝ (chartCurve (I := I) (alpha b) alpha) r (1 : ℝ)) b :=
    (hchart.fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply continuousAt_const
  exact hchart.continuousAt.prodMk (hderiv.congr_of_eventuallyEq heq)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedGeodesic_smooth_tail_of_contMDiffAt_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) {alpha : ℝ → M} {b : ℝ} (hb : 0 < b)
    (hC1 : ContMDiffAt 𝓘(ℝ, ℝ) I 1 alpha b)
    (hregb : T - b ^ 2 ∈ D.regular)
    (halpha : IsLRegularizedGeodesicOn S T alpha (Ioo 0 b)) :
    ∃ c ∈ Ioo 0 b, ∃ U : Set ℝ, IsOpen U ∧ Icc c b ⊆ U ∧
      ∃ beta : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ beta U ∧
        IsLRegularizedGeodesicOn S T beta U ∧ EqOn beta alpha (Icc c b) ∧
        lVelocity (I := I) beta b = lVelocity (I := I) alpha b := by
  let A := lVelocity (I := I) alpha b
  obtain ⟨epsilon, hepsilon, V, hV, hAV, family, hfamily, hcurves⟩ :=
    exists_lRegularizedGeodesicFamily S hS T b (alpha b) A hregb
  let U := Ioo (b - epsilon) (b + epsilon)
  let beta : ℝ → M := fun r => family (A, r)
  have hbU : b ∈ U := ⟨by linarith, by linarith⟩
  have hbeta := hcurves A hAV
  change beta b = alpha b ∧ lVelocity (I := I) beta b = A ∧
    IsLRegularizedGeodesicOn S T beta U at hbeta
  have hbetaSmooth : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ beta U := by
    apply hfamily.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
    intro r hr
    exact ⟨hAV, hr⟩
  let x := alpha b
  have hasrc : ∀ᶠ r in 𝓝 b, alpha r ∈ (chartAt H x).source :=
    hC1.continuousAt.eventually
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  have hbsrc : ∀ᶠ r in 𝓝 b, beta r ∈ (chartAt H x).source := by
    apply (hbeta.2.2 b hbU).2.1.continuousAt.eventually
    rw [hbeta.1]
    exact (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  have hnb : ∀ᶠ r in 𝓝 b,
      r ∈ U ∧ 0 < r ∧ alpha r ∈ (chartAt H x).source ∧
        beta r ∈ (chartAt H x).source := by
    filter_upwards [isOpen_Ioo.mem_nhds hbU, Ioi_mem_nhds hb, hasrc, hbsrc]
      with r hrU hr0 hra hrb
    exact ⟨hrU, hr0, hra, hrb⟩
  obtain ⟨a, hab, ha⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp
    (nhdsWithin_le_nhds hnb)
  have ha0 : 0 < a := (ha ⟨le_rfl, hab.le⟩).2.1
  let za : ℝ → E × E := fun r =>
    (chartCurve (I := I) x alpha r,
      chartRepAtBase (I := I) x alpha (fun t => lVelocity (I := I) alpha t) r)
  let zb : ℝ → E × E := fun r =>
    (chartCurve (I := I) x beta r,
      chartRepAtBase (I := I) x beta (fun t => lVelocity (I := I) beta t) r)
  have hza : ∀ r ∈ Ioo a b, HasDerivAt za (lPhaseField S T x r (za r)) r := by
    intro r hr
    have hr' := ha (Ioo_subset_Icc_self hr)
    have h := halpha r ⟨hr'.2.1, hr.2⟩
    exact lRegularizedCurve_phase S T x alpha r h.2.1 hr'.2.2.1 h.2.2.1 h.2.2.2
  have hzb : ∀ r ∈ Ioo a b, HasDerivAt zb (lPhaseField S T x r (zb r)) r := by
    intro r hr
    have hr' := ha (Ioo_subset_Icc_self hr)
    have h := hbeta.2.2 r hr'.1
    exact lRegularizedCurve_phase S T x beta r h.2.1 hr'.2.2.2 h.2.2.1 h.2.2.2
  have hphase0 : za b = zb b := by
    dsimp only [za, zb, chartCurve, chartRepAtBase]
    rw [hbeta.1, hbeta.2.1]
  have htarget : (za b).1 ∈ interior (extChartAt I x).target := by
    apply mem_interior_iff_mem_nhds.mpr
    exact extChartAt_target_mem_nhds (I := I) x
  have hzab : ContinuousWithinAt za (Iic b) b :=
    (continuousAt_lPhaseState_of_contMDiffAt_one hC1).continuousWithinAt
  have hzbb : ContinuousWithinAt zb (Iic b) b := by
    have h := hbeta.2.2 b hbU
    have hsrcb : beta b ∈ (chartAt H x).source := by
      rw [hbeta.1]
      exact mem_chart_source H x
    exact (lRegularizedCurve_phase S T x beta b h.2.1 hsrcb
      h.2.2.1 h.2.2.2).continuousAt.continuousWithinAt
  obtain ⟨c, hc, heq⟩ :=
    DifferentialGeometry.Analysis.ODE.exists_eqOn_Icc_of_hasDerivAt_of_contDiffAt hab
      ((lPhaseField_smoothAt S hS T x hregb htarget).of_le
        (by norm_num)) hza hzb hzab hzbb hphase0
  have hca : Icc c b ⊆ Icc a b := Icc_subset_Icc_left hc.1.le
  refine ⟨c, ⟨ha0.trans hc.1, hc.2⟩, U, isOpen_Ioo,
    (fun r hr => (ha (hca hr)).1), beta, hbetaSmooth, hbeta.2.2, ?_, hbeta.2.1⟩
  intro r hr
  apply (extChartAt I x).injOn
  · rw [DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source]
    exact (ha (hca hr)).2.2.2
  · rw [DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source]
    exact (ha (hca hr)).2.2.1
  · exact (congrArg Prod.fst (heq hr)).symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_global_lRegularizedGeodesic_smooth_tail_of_contMDiffAt_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) {alpha : ℝ → M} {b : ℝ} (hb : 0 < b)
    (hC1 : ContMDiffAt 𝓘(ℝ, ℝ) I 1 alpha b)
    (hregb : T - b ^ 2 ∈ D.regular)
    (halpha : IsLRegularizedGeodesicOn S T alpha (Ioo 0 b)) :
    ∃ c ∈ Ioo 0 b, ∃ gamma : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma ∧
        IsLRegularizedGeodesicOn S T gamma (Icc c b) ∧ EqOn gamma alpha (Icc c b) ∧
        lVelocity (I := I) gamma b = lVelocity (I := I) alpha b := by
  obtain ⟨c, hc, U, hU, hsub, beta, hbeta, hgeo, heq, hvel⟩ :=
    exists_lRegularizedGeodesic_smooth_tail_of_contMDiffAt_one S hS T hb hC1 hregb halpha
  obtain ⟨rho, lo, hi, hlo, hhi, hrho, hrhoId, _, hrange⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp_range_subset hU hc.2 hsub
  let gamma : ℝ → M := beta ∘ rho
  have hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma :=
    hbeta.comp_contMDiff hrho.contMDiff hrange
  have hlocal (r : ℝ) (hr : r ∈ Icc c b) : gamma =ᶠ[𝓝 r] beta := by
    filter_upwards [Icc_mem_nhds (hlo.trans_le hr.1) (hr.2.trans_lt hhi)] with s hs
    change beta (rho s) = beta s
    rw [hrhoId hs]
    rfl
  refine ⟨c, hc, gamma, hgamma, ?_, ?_, ?_⟩
  · intro r hr
    have hsingle : IsLRegularizedGeodesicOn S T beta {r} := by
      intro s hs
      have hsr : s = r := hs
      subst s
      exact hgeo r (hsub hr)
    exact (hsingle.congr_of_eventuallyEq (fun s hs => by
      have hsr : s = r := hs
      subst s
      exact hlocal r hr)) r rfl
  · intro r hr
    exact (hlocal r hr).eq_of_nhds.trans (heq hr)
  · have hlocalb := hlocal b ⟨hc.2.le, le_rfl⟩
    unfold lVelocity at hvel ⊢
    rw [hlocalb.mfderiv_eq]
    exact hvel

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedGeodesic_extension_Ioc_of_contMDiff_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) {alpha : ℝ → M} {b : ℝ} (hb : 0 < b)
    (hC1 : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (hregb : T - b ^ 2 ∈ D.regular)
    (halpha : IsLRegularizedGeodesicOn S T alpha (Ioo 0 b)) :
    ∃ beta : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 beta ∧
      EqOn beta alpha (Icc 0 b) ∧ IsLRegularizedGeodesicOn S T beta (Ioc 0 b) := by
  classical
  obtain ⟨c, hc, gamma, hgamma, hgeo, heq, hvel⟩ :=
    exists_global_lRegularizedGeodesic_smooth_tail_of_contMDiffAt_one
      S hS T hb hC1.contMDiffAt hregb halpha
  let d := (c + b) / 2
  have hcd : c < d := by dsimp [d]; linarith [hc.2]
  have hdb : d < b := by dsimp [d]; linarith [hc.2]
  have hEqd : alpha =ᶠ[𝓝 d] gamma :=
    (heq.eventuallyEq_of_mem (Icc_mem_nhds hcd hdb)).symm
  let beta := (Iic d).piecewise alpha gamma
  have hbeta : ContMDiff 𝓘(ℝ, ℝ) I 1 beta :=
    hC1.piecewise_Iic (hgamma.of_le (by norm_num)) hEqd
  have hlocalGamma {r : ℝ} (hr : d ≤ r) : beta =ᶠ[𝓝 r] gamma := by
    rcases lt_or_eq_of_le hr with hdr | rfl
    · filter_upwards [Ioi_mem_nhds hdr] with s hs
      exact Set.piecewise_eq_of_notMem (Iic d) alpha gamma (show s ∉ Iic d from not_le.mpr (show d < s from hs))
    · filter_upwards [hEqd] with s hs
      dsimp [beta]
      by_cases hsd : s ∈ Iic d
      · rw [piecewise_eq_of_mem (Iic d) alpha gamma hsd, hs]
      · rw [piecewise_eq_of_notMem (Iic d) alpha gamma hsd]
  refine ⟨beta, hbeta, ?_, ?_⟩
  · intro r hr
    dsimp [beta]
    by_cases hrd : r ∈ Iic d
    · rw [piecewise_eq_of_mem (Iic d) alpha gamma hrd]
    · rw [piecewise_eq_of_notMem (Iic d) alpha gamma hrd]
      exact heq ⟨hcd.le.trans (le_of_not_ge hrd), hr.2⟩
  · intro r hr
    by_cases hrd : r < d
    · have hlocal : beta =ᶠ[𝓝 r] alpha := by
        filter_upwards [Iio_mem_nhds hrd] with s hs
        exact Set.piecewise_eq_of_mem (Iic d) alpha gamma (show s ∈ Iic d from (show s < d from hs).le)
      have hsingle : IsLRegularizedGeodesicOn S T alpha {r} := by
        intro t ht
        have htr : t = r := ht
        subst t
        exact halpha r ⟨hr.1, hrd.trans hdb⟩
      exact (hsingle.congr_of_eventuallyEq (fun t ht => by
        have htr : t = r := ht
        subst t
        exact hlocal)) r rfl
    · have hdr := le_of_not_gt hrd
      have hsingle : IsLRegularizedGeodesicOn S T gamma {r} := by
        intro t ht
        have htr : t = r := ht
        subst t
        exact hgeo r ⟨hcd.le.trans hdr, hr.2⟩
      exact (hsingle.congr_of_eventuallyEq (fun t ht => by
        have htr : t = r := ht
        subst t
        exact hlocalGamma hdr)) r rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
