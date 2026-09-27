import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.TailVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Congruence
import DifferentialGeometry.Analysis.ODE.Regularity.FirstOrderSmoothness

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
theorem IsLRegularizedGeodesicOn.contMDiffOn
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {T : ℝ} {alpha : ℝ → M} {J : Set ℝ}
    (halpha : IsLRegularizedGeodesicOn S T alpha J) (hJ : IsOpen J) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ alpha J := by
  have hcont : ContinuousOn alpha J := fun r hr =>
    (halpha r hr).2.1.continuousAt.continuousWithinAt
  intro r hr
  let x := alpha r
  let U := J ∩ alpha ⁻¹' (chartAt H x).source
  have hU : IsOpen U := hcont.isOpen_inter_preimage hJ (chartAt H x).open_source
  have hrU : r ∈ U := ⟨hr, mem_chart_source H (alpha r)⟩
  let z : ℝ → E × E := fun t =>
    (chartCurve (I := I) x alpha t,
      chartRepAtBase (I := I) x alpha (fun s => lVelocity (I := I) alpha s) t)
  have hz : ∀ t ∈ U, HasDerivAt z (lPhaseField S T x t (z t)) t := by
    intro t ht
    have htgeo := halpha t ht.1
    exact lRegularizedCurve_phase S T x alpha t htgeo.2.1 ht.2
      htgeo.2.2.1 htgeo.2.2.2
  have hv : ∀ t ∈ U, ContDiffAt ℝ ∞
      (Function.uncurry (lPhaseField S T x)) (t, z t) := by
    intro t ht
    apply lPhaseField_smoothAt S hS T x (halpha t ht.1).1
    apply mem_interior_iff_mem_nhds.mpr
    apply extChartAt_target_mem_nhds'
    apply (extChartAt I x).map_source
    rw [DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source]
    exact ht.2
  have hsmooth := DifferentialGeometry.Analysis.ODE.contDiffOn_infty_of_hasDerivAt hU hv hz
  have hchart : ContDiffAt ℝ ∞ (chartCurve (I := I) (alpha r) alpha) r :=
    (hsmooth.contDiffAt (hU.mem_nhds hrU)).fst
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_iff_target.mpr
  exact ⟨(halpha r hr).2.1.continuousAt, hchart.contMDiffAt⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_global_lRegularizedGeodesic_smooth_extension_on_Icc
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) {alpha : ℝ → M} {c b : ℝ} (hc : 0 < c) (hcb : c < b)
    (halpha : IsLRegularizedGeodesicOn S T alpha (Ioc 0 b)) :
    ∃ gamma : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma ∧
      IsLRegularizedGeodesicOn S T gamma (Icc c b) ∧ EqOn gamma alpha (Icc c b) ∧
      (∀ r ∈ Ico c b, gamma =ᶠ[𝓝 r] alpha) ∧
      lVelocity (I := I) gamma b = lVelocity (I := I) alpha b := by
  classical
  obtain ⟨a, ha, V, hV, hsub, eta, heta, hegeo, heq, hvel⟩ :=
    exists_lRegularizedGeodesic_smooth_tail S hS T (hc.trans hcb) halpha
  let d := (a + b) / 2
  have had : a < d := by dsimp [d]; linarith [ha.2]
  have hdb : d < b := by dsimp [d]; linarith [ha.2]
  have hEqd : alpha =ᶠ[𝓝 d] eta :=
    (heq.eventuallyEq_of_mem (Icc_mem_nhds had hdb)).symm
  let beta := (Iic d).piecewise alpha eta
  have hlocalAlpha {r : ℝ} (hr : r < d) : beta =ᶠ[𝓝 r] alpha := by
    filter_upwards [Iio_mem_nhds hr] with s hs
    exact piecewise_eq_of_mem (Iic d) alpha eta (show s ∈ Iic d from (show s < d from hs).le)
  have hlocalEta {r : ℝ} (hr : d ≤ r) : beta =ᶠ[𝓝 r] eta := by
    rcases lt_or_eq_of_le hr with hdr | rfl
    · filter_upwards [Ioi_mem_nhds hdr] with s hs
      exact piecewise_eq_of_notMem (Iic d) alpha eta
        (show s ∉ Iic d from not_le.mpr (show d < s from hs))
    · filter_upwards [hEqd] with s hs
      dsimp [beta]
      by_cases hsd : s ∈ Iic d
      · rw [piecewise_eq_of_mem (Iic d) alpha eta hsd, hs]
      · rw [piecewise_eq_of_notMem (Iic d) alpha eta hsd]
  have halphaSmooth : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ alpha (Ioo 0 b) :=
    IsLRegularizedGeodesicOn.contMDiffOn hS
      (fun r hr => halpha r ⟨hr.1, hr.2.le⟩) isOpen_Ioo
  let U := Ioo 0 b ∪ (V ∩ Ioi d)
  have hU : IsOpen U := isOpen_Ioo.union (hV.inter isOpen_Ioi)
  have hUsub : Icc c b ⊆ U := by
    intro r hr
    rcases lt_or_eq_of_le hr.2 with hrb | rfl
    · exact Or.inl ⟨hc.trans_le hr.1, hrb⟩
    · exact Or.inr ⟨hsub ⟨ha.2.le, le_rfl⟩, hdb⟩
  have hbeta : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ beta U := by
    intro r hr
    apply ContMDiffAt.contMDiffWithinAt
    by_cases hrd : r < d
    · have hrI : r ∈ Ioo 0 b := by
        rcases hr with hr | hr
        · exact hr
        · exact False.elim ((not_lt_of_ge hrd.le) hr.2)
      exact (halphaSmooth.contMDiffAt (isOpen_Ioo.mem_nhds hrI)).congr_of_eventuallyEq
        (hlocalAlpha hrd)
    · have hdr := le_of_not_gt hrd
      have hrV : r ∈ V := by
        rcases hr with hr | hr
        · exact hsub ⟨had.le.trans hdr, hr.2.le⟩
        · exact hr.1
      exact (heta.contMDiffAt (hV.mem_nhds hrV)).congr_of_eventuallyEq
        (hlocalEta hdr)
  have hbetaGeo : IsLRegularizedGeodesicOn S T beta (Icc c b) := by
    intro r hr
    by_cases hrd : r < d
    · have hsingle : IsLRegularizedGeodesicOn S T alpha {r} := by
        intro s hs
        have hsr : s = r := hs
        subst s
        exact halpha r ⟨hc.trans_le hr.1, hr.2⟩
      exact (hsingle.congr_of_eventuallyEq (fun s hs => by
        have hsr : s = r := hs
        subst s
        exact hlocalAlpha hrd)) r rfl
    · have hdr := le_of_not_gt hrd
      have hsingle : IsLRegularizedGeodesicOn S T eta {r} := by
        intro s hs
        have hsr : s = r := hs
        subst s
        exact hegeo r (hsub ⟨had.le.trans hdr, hr.2⟩)
      exact (hsingle.congr_of_eventuallyEq (fun s hs => by
        have hsr : s = r := hs
        subst s
        exact hlocalEta hdr)) r rfl
  have hbetaEq : EqOn beta alpha (Icc c b) := by
    intro r hr
    dsimp [beta]
    by_cases hrd : r ∈ Iic d
    · exact piecewise_eq_of_mem (Iic d) alpha eta hrd
    · rw [piecewise_eq_of_notMem (Iic d) alpha eta hrd]
      exact heq ⟨had.le.trans (le_of_not_ge hrd), hr.2⟩
  obtain ⟨rho, lo, hi, hlo, hhi, hrho, hrhoId, _, hrange⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp_range_subset hU hcb hUsub
  let gamma : ℝ → M := beta ∘ rho
  have hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma :=
    hbeta.comp_contMDiff hrho.contMDiff hrange
  have hlocal (r : ℝ) (hr : r ∈ Icc c b) : gamma =ᶠ[𝓝 r] beta := by
    filter_upwards [Icc_mem_nhds (hlo.trans_le hr.1) (hr.2.trans_lt hhi)] with s hs
    change beta (rho s) = beta s
    rw [hrhoId hs]
    rfl
  refine ⟨gamma, hgamma, hbetaGeo.congr_of_eventuallyEq hlocal, ?_, ?_, ?_⟩
  · intro r hr
    exact (hlocal r hr).eq_of_nhds.trans (hbetaEq hr)
  · intro r hr
    apply (hlocal r ⟨hr.1, hr.2.le⟩).trans
    by_cases hrd : r < d
    · exact hlocalAlpha hrd
    · have hdr := le_of_not_gt hrd
      exact (hlocalEta hdr).trans
        (heq.eventuallyEq_of_mem (Icc_mem_nhds (had.trans_le hdr) hr.2))
  · have hlocalb := (hlocal b ⟨hcb.le, le_rfl⟩).trans (hlocalEta hdb.le)
    unfold lVelocity at hvel ⊢
    rw [hlocalb.mfderiv_eq]
    exact hvel

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
