import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ScalarCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EarlySlabVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Span

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

open DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open Bundle MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Entropy

universe u uE uH

variable {M : Type u}
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [T3Space M] [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]
variable [I.Boundaryless] [BoundarylessManifold I M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [BoundarylessManifold I M] in
theorem scalar_noncollapse_of_lowerW
    [T2Space (TangentBundle I M)]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {t : RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S t) (hB : B.IsScalarControlled) {L : Real}
    (hW : ∀ {theta : Real}, 0 < theta → theta ≤ B.radius ^ 2 →
      ∀ {v : M → Real}, ContMDiff I 𝓘(Real) ∞ v → (∀ x : M, 0 < v x) →
        (∫ x, v x ∂(riemannianVolumeMeasure (I := I) (M := M)
          (S.family.metric (t : Real)))) = 1 →
        L ≤ flowW (I := I) (M := M) S (t : Real) theta v) :
    B.IsKappaNoncollapsed
      (Real.exp (L - scalarCollapseWConst (Module.finrank Real E) - 1)) := by
  let kappa : Real :=
    Real.exp (L - scalarCollapseWConst (Module.finrank Real E) - 1)
  have hkappa : 0 < kappa := by
    exact Real.exp_pos _
  refine ⟨hkappa, ?_⟩
  obtain ⟨B', w, _hnest, hB'radius, _hB'curv, _hnorm,
      hw, hwpos, hwmass, hwupper⟩ :=
    exists_scalar_controlled_w_bound (I := I) (M := M) B hB
      (δ := 1) (hδ := by norm_num)
  have hB'sq : B'.radius ^ 2 ≤ B.radius ^ 2 :=
    (sq_le_sq₀ B'.radius_pos.le B.radius_pos.le).2 hB'radius
  have htheta : 0 < B'.radius ^ 2 := sq_pos_of_pos B'.radius_pos
  have hwsq : ContMDiff I 𝓘(Real) ∞ (fun x : M => w x * w x) := by
    change ContMDiff I 𝓘(Real) ∞ (w * w)
    exact hw.mul hw
  have hwsq_pos : ∀ x : M, 0 < w x * w x := by
    intro x
    exact mul_pos (hwpos x) (hwpos x)
  have hwsq_mass :
      (∫ x, w x * w x
        ∂(riemannianVolumeMeasure (I := I) (M := M)
          (S.family.metric (t : Real)))) = 1 := by
    simpa only [pow_two, SolutionOn.family_metric] using hwmass
  have hwlower :
      L ≤ flowW (I := I) (M := M) S (t : Real) (B'.radius ^ 2)
        (fun x => w x * w x) :=
    hW htheta hB'sq hwsq hwsq_pos hwsq_mass
  have hwupper' :
      flowW (I := I) (M := M) S (t : Real) (B'.radius ^ 2)
          (fun x => w x * w x) ≤
        scalarCollapseWConst (Module.finrank Real E) +
          Real.log (B.volume.toReal /
            B.radius ^ Module.finrank Real E) + 1 := by
    have hscalar : S.base.scalar (t : Real) =
        fun x => metricScalarAt (I := I) (M := M) (S.base.metric (t : Real)) x := by
      funext x
      rfl
    rw [flowW, SolutionOn.family_metric, SolutionOn.scalar, hscalar]
    exact hwupper
  have hlog :
      L - scalarCollapseWConst (Module.finrank Real E) - 1 ≤
        Real.log (B.volume.toReal / B.radius ^ Module.finrank Real E) := by
    linarith [hwlower.trans hwupper']
  have hBvol : 0 < B.volume.toReal := by
    simpa only [FlowMetricBall.volume, FlowMetricBall.set, FlowMetricBall.setAt,
      volumeMeasureOn_eq_metric, SolutionOn.family_metric] using
        edist_vol_pos (I := I) (M := M)
          (S.base.metric t) B.center B.radius_pos
  have hratio :
      0 < B.volume.toReal / B.radius ^ Module.finrank Real E :=
    div_pos hBvol (pow_pos B.radius_pos _)
  have hkappa_ratio :
      kappa ≤ B.volume.toReal / B.radius ^ Module.finrank Real E := by
    dsimp only [kappa]
    rw [← Real.exp_log hratio]
    exact Real.exp_le_exp.mpr hlog
  have hkappa_real :
      kappa * B.radius ^ Module.finrank Real E ≤ B.volume.toReal :=
    (le_div_iff₀ (pow_pos B.radius_pos _)).1 hkappa_ratio
  calc
    ENNReal.ofReal kappa *
          ENNReal.ofReal B.radius ^ Module.finrank Real E =
        ENNReal.ofReal
          (kappa * B.radius ^ Module.finrank Real E) := by
      rw [ENNReal.ofReal_mul hkappa.le,
        ENNReal.ofReal_pow B.radius_pos.le]
    _ ≤ ENNReal.ofReal B.volume.toReal :=
      ENNReal.ofReal_le_ofReal hkappa_real
    _ ≤ B.volume := ENNReal.ofReal_toReal_le

omit [NeZero (Module.finrank ℝ E)] [ConnectedSpace M] [BoundarylessManifold I M] in
theorem early_slab_ball_lower
    [T2Space (TangentBundle I M)]
    {omega : Real} (h0omega : 0 < omega)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 omega h0omega))
    (hG : MetricFamilySmoothOn (I := I) (M := M)
      (RealTimeInterval.closedOpen 0 omega h0omega) S.family.metric)
    {rho : Real} (hrho : 0 < rho) :
    ∃ tau kappa : Real, 0 < tau ∧ tau < omega ∧ 0 < kappa ∧
      ∀ (t : RealTimeInterval.FlowTime (RealTimeInterval.closedOpen 0 omega h0omega)),
        (t : Real) ≤ tau → ∀ B : FlowMetricBall S t, B.radius ≤ rho →
          B.IsKappaNoncollapsed kappa := by
  obtain ⟨tau, kappa, htau, htauomega, hkappa, hvol⟩ :=
    family_early_slab_volume (I := I) h0omega S.family.metric hG hrho
  refine ⟨tau, kappa, htau, htauomega, hkappa, ?_⟩
  intro t ht B hBrho
  refine ⟨hkappa, ?_⟩
  simpa only [FlowMetricBall.volume, FlowMetricBall.set, FlowMetricBall.setAt,
    volumeMeasureOn_eq_metric, SolutionOn.family_metric] using
      hvol t ht B.center B.radius_pos hBrho

omit [NeZero (Module.finrank ℝ E)] [ConnectedSpace M]
  [I.Boundaryless] [BoundarylessManifold I M] [CompactSpace M] in
private theorem noncollapsed_mono_constant
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {t : RealTimeInterval.FlowTime D} {B : FlowMetricBall S t}
    {kappa kappa' : Real} (hkappa : 0 < kappa) (hle : kappa ≤ kappa')
    (hB : B.IsKappaNoncollapsed kappa') : B.IsKappaNoncollapsed kappa := by
  exact ⟨hkappa, (mul_le_mul' (ENNReal.ofReal_le_ofReal hle) le_rfl).trans hB.2⟩

omit [BoundarylessManifold I M] in
theorem strongScalarNoLocalCollapsing_of_lowerW
    [T2Space (TangentBundle I M)]
    {omega : Real} (h0omega : 0 < omega)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 omega h0omega))
    (hG : MetricFamilySmoothOn (I := I) (M := M)
      (RealTimeInterval.closedOpen 0 omega h0omega) S.family.metric)
    {rho : Real} (hrho : 0 < rho)
    (hW : ∀ a : Real, 0 < a → ∃ L : Real,
      ∀ (t : RealTimeInterval.FlowTime (RealTimeInterval.closedOpen 0 omega h0omega)),
        a ≤ (t : Real) → ∀ {theta : Real}, 0 < theta → theta ≤ rho ^ 2 →
        ∀ {v : M → Real}, ContMDiff I 𝓘(Real) ∞ v → (∀ x : M, 0 < v x) →
          (∫ x, v x ∂(riemannianVolumeMeasure (I := I) (M := M)
            (S.family.metric (t : Real)))) = 1 →
          L ≤ flowW (I := I) (M := M) S (t : Real) theta v) :
    StrongScalarNoLocalCollapsing S rho := by
  obtain ⟨tau, kappa0, htau, _htauomega, hkappa0, hearly⟩ :=
    early_slab_ball_lower h0omega S hG hrho
  obtain ⟨L, hL⟩ := hW tau htau
  let kappa1 : Real := Real.exp (L - scalarCollapseWConst (Module.finrank Real E) - 1)
  have hkappa1 : 0 < kappa1 := Real.exp_pos _
  let kappa : Real := min kappa0 kappa1
  have hkappa : 0 < kappa := lt_min hkappa0 hkappa1
  refine ⟨kappa, hkappa, hrho, ?_⟩
  intro t B hBrho hB B' hc hr
  have hB'rho : B'.radius ≤ rho := hr.trans hBrho
  by_cases ht : (t : Real) ≤ tau
  · exact noncollapsed_mono_constant hkappa (min_le_left _ _)
      (hearly t ht B' hB'rho)
  · apply noncollapsed_mono_constant hkappa (min_le_right _ _)
    apply scalar_noncollapse_of_lowerW B'
      (FlowMetricBall.scalarControlled_of_radius_le B B' hc hr hB)
    intro theta htheta hscale v hv hpos hmass
    exact hL t (le_of_not_ge ht) htheta
      (hscale.trans ((sq_le_sq₀ B'.radius_pos.le hrho.le).2 hB'rho)) hv hpos hmass

theorem strongScalarNoLocalCollapsing_three
    [T2Space (TangentBundle I M)]
    {omega : Real} (h0omega : 0 < omega)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 omega h0omega))
    (hS : IsSolutionOn (I := I) S) (hDim : Module.finrank Real E = 3)
    {rho : Real} (hrho : 0 < rho) : StrongScalarNoLocalCollapsing S rho := by
  apply strongScalarNoLocalCollapsing_of_lowerW h0omega S hS.smoothMetric hrho
  intro a ha
  let tauMax : Real := rho ^ 2 + (omega - a) + 1
  obtain ⟨L, hL⟩ := w_span_uniform (I := I) (M := M) S hS hDim
    (a₀ := a / 2) (tauMax := tauMax) (half_lt_self ha)
  refine ⟨L, ?_⟩
  intro t hta theta htheta hthetarho v hv hpos hmass
  have htomega : (t : Real) < omega := t.2.2
  let b : Real := ((t : Real) + omega) / 2
  have htb : (t : Real) ≤ b := by dsimp only [b]; linarith
  have hbomega : b < omega := by dsimp only [b]; linarith
  have hreg : Set.Icc (a / 2) b ⊆
      (RealTimeInterval.closedOpen 0 omega h0omega).regular := by
    intro s hs
    exact ⟨(half_pos ha).trans_le hs.1, hs.2.trans_lt hbomega⟩
  have hbudget : theta + ((t : Real) - a) < tauMax := by
    dsimp only [tauMax]
    linarith
  exact hL (hta.trans htb) hreg (t : Real) ⟨hta, htb⟩ htheta hbudget hv hpos hmass

theorem spatialNoLocalCollapsing_three
    [T2Space (TangentBundle I M)]
    {omega : Real} (h0omega : 0 < omega)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 omega h0omega))
    (hS : IsSolutionOn (I := I) S) (hDim : Module.finrank Real E = 3)
    {rho : Real} (hrho : 0 < rho) : SpatialNoLocalCollapsing S rho := by
  let c := scalarFromRmRadius (Module.finrank Real E)
  have hc : 0 < c := scalarFromRmRadius_pos _
  have h := spatialNoLocalCollapsing_of_strongScalar
    (strongScalarNoLocalCollapsing_three h0omega S hS hDim (div_pos hrho hc))
  have hscale : scalarFromRmRadius (Module.finrank Real E) * (rho / c) = rho := by
    change c * (rho / c) = rho
    field_simp [hc.ne']
  rwa [hscale] at h

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
