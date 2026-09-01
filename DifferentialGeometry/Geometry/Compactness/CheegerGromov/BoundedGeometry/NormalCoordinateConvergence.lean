import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalPhase


import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.DiagonalInverseConvergence

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry
namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace BoundedGeometryNormalData

theorem limit_accel_bounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) (R : Real)
    (c : ∀ n : Nat, (X.obj n).M)
    (hc : ∀ n, hd.dist n (c n) (X.obj n).basepoint ≤ R)
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hgInf_cd : ContDiffOn Real ∞ gInf
      (Metric.ball 0 (d.phaseRadius R)))
    (hgInf_lo : ∀ z ∈ Metric.ball (0 : E) (d.phaseRadius R), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v)
    (hg_conv : MapCInfConvOnCompacts
      (Metric.ball 0 (d.phaseRadius R))
      (fun n ↦ d.chartMetric n (c n)) gInf)
    (V : NNReal) :
    let aInf : E × E → E := fun z ↦ (MetricKoszul.metricSpray gInf z).2
    LipschitzOnWith (d.phaseK V) aInf
        (normalPhaseBox (d.phaseRadius R) V) ∧
      ∀ z ∈ normalPhaseBox (d.phaseRadius R) V,
        ‖aInf z‖ ≤ 3 * d.metricC 1 * (V : Real) ^ 2 := by
  let U : Set E := Metric.ball 0 (d.phaseRadius R)
  let g : Nat → E → E →L[Real] E →L[Real] Real :=
    fun n ↦ d.chartMetric n (c n)
  let a : Nat → E × E → E :=
    fun n ↦ by
      letI : TopologicalSpace (X.obj n).M := (X.obj n).topology
      letI : ChartedSpace H (X.obj n).M := (X.obj n).charted
      letI : IsManifold I ∞ (X.obj n).M := (X.obj n).smooth
      letI : SigmaCompactSpace (X.obj n).M := (X.obj n).sigmaCompact
      letI : T2Space (X.obj n).M := (X.obj n).t2
      letI : T2Space (TangentBundle I (X.obj n).M) :=
        (X.obj n).t2TangentBundle
      exact (d.chart n (c n)).accel (X.obj n).metric
  let aInf : E × E → E := fun z ↦ (MetricKoszul.metricSpray gInf z).2
  have hg_cd : ∀ n, ContDiffOn Real ∞ (g n) U := by
    intro n
    let : TopologicalSpace (X.obj n).M := (X.obj n).topology
    let : ChartedSpace H (X.obj n).M := (X.obj n).charted
    let : IsManifold I ∞ (X.obj n).M := (X.obj n).smooth
    let : T2Space (TangentBundle I (X.obj n).M) :=
      (X.obj n).t2TangentBundle
    have hrad : U ⊆ Metric.ball (0 : E) (d.chart n (c n)).radius := by
      exact (d.phaseRadius_chart (hc n)).trans <|
        Metric.ball_subset_ball (by
          nlinarith [(d.chart n (c n)).radius_pos])
    simpa only [U, g, BoundedGeometryNormalData.chartMetric] using
      (d.chart n (c n)).metric_cont_diff_on (X.obj n).metric
        Metric.isOpen_ball ((d.chart n (c n)).smooth_to.mono hrad)
  have hg_co : ∀ n z, z ∈ U → IsCoercive (g n z) := by
    intro n z hz
    let : TopologicalSpace (X.obj n).M := (X.obj n).topology
    let : ChartedSpace H (X.obj n).M := (X.obj n).charted
    let : IsManifold I ∞ (X.obj n).M := (X.obj n).smooth
    let : T2Space (TangentBundle I (X.obj n).M) :=
      (X.obj n).t2TangentBundle
    exact (d.metricBounds n (c n)).equiv.coercive
      (X.obj n).metric (d.phaseRadius_metric (hc n) hz)
  have hgInf_co : ∀ z, z ∈ U → IsCoercive (gInf z) := by
    intro z hz
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro v
    simpa only [pow_two, mul_assoc] using hgInf_lo z hz v
  have hspray : MapCInfConvOnCompacts (U ×ˢ (Set.univ : Set E))
      (fun n ↦ MetricKoszul.metricSpray (g n))
      (MetricKoszul.metricSpray gInf) :=
    normalGeodesicSpray_conv Metric.isOpen_ball hg_cd hgInf_cd hg_co
      hgInf_co (by simpa only [U, g] using hg_conv)
  have hacc_tendsto : ∀ z ∈ normalPhaseBox (d.phaseRadius R) V,
      Tendsto (fun n ↦ a n z) atTop (nhds (aInf z)) := by
    intro z hz
    have hspray_z := tendsto_of_cInf hspray ⟨hz.1, Set.mem_univ z.2⟩
    have hsnd : Tendsto
        (fun n ↦ (MetricKoszul.metricSpray (g n) z).2) atTop
        (nhds (MetricKoszul.metricSpray gInf z).2) :=
      (continuous_snd.tendsto _).comp hspray_z
    have heq : (fun n ↦ (MetricKoszul.metricSpray (g n) z).2) =
        fun n ↦ a n z := by
      funext n
      let : TopologicalSpace (X.obj n).M := (X.obj n).topology
      let : ChartedSpace H (X.obj n).M := (X.obj n).charted
      let : IsManifold I ∞ (X.obj n).M := (X.obj n).smooth
      let : SigmaCompactSpace (X.obj n).M := (X.obj n).sigmaCompact
      let : T2Space (X.obj n).M := (X.obj n).t2
      let : T2Space (TangentBundle I (X.obj n).M) :=
        (X.obj n).t2TangentBundle
      have hmetric := d.phaseRadius_metric (hc n) hz.1
      have hquarter := d.phaseRadius_chart (hc n) hz.1
      have hco : IsCoercive (g n z.1) :=
        (d.metricBounds n (c n)).equiv.coercive
          (X.obj n).metric hmetric
      rw [MetricKoszul.metricSpray_eq (g n) z hco]
      simpa only [g, a, BoundedGeometryNormalData.chartMetric] using
        ((d.chart n (c n)).accel_eq (X.obj n).metric z hquarter
          ((d.metricBounds n (c n)).equiv.coercive
            (X.obj n).metric hmetric)).symm
    rw [heq] at hsnd
    simpa only [aInf] using hsnd
  refine ⟨?_, ?_⟩
  · rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have hdist : Tendsto (fun n ↦ dist (a n x) (a n y)) atTop
        (nhds (dist (aInf x) (aInf y))) :=
      (continuous_dist.tendsto (aInf x, aInf y)).comp
        ((hacc_tendsto x hx).prodMk_nhds (hacc_tendsto y hy))
    refine le_of_tendsto hdist (Filter.Eventually.of_forall fun n ↦ ?_)
    let : TopologicalSpace (X.obj n).M := (X.obj n).topology
    let : ChartedSpace H (X.obj n).M := (X.obj n).charted
    let : IsManifold I ∞ (X.obj n).M := (X.obj n).smooth
    let : SigmaCompactSpace (X.obj n).M := (X.obj n).sigmaCompact
    let : T2Space (X.obj n).M := (X.obj n).t2
    let : T2Space (TangentBundle I (X.obj n).M) :=
      (X.obj n).t2TangentBundle
    have hlip := chartAccel_lip (I := I) (X.obj n).metric
      (d.chart n (c n)) (d.metricBounds n (c n))
      (d.phaseRadius_metric (hc n)) (d.phaseRadius_chart (hc n)) V
    rw [lipschitzOnWith_iff_dist_le_mul] at hlip
    simpa only [a, d.chartPhaseK_eq] using hlip x hx y hy
  · intro z hz
    have hnorm : Tendsto (fun n ↦ ‖a n z‖) atTop (nhds ‖aInf z‖) :=
      (continuous_norm.tendsto (aInf z)).comp (hacc_tendsto z hz)
    exact le_of_tendsto hnorm (Filter.Eventually.of_forall fun n ↦ by
      let : TopologicalSpace (X.obj n).M := (X.obj n).topology
      let : ChartedSpace H (X.obj n).M := (X.obj n).charted
      let : IsManifold I ∞ (X.obj n).M := (X.obj n).smooth
      let : SigmaCompactSpace (X.obj n).M := (X.obj n).sigmaCompact
      let : T2Space (X.obj n).M := (X.obj n).t2
      let : T2Space (TangentBundle I (X.obj n).M) :=
        (X.obj n).t2TangentBundle
      simpa only [a, BoundedGeometryNormalData.metricBounds] using
        chartAccel_norm (I := I) (X.obj n).metric
          (d.chart n (c n)) (d.metricBounds n (c n))
          (d.phaseRadius_metric (hc n)) (d.phaseRadius_chart (hc n))
          V z hz)

theorem exists_limit_phase
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) (R : Real)
    (c : ∀ n : Nat, (X.obj n).M)
    (hc : ∀ n, hd.dist n (c n) (X.obj n).basepoint ≤ R)
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hgInf_cd : ContDiffOn Real ∞ gInf
      (Metric.ball 0 (d.phaseRadius R)))
    (hgInf_lo : ∀ z ∈ Metric.ball (0 : E) (d.phaseRadius R), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v)
    (hg_conv : MapCInfConvOnCompacts
      (Metric.ball 0 (d.phaseRadius R))
      (fun n ↦ d.chartMetric n (c n)) gInf)
    (q : NNReal) (hq : 0 < q)
    (hqPos : 4 * (q : Real) < d.phaseRadius R)
    (hqAcc : 3 * d.metricC 1 * (2 * (q : Real)) ^ 2 ≤ (q : Real)) :
    ∃ ΦInf : (E × E) → Real → E × E,
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ΦInf z 0 = z) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        IsIntegralCurveOn (ΦInf z)
          (fun _ ↦ MetricKoszul.metricSpray gInf) (Icc 0 1)) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        ∀ t ∈ Icc (0 : Real) 1,
          (ΦInf z t).1 ∈ Metric.ball 0 (d.phaseRadius R)) ∧
      ΦInf 0 1 = 0 ∧
      ApproximatesLinearOn (fun z ↦ (z.1, (ΦInf z 1).1))
        PhaseFlow.freeDiag (Metric.closedBall (0 : E × E) q)
        (PhaseFlow.phaseErr (d.phaseK (2 * q))) ∧
      ContDiffOn Real ∞ (fun z ↦ (z.1, (ΦInf z 1).1))
        (Metric.ball (0 : E × E) q) := by
  let U : Set E := Metric.ball 0 (d.phaseRadius R)
  let phaseU : Set (E × E) := U ×ˢ (Set.univ : Set E)
  let aInf : E × E → E := fun z ↦ (MetricKoszul.metricSpray gInf z).2
  let P : NNReal := 4 * q
  let V : NNReal := 2 * q
  let half : NNReal := 1 / 2
  let A : NNReal :=
    ⟨3 * d.metricC 1 * (V : Real) ^ 2,
      mul_nonneg (mul_nonneg (by norm_num) (d.metricC_nonneg 1))
        (sq_nonneg _)⟩
  have hP : 0 < P := by dsimp only [P]; positivity
  have hV : 0 < V := by dsimp only [V]; positivity
  obtain ⟨haLipFull, haNormFull⟩ :=
    d.limit_accel_bounds R c hc hgInf_cd hgInf_lo hg_conv V
  have hbox : PhaseFlow.phaseBox (E := E) P V ⊆
      normalPhaseBox (d.phaseRadius R) V := by
    intro z hz
    refine ⟨?_, hz.2⟩
    rw [mem_ball_zero_iff]
    exact hz.1.trans_lt (by
      with_unfolding_all exact hqPos)
  have haLip : LipschitzOnWith (d.phaseK V) aInf
      (PhaseFlow.phaseBox (E := E) P V) := haLipFull.mono hbox
  have haNorm : ∀ z ∈ PhaseFlow.phaseBox (E := E) P V,
      ‖aInf z‖ ≤ (A : Real) := by
    intro z hz
    with_unfolding_all exact haNormFull z (hbox hz)
  have hVP : V ≤ half * P := by
    rw [← NNReal.coe_le_coe]
    change (2 : Real) * (q : Real) ≤ (1 / 2 : Real) * (4 * (q : Real))
    nlinarith
  have hAV : A ≤ half * V := by
    rw [← NNReal.coe_le_coe]
    change 3 * d.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (1 / 2 : Real) * (2 * (q : Real))
    nlinarith [hqAcc]
  have hhalf : (half : Real) ≤ 1 - (half : Real) := by norm_num [half]
  obtain ⟨ΦInf, hΦ⟩ := PhaseFlow.exists_fenced_sym (E := E)
    hP hV haLip haNorm hVP hAV hhalf
  have hqP : q ≤ half * P := by
    rw [← NNReal.coe_le_coe]
    change (q : Real) ≤ (1 / 2 : Real) * (4 * (q : Real))
    nlinarith [q.coe_nonneg]
  have hqV : q ≤ half * V := by
    rw [← NNReal.coe_le_coe]
    change (q : Real) ≤ (1 / 2 : Real) * (2 * (q : Real))
    nlinarith
  have hscale := PhaseFlow.scale_maps_ball (E := E) hP hV hqP hqV
  have hspec := fun z (hz : z ∈ Metric.closedBall (0 : E × E) q) ↦
    hΦ z (hscale hz)
  have hinit : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ΦInf z 0 = z := fun z hz ↦ (hspec z hz).1
  have hcont : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ContinuousOn (ΦInf z) (Icc (-1) 1) := fun z hz ↦ (hspec z hz).2.1
  have hwithin : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ∀ t ∈ Icc (-1 : Real) 1,
        HasDerivWithinAt (ΦInf z)
          (PhaseFlow.phaseField aInf (ΦInf z t)) (Icc (-1) 1) t :=
    fun z hz ↦ (hspec z hz).2.2.1
  have hderiv : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ∀ t ∈ Ioo (-1 : Real) 1,
        HasDerivAt (ΦInf z) (PhaseFlow.phaseField aInf (ΦInf z t)) t :=
    fun z hz ↦ (hspec z hz).2.2.2.1
  have hmem : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ∀ t ∈ Icc (-1 : Real) 1,
        ΦInf z t ∈ PhaseFlow.phaseBox P V :=
    fun z hz ↦ (hspec z hz).2.2.2.2
  have hsmall : Icc (0 : Real) 1 ⊆ Icc (-1) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hcurve : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      IsIntegralCurveOn (ΦInf z)
        (fun _ ↦ MetricKoszul.metricSpray gInf) (Icc 0 1) := by
    intro z hz t ht
    have hder := (hwithin z hz t (hsmall ht)).mono hsmall
    simpa only [aInf, PhaseFlow.phaseField,
      MetricKoszul.metricSpray] using hder
  have hstay : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ∀ t ∈ Icc (0 : Real) 1,
        (ΦInf z t).1 ∈ U := by
    intro z hz t ht
    have hpos := (hmem z hz t (hsmall ht)).1
    simpa only [U, mem_ball_zero_iff] using hpos.trans_lt (by
      with_unfolding_all exact hqPos)
  have hcont01 : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ContinuousOn (ΦInf z) (Icc 0 1) :=
    fun z hz ↦ (hcont z hz).mono hsmall
  have hderiv01 : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ∀ t ∈ Ico (0 : Real) 1,
        HasDerivWithinAt (ΦInf z)
          (PhaseFlow.phaseField aInf (ΦInf z t)) (Ici t) t := by
    intro z hz t ht
    exact (hderiv z hz t ⟨by linarith [ht.1], ht.2⟩).hasDerivWithinAt
  have happ := PhaseFlow.phase_diag_approx haLip hinit hcont01 hderiv01
    (fun z hz t ht ↦ hmem z hz t (hsmall ⟨ht.1, ht.2.le⟩))
  have hzeroMem : (0 : E × E) ∈ Metric.closedBall (0 : E × E) q := by
    simp only [Metric.mem_closedBall, dist_self, q.coe_nonneg]
  have hzeroCurve : IsIntegralCurveOn (fun _ : Real ↦ (0 : E × E))
      (fun _ ↦ MetricKoszul.metricSpray gInf) (Icc 0 1) := by
    intro t _ht
    convert hasDerivWithinAt_const (x := t) (s := Icc (0 : Real) 1)
      (c := (0 : E × E)) using 1 ; simp [MetricKoszul.metricSpray]
  have hspraySmooth : ContDiffOn Real ∞ (MetricKoszul.metricSpray gInf)
      phaseU := by
    apply MetricKoszul.metricSpray_contDiffOn Metric.isOpen_ball hgInf_cd
    intro z hz
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro v
    simpa only [pow_two, mul_assoc] using hgInf_lo z hz v
  have hzeroStay : Set.MapsTo (fun _ : Real ↦ (0 : E × E))
      (Icc (0 : Real) 1) phaseU := by
    intro t _ht
    refine ⟨?_, Set.mem_univ _⟩
    change (0 : E) ∈ Metric.ball 0 (d.phaseRadius R)
    simpa only [Metric.mem_ball, dist_self] using d.phaseRadius_pos R
  have hzeroEq : Set.EqOn (ΦInf 0) (fun _ : Real ↦ (0 : E × E))
      (Icc (0 : Real) 1) :=
    Analysis.ODE.Flow.orbit_unique_Icc_on (Ω := phaseU)
      (Metric.isOpen_ball.prod isOpen_univ) hspraySmooth
      (hcurve 0 hzeroMem) hzeroCurve
      (fun t ht ↦ ⟨hstay 0 hzeroMem t ht, Set.mem_univ _⟩)
      hzeroStay (hinit 0 hzeroMem)
  have hzeroEnd : ΦInf 0 1 = 0 := hzeroEq (by norm_num)
  have hslice : ContDiffOn Real ∞ (fun z ↦ ΦInf z 1)
      (Metric.ball (0 : E × E) q) := by
    exact Analysis.ODE.Flow.flow_slice_right_on
      (P := E × E) (E := E × E) (A := Metric.ball (0 : E × E) q)
      (a := 0) (b := 1) (a₀ := id) (γ := ΦInf)
      (Metric.isOpen_ball.prod isOpen_univ) hspraySmooth Metric.isOpen_ball
      contDiff_id.contDiffOn
      (fun z hz ↦ ⟨hinit z (Metric.ball_subset_closedBall hz),
        hcurve z (Metric.ball_subset_closedBall hz)⟩)
      (fun z hz t ht ↦ ⟨hstay z (Metric.ball_subset_closedBall hz) t ht,
        Set.mem_univ _⟩) 1 (by norm_num)
  have hendSmooth : ContDiffOn Real ∞
      (fun z ↦ (z.1, (ΦInf z 1).1)) (Metric.ball (0 : E × E) q) :=
    (contDiff_fst.contDiffOn : ContDiffOn Real ∞
      (fun z : E × E ↦ z.1) _).prodMk hslice.fst
  exact ⟨ΦInf, hinit, hcurve, hstay, hzeroEnd, happ, hendSmooth⟩

theorem exists_limit_diag
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd) (R : Real)
    (c : ∀ n : Nat, (X.obj n).M)
    (hc : ∀ n, hd.dist n (c n) (X.obj n).basepoint ≤ R)
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hgInf_cd : ContDiffOn Real ∞ gInf
      (Metric.ball 0 (d.phaseRadius R)))
    (hgInf_lo : ∀ z ∈ Metric.ball (0 : E) (d.phaseRadius R), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v)
    (hg_conv : MapCInfConvOnCompacts
      (Metric.ball 0 (d.phaseRadius R))
      (fun n ↦ d.chartMetric n (c n)) gInf)
    (q : NNReal) (hq : 0 < q)
    (hqPos : 4 * (q : Real) < d.phaseRadius R)
    (hqAcc : 3 * d.metricC 1 * (2 * (q : Real)) ^ 2 ≤ (q : Real))
    (herr : PhaseFlow.phaseErr (d.phaseK (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹) :
    ∃ (ΦInf : (E × E) → Real → E × E)
        (eInf : OpenPartialHomeomorph (E × E) (E × E))
        (deltaInf : Real),
      0 < deltaInf ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ΦInf z 0 = z) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        IsIntegralCurveOn (ΦInf z)
          (fun _ ↦ MetricKoszul.metricSpray gInf) (Icc 0 1)) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        ∀ t ∈ Icc (0 : Real) 1,
          (ΦInf z t).1 ∈ Metric.ball 0 (d.phaseRadius R)) ∧
      eInf.source = Metric.ball (0 : E × E) q ∧
      eInf 0 = 0 ∧
      (eInf : E × E → E × E) =
        (fun z ↦ (z.1, (ΦInf z 1).1)) ∧
      Metric.closedBall (0 : E × E) deltaInf ⊆ eInf.target ∧
      ContDiffOn Real ∞ (eInf : E × E → E × E) eInf.source ∧
      ContDiffOn Real ∞ eInf.symm eInf.target ∧
      (∀ z ∈ Metric.ball (0 : E) q,
        (z, z) ∈ eInf.target ∧ eInf.symm (z, z) = (z, 0)) ∧
      ApproximatesLinearOn
        (eInf.symm : E × E → E × E)
        ((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))
        eInf.target
        (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊ *
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
            PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (d.phaseK (2 * q))) := by
  obtain ⟨ΦInf, hinit, hcurve, hstay, hzeroEnd, happ, hendSmooth⟩ :=
    d.exists_limit_phase R c hc hgInf_cd hgInf_lo hg_conv q hq hqPos hqAcc
  let f : E × E → E × E := fun z ↦ (z.1, (ΦInf z 1).1)
  obtain ⟨eInf, deltaInf, hdeltaInf, hsource, hcoe, htarget,
      _hdeltaEq, hinvApprox⟩ :=
    PhaseFlow.exists_quant_inv_bi hq (by simpa only [f] using happ) herr
  have hfzero : f 0 = 0 := by
    dsimp only [f]
    rw [hzeroEnd]
    rfl
  have hcoe_f : (eInf : E × E → E × E) = f := by
    simpa only [f] using hcoe
  have hezero : eInf 0 = 0 := by
    rw [hcoe_f]
    exact hfzero
  have htarget' : Metric.closedBall (0 : E × E) deltaInf ⊆
      eInf.target := by
    have hcenter : ((0 : E × E).1, (ΦInf 0 1).1) = (0 : E × E) := by
      rw [hzeroEnd]
      rfl
    rw [hcenter] at htarget
    exact htarget
  have hforwardSmooth : ContDiffOn Real ∞
      (eInf : E × E → E × E) eInf.source := by
    rw [hsource, hcoe_f]
    simpa only [f] using hendSmooth
  have happClosed : ApproximatesLinearOn f
      PhaseFlow.freeDiag (Metric.closedBall (0 : E × E) q)
      (PhaseFlow.phaseErr (d.phaseK (2 * q))) := by
    simpa only [f] using happ
  have happOpen : ApproximatesLinearOn f
      PhaseFlow.freeDiag (Metric.ball (0 : E × E) q)
      (PhaseFlow.phaseErr (d.phaseK (2 * q))) :=
    happClosed.mono_set Metric.ball_subset_closedBall
  have hendSmooth_f : ContDiffOn Real ∞ f
      (Metric.ball (0 : E × E) q) := by
    simpa only [f] using hendSmooth
  have hinvSmooth : ContDiffOn Real ∞ eInf.symm eInf.target :=
    PhaseFlow.inv_smooth_of_approx happOpen (Or.inr herr)
      Metric.isOpen_ball hendSmooth_f eInf hsource hcoe_f
  have hdiagInv : ∀ z ∈ Metric.ball (0 : E) q,
      (z, z) ∈ eInf.target ∧ eInf.symm (z, z) = (z, 0) := by
    intro z hz
    have hpClosed : (z, 0) ∈ Metric.closedBall (0 : E × E) q := by
      have hzClosed := Metric.ball_subset_closedBall hz
      rw [Metric.mem_closedBall] at hzClosed ⊢
      rw [Prod.dist_eq]
      change max (dist z (0 : E)) (dist (0 : E) 0) ≤ (q : Real)
      simpa only [dist_self, max_eq_left dist_nonneg] using hzClosed
    have hpOpen : (z, 0) ∈ Metric.ball (0 : E × E) q := by
      rw [Metric.mem_ball] at hz ⊢
      rw [Prod.dist_eq]
      change max (dist z (0 : E)) (dist (0 : E) 0) < (q : Real)
      simpa only [dist_self, max_eq_left dist_nonneg] using hz
    have hconstCurve : IsIntegralCurveOn (fun _ : Real ↦ (z, 0))
        (fun _ ↦ MetricKoszul.metricSpray gInf) (Icc 0 1) := by
      intro t _ht
      convert hasDerivWithinAt_const (x := t) (s := Icc (0 : Real) 1)
        (c := (z, (0 : E))) using 1 ; simp [MetricKoszul.metricSpray]
    let phaseU : Set (E × E) :=
      Metric.ball (0 : E) (d.phaseRadius R) ×ˢ Set.univ
    have hspraySmooth : ContDiffOn Real ∞ (MetricKoszul.metricSpray gInf)
        phaseU := by
      apply MetricKoszul.metricSpray_contDiffOn Metric.isOpen_ball hgInf_cd
      intro w hw
      refine ⟨1 / 2, by norm_num, ?_⟩
      intro v
      simpa only [pow_two, mul_assoc] using hgInf_lo w hw v
    have hzPhase : z ∈ Metric.ball (0 : E) (d.phaseRadius R) := by
      rw [Metric.mem_ball] at hz ⊢
      have hqReal : (q : Real) < d.phaseRadius R := by
        nlinarith [q.coe_nonneg]
      exact hz.trans hqReal
    have hconstStay : Set.MapsTo (fun _ : Real ↦ (z, 0))
        (Icc (0 : Real) 1) phaseU := by
      intro t _ht
      exact ⟨hzPhase, Set.mem_univ _⟩
    have horbit : Set.EqOn (ΦInf (z, 0)) (fun _ : Real ↦ (z, 0))
        (Icc (0 : Real) 1) :=
      Analysis.ODE.Flow.orbit_unique_Icc_on (Ω := phaseU)
        (Metric.isOpen_ball.prod isOpen_univ) hspraySmooth
        (hcurve (z, 0) hpClosed) hconstCurve
        (fun t ht ↦ ⟨hstay (z, 0) hpClosed t ht, Set.mem_univ _⟩)
        hconstStay (hinit (z, 0) hpClosed)
    have hend : ΦInf (z, 0) 1 = (z, 0) := horbit (by norm_num)
    have heval : eInf (z, 0) = (z, z) := by
      rw [hcoe_f]
      dsimp only [f]
      rw [hend]
    have hpSource : (z, 0) ∈ eInf.source := by
      simpa only [hsource] using hpOpen
    have htargetDiag := eInf.map_source hpSource
    rw [heval] at htargetDiag
    have hleft := eInf.left_inv hpSource
    rw [heval] at hleft
    exact ⟨htargetDiag, hleft⟩
  exact ⟨ΦInf, eInf, deltaInf, hdeltaInf, hinit, hcurve, hstay,
    hsource, hezero, hcoe, htarget', hforwardSmooth, hinvSmooth,
    hdiagInv, hinvApprox⟩

private theorem exists_stage_flow
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) (n : Nat) (x : (X.obj n).M)
    (hx : hd.dist n x (X.obj n).basepoint ≤ R)
    (q : NNReal) (hq : 0 < q)
    (hqWide : 6 * (q : Real) < d.phaseRadius R)
    (hqAcc : 3 * d.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real))
    (herr : PhaseFlow.phaseErr (d.phaseK (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹) :
    ∃ (Φ : (E × E) → Real → E × E)
        (e : OpenPartialHomeomorph (E × E) (E × E)) (delta : Real),
      0 < delta ∧
      delta = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (d.phaseK (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
      IsNormalDiag (I := I) (X.obj n) (hcomplete.complete n) (hconn n)
        x q delta e (c := d.chart n x) ∧
      NormalDiagFence (I := I) (X.obj n) x q e
        (c := d.chart n x) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        IsIntegralCurveOn (Φ z)
          (fun _ ↦ MetricKoszul.metricSpray (d.chartMetric n x))
          (Icc 0 1)) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        ∀ t ∈ Icc (0 : Real) 1,
          (Φ z t).1 ∈ Metric.ball 0 (d.phaseRadius R)) ∧
      (e : E × E → E × E) = (fun z ↦ (z.1, (Φ z 1).1)) ∧
      ApproximatesLinearOn
        (e.symm : E × E → E × E)
        ((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))
        e.target
        (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊ *
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
            PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (d.phaseK (2 * q))) := by
  let : TopologicalSpace (X.obj n).M := (X.obj n).topology
  let : ChartedSpace H (X.obj n).M := (X.obj n).charted
  let : IsManifold I ∞ (X.obj n).M := (X.obj n).smooth
  let : IsManifold I 1 (X.obj n).M := IsManifold.of_le
    (I := I) (M := (X.obj n).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj n).M := (X.obj n).sigmaCompact
  let : T2Space (X.obj n).M := (X.obj n).t2
  let : ConnectedSpace (X.obj n).M := hconn n
  let : T2Space (TangentBundle I (X.obj n).M) :=
    (X.obj n).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj n).M :=
    Manifold.metrizableSpace I (X.obj n).M
  let : T3Space (X.obj n).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj n).M ↦ TangentSpace I y) :=
    (X.obj n).riemBundle (I := I)
  let : (y : (X.obj n).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (X.obj n).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj n).M ↦ TangentSpace I y) :=
    (X.obj n).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj n).M := (X.obj n).emetricSpace (I := I)
  let : CompleteSpace (X.obj n).M :=
    MetricComplete.complete (I := I) (X.obj n) (hcomplete.complete n)
  let c := d.chart n x
  let b := d.metricBounds n x
  have hrMetric : Metric.ball (0 : E) (d.phaseRadius R) ⊆
      Metric.ball (0 : E) b.radius := by
    simpa only [b] using d.phaseRadius_metric hx
  have hrQuarter : Metric.ball (0 : E) (d.phaseRadius R) ⊆
      Metric.ball (0 : E) (c.radius / 4) := by
    simpa only [c] using d.phaseRadius_chart hx
  have hqAcc' :
      3 * b.C 1 * (2 * (q : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q : Real) := by
    simpa only [b, BoundedGeometryNormalData.metricBounds] using hqAcc
  have herr' : PhaseFlow.phaseErr
      (chartPhaseK (X.obj n).metric b (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ := by
    simpa only [b, d.chartPhaseK_eq] using herr
  obtain ⟨Φ, hΦ0, hΦcont, hΦwithin, _hΦat, hΦbox, hΦzero,
      happrox, hΦsmooth⟩ :=
    exists_chartBiflow (I := I) (X.obj n).metric c b
      hrMetric hrQuarter q hq hqWide hqAcc'
  obtain ⟨e, delta, hdelta, hsource, hcoe, htarget, hdeltaEq,
      hinvApprox⟩ :=
    PhaseFlow.exists_quant_inv_bi hq happrox herr'
  have happroxOpen : ApproximatesLinearOn
      (fun z ↦ (z.1, (Φ z 1).1))
      (PhaseFlow.freeDiagCLE (E := E) : (E × E) →L[Real] (E × E))
      (Metric.ball (0 : E × E) q)
      (PhaseFlow.phaseErr (chartPhaseK (X.obj n).metric b (2 * q))) := by
    simpa only [PhaseFlow.freeDiagCLE_coe] using
      happrox.mono_set Metric.ball_subset_closedBall
  have hinvSmooth : ContDiffOn Real ∞ e.symm e.target :=
    PhaseFlow.inv_smooth_of_approx happroxOpen (Or.inr herr')
      Metric.isOpen_ball hΦsmooth e hsource hcoe
  have heZero : e 0 = 0 := by
    rw [hcoe]
    simp only [Prod.fst_zero, hΦzero]
    rfl
  have heSmooth : ContDiffOn Real ∞ (e : E × E → E × E) e.source := by
    rw [hsource, hcoe]
    exact hΦsmooth
  have htargetE : Metric.closedBall (e 0) delta ⊆ e.target := by
    simpa only [hcoe] using htarget
  have htarget' : Metric.closedBall (0 : E × E) delta ⊆ e.target := by
    simpa only [heZero] using htargetE
  have hdiag : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) (X.obj n) x (e z) (c := c) =
        diagExp (I := I) (X.obj n).metric
          (normal_enorm (I := I) (X.obj n))
          (normalTangent (I := I) (X.obj n) x z (c := c)) := by
    intro z hz
    have hzdiag := chart_end_eq_diag (I := I) (X.obj n)
      (hcomplete.complete n) (hconn n) x c
      hrQuarter (hΦcont z hz) (hΦwithin z hz) (hΦbox z hz)
    rw [hcoe]
    simpa only [hΦ0 z hz] using hzdiag
  have hIsDiag : IsNormalDiag (I := I) (X.obj n)
      (hcomplete.complete n) (hconn n) x q delta e (c := c) := by
    change e.source = Metric.ball (0 : E × E) q ∧
      e 0 = 0 ∧
      ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
      Metric.closedBall (0 : E × E) delta ⊆ e.target ∧
      ContDiffOn Real ∞ e.symm e.target ∧
      ∀ z ∈ Metric.closedBall (0 : E × E) q,
        normalPair (I := I) (X.obj n) x (e z) (c := c) =
          diagExp (I := I) (X.obj n).metric
            (normal_enorm (I := I) (X.obj n))
            (normalTangent (I := I) (X.obj n) x z (c := c))
    exact ⟨hsource, heZero, heSmooth, htarget', hinvSmooth, hdiag⟩
  have hrChart : Metric.ball (0 : E) (d.phaseRadius R) ⊆
      Metric.ball (0 : E) c.radius := by
    intro z hz
    exact Metric.ball_subset_ball (by nlinarith [c.radius_pos])
      (hrQuarter hz)
  have hfence : NormalDiagFence (I := I) (X.obj n) x q e
      (c := c) := by
    intro z hz
    have hzNorm : ‖z‖ ≤ (q : Real) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hqr : (q : Real) < d.phaseRadius R := by
      nlinarith [hqWide]
    have hzFirst : z.1 ∈ Metric.ball (0 : E) (d.phaseRadius R) := by
      rw [Metric.mem_ball, dist_zero_right]
      exact (norm_fst_le z).trans_lt (hzNorm.trans_lt hqr)
    have htime : (1 : Real) ∈ Set.Icc (-1) 1 := by norm_num
    have hzEnd : (Φ z 1).1 ∈ Metric.ball (0 : E) (d.phaseRadius R) :=
      (hΦbox z hz 1 htime).1
    rw [hcoe]
    exact ⟨hrChart hzFirst, hrChart hzFirst, hrChart hzEnd⟩
  have hsmall : Icc (0 : Real) 1 ⊆ Icc (-1) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hcurve : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      IsIntegralCurveOn (Φ z)
        (fun _ ↦ MetricKoszul.metricSpray (d.chartMetric n x))
        (Icc 0 1) := by
    intro z hz t ht
    have hder := (hΦwithin z hz t (hsmall ht)).mono hsmall
    have hpos := (hΦbox z hz t (hsmall ht)).1
    have hmetric := hrMetric hpos
    have hquarter := hrQuarter hpos
    have hco : IsCoercive (d.chartMetric n x (Φ z t).1) := by
      exact b.equiv.coercive (X.obj n).metric hmetric
    have hfield :
        PhaseFlow.phaseField (c.accel (X.obj n).metric) (Φ z t) =
          MetricKoszul.metricSpray (d.chartMetric n x) (Φ z t) := by
      rw [MetricKoszul.metricSpray_eq _ _ hco]
      apply Prod.ext
      · rfl
      · simpa only [c, b, BoundedGeometryNormalData.chartMetric,
          PhaseFlow.phaseField] using
          (c.accel_eq (X.obj n).metric (Φ z t) hquarter
            (b.equiv.coercive (X.obj n).metric hmetric))
    rwa [hfield] at hder
  have hstay : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ∀ t ∈ Icc (0 : Real) 1,
        (Φ z t).1 ∈ Metric.ball 0 (d.phaseRadius R) := by
    intro z hz t ht
    exact (hΦbox z hz t (hsmall ht)).1
  exact ⟨Φ, e, delta, hdelta,
    by simpa only [b, d.chartPhaseK_eq] using hdeltaEq,
    by simpa only [c] using hIsDiag,
    by simpa only [c] using hfence, hΦ0, hcurve, hstay, hcoe,
    by simpa only [b, d.chartPhaseK_eq] using hinvApprox⟩

theorem exists_diagInv_conv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) (c : ∀ n : Nat, (X.obj n).M)
    (hc : ∀ n, hd.dist n (c n) (X.obj n).basepoint ≤ R)
    (qStage qInf : NNReal) (hqInf : 0 < qInf)
    (hqInf_lt : qInf < qStage) (delta deltaInf : Real)
    (hdelta : 0 < delta) (hdeltaInf : 0 < deltaInf)
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hgInf_cd : ContDiffOn Real ∞ gInf
      (Metric.ball 0 (d.phaseRadius R)))
    (hgInf_lo : ∀ z ∈ Metric.ball (0 : E) (d.phaseRadius R), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v)
    (hg_conv : MapCInfConvOnCompacts
      (Metric.ball 0 (d.phaseRadius R))
      (fun n ↦ d.chartMetric n (c n)) gInf)
    {Φ : Nat → (E × E) → Real → E × E}
    {ΦInf : (E × E) → Real → E × E}
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    (hΦ : ∀ n z, z ∈ Metric.closedBall (0 : E × E) qStage →
      Φ n z 0 = z ∧
      IsIntegralCurveOn (Φ n z)
        (fun _ ↦ MetricKoszul.metricSpray (d.chartMetric n (c n)))
        (Icc 0 1))
    (hΦInf : ∀ z, z ∈ Metric.closedBall (0 : E × E) qInf →
      ΦInf z 0 = z ∧
      IsIntegralCurveOn (ΦInf z)
        (fun _ ↦ MetricKoszul.metricSpray gInf) (Icc 0 1))
    (hstay : ∀ n z, z ∈ Metric.closedBall (0 : E × E) qStage →
      ∀ t ∈ Icc (0 : Real) 1,
        (Φ n z t).1 ∈ Metric.ball 0 (d.phaseRadius R))
    (hstayInf : ∀ z, z ∈ Metric.closedBall (0 : E × E) qInf →
      ∀ t ∈ Icc (0 : Real) 1,
        (ΦInf z t).1 ∈ Metric.ball 0 (d.phaseRadius R))
    (he : ∀ n, (e n : E × E → E × E) =
      fun z ↦ (z.1, (Φ n z 1).1))
    (heInf : (eInf : E × E → E × E) =
      fun z ↦ (z.1, (ΦInf z 1).1))
    (hdiag : ∀ n, IsNormalDiag (I := I) (X.obj n)
      (hcomplete.complete n) (hconn n) (c n) qStage delta (e n)
      (c := d.chart n (c n)))
    (hInf_source : eInf.source = Metric.ball (0 : E × E) qInf)
    (hInf_zero : eInf 0 = 0)
    (hInf_cd : ContDiffOn Real ∞ (eInf : E × E → E × E)
      eInf.source)
    (hInf_target : Metric.closedBall (0 : E × E) deltaInf ⊆
      eInf.target)
    (hInf_symm_cd : ContDiffOn Real ∞ eInf.symm eInf.target) :
    MapCInfConvOnCompacts (Metric.ball (0 : E × E) qInf)
        (fun n ↦ (e n : E × E → E × E)) eInf ∧
      ∃ delta₀ : Real,
        0 < delta₀ ∧ delta₀ < min delta deltaInf ∧
        eInf.symm '' Metric.closedBall 0 delta₀ ⊆
          Metric.ball 0 qInf ∧
        Filter.Eventually
          (fun n : Nat ↦ Set.MapsTo (e n).symm
            (Metric.closedBall 0 delta₀)
            (Metric.ball 0 qInf)) Filter.atTop ∧
        MapCInfConvOnCompacts (Metric.ball 0 delta₀)
          (fun n ↦ ((e n).symm : E × E → E × E)) eInf.symm := by
  let U : Set E := Metric.ball 0 (d.phaseRadius R)
  let Q : Set (E × E) := Metric.ball 0 qInf
  have hg_cd : ∀ n, ContDiffOn Real ∞ (d.chartMetric n (c n)) U := by
    intro n
    let : TopologicalSpace (X.obj n).M := (X.obj n).topology
    let : ChartedSpace H (X.obj n).M := (X.obj n).charted
    let : IsManifold I ∞ (X.obj n).M := (X.obj n).smooth
    let : T2Space (X.obj n).M := (X.obj n).t2
    let : T2Space (TangentBundle I (X.obj n).M) :=
      (X.obj n).t2TangentBundle
    have hrad : U ⊆ Metric.ball (0 : E) (d.chart n (c n)).radius := by
      exact (d.phaseRadius_chart (hc n)).trans <|
        Metric.ball_subset_ball (by
          nlinarith [(d.chart n (c n)).radius_pos])
    simpa only [U, BoundedGeometryNormalData.chartMetric] using
      (d.chart n (c n)).metric_cont_diff_on (X.obj n).metric
        Metric.isOpen_ball ((d.chart n (c n)).smooth_to.mono hrad)
  have hg_co : ∀ n z, z ∈ U →
      IsCoercive (d.chartMetric n (c n) z) := by
    intro n z hz
    let : TopologicalSpace (X.obj n).M := (X.obj n).topology
    let : ChartedSpace H (X.obj n).M := (X.obj n).charted
    let : IsManifold I ∞ (X.obj n).M := (X.obj n).smooth
    let : T2Space (X.obj n).M := (X.obj n).t2
    let : T2Space (TangentBundle I (X.obj n).M) :=
      (X.obj n).t2TangentBundle
    exact (d.metricBounds n (c n)).equiv.coercive
      (X.obj n).metric (d.phaseRadius_metric (hc n) hz)
  have hgInf_co : ∀ z, z ∈ U → IsCoercive (gInf z) := by
    intro z hz
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro v
    simpa only [pow_two, mul_assoc] using hgInf_lo z hz v
  have hqInfReal : (0 : Real) < qInf := by exact_mod_cast hqInf
  have hqInfStage : (qInf : Real) < qStage := by exact_mod_cast hqInf_lt
  have hQStage : Q ⊆ Metric.closedBall (0 : E × E) qStage := by
    intro z hz
    change dist z 0 < (qInf : Real) at hz
    change dist z 0 ≤ (qStage : Real)
    linarith
  have hQInf : Q ⊆ Metric.closedBall (0 : E × E) qInf := by
    intro z hz
    exact Metric.ball_subset_closedBall hz
  have hforwardFormula := normalDiag_end_conv
    (Metric.isOpen_ball : IsOpen U) (Metric.isOpen_ball : IsOpen Q)
    hg_cd hgInf_cd hg_co hgInf_co
    (by simpa only [U] using hg_conv)
    (fun n z hz ↦ hΦ n z (hQStage hz))
    (fun z hz ↦ hΦInf z (hQInf hz))
    (fun n z hz ↦ hstay n z (hQStage hz))
    (fun z hz ↦ hstayInf z (hQInf hz))
  have hforward : MapCInfConvOnCompacts Q
      (fun n ↦ (e n : E × E → E × E)) eInf :=
    hforwardFormula.congr Metric.isOpen_ball
      (fun n z _hz ↦ congrFun (he n) z)
      (fun z _hz ↦ congrFun heInf z)
  have hclosureQ : closure Q ⊆ Metric.ball (0 : E × E) qStage := by
    change closure (Metric.ball (0 : E × E) qInf) ⊆
      Metric.ball 0 qStage
    rw [closure_ball 0 hqInfReal.ne']
    intro z hz
    rw [Metric.mem_closedBall, Metric.mem_ball] at *
    linarith
  have hsource : ∀ᶠ n in Filter.atTop, closure Q ⊆ (e n).source :=
    Filter.Eventually.of_forall fun n ↦ by
      rw [(hdiag n).1]
      exact hclosureQ
  have hstage_cd : ∀ n,
      ContDiffOn Real ∞ (e n : E × E → E × E) Q := by
    intro n
    exact (hdiag n).2.2.1.mono fun z hz ↦ by
      rw [(hdiag n).1]
      exact hclosureQ (subset_closure hz)
  have htarget : ∀ n,
      Metric.closedBall (0 : E × E) (min delta deltaInf) ⊆
        (e n).target := by
    intro n
    exact (Metric.closedBall_subset_closedBall
      (min_le_left delta deltaInf)).trans (hdiag n).2.2.2.1
  have htargetInf : Metric.closedBall (0 : E × E)
      (min delta deltaInf) ⊆ eInf.target :=
    (Metric.closedBall_subset_closedBall
      (min_le_right delta deltaInf)).trans hInf_target
  have hInf_cd' : ContDiffOn Real ∞
      (eInf : E × E → E × E) (interior eInf.source) :=
    hInf_cd.mono interior_subset
  have hInf_symm_cd' : ContDiffOn Real ∞ eInf.symm
      (Metric.ball (0 : E × E) (min delta deltaInf)) :=
    hInf_symm_cd.mono <|
      Metric.ball_subset_closedBall.trans <|
        (Metric.closedBall_subset_closedBall
          (min_le_right delta deltaInf)).trans hInf_target
  have hzero_source : (0 : E × E) ∈ eInf.source := by
    rw [hInf_source]
    simpa only [Metric.mem_ball, dist_self] using hqInfReal
  have hbase_eq : eInf.symm 0 = 0 := by
    have hleft := eInf.left_inv hzero_source
    simpa only [hInf_zero] using hleft
  have hbase : eInf.symm 0 ∈ Q := by
    change dist (eInf.symm 0) 0 < (qInf : Real)
    rw [hbase_eq]
    simpa only [dist_self] using hqInfReal
  refine ⟨hforward, ?_⟩
  exact Analysis.OpenPartialHomeomorph.exists_symm_convOn_ball
    Metric.isOpen_ball hforward hsource hstage_cd
    (lt_min hdelta hdeltaInf) htarget htargetInf
    hInf_cd' hInf_symm_cd' hbase

theorem exists_diagPair_at
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) (c : ∀ n : Nat, (X.obj n).M)
    (hc : ∀ n, hd.dist n (c n) (X.obj n).basepoint ≤ R)
    (q : NNReal) (hq : 0 < q)
    (hqWide : 6 * (q : Real) < d.phaseRadius R)
    (hqAcc : 3 * d.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real))
    (herr : PhaseFlow.phaseErr (d.phaseK (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹)
    (hinvErr :
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊ *
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
            PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (d.phaseK (2 * q)) < 1 / 24)
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hgInf_cd : ContDiffOn Real ∞ gInf
      (Metric.ball 0 (d.phaseRadius R)))
    (hgInf_lo : ∀ z ∈ Metric.ball (0 : E) (d.phaseRadius R), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v)
    (hg_conv : MapCInfConvOnCompacts
      (Metric.ball 0 (d.phaseRadius R))
      (fun n ↦ d.chartMetric n (c n)) gInf) :
    ∃ (deltaStage deltaInf : Real)
        (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
        (eInf : OpenPartialHomeomorph (E × E) (E × E)),
      HasDiagPairConv (I := I) hcomplete hconn c q (q / 2)
        deltaStage deltaInf e eInf (chart := d.chart) ∧
      ∀ n, NormalDiagFence (I := I) (X.obj n) (c n) q (e n)
          (c := d.chart n (c n)) ∧
        ApproximatesLinearOn
          ((e n).symm : E × E → E × E)
          ((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))
          (e n).target
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊ *
            (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                (E × E) →L[Real] (E × E))‖₊⁻¹ -
              PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
            PhaseFlow.phaseErr (d.phaseK (2 * q))) := by
  classical
  let qInf : NNReal := q / 2
  have hqInf : 0 < qInf := by
    dsimp only [qInf]
    positivity
  have hqInfStage : qInf < q := by
    dsimp only [qInf]
    exact div_lt_self hq (by norm_num)
  have hqInfRadius : 4 * (qInf : Real) < d.phaseRadius R := by
    have hqReal : (0 : Real) < q := by exact_mod_cast hq
    dsimp only [qInf]
    push_cast
    nlinarith
  have hqInfAcc : 3 * d.metricC 1 * (2 * (qInf : Real)) ^ 2 ≤
      (qInf : Real) := by
    have hqReal : (0 : Real) ≤ q := by exact_mod_cast hq.le
    have hC : 0 ≤ d.metricC 1 := d.metricC_nonneg 1
    dsimp only [qInf]
    push_cast
    nlinarith [hqAcc]
  have hqInfTwo : 2 * qInf ≤ 2 * q :=
    mul_le_mul_of_nonneg_left hqInfStage.le (by norm_num)
  have hphaseK : d.phaseK (2 * qInf) ≤ d.phaseK (2 * q) := by
    let Y := X.obj 0
    let x₀ := Y.basepoint
    let : TopologicalSpace Y.M := Y.topology
    let : ChartedSpace H Y.M := Y.charted
    let : IsManifold I ∞ Y.M := Y.smooth
    let : SigmaCompactSpace Y.M := Y.sigmaCompact
    let : T2Space Y.M := Y.t2
    let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    simpa only [Y, x₀, d.chartPhaseK_eq] using
      chartPhaseK_mono (I := I) Y.metric (d.metricBounds 0 x₀) hqInfTwo
  have herrLe : PhaseFlow.phaseErr (d.phaseK (2 * qInf)) ≤
      PhaseFlow.phaseErr (d.phaseK (2 * q)) :=
    PhaseFlow.phaseErr_mono hphaseK
  have hqInfErr : PhaseFlow.phaseErr (d.phaseK (2 * qInf)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ :=
    herrLe.trans_lt herr
  have hstage : ∀ n,
      ∃ (Φ : (E × E) → Real → E × E)
          (e : OpenPartialHomeomorph (E × E) (E × E)) (delta : Real),
        0 < delta ∧
        delta = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊⁻¹ -
            PhaseFlow.phaseErr (d.phaseK (2 * q)) : NNReal) : Real) *
          ((q : Real) / 2) ∧
        IsNormalDiag (I := I) (X.obj n) (hcomplete.complete n) (hconn n)
          (c n) q delta e (c := d.chart n (c n)) ∧
        NormalDiagFence (I := I) (X.obj n) (c n) q e
          (c := d.chart n (c n)) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q,
          IsIntegralCurveOn (Φ z)
            (fun _ ↦ MetricKoszul.metricSpray (d.chartMetric n (c n)))
            (Icc 0 1)) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q,
          ∀ t ∈ Icc (0 : Real) 1,
            (Φ z t).1 ∈ Metric.ball 0 (d.phaseRadius R)) ∧
        (e : E × E → E × E) = (fun z ↦ (z.1, (Φ z 1).1)) ∧
        ApproximatesLinearOn
          (e.symm : E × E → E × E)
          ((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))
          e.target
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊ *
            (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                (E × E) →L[Real] (E × E))‖₊⁻¹ -
              PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
            PhaseFlow.phaseErr (d.phaseK (2 * q))) := by
    intro n
    exact d.exists_stage_flow hcomplete hconn R n (c n) (hc n)
      q hq hqWide hqAcc herr
  choose Φ e delta hdelta hdeltaEq hdiag hfence hΦ0 hΦcurve hΦstay he
    hinvStage using hstage
  let deltaStage : Real :=
    ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊⁻¹ -
        PhaseFlow.phaseErr (d.phaseK (2 * q)) : NNReal) : Real) *
      ((q : Real) / 2)
  have hdeltaStage : 0 < deltaStage := by
    simpa only [deltaStage, hdeltaEq 0] using hdelta 0
  have hdiagStage : ∀ n, IsNormalDiag (I := I) (X.obj n)
      (hcomplete.complete n) (hconn n) (c n) q deltaStage (e n)
      (c := d.chart n (c n)) := by
    intro n
    simpa only [deltaStage, hdeltaEq n] using hdiag n
  obtain ⟨ΦInf, eInf, deltaInf, hdeltaInf, hΦInf0, hΦInfCurve,
      hΦInfStay, hInfSource, hInfZero, heInf, hInfTarget,
      hInfSmooth, hInfSymmSmooth, hInfDiag, hInfApprox⟩ :=
    d.exists_limit_diag R c hc hgInf_cd hgInf_lo hg_conv qInf hqInf
      hqInfRadius hqInfAcc hqInfErr
  obtain ⟨hforward, delta₀, hdelta₀, hdelta₀lt, hInfMaps,
      hstageMaps, hinverse⟩ :=
    d.exists_diagInv_conv hcomplete hconn R c hc q qInf hqInf
      hqInfStage deltaStage deltaInf hdeltaStage hdeltaInf
      hgInf_cd hgInf_lo hg_conv
      (fun n z hz ↦ ⟨hΦ0 n z hz, hΦcurve n z hz⟩)
      (fun z hz ↦ ⟨hΦInf0 z hz, hΦInfCurve z hz⟩)
      hΦstay hΦInfStay he heInf hdiagStage hInfSource hInfZero
      hInfSmooth hInfTarget hInfSymmSmooth
  let N : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊
  let cInf : NNReal := PhaseFlow.phaseErr (d.phaseK (2 * qInf))
  let cStage : NNReal := PhaseFlow.phaseErr (d.phaseK (2 * q))
  let η : NNReal := N * (N⁻¹ - cInf)⁻¹ * cInf
  have hInvMono : N * (N⁻¹ - cInf)⁻¹ * cInf ≤
      N * (N⁻¹ - cStage)⁻¹ * cStage := by
    exact PhaseFlow.invErr_mono
      (by simpa only [cInf, cStage] using herrLe)
      (by simpa only [N, cStage] using herr)
  have hη : η < 1 := by
    calc
      η ≤ N * (N⁻¹ - cStage)⁻¹ * cStage := hInvMono
      _ < 1 / 24 := by
        simpa only [N, cStage] using hinvErr
      _ < 1 := by norm_num
  have hInfApproxη : ApproximatesLinearOn
      (eInf.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) eInf.target η := by
    simpa only [η, N, cInf] using hInfApprox
  refine ⟨deltaStage, deltaInf, e, eInf, ?_, ?_⟩
  · simpa only [qInf] using
      (show HasDiagPairConv (I := I) hcomplete hconn c q qInf
        deltaStage deltaInf e eInf (chart := d.chart) from
        ⟨hq, hqInf, hqInfStage, hdeltaStage, hdeltaInf, hdiagStage,
          hInfSource, hInfZero, hInfTarget, hInfSmooth, hInfSymmSmooth,
          hInfDiag, ⟨η, hη, hInfApproxη⟩, hforward,
          delta₀, hdelta₀, hdelta₀lt, hInfMaps, hstageMaps, hinverse⟩)
  · intro n
    exact ⟨hfence n, hinvStage n⟩

end BoundedGeometryNormalData

end HCGCompactness
end DifferentialGeometry
