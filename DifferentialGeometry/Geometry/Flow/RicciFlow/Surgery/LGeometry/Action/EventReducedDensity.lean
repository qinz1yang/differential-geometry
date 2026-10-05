import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventAction

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)

private local instance : MeasurableSpace P.Carrier := borel P.Carrier
private local instance : BorelSpace P.Carrier := ⟨rfl⟩

def eventRegularizedC1Density (T d v : ℝ) (p : Q.Carrier) (q : P.Carrier) : ℝ≥0∞ :=
  ⨆ A ∈ E.eventRegularizedC1ActionValues G T d v p q,
    ENNReal.ofReal (Real.exp (-A / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
      (3 / 2 : ℝ) * Real.log (4 * Real.pi)))

theorem eventRegularizedC1Density_eq_zero_of_no_competitor
    (T d v : ℝ) (p : Q.Carrier) (q : P.Carrier)
    (h : E.eventRegularizedC1ActionValues G T d v p q = ∅) :
    E.eventRegularizedC1Density G T d v p q = 0 := by
  simp [eventRegularizedC1Density, h]

theorem le_eventRegularizedC1Density_of_action_le
    (T d : ℝ) {v L A : ℝ} (hv : 0 < v) (p : Q.Carrier) (q : P.Carrier)
    (hA : A ∈ E.eventRegularizedC1ActionValues G T d v p q) (hAL : A ≤ L) :
    ENNReal.ofReal (Real.exp (-L / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
      (3 / 2 : ℝ) * Real.log (4 * Real.pi))) ≤ E.eventRegularizedC1Density G T d v p q := by
  apply le_trans _ (le_iSup_of_le A (le_iSup_of_le hA le_rfl))
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hh := div_le_div_of_nonneg_right (neg_le_neg hAL) (by positivity : 0 ≤ 2 * v)
  linarith

theorem eventRegularizedC1Density_eq_of_minimum
    (T d : ℝ) {v A : ℝ} (hv : 0 < v) (p : Q.Carrier) (q : P.Carrier)
    (hA : A ∈ E.eventRegularizedC1ActionValues G T d v p q)
    (hmin : ∀ L ∈ E.eventRegularizedC1ActionValues G T d v p q, A ≤ L) :
    E.eventRegularizedC1Density G T d v p q =
      ENNReal.ofReal (Real.exp (-A / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) := by
  apply le_antisymm
  · apply iSup_le
    intro L
    apply iSup_le
    intro hL
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_right (neg_le_neg (hmin L hL)) (by positivity : 0 ≤ 2 * v)
    linarith
  · exact E.le_eventRegularizedC1Density_of_action_le G T d hv p q hA le_rfl

theorem volume_mul_exp_le_lintegral_eventRegularizedC1Density
    (T d : ℝ) {v L : ℝ} (hv : 0 < v) (p : Q.Carrier) {U : Set P.Carrier}
    (hU : MeasurableSet U)
    (haccess : ∀ q ∈ U, ∃ A ∈ E.eventRegularizedC1ActionValues G T d v p q, A ≤ L) :
    riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric (T - v ^ 2)) U *
      ENNReal.ofReal (Real.exp (-L / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) ≤
      ∫⁻ q in U, E.eventRegularizedC1Density G T d v p q
        ∂riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric (T - v ^ 2)) := by
  let μ := riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric (T - v ^ 2))
  let c := ENNReal.ofReal (Real.exp (-L / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
    (3 / 2 : ℝ) * Real.log (4 * Real.pi)))
  have hh : (∫⁻ _q in U, c ∂μ) ≤ ∫⁻ q in U, E.eventRegularizedC1Density G T d v p q ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hU] with q hq
    obtain ⟨A, hA, hAL⟩ := haccess q hq
    exact E.le_eventRegularizedC1Density_of_action_le G T d hv p q hA hAL
  simpa only [lintegral_const, Measure.restrict_apply_univ, mul_comm, μ, c] using hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
  (hcross : ∀ z : X, E.RegularCrossing (f z) (g z))

private local instance : MeasurableSpace P.Carrier := borel P.Carrier
private local instance : BorelSpace P.Carrier := ⟨rfl⟩

include hcross in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_open_pos_eventRegularizedC1Density_mass_of_survivor_seed
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v L : ℝ} (hd : 0 < d) (hdv : d < v)
    (hclock : T - d ^ 2 = s)
    (hcarrier : ∀ r ∈ Icc 0 v, T - r ^ 2 ∈ D.carrier)
    (htimePlus : ∀ r ∈ Icc 0 d, T - r ^ 2 ∈ (RealTimeInterval.closedOpen s b G.lt).carrier)
    (htimeMinus : ∀ r ∈ Ioc d v, T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s E.incoming.lt).carrier)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (η : ℝ → X) (hη : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η)
    (hseed : lRegularizedAction S T η 0 v < L) :
    ∃ U : Set P.Carrier, IsOpen U ∧ f (η v) ∈ U ∧ U ⊆ range f ∧
      0 < riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric (T - v ^ 2)) U ∧
      riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric (T - v ^ 2)) U *
        ENNReal.ofReal (Real.exp (-L / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
          (3 / 2 : ℝ) * Real.log (4 * Real.pi))) ≤
        ∫⁻ q in U, E.eventRegularizedC1Density G T d v (g (η 0)) q
          ∂riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric (T - v ^ 2)) := by
  obtain ⟨V, hV, hηV, α, hα, hstart, hend, _, hact⟩ :=
    exists_open_endpoint_family_of_lRegularizedAction_lt S hS T (hd.trans hdv) hcarrier η hη hseed
  have hopen : IsOpen (f '' V) := hf.isOpenMap V hV
  refine ⟨f '' V, hopen, ⟨η v, hηV, rfl⟩, image_subset_range _ _, ?_, ?_⟩
  · let _ : (riemannianVolumeMeasure ThreeModel P.Carrier
        (E.incoming.flow.base.metric (T - v ^ 2))).IsOpenPosMeasure :=
      riemannianVolumeMeasure_isOpenPosMeasure _
    exact hopen.measure_pos _ ⟨_, ⟨η v, hηV, rfl⟩⟩
  · apply E.volume_mul_exp_le_lintegral_eventRegularizedC1Density G T d (hd.trans hdv)
      (g (η 0)) hopen.measurableSet
    rintro y ⟨z, hz, rfl⟩
    refine ⟨lRegularizedAction S T (α z) 0 v, ?_, (hact z hz).le⟩
    have hmem := E.action_mem_eventRegularizedC1ActionValues_of_survivor_curve G f g hf hg hcross
      S hS T hd hdv hclock hcarrier htimePlus htimeMinus
      hbefore hafter (α z) (hα z hz)
    simpa only [hstart z hz, hend z hz] using hmem

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end
