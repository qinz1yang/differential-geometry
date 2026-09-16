import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Diameter
import DifferentialGeometry.Geometry.Curvature.Metric.ConstantRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelDistanceTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundCanonicalWitness

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
theorem metricDistance_scaleMetric (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I3 M) (x y : M) :
    metricDistance (scaleMetric (I := I3) c hc g) x y =
      Real.sqrt c * metricDistance g x y := by
  rw [metricDistance, metricDistance, edistOf_scale, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg c)]

theorem metricDistance_le_of_roundComponent_diameterBound
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {eps : ℝ} {x : M} {t : ℝ} (RC : RoundComponent S eps x t Set.univ)
    (heps0 : 0 ≤ eps) (heps1 : eps < 1) {Dia : ℝ} (hDia0 : 0 ≤ Dia) :
    letI : TopologicalSpace RC.Z := RC.topology
    letI : ChartedSpace ThreeSpace RC.Z := RC.charted
    letI : IsManifold I3 ∞ RC.Z := RC.smooth
    letI : T2Space RC.Z := RC.t2
    letI : CompactSpace RC.Z := RC.compact
    (∀ z : RC.Z,
      riemannianEDistOf (I := I3) RC.metric RC.p z ≤ ENNReal.ofReal Dia) →
      ∀ z : RC.Z,
        metricDistance (S.base.metric t) (RC.map RC.p) (RC.map z) ≤
          Real.sqrt (1 + eps) * Dia / Real.sqrt (S.scalar t x) := by
  intro hDia z
  let : TopologicalSpace RC.Z := RC.topology
  let : ChartedSpace ThreeSpace RC.Z := RC.charted
  let : IsManifold I3 ∞ RC.Z := RC.smooth
  let : T2Space RC.Z := RC.t2
  let : CompactSpace RC.Z := RC.compact
  have hQ : 0 < S.scalar t x := RC.Q_pos
  have hs0 : 0 < Real.sqrt (1 - eps) := Real.sqrt_pos.mpr (by linarith)
  have hspos : 0 < Real.sqrt (S.scalar t x) := Real.sqrt_pos.mpr hQ
  have hRpos : 0 < 3 * (Dia + 1) * Real.sqrt (1 + eps) / Real.sqrt (1 - eps) + 1 := by
    have h1 : 0 < Dia + 1 := by linarith
    have h2 : 0 < Real.sqrt (1 + eps) := Real.sqrt_pos.mpr (by linarith)
    have h3 : 0 < 3 * (Dia + 1) * Real.sqrt (1 + eps) := by positivity
    have h4 : 0 < 3 * (Dia + 1) * Real.sqrt (1 + eps) / Real.sqrt (1 - eps) :=
      div_pos h3 hs0
    linarith
  have hroom : Real.sqrt (1 + eps) * (3 * (Dia + 1)) <
      Real.sqrt (1 - eps) *
        (3 * (Dia + 1) * Real.sqrt (1 + eps) / Real.sqrt (1 - eps) + 1) := by
    have hkey : Real.sqrt (1 - eps) *
        (3 * (Dia + 1) * Real.sqrt (1 + eps) / Real.sqrt (1 - eps)) =
        3 * (Dia + 1) * Real.sqrt (1 + eps) := by
      field_simp
    nlinarith [hs0, hkey]
  have hcpt : IsCompact (riemannianClosedBallOf (I := I3) RC.metric RC.p
      (3 * (Dia + 1) * Real.sqrt (1 + eps) / Real.sqrt (1 - eps) + 1)) :=
    RiemannianMetricComplete.closedEBall_isCompact (I := I3) (M := RC.Z)
      (RiemannianMetricComplete.of_compact RC.metric) RC.p _
  have hpmem : RC.p ∈ riemannianClosedBallOf (I := I3) RC.metric RC.p (Dia + 1) := by
    change riemannianEDistOf (I := I3) RC.metric RC.p RC.p ≤ ENNReal.ofReal (Dia + 1)
    rw [riemannianEDistOf_self]
    exact bot_le
  have hzmem : z ∈ riemannianClosedBallOf (I := I3) RC.metric RC.p (Dia + 1) := by
    change riemannianEDistOf (I := I3) RC.metric RC.p z ≤ ENNReal.ofReal (Dia + 1)
    exact (hDia z).trans (ENNReal.ofReal_le_ofReal (by linarith))
  obtain ⟨-, hhi⟩ := crossModel_edist_transfer_of_comparison RC.metric
    (scaleMetric (I := I3) (S.scalar t x) RC.Q_pos (S.base.metric t)) RC.map
    RC.comparison RC.p hRpos heps0 heps1 (by linarith) hcpt
    (fun _ _ => trivial) (by rw [RC.source_eq]; exact subset_univ _) hroom RC.p hpmem z hzmem
  have hb : riemannianEDistOf (I := I3)
      (scaleMetric (I := I3) (S.scalar t x) RC.Q_pos (S.base.metric t))
      (RC.map RC.p) (RC.map z) ≤ ENNReal.ofReal (Real.sqrt (1 + eps) * Dia) := by
    have hstep : riemannianEDistOf (I := I3)
        (scaleMetric (I := I3) (S.scalar t x) RC.Q_pos (S.base.metric t))
        (RC.map RC.p) (RC.map z) ≤
        ENNReal.ofReal (Real.sqrt (1 + eps)) * ENNReal.ofReal Dia :=
      hhi.trans ((ENNReal.mul_le_mul_iff_right
        (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (by linarith))))
        ENNReal.ofReal_ne_top).mpr (hDia z))
    rwa [← ENNReal.ofReal_mul (Real.sqrt_nonneg (1 + eps))] at hstep
  have hmd : metricDistance
      (scaleMetric (I := I3) (S.scalar t x) RC.Q_pos (S.base.metric t))
      (RC.map RC.p) (RC.map z) ≤ Real.sqrt (1 + eps) * Dia := by
    rw [metricDistance]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  rw [metricDistance_scaleMetric (S.scalar t x) RC.Q_pos (S.base.metric t)
    (RC.map RC.p) (RC.map z)] at hmd
  rw [le_div_iff₀ hspos]
  simpa only [mul_comm] using hmd

def RoundComponentEdistDiameterBound (Dia : ℝ) : Prop :=
  0 ≤ Dia ∧ ∀ {D : RealTimeInterval} {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    {S : SolutionOn (I := I3) (M := M) D} {eps : ℝ} {x : M} {t : ℝ}
    (RC : RoundComponent S eps x t Set.univ),
    letI : TopologicalSpace RC.Z := RC.topology
    letI : ChartedSpace ThreeSpace RC.Z := RC.charted
    letI : IsManifold I3 ∞ RC.Z := RC.smooth
    letI : T2Space RC.Z := RC.t2
    letI : CompactSpace RC.Z := RC.compact
    ∀ z : RC.Z, riemannianEDistOf (I := I3) RC.metric RC.p z ≤ ENNReal.ofReal Dia

theorem metricDistance_le_of_roundComponent_edistDiameter {Dia : ℝ}
    (h : RoundComponentEdistDiameterBound.{u} Dia)
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {eps : ℝ} {x : M} {t : ℝ} (RC : RoundComponent S eps x t Set.univ)
    (heps0 : 0 ≤ eps) (heps1 : eps < 1) :
    letI : TopologicalSpace RC.Z := RC.topology
    letI : ChartedSpace ThreeSpace RC.Z := RC.charted
    letI : IsManifold I3 ∞ RC.Z := RC.smooth
    letI : T2Space RC.Z := RC.t2
    letI : CompactSpace RC.Z := RC.compact
    ∀ z : RC.Z,
      metricDistance (S.base.metric t) (RC.map RC.p) (RC.map z) ≤
        Real.sqrt (1 + eps) * Dia / Real.sqrt (S.scalar t x) := by
  let : TopologicalSpace RC.Z := RC.topology
  let : ChartedSpace ThreeSpace RC.Z := RC.charted
  let : IsManifold I3 ∞ RC.Z := RC.smooth
  let : T2Space RC.Z := RC.t2
  let : CompactSpace RC.Z := RC.compact
  exact metricDistance_le_of_roundComponent_diameterBound RC heps0 heps1 h.1 (h.2 RC)

theorem exists_roundSphereThree_edistDiameterBound (x : RoundSphereThree) :
    ∃ Dia : ℝ, 0 ≤ Dia ∧ ∀ z : RoundSphereThree,
      riemannianEDistOf (I := I3) roundSphereThreeMetric x z ≤ ENNReal.ofReal Dia := by
  obtain ⟨R, hRpos, hRball⟩ := exists_roundSphereThree_ball_eq_univ x
  exact ⟨R, hRpos.le, fun z => (hRball trivial).le⟩

theorem roundComponent_edist_diameter_bound :
    RoundComponentEdistDiameterBound.{u} (Real.pi / Real.sqrt (1 / 6)) := by
  refine ⟨by positivity, ?_⟩
  intro D M _ _ _ _ _ S eps x t RC
  let _ : TopologicalSpace RC.Z := RC.topology
  let _ : ChartedSpace ThreeSpace RC.Z := RC.charted
  let _ : IsManifold I3 ∞ RC.Z := RC.smooth
  let _ : T2Space RC.Z := RC.t2
  let _ : CompactSpace RC.Z := RC.compact
  let _ : ConnectedSpace RC.Z := RC.connected
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hRic := ricciBound_of_sec (I := I3) RC.metric (1 / 6) (by
    intro z v w
    have h := RC.constant_curvature z v w
    have hv : (fun i : Fin 4 => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
      funext i
      fin_cases i <;> simp [vec4]
    rw [hv, ← metricRm04StandardAt_apply] at h
    simpa only [pow_two] using h)
  intro z
  exact BonnetMyers.bonnet_myers_pairwise_edist_le_of_complete_metric (I := I3)
    RC.metric (RiemannianMetricComplete.of_compact RC.metric)
    (by simp [ThreeSpace]) (by norm_num : (0 : ℝ) < 1 / 6) hRic RC.p z

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
