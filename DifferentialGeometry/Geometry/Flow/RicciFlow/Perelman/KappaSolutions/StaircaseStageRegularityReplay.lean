import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.StageComparison.HigherRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormalChartTransitionLimits
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaircaseChartReplayBlock

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal NNReal
open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

namespace SeqBallNormalChartData

def phaseKOf (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p) (R : NNReal) : NNReal where
  val := (6 * (CB 1) ^ 2 + 3 * CB 2) * (R : Real) ^ 2 + 6 * CB 1 * (R : Real)
  property := by
    have hA : 0 ≤ 6 * (CB 1) ^ 2 + 3 * CB 2 :=
      add_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg (CB 1)))
        (mul_nonneg (by norm_num) (hCB 2))
    exact add_nonneg
      (mul_nonneg hA (sq_nonneg (R : Real)))
      (mul_nonneg (mul_nonneg (by norm_num) (hCB 1)) R.coe_nonneg)

def toBoundedGeometryNormalChartData
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p) :
    BoundedGeometryNormalChartData (I := I) X hd where
  ratio := d.ratio
  ratio_pos := d.ratio_pos
  ratio_mu0_le := d.ratio_mu0_le
  chart := d.chart
  radius_eq := d.radius_eq
  hom_eq := d.hom_eq
  metricC := CB
  metricC_nonneg := hCB
  metric_equiv := by
    intro k x
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    obtain ⟨b, hrad, _⟩ := hunif k x
    have hmain : (d.chart k x).MetricEquivOn (X.obj k).metric
        (Metric.ball (0 : E) b.radius) := b.equiv
    rw [← hrad]
    exact hmain
  metric_deriv := by
    intro k p x
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    obtain ⟨b, hrad, hC⟩ := hunif k x
    have hmain : (d.chart k x).MetricDerivBound (X.obj k).metric
        (Metric.ball (0 : E) b.radius) p (b.C p) := b.deriv p
    have hle : b.C p ≤ CB p := hC p
    rw [← hrad]
    exact fun z hz => (hmain z hz).trans hle

omit [CompleteSpace E] in
theorem subseq_chartTransition
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (f : Nat → Nat)
    (hf : ∀ j : Nat, j ≤ f j) (k : Nat)
    (x y : ((X.subseq f).obj k).M) :
    (d.subseq f hf).chartTransition k x y = d.chartTransition (f k) x y :=
  rfl

omit [CompleteSpace E] in
theorem toBoundedGeometryNormalChartData_metricC
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
    (p : Nat) :
    (d.toBoundedGeometryNormalChartData CB hCB hunif).metricC p = CB p :=
  rfl

omit [CompleteSpace E] in
theorem toBoundedGeometryNormalChartData_phaseRadius
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
    (R : Real) :
    (d.toBoundedGeometryNormalChartData CB hCB hunif).phaseRadius R =
      d.phaseRadius R :=
  rfl

omit [CompleteSpace E] in
theorem toBoundedGeometryNormalChartData_chart
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p) :
    (d.toBoundedGeometryNormalChartData CB hCB hunif).chart = d.chart :=
  rfl

omit [CompleteSpace E] in
theorem toBoundedGeometryNormalChartData_phaseK
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
    (R : NNReal) :
    (d.toBoundedGeometryNormalChartData CB hCB hunif).phaseK R =
      phaseKOf CB hCB R :=
  Subtype.ext rfl


noncomputable def stageScale
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
    (hre : hd.RealizesDistance)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) : Real :=
  (d.toBoundedGeometryNormalChartData CB hCB hunif).stageScale hre hcomplete hconn

theorem exists_stage_jet_convergence
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (d : SeqBallNormalChartData (I := I) X inp.decay)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hphys : 8 * Real.exp inp.decay.C <
      d.stageScale CB hCB hunif inp.realizes hcomplete hconn * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    (r : Real) (hr : 0 ≤ r) :
    ∃ (phi : Nat → Nat) (hphi : StrictMono phi)
        (V U C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (gInf : LiveSlot L inp.pack r →
          E → (E →L[Real] E →L[Real] Real)),
      HasStageJetConvergenceOn (I := I) inp P L hr phi hphi d.chart
        V U C0 C1 aInf Jinf Jbarinf gInf :=
  BoundedGeometryNormalChartData.exists_stage_jet_convergence inp
    (d.toBoundedGeometryNormalChartData CB hCB hunif)
    hcomplete hconn hphys P L hstable r hr

theorem exists_scale_with_stage_jet_convergence
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (d : SeqBallNormalChartData (I := I) X inp.decay)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ aMin : Real, 0 < aMin ∧ 48 * aMin < d.ratio ∧
      ∀ (_hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
        (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
        (L : NetLimitData inp.decay inp.D P)
        (_hstable : ∀ a b : Nat,
          (∀ᶠ k in Filter.atTop,
            BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
          (∀ᶠ k in Filter.atTop,
            ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
        (r : Real) (hr : 0 ≤ r),
        ∃ (phi : Nat → Nat) (hphi : StrictMono phi)
            (V U C0 C1 : LiveSlot L inp.pack r → Set E)
            (aInf : (alpha : LiveSlot L inp.pack r) →
              Fin (inp.pack.A r) → E → Real)
            (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
              InterSlot L inp.pack r alpha → E → E)
            (gInf : LiveSlot L inp.pack r →
              E → (E →L[Real] E →L[Real] Real)),
          HasStageJetConvergenceOn (I := I) inp P L hr phi hphi d.chart
            V U C0 C1 aInf Jinf Jbarinf gInf :=
  BoundedGeometryNormalChartData.exists_scale_with_stage_jet_convergence inp
    (d.toBoundedGeometryNormalChartData CB hCB hunif) hcomplete hconn

theorem stage_diag
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (d : SeqBallNormalChartData (I := I) X inp.decay)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hphys : 8 * Real.exp inp.decay.C <
      d.stageScale CB hCB hunif inp.realizes hcomplete hconn * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hstable : IsStableNet inp P L0) :
    ∃ (hseed : HasStageSeedOn inp P L0 d.chart)
        (psi : Nat → Nat) (_hpsi : StrictMono psi),
      ∀ q : Nat,
        HasRadiusTailOn inp P L0 d.chart hseed psi q :=
  BoundedGeometryNormalChartData.stage_diag inp
    (d.toBoundedGeometryNormalChartData CB hCB hunif)
    hcomplete hconn hphys P L0 hstable

theorem exists_stage_diag
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (d : SeqBallNormalChartData (I := I) X inp.decay)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ aMin : Real, 0 < aMin ∧ 48 * aMin < d.ratio ∧
      ∀ (_hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
        (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
        (L0 : NetLimitData inp.decay inp.D P)
        (_hstable : IsStableNet inp P L0),
        ∃ (hseed : HasStageSeedOn inp P L0 d.chart)
            (psi : Nat → Nat) (_hpsi : StrictMono psi),
          ∀ q : Nat,
            HasRadiusTailOn inp P L0 d.chart hseed psi q :=
  BoundedGeometryNormalChartData.exists_stage_diag inp
    (d.toBoundedGeometryNormalChartData CB hCB hunif) hcomplete hconn

theorem exists_transition_limit_subsequence_fin
    {ι : Type*} (s : Finset ι)
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    (n : Nat)
    (x y : ι → ∀ k : Nat, (X.obj k).M)
    (U V Ua Va : ι → Set E)
    (hU : ∀ i, i ∈ s → IsOpen (U i))
    (hV : ∀ i, i ∈ s → IsOpen (V i))
    (hUa : ∀ i, i ∈ s → IsOpen (Ua i))
    (hVa : ∀ i, i ∈ s → IsOpen (Va i))
    (hUanorm : ∀ i, i ∈ s → ∃ Z : Real, ∀ z ∈ Ua i, ‖z‖ ≤ Z)
    (hVanorm : ∀ i, i ∈ s → ∃ Z : Real, ∀ z ∈ Va i, ‖z‖ ≤ Z)
    (hxdist : ∀ i, i ∈ s → ∀ k,
      hd.dist k (x i k) (X.obj k).basepoint ≤ (n : Real))
    (hydist : ∀ i, i ∈ s → ∀ k,
      hd.dist k (y i k) (X.obj k).basepoint ≤ (n : Real))
    (hUarad : ∀ i, i ∈ s → ∀ k,
      Ua i ⊆ Metric.ball (0 : E)
        (d.ratio * hd.mu (hd.dist k (x i k) (X.obj k).basepoint)))
    (hVarad : ∀ i, i ∈ s → ∀ k,
      Va i ⊆ Metric.ball (0 : E)
        (d.ratio * hd.mu (hd.dist k (y i k) (X.obj k).basepoint)))
    (hovlJ : ∀ i, i ∈ s → ∀ k, d.chartOverlapOn k (x i k) (y i k) (U i))
    (hovlJbar : ∀ i, i ∈ s → ∀ k, d.chartOverlapOn k (y i k) (x i k) (V i))
    (hmapJ : ∀ i, i ∈ s → ∀ k, Set.MapsTo
      (d.chartTransition k (x i k) (y i k)) (U i) (Va i))
    (hmapJbar : ∀ i, i ∈ s → ∀ k, Set.MapsTo
      (d.chartTransition k (y i k) (x i k)) (V i) (Ua i)) :
    ∃ phi : Nat → Nat, StrictMono phi ∧ (∀ j : Nat, j ≤ phi j) ∧
      ∀ i, i ∈ s → ∃ Jinf : E → E, ∃ Jbarinf : E → E,
        ContDiffOn Real (⊤ : ℕ∞) Jinf (U i) ∧
        ContDiffOn Real (⊤ : ℕ∞) Jbarinf (V i) ∧
        MapCInfConvergenceOnCompacts (U i)
          (fun k => d.chartTransition (phi k)
            (x i (phi k)) (y i (phi k))) Jinf ∧
        MapCInfConvergenceOnCompacts (V i)
          (fun k => d.chartTransition (phi k)
            (y i (phi k)) (x i (phi k))) Jbarinf ∧
        (∀ z ∈ U i, Jinf z ∈ V i → Jbarinf (Jinf z) = z) ∧
        (∀ z ∈ V i, Jbarinf z ∈ U i → Jinf (Jbarinf z) = z) := by
  classical
  revert hU hV hUa hVa hUanorm hVanorm hxdist hydist hUarad hVarad
    hovlJ hovlJbar hmapJ hmapJbar
  induction s using Finset.induction with
  | empty =>
      intro hU hV hUa hVa hUanorm hVanorm hxdist hydist hUarad hVarad
        hovlJ hovlJbar hmapJ hmapJbar
      exact ⟨id, strictMono_id, fun j => le_rfl, fun i hi => by simp at hi⟩
  | @insert a s ha ih =>
      intro hU hV hUa hVa hUanorm hVanorm hxdist hydist hUarad hVarad
        hovlJ hovlJbar hmapJ hmapJbar
      obtain ⟨phi0, hphi0, hid0, hprev⟩ :=
        ih
          (fun i hi => hU i (Finset.mem_insert_of_mem hi))
          (fun i hi => hV i (Finset.mem_insert_of_mem hi))
          (fun i hi => hUa i (Finset.mem_insert_of_mem hi))
          (fun i hi => hVa i (Finset.mem_insert_of_mem hi))
          (fun i hi => hUanorm i (Finset.mem_insert_of_mem hi))
          (fun i hi => hVanorm i (Finset.mem_insert_of_mem hi))
          (fun i hi => hxdist i (Finset.mem_insert_of_mem hi))
          (fun i hi => hydist i (Finset.mem_insert_of_mem hi))
          (fun i hi => hUarad i (Finset.mem_insert_of_mem hi))
          (fun i hi => hVarad i (Finset.mem_insert_of_mem hi))
          (fun i hi => hovlJ i (Finset.mem_insert_of_mem hi))
          (fun i hi => hovlJbar i (Finset.mem_insert_of_mem hi))
          (fun i hi => hmapJ i (Finset.mem_insert_of_mem hi))
          (fun i hi => hmapJbar i (Finset.mem_insert_of_mem hi))
      obtain ⟨phi1, Jinf, Jbarinf, hphi1, hJinf, hJbarinf,
          hJ, hJbar, hleft, hright⟩ :=
        (d.subseq phi0 hid0).exists_transition_limit_subsequence
          (hreal.subseq phi0) n
          (fun k => x a (phi0 k)) (fun k => y a (phi0 k))
          (hU a (Finset.mem_insert_self a s))
          (hV a (Finset.mem_insert_self a s))
          (hUa a (Finset.mem_insert_self a s))
          (hVa a (Finset.mem_insert_self a s))
          (hUanorm a (Finset.mem_insert_self a s))
          (hVanorm a (Finset.mem_insert_self a s))
          (fun k => by
            with_unfolding_all
              exact hxdist a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => by
            with_unfolding_all
              exact hydist a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => by
            with_unfolding_all
              exact hUarad a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => by
            with_unfolding_all
              exact hVarad a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => by
            with_unfolding_all
              exact hovlJ a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => by
            with_unfolding_all
              exact hovlJbar a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => by
            with_unfolding_all
              exact hmapJ a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => by
            with_unfolding_all
              exact hmapJbar a (Finset.mem_insert_self a s) (phi0 k))
      refine ⟨phi0 ∘ phi1, hphi0.comp hphi1, ?_, fun i hi => ?_⟩
      · intro j
        exact le_trans (hphi1.le_apply (x := j)) (hid0 (phi1 j))
      rcases Finset.mem_insert.mp hi with rfl | his
      · refine ⟨Jinf, Jbarinf, hJinf, hJbarinf, ?_, ?_, hleft, hright⟩
        · have hfun : (fun k =>
              (d.subseq phi0 hid0).chartTransition (phi1 k)
                (x i (phi0 (phi1 k))) (y i (phi0 (phi1 k)))) =
              fun k => d.chartTransition (phi0 (phi1 k))
                (x i (phi0 (phi1 k))) (y i (phi0 (phi1 k))) := by
            funext k
            exact subseq_chartTransition d phi0 hid0 (phi1 k)
              (x i (phi0 (phi1 k))) (y i (phi0 (phi1 k)))
          simpa only [hfun, Function.comp_apply] using hJ
        · have hfun : (fun k =>
              (d.subseq phi0 hid0).chartTransition (phi1 k)
                (y i (phi0 (phi1 k))) (x i (phi0 (phi1 k)))) =
              fun k => d.chartTransition (phi0 (phi1 k))
                (y i (phi0 (phi1 k))) (x i (phi0 (phi1 k))) := by
            funext k
            exact subseq_chartTransition d phi0 hid0 (phi1 k)
              (y i (phi0 (phi1 k))) (x i (phi0 (phi1 k)))
          simpa only [hfun, Function.comp_apply] using hJbar
      · obtain ⟨Jprev, Jbarprev, hJprev, hJbarprev, hconv, hconvbar,
            hleftprev, hrightprev⟩ := hprev i his
        refine ⟨Jprev, Jbarprev, hJprev, hJbarprev, ?_, ?_,
          hleftprev, hrightprev⟩
        · simpa only [Function.comp_apply] using hconv.comp_subseq hphi1
        · simpa only [Function.comp_apply] using hconvbar.comp_subseq hphi1

theorem exists_transition_limit_subsequence_fin_of_tail
    {ι : Type*} (s : Finset ι)
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    (n N : Nat)
    (x y : ι → ∀ k : Nat, (X.obj k).M)
    (U V Ua Va : ι → Set E)
    (hU : ∀ i, i ∈ s → IsOpen (U i))
    (hV : ∀ i, i ∈ s → IsOpen (V i))
    (hUa : ∀ i, i ∈ s → IsOpen (Ua i))
    (hVa : ∀ i, i ∈ s → IsOpen (Va i))
    (hUanorm : ∀ i, i ∈ s → ∃ Z : Real, ∀ z ∈ Ua i, ‖z‖ ≤ Z)
    (hVanorm : ∀ i, i ∈ s → ∃ Z : Real, ∀ z ∈ Va i, ‖z‖ ≤ Z)
    (hxdist : ∀ i, i ∈ s → ∀ k, N ≤ k →
      hd.dist k (x i k) (X.obj k).basepoint ≤ (n : Real))
    (hydist : ∀ i, i ∈ s → ∀ k, N ≤ k →
      hd.dist k (y i k) (X.obj k).basepoint ≤ (n : Real))
    (hUarad : ∀ i, i ∈ s → ∀ k,
      Ua i ⊆ Metric.ball (0 : E)
        (d.ratio * hd.mu (hd.dist k (x i k) (X.obj k).basepoint)))
    (hVarad : ∀ i, i ∈ s → ∀ k,
      Va i ⊆ Metric.ball (0 : E)
        (d.ratio * hd.mu (hd.dist k (y i k) (X.obj k).basepoint)))
    (hovlJ : ∀ i, i ∈ s → ∀ k, d.chartOverlapOn k (x i k) (y i k) (U i))
    (hovlJbar : ∀ i, i ∈ s → ∀ k, d.chartOverlapOn k (y i k) (x i k) (V i))
    (hmapJ : ∀ i, i ∈ s → ∀ k, Set.MapsTo
      (d.chartTransition k (x i k) (y i k)) (U i) (Va i))
    (hmapJbar : ∀ i, i ∈ s → ∀ k, Set.MapsTo
      (d.chartTransition k (y i k) (x i k)) (V i) (Ua i)) :
    ∃ phi : Nat → Nat, StrictMono phi ∧ (∀ j : Nat, j ≤ phi j) ∧
      ∀ i, i ∈ s → ∃ Jinf : E → E, ∃ Jbarinf : E → E,
        ContDiffOn Real (⊤ : ℕ∞) Jinf (U i) ∧
        ContDiffOn Real (⊤ : ℕ∞) Jbarinf (V i) ∧
        MapCInfConvergenceOnCompacts (U i)
          (fun k => d.chartTransition (phi k)
            (x i (phi k)) (y i (phi k))) Jinf ∧
        MapCInfConvergenceOnCompacts (V i)
          (fun k => d.chartTransition (phi k)
            (y i (phi k)) (x i (phi k))) Jbarinf ∧
        (∀ z ∈ U i, Jinf z ∈ V i → Jbarinf (Jinf z) = z) ∧
        (∀ z ∈ V i, Jbarinf z ∈ U i → Jinf (Jbarinf z) = z) := by
  classical
  obtain ⟨phi', hphi', hid', hlim'⟩ :=
    exists_transition_limit_subsequence_fin (s := s)
      (d.subseq (fun k => k + N) fun j => Nat.le_add_right j N)
      (hreal.subseq fun k => k + N) n
      (fun i k => x i (k + N)) (fun i k => y i (k + N)) U V Ua Va
      hU hV hUa hVa hUanorm hVanorm
      (fun i hi k => by
        with_unfolding_all
          exact hxdist i hi (k + N) (Nat.le_add_left N k))
      (fun i hi k => by
        with_unfolding_all
          exact hydist i hi (k + N) (Nat.le_add_left N k))
      (fun i hi k => by
        with_unfolding_all
          exact hUarad i hi (k + N))
      (fun i hi k => by
        with_unfolding_all
          exact hVarad i hi (k + N))
      (fun i hi k => by
        with_unfolding_all
          exact hovlJ i hi (k + N))
      (fun i hi k => by
        with_unfolding_all
          exact hovlJbar i hi (k + N))
      (fun i hi k => by
        with_unfolding_all
          exact hmapJ i hi (k + N))
      (fun i hi k => by
        with_unfolding_all
          exact hmapJbar i hi (k + N))
  refine ⟨fun k => phi' k + N,
    fun a b hab => Nat.add_lt_add_right (hphi' hab) N, ?_, fun i hi => ?_⟩
  · intro j
    exact le_trans (hid' j) (Nat.le_add_right (phi' j) N)
  obtain ⟨Jinf, Jbarinf, hJinf, hJbarinf, hJ, hJbar, hleft, hright⟩ :=
    hlim' i hi
  refine ⟨Jinf, Jbarinf, hJinf, hJbarinf, ?_, ?_, hleft, hright⟩
  · have hfun : (fun k =>
        (d.subseq (fun k => k + N) fun j => Nat.le_add_right j N).chartTransition
          (phi' k) (x i (phi' k + N)) (y i (phi' k + N))) =
        fun k => d.chartTransition (phi' k + N)
          (x i (phi' k + N)) (y i (phi' k + N)) := by
      funext k
      exact subseq_chartTransition d (fun k => k + N)
        (fun j => Nat.le_add_right j N) (phi' k)
        (x i (phi' k + N)) (y i (phi' k + N))
    simpa only [hfun] using hJ
  · have hfun : (fun k =>
        (d.subseq (fun k => k + N) fun j => Nat.le_add_right j N).chartTransition
          (phi' k) (y i (phi' k + N)) (x i (phi' k + N))) =
        fun k => d.chartTransition (phi' k + N)
          (y i (phi' k + N)) (x i (phi' k + N)) := by
      funext k
      exact subseq_chartTransition d (fun k => k + N)
        (fun j => Nat.le_add_right j N) (phi' k)
        (y i (phi' k + N)) (x i (phi' k + N))
    simpa only [hfun] using hJbar

theorem stage_root_tail
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (d : SeqBallNormalChartData (I := I) X inp.decay)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
    (aMin : Real) (haMin : 0 < aMin)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSupportedCenterMapConvergenceOn (I := I) inp P L r hr phi hphi d.chart
      U C0 C1 aInf Jinf Jbarinf)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L inp.pack r → NNReal)
    (δ : LiveSlot L inp.pack r → Real)
    (hqdata : ∀ gamma : LiveSlot L inp.pack r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * inp.decay.mu Rgamma
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real) ∧
        6 * (q gamma : Real) < d.phaseRadius Rgamma ∧
        3 * CB 1 * (2 * (q gamma : Real)) ^ 2 ≤
          (2 / 3 : Real) * (q gamma : Real) ∧
        PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)) <
          ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊⁻¹ ∧
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊ *
            (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
              PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)))⁻¹ *
            PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)) < 1 / 24)
    (hbranch : ∀ᶠ n in Filter.atTop,
      ∀ gamma : LiveSlot L inp.pack r,
        let Rgamma := L.rInf (gamma.1 : Nat) + 1
        let rho := aMin * inp.decay.mu Rgamma
        let x0 := seqCenterD inp.decay P (L.subseq hphi) n
          (gamma.1 : Nat)
        letI : TopologicalSpace (X.obj ((L.subseq hphi).φ n)).M :=
          (X.obj ((L.subseq hphi).φ n)).topology
        letI : ChartedSpace H (X.obj ((L.subseq hphi).φ n)).M :=
          (X.obj ((L.subseq hphi).φ n)).charted
        letI : IsManifold I ∞ (X.obj ((L.subseq hphi).φ n)).M :=
          (X.obj ((L.subseq hphi).φ n)).smooth
        letI : T2Space
            (TangentBundle I (X.obj ((L.subseq hphi).φ n)).M) :=
          (X.obj ((L.subseq hphi).φ n)).t2TangentBundle
        ∃ e : OpenPartialHomeomorph (E × E) (E × E),
          IsNormalDiag (I := I) (X.obj ((L.subseq hphi).φ n))
              (hcomplete.complete ((L.subseq hphi).φ n))
              (hconn ((L.subseq hphi).φ n))
              x0 (q gamma) (δ gamma) e
              (c := d.chart ((L.subseq hphi).φ n) x0) ∧
            NormalDiagFence (I := I) (X.obj ((L.subseq hphi).φ n))
              x0 (q gamma) e
                (c := d.chart ((L.subseq hphi).φ n) x0) ∧
            ApproximatesLinearOn
              (e.symm : E × E → E × E)
              ((PhaseFlow.freeDiagCLE (E := E)).symm :
                (E × E) →L[Real] (E × E))
              e.target
              (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                  (E × E) →L[Real] (E × E))‖₊ *
                (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                    (E × E) →L[Real] (E × E))‖₊⁻¹ -
                  PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)))⁻¹ *
                PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma))) ∧
            rho ≤ (d.chart ((L.subseq hphi).φ n) x0).radius / 4)
    (alpha : LiveSlot L inp.pack r)
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (hdiag :
      let Lphi := L.subseq hphi
      ∀ n, IsNormalDiag (I := I) (X.obj (Lphi.φ n))
        (hcomplete.complete (Lphi.φ n)) (hconn (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (δ alpha) (e n)
        (c := d.chart (Lphi.φ n)
          (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))))
    (hfence :
      let Lphi := L.subseq hphi
      ∀ n, NormalDiagFence (I := I) (X.obj (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (e n)
        (c := d.chart (Lphi.φ n)
          (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))))
    (W : Set E) (PhiInf : E → E) (rootRho : Real)
    (Phi3 : Nat → Nat → Nat → E → E)
    (hroot : HasStageRootCube inp P L hr phi hphi C1 alpha e
      W PhiInf rootRho Phi3 (chart := d.chart)) :
    HasStageRootChartEquation inp P L hr phi hphi C0 alpha Phi3
      (chart := d.chart) := by
  simpa only [toBoundedGeometryNormalChartData_chart] using
  BoundedGeometryNormalChartData.stage_root_tail inp
    (d.toBoundedGeometryNormalChartData CB hCB hunif)
    aMin haMin hphys P L hstable hr phi hphi U C0 C1 aInf Jinf Jbarinf
    hdata hcomplete hconn q δ
    (fun gamma => by
      simpa only [toBoundedGeometryNormalChartData_metricC,
        toBoundedGeometryNormalChartData_phaseRadius,
        toBoundedGeometryNormalChartData_phaseK] using hqdata gamma)
    hbranch alpha e hdiag hfence W PhiInf rootRho Phi3 hroot

theorem stage_jet_tail
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (d : SeqBallNormalChartData (I := I) X inp.decay)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
    (aMin : Real) (haMin : 0 < aMin)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSupportedCenterMapConvergenceOn (I := I) inp P L r hr phi hphi d.chart
      U C0 C1 aInf Jinf Jbarinf)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L inp.pack r → NNReal)
    (δ : LiveSlot L inp.pack r → Real)
    (hqdata : ∀ gamma : LiveSlot L inp.pack r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * inp.decay.mu Rgamma
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real) ∧
        6 * (q gamma : Real) < d.phaseRadius Rgamma ∧
        3 * CB 1 * (2 * (q gamma : Real)) ^ 2 ≤
          (2 / 3 : Real) * (q gamma : Real) ∧
        PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)) <
          ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊⁻¹ ∧
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊ *
            (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
              PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)))⁻¹ *
            PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)) < 1 / 24)
    (hbranch : ∀ᶠ n in Filter.atTop,
      ∀ gamma : LiveSlot L inp.pack r,
        let Rgamma := L.rInf (gamma.1 : Nat) + 1
        let rho := aMin * inp.decay.mu Rgamma
        let x0 := seqCenterD inp.decay P (L.subseq hphi) n
          (gamma.1 : Nat)
        letI : TopologicalSpace (X.obj ((L.subseq hphi).φ n)).M :=
          (X.obj ((L.subseq hphi).φ n)).topology
        letI : ChartedSpace H (X.obj ((L.subseq hphi).φ n)).M :=
          (X.obj ((L.subseq hphi).φ n)).charted
        letI : IsManifold I ∞ (X.obj ((L.subseq hphi).φ n)).M :=
          (X.obj ((L.subseq hphi).φ n)).smooth
        letI : T2Space
            (TangentBundle I (X.obj ((L.subseq hphi).φ n)).M) :=
          (X.obj ((L.subseq hphi).φ n)).t2TangentBundle
        ∃ e : OpenPartialHomeomorph (E × E) (E × E),
          IsNormalDiag (I := I) (X.obj ((L.subseq hphi).φ n))
              (hcomplete.complete ((L.subseq hphi).φ n))
              (hconn ((L.subseq hphi).φ n))
              x0 (q gamma) (δ gamma) e
              (c := d.chart ((L.subseq hphi).φ n) x0) ∧
            NormalDiagFence (I := I) (X.obj ((L.subseq hphi).φ n))
              x0 (q gamma) e
                (c := d.chart ((L.subseq hphi).φ n) x0) ∧
            ApproximatesLinearOn
              (e.symm : E × E → E × E)
              ((PhaseFlow.freeDiagCLE (E := E)).symm :
                (E × E) →L[Real] (E × E))
              e.target
              (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                  (E × E) →L[Real] (E × E))‖₊ *
                (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                    (E × E) →L[Real] (E × E))‖₊⁻¹ -
                  PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)))⁻¹ *
                PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma))) ∧
            rho ≤ (d.chart ((L.subseq hphi).φ n) x0).radius / 4)
    (e : (alpha : LiveSlot L inp.pack r) →
      Nat → OpenPartialHomeomorph (E × E) (E × E))
    (hdiag : ∀ alpha,
      let Lphi := L.subseq hphi
      ∀ n, IsNormalDiag (I := I) (X.obj (Lphi.φ n))
        (hcomplete.complete (Lphi.φ n)) (hconn (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (δ alpha) (e alpha n)
        (c := d.chart (Lphi.φ n)
          (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))))
    (hfence : ∀ alpha,
      let Lphi := L.subseq hphi
      ∀ n, NormalDiagFence (I := I) (X.obj (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (e alpha n)
        (c := d.chart (Lphi.φ n)
          (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))))
    (W : LiveSlot L inp.pack r → Set E)
    (PhiInf : LiveSlot L inp.pack r → E → E)
    (rootRho : LiveSlot L inp.pack r → Real)
    (Phi3 : LiveSlot L inp.pack r → Nat → Nat → Nat → E → E)
    (hroot : ∀ alpha, HasStageRootCube inp P L hr phi hphi C1 alpha
      (e alpha) (W alpha) (PhiInf alpha) (rootRho alpha) (Phi3 alpha)
      (chart := d.chart))
    (R : Real) (hRr : R < r)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    HasStageJetTail inp P L hr phi hphi C0 R p eps
      (chart := d.chart) := by
  simpa only [toBoundedGeometryNormalChartData_chart] using
  BoundedGeometryNormalChartData.stage_jet_tail inp
    (d.toBoundedGeometryNormalChartData CB hCB hunif)
    aMin haMin hphys P L hstable hr phi hphi U C0 C1 aInf Jinf Jbarinf
    hdata hcomplete hconn q δ
    (fun gamma => by
      simpa only [toBoundedGeometryNormalChartData_metricC,
        toBoundedGeometryNormalChartData_phaseRadius,
        toBoundedGeometryNormalChartData_phaseK] using hqdata gamma)
    hbranch e hdiag hfence W PhiInf rootRho Phi3 hroot R hRr p eps heps

theorem stage_jet_convergence_of_supported_center_maps_and_metrics
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (d : SeqBallNormalChartData (I := I) X inp.decay)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
    (aMin : Real) (haMin : 0 < aMin)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (hratio : 48 * aMin < d.ratio)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (V U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hV : ∀ alpha, V alpha =
      Metric.ball 0 (d.phaseRadius (L.rInf (alpha.1 : Nat) + 1)))
    (hdata : HasSupportedCenterMapConvergenceOn (I := I) inp P L r hr phi hphi d.chart
      U C0 C1 aInf Jinf Jbarinf)
    (hmetric : HasStageMetricOn inp P L phi hphi d.chart V C1 gInf)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hbase : HasStageBaseTail inp P L hr phi hphi
      (chart := d.chart))
    (hcenter : ∀ n (alpha : LiveSlot L inp.pack r),
      inp.decay.dist ((L.subseq hphi).φ n)
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
        (X.obj ((L.subseq hphi).φ n)).basepoint ≤
          L.rInf (alpha.1 : Nat) + 1)
    (q : LiveSlot L inp.pack r → NNReal)
    (hqdata : ∀ gamma : LiveSlot L inp.pack r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * inp.decay.mu Rgamma
      0 < q gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real) ∧
        6 * (q gamma : Real) < d.phaseRadius Rgamma ∧
        3 * CB 1 * (2 * (q gamma : Real)) ^ 2 ≤
          (2 / 3 : Real) * (q gamma : Real) ∧
        PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)) <
          ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊⁻¹ ∧
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊ *
            (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                (E × E) →L[Real] (E × E))‖₊⁻¹ -
              PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)))⁻¹ *
            PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)) < 1 / 24) :
    HasStageJetConvergenceOn (I := I) inp P L hr phi hphi d.chart
      V U C0 C1 aInf Jinf Jbarinf gInf := by
  simpa only [toBoundedGeometryNormalChartData_chart] using
  BoundedGeometryNormalChartData.stage_jet_convergence_of_supported_center_maps_and_metrics
    inp (d.toBoundedGeometryNormalChartData CB hCB hunif)
    aMin haMin hphys hratio P L hstable hr phi hphi V U C0 C1 aInf Jinf Jbarinf gInf
    hV hdata hmetric hcomplete hconn hbase hcenter q
    (fun gamma => by
      simpa only [toBoundedGeometryNormalChartData_metricC,
        toBoundedGeometryNormalChartData_phaseRadius,
        toBoundedGeometryNormalChartData_phaseK] using hqdata gamma)

theorem points_target_tail
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (d : SeqBallNormalChartData (I := I) X inp.decay)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
    (aMin : Real) (haMin : 0 < aMin)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSupportedCenterMapConvergenceOn (I := I) inp P L r hr phi hphi d.chart
      U C0 C1 aInf Jinf Jbarinf)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L inp.pack r → NNReal)
    (δ : LiveSlot L inp.pack r → Real)
    (hqdata : ∀ gamma : LiveSlot L inp.pack r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * inp.decay.mu Rgamma
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real) ∧
        6 * (q gamma : Real) < d.phaseRadius Rgamma ∧
        3 * CB 1 * (2 * (q gamma : Real)) ^ 2 ≤
          (2 / 3 : Real) * (q gamma : Real) ∧
        PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)) <
          ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊⁻¹ ∧
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊ *
            (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
              PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)))⁻¹ *
            PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)) < 1 / 24) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
      ∀ (alpha : LiveSlot L inp.pack r) (z : E), z ∈ U alpha →
        ∀ gamma : Fin (inp.pack.A r),
          stageWeightSub inp P L hr phi hphi alpha k z gamma
              (chart := d.chart) ≠ 0 →
            let Lphi := L.subseq hphi
            let Yk := X.obj (Lphi.φ k)
            let Yl := X.obj (Lphi.φ l)
            letI : TopologicalSpace Yk.M := Yk.topology
            letI : ChartedSpace H Yk.M := Yk.charted
            letI : IsManifold I ∞ Yk.M := Yk.smooth
            letI : T2Space Yk.M := Yk.t2
            letI : T2Space (TangentBundle I Yk.M) :=
              Yk.t2TangentBundle
            letI : TopologicalSpace Yl.M := Yl.topology
            letI : ChartedSpace H Yl.M := Yl.charted
            letI : IsManifold I ∞ Yl.M := Yl.smooth
            letI : T2Space Yl.M := Yl.t2
            letI : T2Space (TangentBundle I Yl.M) :=
              Yl.t2TangentBundle
            (d.chart (Lphi.φ l)
                (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))).hom
                (stagePointsSub inp P L phi hphi alpha k l z gamma
                  (chart := d.chart)) =
              stageTarget inp P Lphi r k l
                ((d.chart (Lphi.φ k)
                  (seqCenterD inp.decay P Lphi k
                    (alpha.1 : Nat))).hom z)
                gamma (chart := d.chart) ∧
            (d.chart (Lphi.φ l)
                (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))).inv
                (stageTarget inp P Lphi r k l
                  ((d.chart (Lphi.φ k)
                    (seqCenterD inp.decay P Lphi k
                      (alpha.1 : Nat))).hom z)
                  gamma (chart := d.chart)) =
              stagePointsSub inp P L phi hphi alpha k l z gamma
                (chart := d.chart) := by
  simpa only [toBoundedGeometryNormalChartData_chart] using
  BoundedGeometryNormalChartData.points_target_tail inp
    (d.toBoundedGeometryNormalChartData CB hCB hunif)
    aMin haMin hphys P L hstable hr phi hphi U C0 C1 aInf Jinf Jbarinf
    hdata hcomplete hconn q δ
    (fun gamma => by
      simpa only [toBoundedGeometryNormalChartData_metricC,
        toBoundedGeometryNormalChartData_phaseRadius,
        toBoundedGeometryNormalChartData_phaseK] using hqdata gamma)

theorem actual_cm_tail
    (inp : MetricCompactSeedWithDivisor (I := I) X)
    (d : SeqBallNormalChartData (I := I) X inp.decay)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
    (aMin : Real) (haMin : 0 < aMin)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSupportedCenterMapConvergenceOn (I := I) inp P L r hr phi hphi d.chart
      U C0 C1 aInf Jinf Jbarinf)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L inp.pack r → NNReal)
    (δ : LiveSlot L inp.pack r → Real)
    (hqdata : ∀ gamma : LiveSlot L inp.pack r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * inp.decay.mu Rgamma
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real) ∧
        6 * (q gamma : Real) < d.phaseRadius Rgamma ∧
        3 * CB 1 * (2 * (q gamma : Real)) ^ 2 ≤
          (2 / 3 : Real) * (q gamma : Real) ∧
        PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)) <
          ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊⁻¹ ∧
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊ *
            (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
              PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)))⁻¹ *
            PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)) < 1 / 24)
    (hbranch : ∀ᶠ n in Filter.atTop,
      ∀ gamma : LiveSlot L inp.pack r,
        let Rgamma := L.rInf (gamma.1 : Nat) + 1
        let rho := aMin * inp.decay.mu Rgamma
        let x0 := seqCenterD inp.decay P (L.subseq hphi) n
          (gamma.1 : Nat)
        letI : TopologicalSpace (X.obj ((L.subseq hphi).φ n)).M :=
          (X.obj ((L.subseq hphi).φ n)).topology
        letI : ChartedSpace H (X.obj ((L.subseq hphi).φ n)).M :=
          (X.obj ((L.subseq hphi).φ n)).charted
        letI : IsManifold I ∞ (X.obj ((L.subseq hphi).φ n)).M :=
          (X.obj ((L.subseq hphi).φ n)).smooth
        letI : T2Space
            (TangentBundle I (X.obj ((L.subseq hphi).φ n)).M) :=
          (X.obj ((L.subseq hphi).φ n)).t2TangentBundle
        ∃ e : OpenPartialHomeomorph (E × E) (E × E),
          IsNormalDiag (I := I) (X.obj ((L.subseq hphi).φ n))
              (hcomplete.complete ((L.subseq hphi).φ n))
              (hconn ((L.subseq hphi).φ n))
              x0 (q gamma) (δ gamma) e
              (c := d.chart ((L.subseq hphi).φ n) x0) ∧
            NormalDiagFence (I := I) (X.obj ((L.subseq hphi).φ n))
              x0 (q gamma) e
                (c := d.chart ((L.subseq hphi).φ n) x0) ∧
            ApproximatesLinearOn
              (e.symm : E × E → E × E)
              ((PhaseFlow.freeDiagCLE (E := E)).symm :
                (E × E) →L[Real] (E × E))
              e.target
              (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                  (E × E) →L[Real] (E × E))‖₊ *
                (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                    (E × E) →L[Real] (E × E))‖₊⁻¹ -
                  PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)))⁻¹ *
                PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma))) ∧
            rho ≤ (d.chart ((L.subseq hphi).φ n) x0).radius / 4)
    (alpha : LiveSlot L inp.pack r)
    (eps : Real) (heps : 0 < eps) :
    ∃ rad : Real, 0 < rad ∧ rad < eps ∧
      ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
        let Lphi := L.subseq hphi
        let Yl := X.obj (Lphi.φ l)
        letI : TopologicalSpace Yl.M := Yl.topology
        letI : ChartedSpace H Yl.M := Yl.charted
        letI : IsManifold I ∞ Yl.M := Yl.smooth
        letI : IsManifold I 1 Yl.M := IsManifold.of_le
          (I := I) (M := Yl.M) (n := ∞) (by decide)
        letI : SigmaCompactSpace Yl.M := Yl.sigmaCompact
        letI : T2Space Yl.M := Yl.t2
        letI : ConnectedSpace Yl.M := hconn (Lphi.φ l)
        letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
        letI : TopologicalSpace.MetrizableSpace Yl.M :=
          Manifold.metrizableSpace I Yl.M
        letI : T3Space Yl.M := inferInstance
        letI : RiemannianBundle (fun y : Yl.M ↦ TangentSpace I y) :=
          Yl.riemBundle (I := I)
        letI : (y : Yl.M) → InnerProductSpace Real (TangentSpace I y) :=
          Yl.riemInner (I := I)
        letI : IsContinuousRiemannianBundle E
            (fun y : Yl.M ↦ TangentSpace I y) := Yl.riemBundle_cont (I := I)
        letI : EMetricSpace Yl.M := Yl.emetricSpace (I := I)
        letI : CompleteSpace Yl.M :=
          MetricComplete.complete (I := I) Yl
            (hcomplete.complete (Lphi.φ l))
        letI : MetricSpace Yl.M :=
          HopfRinow.riemMetricSpace (I := I) (M := Yl.M)
        let x0 := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
        let chiL := d.chart (Lphi.φ l) x0
        let mu := stageWeightSub inp P L hr phi hphi alpha k
          (chart := d.chart)
        let stagePoints := fun w gamma =>
          chiL.hom (stagePointsSub inp P L phi hphi alpha k l w gamma
            (chart := d.chart))
        let qstar := chiL.hom
        let join := minJoin (I := I) Yl.metric (normal_enorm (I := I) Yl)
        let p := qstar z
        let points := centerAverage.activeFill mu stagePoints qstar z
        ∃ hcm : CenterOfMassConditions (I := I) Yl.metric (mu z) points join p rad,
          HasLiveChartCenterSolution (I := I)
            (d.toBoundedGeometryNormalChartData CB hCB hunif) P L inp.pack r (phi l) hcomplete hconn
            q δ alpha (mu z) points join p rad hcm ∧
          dist
              (chiL.inv (centerOfMass (I := I) Yl.metric (mu z)
                points join p rad hcm))
              z ≤ 4 * rad := by
  simpa only [toBoundedGeometryNormalChartData_chart] using
  BoundedGeometryNormalChartData.actual_cm_tail inp
    (d.toBoundedGeometryNormalChartData CB hCB hunif)
    aMin haMin hphys P L hr phi hphi U C0 C1 aInf Jinf Jbarinf
    hdata hcomplete hconn q δ
    (fun gamma => by
      simpa only [toBoundedGeometryNormalChartData_metricC,
        toBoundedGeometryNormalChartData_phaseRadius,
        toBoundedGeometryNormalChartData_phaseK] using hqdata gamma)
    hbranch alpha eps heps
end SeqBallNormalChartData

end CheegerGromovCompactness
end DifferentialGeometry
