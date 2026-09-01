import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.ScaleSelection



import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.StrictConvexity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.ChartCenterSolution
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.UniformData

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff Manifold NNReal Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

def HasLiveChartCenterSolution
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) {D : Real}
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L pb r → NNReal) (δ : LiveSlot L pb r → Real)
    (alpha : LiveSlot L pb r)
    (mu : Fin (pb.A r) → Real)
    (pts : Fin (pb.A r) → (X.obj (L.φ n)).M)
    (join : (X.obj (L.φ n)).M → (X.obj (L.φ n)).M → Real →
      (X.obj (L.φ n)).M)
    (x : (X.obj (L.φ n)).M) (rad : Real)
    (hcm :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
        (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
        (X.obj (L.φ n)).riemBundle (I := I)
      letI : (z : (X.obj (L.φ n)).M) →
          InnerProductSpace Real (TangentSpace I z) :=
        (X.obj (L.φ n)).riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
        (X.obj (L.φ n)).riemBundle_cont (I := I)
      letI : EMetricSpace (X.obj (L.φ n)).M :=
        (X.obj (L.φ n)).emetricSpace (I := I)
      letI : CompleteSpace (X.obj (L.φ n)).M :=
        MetricComplete.complete (I := I) (X.obj (L.φ n))
          (hcomplete.complete (L.φ n))
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      CenterInput (I := I) (X.obj (L.φ n)).metric mu pts join x rad) : Prop :=
  HasChartCmSol (I := I) (X.obj (L.φ n))
    (hcomplete.complete (L.φ n)) (hconn (L.φ n))
    (seqCenterD hd P L n (alpha.1 : Nat))
    (d.chart (L.φ n) (seqCenterD hd P L n (alpha.1 : Nat)))
    (q := q alpha) (delta := δ alpha) mu pts join x rad hcm

namespace BoundedGeometryNormalChartData

theorem has_live_chart_center_solution_of_cage
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) {D aMin : Real}
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (hre : hd.RealizesDistance) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L pb r → NNReal) (δ : LiveSlot L pb r → Real)
    (hqdata : ∀ gamma : LiveSlot L pb r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * hd.mu Rgamma
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real) ∧
        6 * (q gamma : Real) < d.phaseRadius Rgamma ∧
        3 * d.metricC 1 * (2 * (q gamma : Real)) ^ 2 ≤
          (2 / 3 : Real) * (q gamma : Real) ∧
        PhaseFlow.phaseErr (d.phaseK (2 * q gamma)) <
          ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊⁻¹ ∧
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊ *
            (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
              PhaseFlow.phaseErr (d.phaseK (2 * q gamma)))⁻¹ *
            PhaseFlow.phaseErr (d.phaseK (2 * q gamma)) < 1 / 24)
    (hbranch : ∀ gamma : LiveSlot L pb r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * hd.mu Rgamma
      let x0 := seqCenterD hd P L k (gamma.1 : Nat)
      letI : TopologicalSpace (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M :=
        (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      ∃ e : OpenPartialHomeomorph (E × E) (E × E),
        IsNormalDiag (I := I) (X.obj (L.φ k))
            (hcomplete.complete (L.φ k)) (hconn (L.φ k))
            x0 (q gamma) (δ gamma) e (c := d.chart (L.φ k) x0) ∧
          NormalDiagFence (I := I) (X.obj (L.φ k))
            x0 (q gamma) e (c := d.chart (L.φ k) x0) ∧
          ApproximatesLinearOn
            (e.symm : E × E → E × E)
            ((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))
            e.target
            (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                (E × E) →L[Real] (E × E))‖₊ *
              (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
                  (E × E) →L[Real] (E × E))‖₊⁻¹ -
                PhaseFlow.phaseErr (d.phaseK (2 * q gamma)))⁻¹ *
              PhaseFlow.phaseErr (d.phaseK (2 * q gamma))) ∧
          rho ≤ (d.chart (L.φ k) x0).radius / 4)
    (alpha : LiveSlot L pb r) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : IsManifold I 1 (X.obj (L.φ k)).M := IsManifold.of_le
      (I := I) (M := (X.obj (L.φ k)).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : ConnectedSpace (X.obj (L.φ k)).M := hconn (L.φ k)
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ k)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ k)).M
    letI : T3Space (X.obj (L.φ k)).M := inferInstance
    letI : RiemannianBundle
        (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
      (X.obj (L.φ k)).riemBundle (I := I)
    letI : (z : (X.obj (L.φ k)).M) →
        InnerProductSpace Real (TangentSpace I z) :=
      (X.obj (L.φ k)).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
      (X.obj (L.φ k)).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj (L.φ k)).M :=
      (X.obj (L.φ k)).emetricSpace (I := I)
    letI : CompleteSpace (X.obj (L.φ k)).M :=
      MetricComplete.complete (I := I) (X.obj (L.φ k))
        (hcomplete.complete (L.φ k))
    letI : MetricSpace (X.obj (L.φ k)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ k)).M)
    ∀ (mu : Fin (pb.A r) → Real)
        (pts : Fin (pb.A r) → (X.obj (L.φ k)).M)
        (join : (X.obj (L.φ k)).M → (X.obj (L.φ k)).M → Real →
          (X.obj (L.φ k)).M)
        (x : (X.obj (L.φ k)).M) (rad : Real),
      ∀ h : CenterInput (I := I) (X.obj (L.φ k)).metric
          mu pts join x rad,
        ∑ i, mu i = 1 →
        x ∈ NetLimitData.hatBall (I := I) (X := X)
          hd D P L pb r k alpha.1 →
        ENNReal.ofReal
            (4 * L.lamInf (alpha.1 : Nat) + 2 * rad) <
          ENNReal.ofReal
            ((aMin * hd.mu (L.rInf (alpha.1 : Nat) + 1)) / 2) →
        HasLiveChartCenterSolution (I := I) d P L pb r k hcomplete hconn q δ alpha
          mu pts join x rad h := by
  classical
  let : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  let : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  let : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  let : IsManifold I 1 (X.obj (L.φ k)).M := IsManifold.of_le
    (I := I) (M := (X.obj (L.φ k)).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).sigmaCompact
  let : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  let : ConnectedSpace (X.obj (L.φ k)).M := hconn (L.φ k)
  let : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj (L.φ k)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ k)).M
  let : T3Space (X.obj (L.φ k)).M := inferInstance
  let : RiemannianBundle
      (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ k)).riemBundle (I := I)
  let : (z : (X.obj (L.φ k)).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj (L.φ k)).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : (X.obj (L.φ k)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ k)).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj (L.φ k)).M :=
    (X.obj (L.φ k)).emetricSpace (I := I)
  let : CompleteSpace (X.obj (L.φ k)).M :=
    MetricComplete.complete (I := I) (X.obj (L.φ k))
      (hcomplete.complete (L.φ k))
  let : MetricSpace (X.obj (L.φ k)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ k)).M)
  intro mu pts join x rad h hsum hxhat hradCage
  let x0 := seqCenterD hd P L k (alpha.1 : Nat)
  let rho0 := aMin * hd.mu (L.rInf (alpha.1 : Nat) + 1)
  rcases hqdata alpha with
    ⟨hq, _hδ, hρ, hρq, _hqWide, _hqAcc, _herr, hinvErr⟩
  rcases hbranch alpha with ⟨e, he, hf, happrox, hρInner⟩
  have hproper :
      (letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
       dist x x0) < 4 * L.lamInf (alpha.1 : Nat) := by
    simpa only [x0] using hat_dist_centerD hd P L pb r hxhat
  have hhd : hd.dist (L.φ k) x x0 <
      4 * L.lamInf (alpha.1 : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ k) x x0]
    exact hproper
  have hed : riemannianEDist I x x0 =
      ENNReal.ofReal (hd.dist (L.φ k) x x0) := by
    have : IsRiemannianManifold I (X.obj (L.φ k)).M :=
      ⟨fun _ _ => rfl⟩
    have hrealize := hre.edist_eq (L.φ k) x x0
    rw [← IsRiemannianManifold.out (I := I) x x0]
    exact hrealize
  have hpq : dist x0 x ≤ 4 * L.lamInf (alpha.1 : Nat) := by
    rw [dist_comm, HopfRinow.riemMetric_dist_eq, hed,
      ENNReal.toReal_ofReal (hre.dist_nonneg (L.φ k) x x0)]
    exact hhd.le
  let y := centerOfMass (I := I) (X.obj (L.φ k)).metric
    mu pts join x rad h
  have hyMem : y ∈ Metric.closedBall x (2 * rad) := by
    simpa only [y] using centerOfMass.mem (I := I) h
  have hyDist : dist x0 y ≤
      4 * L.lamInf (alpha.1 : Nat) + 2 * rad := by
    calc
      dist x0 y ≤ dist x0 x + dist x y := dist_triangle _ _ _
      _ ≤ 4 * L.lamInf (alpha.1 : Nat) + 2 * rad := by
        have hxy : dist x y ≤ 2 * rad := by
          simpa only [dist_comm] using Metric.mem_closedBall.mp hyMem
        linarith
  have hptDist (i : Fin (pb.A r)) : dist x0 (pts i) <
      4 * L.lamInf (alpha.1 : Nat) + 2 * rad := by
    calc
      dist x0 (pts i) ≤ dist x0 x + dist x (pts i) := dist_triangle _ _ _
      _ < 4 * L.lamInf (alpha.1 : Nat) + rad := by
        linarith [h.pts_mem i]
      _ < 4 * L.lamInf (alpha.1 : Nat) + 2 * rad := by
        linarith [h.r_pos]
  have hriem_eq (a b : (X.obj (L.φ k)).M) :
      riemannianEDist I a b = ENNReal.ofReal (dist a b) := by
    rw [HopfRinow.riemMetric_dist_eq]
    exact (ENNReal.ofReal_toReal
      (riemannianEDist_ne_top (I := I) a b)).symm
  have hpairs : ∀ i, max (riemannianEDist I x0 y)
        (riemannianEDist I x0 (pts i)) < ENNReal.ofReal (rho0 / 2) := by
    intro i
    rw [max_lt_iff, hriem_eq, hriem_eq]
    constructor
    · exact (ENNReal.ofReal_le_ofReal hyDist).trans_lt
        (by simpa only [rho0] using hradCage)
    · exact (ENNReal.ofReal_lt_ofReal_iff
        (by nlinarith [h.r_pos, show 0 ≤ dist x0 x from dist_nonneg])).2
          (hptDist i) |>.trans
            (by simpa only [rho0] using hradCage)
  have hρChart : rho0 ≤ (d.chart (L.φ k) x0).radius := by
    have hradius := (d.chart (L.φ k) x0).radius_pos
    exact hρInner.trans (by nlinarith)
  have hsol := d.center_of_mass_satisfies_normal_coordinate_equation
    (L.φ k) (hcomplete.complete (L.φ k))
    (hconn (L.φ k)) x0 hq he hf happrox
    (by
      exact hinvErr.trans (by norm_num)) mu pts join x rad hsum h hρ hρq
      hρChart hpairs
  exact ⟨hq, e, he, hf, by simpa only [x0, y, rho0] using hsol⟩

theorem exists_live_chart_center_solutions
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd)
    (hre : hd.RealizesDistance)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ aMin : Real, 0 < aMin ∧
      ∀ {D : Real} (hD : 0 < D)
        (hphys : 8 * Real.exp hd.C < aMin * D)
        (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
        (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real),
        ∃ q : LiveSlot L pb r → NNReal,
          ∃ δ : LiveSlot L pb r → Real,
            (∀ gamma : LiveSlot L pb r,
              let Rgamma := L.rInf (gamma.1 : Nat) + 1
              let rho := aMin * hd.mu Rgamma
              0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
                2 * rho < (q gamma : Real) ∧
                6 * (q gamma : Real) < d.phaseRadius Rgamma ∧
                3 * d.metricC 1 * (2 * (q gamma : Real)) ^ 2 ≤
                  (2 / 3 : Real) * (q gamma : Real) ∧
                PhaseFlow.phaseErr (d.phaseK (2 * q gamma)) < T ∧
                N * (T - PhaseFlow.phaseErr
                    (d.phaseK (2 * q gamma)))⁻¹ *
                    PhaseFlow.phaseErr (d.phaseK (2 * q gamma)) < 1 / 24) ∧
            ∀ᶠ n in Filter.atTop,
              letI : TopologicalSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).topology
              letI : ChartedSpace H (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).charted
              letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).smooth
              letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
                (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
              letI : SigmaCompactSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).sigmaCompact
              letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
              letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
              letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
                (X.obj (L.φ n)).t2TangentBundle
              letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
                Manifold.metrizableSpace I (X.obj (L.φ n)).M
              letI : T3Space (X.obj (L.φ n)).M := inferInstance
              letI : RiemannianBundle
                  (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
                (X.obj (L.φ n)).riemBundle (I := I)
              letI : (z : (X.obj (L.φ n)).M) →
                  InnerProductSpace Real (TangentSpace I z) :=
                (X.obj (L.φ n)).riemInner (I := I)
              letI : IsContinuousRiemannianBundle E
                  (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
                (X.obj (L.φ n)).riemBundle_cont (I := I)
              letI : EMetricSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).emetricSpace (I := I)
              letI : CompleteSpace (X.obj (L.φ n)).M :=
                MetricComplete.complete (I := I) (X.obj (L.φ n))
                  (hcomplete.complete (L.φ n))
              letI : MetricSpace (X.obj (L.φ n)).M :=
                HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
              (∀ gamma : LiveSlot L pb r,
                let Rgamma := L.rInf (gamma.1 : Nat) + 1
                let rho := aMin * hd.mu Rgamma
                let x0 := seqCenterD hd P L n (gamma.1 : Nat)
                ∃ e : OpenPartialHomeomorph (E × E) (E × E),
                  IsNormalDiag (I := I) (X.obj (L.φ n))
                      (hcomplete.complete (L.φ n)) (hconn (L.φ n))
                      x0 (q gamma) (δ gamma) e
                      (c := d.chart (L.φ n) x0) ∧
                    NormalDiagFence (I := I) (X.obj (L.φ n))
                      x0 (q gamma) e (c := d.chart (L.φ n) x0) ∧
                    ApproximatesLinearOn
                      (e.symm : E × E → E × E)
                      ((PhaseFlow.freeDiagCLE (E := E)).symm :
                        (E × E) →L[Real] (E × E))
                      e.target
                      (N * (T - PhaseFlow.phaseErr
                        (d.phaseK (2 * q gamma)))⁻¹ *
                        PhaseFlow.phaseErr (d.phaseK (2 * q gamma))) ∧
                    rho ≤ (d.chart (L.φ n) x0).radius / 4) ∧
              ∀ (alpha : LiveSlot L pb r)
                (s : Set (X.obj (L.φ n)).M)
                (hs : s ⊆ NetLimitData.hatBall (I := I) (X := X)
                  hd D P L pb r n alpha.1)
                (mu : (X.obj (L.φ n)).M → Fin (pb.A r) → Real)
                (hmu : centerAverage.WeightDataOn s
                  (fun _ : Fin (pb.A r) => Set.univ) mu)
                (ptsSeq : Nat → Nat → (X.obj (L.φ n)).M →
                  Fin (pb.A r) → (X.obj (L.φ n)).M)
                (hpts : ∀ gamma : Fin (pb.A r), ∀ epsilon : Real,
                  0 < epsilon → ∃ N : Nat,
                    ∀ a ≥ N, ∀ b ≥ N,
                      ∀ x ∈ s, mu x gamma ≠ 0 →
                        dist x (ptsSeq a b x gamma) < epsilon),
                  ∃ radSeq : Nat → Nat → (X.obj (L.φ n)).M → Real,
                    (∀ a b x, x ∈ s → 0 < radSeq a b x) ∧
                    (∀ a b x, x ∈ s → ∀ gamma, mu x gamma ≠ 0 →
                      dist x (ptsSeq a b x gamma) < radSeq a b x) ∧
                    (∀ epsilon > 0, ∃ N : Nat,
                      ∀ a ≥ N, ∀ b ≥ N,
                        ∀ x ∈ s, radSeq a b x < epsilon) ∧
                    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
                      ∀ x ∈ s,
                        let join := minJoin (I := I) (X.obj (L.φ n)).metric
                          (normal_enorm (I := I) (X.obj (L.φ n)))
                        let pts := centerAverage.activeFill mu (ptsSeq a b)
                          (fun y => y) x
                        ∃ hcm : CenterInput (I := I)
                            (X.obj (L.φ n)).metric (mu x) pts join x
                            (radSeq a b x),
                          HasLiveChartCenterSolution (I := I) d P L pb r n hcomplete hconn
                            q δ alpha (mu x) pts join x (radSeq a b x) hcm := by
  classical
  let N : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊
  let T : NNReal := N⁻¹
  obtain ⟨aMin, haMin, hmin⟩ :=
    d.exists_center_of_mass_scale hre hcomplete hconn
  refine ⟨aMin, haMin, ?_⟩
  intro D hD hphys P L pb r
  obtain ⟨q, δ, hqdata, hbranch⟩ := hmin P L pb r
  refine ⟨q, δ, ?_, ?_⟩
  · simpa only [N, T] using hqdata
  filter_upwards [hbranch] with n hn
  let : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  let : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  let : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  let : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
    (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj (L.φ n)).M :=
    (X.obj (L.φ n)).sigmaCompact
  let : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  let : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
  let : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  let : T3Space (X.obj (L.φ n)).M := inferInstance
  let : RiemannianBundle
      (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle (I := I)
  let : (z : (X.obj (L.φ n)).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj (L.φ n)).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj (L.φ n)).M :=
    (X.obj (L.φ n)).emetricSpace (I := I)
  let : CompleteSpace (X.obj (L.φ n)).M :=
    MetricComplete.complete (I := I) (X.obj (L.φ n))
      (hcomplete.complete (L.φ n))
  let : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  refine ⟨?_, ?_⟩
  · simpa only [N, T] using hn
  intro alpha s hs mu hmu ptsSeq hpts
  obtain ⟨radSeq, hpos, hactive, htail⟩ :=
    centerAverage.exists_active_radius
      (s := s) (target := fun x => x)
      (μSeq := fun _ _ => mu) (ptsSeq := ptsSeq) hpts
  refine ⟨radSeq, ?_, ?_, htail, ?_⟩
  · intro a b x _hx
    exact hpos a b x
  · intro a b x hx gamma hne
    exact hactive a b x hx gamma hne
  · have htail3 : ∀ epsilon > 0, ∃ N : Nat,
        ∀ a ≥ N, ∀ b ≥ N, ∀ x ∈ s,
          3 * radSeq a b x < epsilon := by
      intro epsilon hepsilon
      obtain ⟨N0, hN0⟩ :=
        htail (epsilon / 3) (div_pos hepsilon (by norm_num))
      refine ⟨N0, ?_⟩
      intro a ha b hb x hx
      nlinarith [hN0 a ha b hb x hx]
    obtain ⟨N0, hN0⟩ := exists_rad_cage hd hD haMin hphys P L pb r n
      s (fun a b x => 3 * radSeq a b x) htail3
    refine ⟨N0, ?_⟩
    intro a ha b hb x hx
    let pts := centerAverage.activeFill mu (ptsSeq a b) (fun y => y) x
    let join := minJoin (I := I) (X.obj (L.φ n)).metric
      (normal_enorm (I := I) (X.obj (L.φ n)))
    let x0 := seqCenterD hd P L n (alpha.1 : Nat)
    let rho0 := aMin * hd.mu (L.rInf (alpha.1 : Nat) + 1)
    rcases hqdata alpha with
      ⟨hq, _hδ, hρ, hρq, _hqWide, hqAcc, _herr, hinvErr⟩
    rcases hn alpha with ⟨e, he, hf, happrox, hρInner⟩
    have hproper :
        (letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
         dist x x0) < 4 * L.lamInf (alpha.1 : Nat) := by
      simpa only [x0] using hat_dist_centerD hd P L pb r (hs hx)
    have hhd : hd.dist (L.φ n) x x0 <
        4 * L.lamInf (alpha.1 : Nat) := by
      rw [← ProperMetricOn.dist_eq hd hre P (L.φ n) x x0]
      exact hproper
    have hed : riemannianEDist I x x0 =
        ENNReal.ofReal (hd.dist (L.φ n) x x0) := by
      have : IsRiemannianManifold I (X.obj (L.φ n)).M :=
        ⟨fun _ _ => rfl⟩
      have hrealize := hre.edist_eq (L.φ n) x x0
      rw [← IsRiemannianManifold.out (I := I) x x0]
      exact hrealize
    have hpq : dist x0 x ≤ 4 * L.lamInf (alpha.1 : Nat) := by
      rw [dist_comm, HopfRinow.riemMetric_dist_eq, hed,
        ENNReal.toReal_ofReal (hre.dist_nonneg (L.φ n) x x0)]
      exact hhd.le
    have hptsFilled : ∀ gamma, dist x (pts gamma) < radSeq a b x := by
      simpa only [pts] using centerAverage.activeFill_close
        (g := (X.obj (L.φ n)).metric) (μ := mu) (pts := ptsSeq a b)
          (qstar := fun y => y) (x := x) (hpos a b x)
          (hactive a b x hx)
    have hcage6 : ENNReal.ofReal
          (4 * L.lamInf (alpha.1 : Nat) + 6 * radSeq a b x) <
        ENNReal.ofReal (rho0 / 2) := by
      have hc := hN0 a ha b hb x hx alpha
      have heq : 4 * L.lamInf (alpha.1 : Nat) +
          2 * (3 * radSeq a b x) =
          4 * L.lamInf (alpha.1 : Nat) + 6 * radSeq a b x := by
        ring
      rw [heq] at hc
      simpa only [rho0] using hc
    have hstrict : StrictDistInput (I := I) (X.obj (L.φ n)).metric
        pts join x (radSeq a b x) := by
      simpa only [pts, join, x0, rho0] using
        d.strict_dist_input (L.φ n) (hcomplete.complete (L.φ n))
          (hconn (L.φ n)) x0 hq he hf happrox hinvErr hqAcc
          pts x (radSeq a b x) (4 * L.lamInf (alpha.1 : Nat))
          hρInner hρ hρq (hpos a b x) hpq hptsFilled hcage6
    have hcm : CenterInput (I := I) (X.obj (L.φ n)).metric
        (mu x) pts join x (radSeq a b x) := by
      simpa only [pts, join] using
        centerAverage.inputOfFillSelf (I := I)
          (g := (X.obj (L.φ n)).metric) (μ := mu)
          (pts := ptsSeq a b) (join := join) (r := radSeq a b)
          (qstar := fun y => y) x
          (inferInstance : CompleteSpace (X.obj (L.φ n)).M)
          (hpos a b x)
          (hactive a b x hx) (hmu.nonneg x hx) (hmu.pos x hx) hstrict
    have hradCage : ENNReal.ofReal
          (4 * L.lamInf (alpha.1 : Nat) + 2 * radSeq a b x) <
        ENNReal.ofReal (rho0 / 2) := by
      apply (ENNReal.ofReal_le_ofReal ?_).trans_lt hcage6
      nlinarith [hpos a b x]
    refine ⟨hcm, ?_⟩
    have hout := d.has_live_chart_center_solution_of_cage
      P hre L pb r n hcomplete hconn
      q δ hqdata hn alpha (mu x) pts join x (radSeq a b x) hcm
      (hmu.sum_one x hx) (hs hx) hradCage
    simpa only [pts, join] using hout

end BoundedGeometryNormalChartData

end HCGCompactness
end DifferentialGeometry
