import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Construction.ChartSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaircaseStageRegularityReplay

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter Bundle Manifold Set TopologicalSpace
open scoped ContDiff Manifold NNReal Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace SeqBallNormalChartData
omit [CompleteSpace E] in
theorem exists_center_of_mass_scale
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
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
      ConnectedSpace (X.obj k).M) :
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ aMin : Real, 0 < aMin ∧
      ∀ {D : Real} (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
        (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real),
        ∃ q : LiveSlot L pb r → NNReal,
          ∃ δ : LiveSlot L pb r → Real,
            (∀ gamma : LiveSlot L pb r,
              let Rgamma := L.rInf (gamma.1 : Nat) + 1
              let rho := aMin * hd.mu Rgamma
              0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
                2 * rho < (q gamma : Real) ∧
                6 * (q gamma : Real) < d.phaseRadius Rgamma ∧
                3 * CB 1 * (2 * (q gamma : Real)) ^ 2 ≤
                  (2 / 3 : Real) * (q gamma : Real) ∧
                PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)) < T ∧
                N * (T - PhaseFlow.phaseErr
                    (phaseKOf CB hCB (2 * q gamma)))⁻¹ *
                    PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)) < 1 / 24) ∧
            ∀ᶠ n in Filter.atTop, ∀ gamma : LiveSlot L pb r,
              let Rgamma := L.rInf (gamma.1 : Nat) + 1
              let rho := aMin * hd.mu Rgamma
              let x := seqCenterD hd P L n (gamma.1 : Nat)
              letI : TopologicalSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).topology
              letI : ChartedSpace H (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).charted
              letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).smooth
              letI : SigmaCompactSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).sigmaCompact
              letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
              letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
                (X.obj (L.φ n)).t2TangentBundle
              ∃ e : OpenPartialHomeomorph (E × E) (E × E),
                IsNormalDiag (I := I) (X.obj (L.φ n))
                    (hcomplete.complete (L.φ n)) (hconn (L.φ n))
                    x (q gamma) (δ gamma) e (c := d.chart (L.φ n) x) ∧
                  NormalDiagFence (I := I) (X.obj (L.φ n))
                    x (q gamma) e (c := d.chart (L.φ n) x) ∧
                  ApproximatesLinearOn
                    (e.symm : E × E → E × E)
                    ((PhaseFlow.freeDiagCLE (E := E)).symm :
                      (E × E) →L[Real] (E × E))
                    e.target
                    (N * (T - PhaseFlow.phaseErr
                      (phaseKOf CB hCB (2 * q gamma)))⁻¹ *
                      PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma))) ∧
                  rho ≤ (d.chart (L.φ n) x).radius / 4 := by
  simpa only [toBoundedGeometryNormalChartData_chart,
    toBoundedGeometryNormalChartData_phaseRadius,
    toBoundedGeometryNormalChartData_metricC,
    toBoundedGeometryNormalChartData_phaseK] using
    BoundedGeometryNormalChartData.exists_center_of_mass_scale
      (d.toBoundedGeometryNormalChartData CB hCB hunif) hre hcomplete hconn

theorem has_live_chart_center_solution_of_cage
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) {D aMin : Real}
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
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
                PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)))⁻¹ *
              PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma))) ∧
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
        (points : Fin (pb.A r) → (X.obj (L.φ k)).M)
        (join : (X.obj (L.φ k)).M → (X.obj (L.φ k)).M → Real →
          (X.obj (L.φ k)).M)
        (x : (X.obj (L.φ k)).M) (rad : Real),
      ∀ h : CenterOfMassConditions (I := I) (X.obj (L.φ k)).metric
          mu points join x rad,
        ∑ i, mu i = 1 →
        x ∈ NetLimitData.hatBall (I := I) (X := X)
          hd D P L pb r k alpha.1 →
        ENNReal.ofReal
            (4 * L.lamInf (alpha.1 : Nat) + 2 * rad) <
          ENNReal.ofReal
            ((aMin * hd.mu (L.rInf (alpha.1 : Nat) + 1)) / 2) →
        HasLiveChartCenterSolution (I := I)
          (d.toBoundedGeometryNormalChartData CB hCB hunif) P L pb r k hcomplete hconn q δ alpha
          mu points join x rad h := by
  simpa only [toBoundedGeometryNormalChartData_chart] using
    BoundedGeometryNormalChartData.has_live_chart_center_solution_of_cage
      (d.toBoundedGeometryNormalChartData CB hCB hunif) P hre L pb r k hcomplete hconn q δ
      (fun gamma => by
        simpa only [toBoundedGeometryNormalChartData_metricC,
          toBoundedGeometryNormalChartData_phaseRadius,
          toBoundedGeometryNormalChartData_phaseK] using hqdata gamma)
      (fun gamma => by
        simpa only [toBoundedGeometryNormalChartData_chart,
          toBoundedGeometryNormalChartData_phaseK] using hbranch gamma)
      alpha

theorem exists_live_chart_center_solutions
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
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
                3 * CB 1 * (2 * (q gamma : Real)) ^ 2 ≤
                  (2 / 3 : Real) * (q gamma : Real) ∧
                PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)) < T ∧
                N * (T - PhaseFlow.phaseErr
                    (phaseKOf CB hCB (2 * q gamma)))⁻¹ *
                    PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma)) < 1 / 24) ∧
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
                        (phaseKOf CB hCB (2 * q gamma)))⁻¹ *
                        PhaseFlow.phaseErr (phaseKOf CB hCB (2 * q gamma))) ∧
                    rho ≤ (d.chart (L.φ n) x0).radius / 4) ∧
              ∀ (alpha : LiveSlot L pb r)
                (s : Set (X.obj (L.φ n)).M)
                (hs : s ⊆ NetLimitData.hatBall (I := I) (X := X)
                  hd D P L pb r n alpha.1)
                (mu : (X.obj (L.φ n)).M → Fin (pb.A r) → Real)
                (hmu : centerAverage.WeightDataOn s
                  (fun _ : Fin (pb.A r) => Set.univ) mu)
                (pointsSeq : Nat → Nat → (X.obj (L.φ n)).M →
                  Fin (pb.A r) → (X.obj (L.φ n)).M)
                (hpts : ∀ gamma : Fin (pb.A r), ∀ epsilon : Real,
                  0 < epsilon → ∃ N : Nat,
                    ∀ a ≥ N, ∀ b ≥ N,
                      ∀ x ∈ s, mu x gamma ≠ 0 →
                        dist x (pointsSeq a b x gamma) < epsilon),
                  ∃ radSeq : Nat → Nat → (X.obj (L.φ n)).M → Real,
                    (∀ a b x, x ∈ s → 0 < radSeq a b x) ∧
                    (∀ a b x, x ∈ s → ∀ gamma, mu x gamma ≠ 0 →
                      dist x (pointsSeq a b x gamma) < radSeq a b x) ∧
                    (∀ epsilon > 0, ∃ N : Nat,
                      ∀ a ≥ N, ∀ b ≥ N,
                        ∀ x ∈ s, radSeq a b x < epsilon) ∧
                    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
                      ∀ x ∈ s,
                        let join := minJoin (I := I) (X.obj (L.φ n)).metric
                          (normal_enorm (I := I) (X.obj (L.φ n)))
                        let points := centerAverage.activeFill mu (pointsSeq a b)
                          (fun y => y) x
                        ∃ hcm : CenterOfMassConditions (I := I)
                            (X.obj (L.φ n)).metric (mu x) points join x
                            (radSeq a b x),
                          HasLiveChartCenterSolution (I := I)
                            (d.toBoundedGeometryNormalChartData CB hCB hunif) P L pb r n
                            hcomplete hconn
                            q δ alpha (mu x) points join x (radSeq a b x) hcm := by
  simpa only [toBoundedGeometryNormalChartData_chart,
    toBoundedGeometryNormalChartData_phaseRadius,
    toBoundedGeometryNormalChartData_metricC,
    toBoundedGeometryNormalChartData_phaseK] using
    BoundedGeometryNormalChartData.exists_live_chart_center_solutions
      (d.toBoundedGeometryNormalChartData CB hCB hunif) hre hcomplete hconn

theorem strict_distance_convexity
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (k : Nat)
    (CB : Nat → Real) (hCB : ∀ p : Nat, 0 ≤ CB p)
    (hunif : ∀ (j : Nat) (x : (X.obj j).M),
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      letI : T2Space (TangentBundle I (X.obj j).M) :=
        (X.obj j).t2TangentBundle
      ∃ b : (d.chart j x).MetricBounds (X.obj j).metric,
        b.radius = (d.chart j x).radius ∧ ∀ p : Nat, b.C p ≤ CB p)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q eta : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q)
    (he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn
      x q δ e (c := d.chart k x))
    (hf : NormalDiagFence (I := I) (X.obj k) x q e
      (c := d.chart k x))
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) e.target eta)
    (heta : eta < (1 / 24 : NNReal))
    (hqAcc : 3 * CB 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real))
    {ι : Type} [Fintype ι] (points : ι → (X.obj k).M)
    (p : (X.obj k).M) (r R : Real) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : (z : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I z) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    letI : MetricSpace (X.obj k).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
    let c := d.chart k x
    ρ ≤ c.radius / 4 →
    0 < ρ →
    2 * ρ < (q : Real) →
    0 < r →
    dist x p ≤ R →
    (∀ i, dist p (points i) < r) →
    ENNReal.ofReal (R + 6 * r) < ENNReal.ofReal (ρ / 2) →
    StrictDistanceConvexity (I := I) (X.obj k).metric points
      (minJoin (I := I) (X.obj k).metric
        (normal_enorm (I := I) (X.obj k))) p r := by
  simpa only [toBoundedGeometryNormalChartData_chart] using
    BoundedGeometryNormalChartData.strict_distance_convexity
      (d.toBoundedGeometryNormalChartData CB hCB hunif) k hcomplete hconn x hq he hf
      happrox heta
      (by simpa only [toBoundedGeometryNormalChartData_metricC] using hqAcc)
      points p r R

end SeqBallNormalChartData

end CheegerGromovCompactness
end DifferentialGeometry
