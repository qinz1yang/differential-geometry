import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Construction.ChartSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaircaseStageRegularityReplay
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.NormalCoordinates.BoundedGeometryReplay

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

omit [CompleteSpace E] in
theorem strict_distance_convexity
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M)
    (mb :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      (d.chart k x).MetricBounds (X.obj k).metric)
    (CB : Real)
    {q eta : NNReal} {δ ρ : Real}
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
    (hqAcc : 3 * CB * (2 * (q : Real)) ^ 2 ≤
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
    mb.radius = c.radius / 4 →
    mb.C 1 ≤ CB →
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
  classical
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  let : (z : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let : MetricSpace (X.obj k).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M)
  dsimp only
  intro hmb hCB hρInner hρ hρq hr hxp hpts hcage
  let hEnorm := normal_enorm (I := I) (X.obj k)
  let join := minJoin (I := I) (X.obj k).metric hEnorm
  let c := d.chart k x
  have hR6pos : 0 < R + 6 * r := by
    nlinarith [show 0 ≤ dist x p from dist_nonneg]
  have hjoin_dist (a b : (X.obj k).M) {t : Real} (ht : 0 ≤ t) :
      dist a (join a b t) ≤ dist a b * t := by
    have hed := minJoin_edist_le
      (I := I) (X.obj k).metric hEnorm a b ht
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
    have hmul : 0 ≤ (riemannianEDist I a b).toReal * t :=
      mul_nonneg ENNReal.toReal_nonneg ht
    rw [ENNReal.toReal_ofReal hmul] at hmono
    simpa only [join, ← HopfRinow.riemMetric_dist_eq] using hmono
  have hjoin_cage (a : (X.obj k).M)
      (ha : a ∈ Metric.closedBall p (2 * r)) (b : (X.obj k).M)
      (hbmem : b ∈ Metric.closedBall p (2 * r)) {t : Real}
      (ht : t ∈ unitInterval) :
      dist x (join a b t) ≤ R + 6 * r := by
    have ha' : dist p a ≤ 2 * r := by
      simpa only [dist_comm] using Metric.mem_closedBall.mp ha
    have hb' : dist p b ≤ 2 * r := by
      simpa only [dist_comm] using Metric.mem_closedBall.mp hbmem
    have hab : dist a b ≤ 4 * r := by
      calc
        dist a b ≤ dist a p + dist p b := dist_triangle _ _ _
        _ ≤ 4 * r := by
          have hap : dist a p ≤ 2 * r := Metric.mem_closedBall.mp ha
          linarith
    have hajoin : dist a (join a b t) ≤ 4 * r := by
      have hraw := hjoin_dist a b ht.1
      have habt : dist a b * t ≤ 4 * r := by
        calc
          dist a b * t ≤ dist a b * 1 :=
            mul_le_mul_of_nonneg_left ht.2 dist_nonneg
          _ ≤ 4 * r := by simpa only [mul_one] using hab
      exact hraw.trans habt
    calc
      dist x (join a b t) ≤
          dist x p + dist p a + dist a (join a b t) :=
        dist_triangle4 _ _ _ _
      _ ≤ R + 6 * r := by linarith
  have hriem_eq (a b : (X.obj k).M) :
      riemannianEDist I a b = ENNReal.ofReal (dist a b) := by
    rw [HopfRinow.riemMetric_dist_eq]
    exact (ENNReal.ofReal_toReal
      (riemannianEDist_ne_top (I := I) a b)).symm
  have hpair_cage (pt : (X.obj k).M) (hpt : dist x pt < R + 6 * r)
      (a : (X.obj k).M) (ha : a ∈ Metric.closedBall p (2 * r))
      (b : (X.obj k).M) (hbmem : b ∈ Metric.closedBall p (2 * r))
      {t : Real} (ht : t ∈ unitInterval) :
      max (riemannianEDist I x (join a b t))
          (riemannianEDist I x pt) <
        ENNReal.ofReal (ρ / 2) := by
    rw [max_lt_iff]
    constructor
    · have hjoinEd : riemannianEDist I x (join a b t) ≤
          ENNReal.ofReal (R + 6 * r) := by
        rw [hriem_eq]
        exact ENNReal.ofReal_le_ofReal (hjoin_cage a ha b hbmem ht)
      exact hjoinEd.trans_lt hcage
    · have hptEd : riemannianEDist I x pt <
          ENNReal.ofReal (R + 6 * r) := by
        rw [hriem_eq]
        exact (ENNReal.ofReal_lt_ofReal_iff hR6pos).2 hpt
      exact hptEd.trans hcage
  have hpCage : dist x p < R + 6 * r := by
    linarith
  have hptsCage (i : ι) : dist x (points i) < R + 6 * r := by
    calc
      dist x (points i) ≤ dist x p + dist p (points i) :=
        dist_triangle _ _ _
      _ < R + r := add_lt_add_of_le_of_lt hxp (hpts i)
      _ < R + 6 * r := by nlinarith
  have hstrict_pt (pt : (X.obj k).M) (hpt : dist x pt < R + 6 * r)
      (a : (X.obj k).M) (ha : a ∈ Metric.closedBall p (2 * r))
      (b : (X.obj k).M) (hbmem : b ∈ Metric.closedBall p (2 * r))
      (hab : a ≠ b) :
      StrictConvexOn Real unitInterval
        (fun t : Real => CenterOfMass.halfSqDist pt (join a b t)) := by
    let S : Set (X.obj k).M :=
      {y | max (riemannianEDist I x y) (riemannianEDist I x pt) <
        ENNReal.ofReal (ρ / 2)}
    let γ : Real → (X.obj k).M := join a b
    let v₀ : TangentSpace I a := minimizingVec
      (I := I) (X.obj k).metric hEnorm a b
    have hSopen : IsOpen S := by
      dsimp only [S]
      exact isOpen_lt
        ((continuous_riemannianEDist (I := I) (X.obj k).metric x).max
          continuous_const) continuous_const
    have hsmooth : ContMDiffOn I 𝓘(Real) ∞
        (CenterOfMass.halfSqDist pt) S := by
      simpa only [S] using
        d.halfSqDist_contMDiffOn k hcomplete hconn x hq he hf
          mb hmb hρ hρq hρInner
    have hmap : MapsTo γ unitInterval S := by
      intro t ht
      with_unfolding_all
        exact hpair_cage pt hpt a ha b hbmem ht
    have hgeo : IsGeodesic (I := I) (X.obj k).metric γ := by
      with_unfolding_all
        exact intrinsicGeodesic_isGeodesic
          (I := I) (X.obj k).metric hEnorm a v₀
    have hγcont : Continuous γ := by
      simpa only [γ, join] using
        minJoin_cont (I := I) (X.obj k).metric hEnorm a b
    have hγsmooth : ContMDiff 𝓘(Real) I ∞ γ :=
      isGeodesic_contMDiff (I := I) (X.obj k).metric hgeo hγcont
    have hv₀ : v₀ ≠ 0 := by
      intro hvzero
      apply hab
      calc
        a = expMapIntrinsic (I := I) (X.obj k).metric hEnorm a 0 :=
          (expMapIntrinsic_zero
            (I := I) (X.obj k).metric hEnorm a).symm
        _ = expMapIntrinsic (I := I) (X.obj k).metric hEnorm a v₀ := by
          rw [hvzero]
        _ = b := by
          simpa only [v₀] using
            minimizingVec_exp (I := I) (X.obj k).metric hEnorm a b
    have hvel (t : Real) :
        mfderiv 𝓘(Real) I γ t 1 ≠ 0 := by
      intro hzero
      have hspeed := intrinsicGeodesic_speedSq_eq
        (I := I) (X.obj k).metric hEnorm a v₀ t
      have hspeed' : (X.obj k).metric.inner (γ t)
          (mfderiv 𝓘(Real) I γ t 1) (mfderiv 𝓘(Real) I γ t 1) =
          (X.obj k).metric.inner a v₀ v₀ := by
        with_unfolding_all
          exact hspeed
      have hlaunch : 0 < (X.obj k).metric.inner a v₀ v₀ :=
        (X.obj k).metric.pos a v₀ hv₀
      apply ne_of_gt hlaunch
      rw [← hspeed', hzero]
      simp
    have hcont : ContinuousOn
        ((CenterOfMass.halfSqDist pt) ∘ γ) unitInterval :=
      hsmooth.continuousOn.comp hγsmooth.continuous.continuousOn hmap
    have hmem : MapsTo γ (interior unitInterval) S :=
      fun t ht => hmap (interior_subset ht)
    have hpos : ∀ t ∈ interior unitInterval,
        0 < hessFun (I := I) (X.obj k).metric
          (CenterOfMass.halfSqDist pt) (γ t)
          (mfderiv 𝓘(Real) I γ t 1)
          (mfderiv 𝓘(Real) I γ t 1) := by
      intro t ht
      exact d.hess_pos k hcomplete hconn x hq he hf happrox heta mb CB hqAcc
        hmb hCB hρInner hρ hρq
        (by
          with_unfolding_all
            exact hmem ht) (hvel t)
    with_unfolding_all
      exact strictConvex_geo (I := I) (X.obj k).metric hSopen hsmooth
        hγsmooth hgeo (convex_Icc (0 : Real) 1) hcont hmem hpos
  change StrictDistanceConvexity (I := I) (X.obj k).metric points join p r
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hbmem hab
    have hstrictP := hstrict_pt p hpCage a ha b hbmem hab
    have hlt := hstrictP.2 unitInterval.zero_mem unitInterval.one_mem
      (by norm_num : (0 : Real) ≠ 1)
      (by norm_num : (0 : Real) < 1 / 2)
      (by norm_num : (0 : Real) < 1 / 2)
      (by norm_num : (1 / 2 : Real) + 1 / 2 = 1)
    norm_num at hlt
    have hltMid :
        CenterOfMass.halfSqDist p (join a b (1 / 2 : Real)) <
          (1 / 2 : Real) * CenterOfMass.halfSqDist p a +
            (1 / 2 : Real) * CenterOfMass.halfSqDist p b := by
      simpa only [join, minJoin_zero, minJoin_one, one_smul,
        Function.comp_apply, smul_eq_mul] using hlt
    have hRnonneg : 0 ≤ 2 * r := by positivity
    have haDist : dist a p ≤ 2 * r := Metric.mem_closedBall.mp ha
    have hbDist : dist b p ≤ 2 * r := Metric.mem_closedBall.mp hbmem
    have haSq : dist a p ^ 2 ≤ (2 * r) ^ 2 :=
      (sq_le_sq₀ dist_nonneg hRnonneg).2 haDist
    have hbSq : dist b p ^ 2 ≤ (2 * r) ^ 2 :=
      (sq_le_sq₀ dist_nonneg hRnonneg).2 hbDist
    have hsq : dist (join a b (1 / 2 : Real)) p ^ 2 ≤
        (2 * r) ^ 2 := by
      simp only [CenterOfMass.halfSqDist] at hltMid
      nlinarith
    exact Metric.mem_closedBall.2
      ((sq_le_sq₀ dist_nonneg hRnonneg).1 hsq)
  · intro a _ha b _hb
    exact minJoin_zero (I := I) (X.obj k).metric hEnorm a b
  · intro a _ha b _hb
    exact minJoin_one (I := I) (X.obj k).metric hEnorm a b
  · intro i a ha b hbmem hab
    exact hstrict_pt (points i) (hptsCage i) a ha b hbmem hab

end SeqBallNormalChartData

end CheegerGromovCompactness
end DifferentialGeometry
