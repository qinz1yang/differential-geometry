import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.PositiveRicci.Compactness.FlowUpgrade
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.PositiveRicci.LimitRoundness
import DifferentialGeometry.Geometry.Metric.Sphere.SpaceForm

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Topology.ThreeManifold
open DifferentialGeometry.Geometry

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HamiltonPositiveRicci

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

def hamiltonCGHLimitOfSmoothCGH
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (origIndex : Nat -> Nat) (horig : StrictMono origIndex)
    (toOrig : forall i : Nat,
      letI : TopologicalSpace (X.term i).M := (X.term i).topology
      letI : ChartedSpace H (X.term i).M := (X.term i).charted
      (X.term i).M ≃ₘ⟮I, I⟯ M)
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (subseq : Nat -> Nat) (hsubseq : StrictMono subseq)
    (hconv : SmoothCGHConverges (I := I) X L subseq)
    (hcomplete : forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) (L.atTime (I := I) t)) :
    HamiltonCGHLimit (I := I) M where
  N := L.M
  topology := L.topology
  charted := L.charted
  smooth := L.smooth
  smooth_plus := by
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    change IsManifold I ∞ L.M
    infer_instance
  sigmaCompact := L.sigmaCompact
  t2 := L.t2
  t2TangentBundle := L.t2TangentBundle
  basepoint := L.basepoint
  D := X.D
  S := L.S
  isSolution := L.isSolution
  sourceTerm := X.term
  origIndex := origIndex
  origStrict := horig
  cghSubseq := subseq
  cghStrict := hsubseq
  cgh := hconv
  sourceToOrig := toOrig
  limitComplete := hcomplete

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem HamiltonSourceLink.realizes
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (hsource : HamiltonSourceLink (I := I) (M := M) P Q hsel X)
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (subseq : Nat -> Nat) (hsubseq : StrictMono subseq)
    (hconv : SmoothCGHConverges (I := I) X L subseq)
    (hcomplete : forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) (L.atTime (I := I) t)) :
    HamiltonSourceRealization (I := I) (M := M) P Q hsel
      (hamiltonCGHLimitOfSmoothCGH (I := I) (M := M) X hsource.origIndex hsource.strictMono
        hsource.toOrig L subseq hsubseq hconv hcomplete) := by
  refine
    { time_mem := ?_
      basepoint_map := ?_
      metric_eq := ?_ }
  · intro i t ht
    exact hsource.time_mem i t ht
  · intro i
    simpa [hamiltonCGHLimitOfSmoothCGH] using hsource.basepoint_map i
  · intro i t ht
    simpa [hamiltonCGHLimitOfSmoothCGH] using hsource.metric_eq i t ht

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem base_scalar_convergence_of_smooth_cgh
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat -> Nat}
    (hsource : HamiltonSourceLink (I := I) (M := M) P Q hsel X)
    (h0 : (0 : Real) ∈ X.D.carrier)
    (hsubseq : StrictMono subseq)
    (hconv : SmoothCGHConverges (I := I) X L subseq)
    (hcomplete : forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) (L.atTime (I := I) t)) :
    hamiltonLimitBaseScalarConvergence (I := I) (M := M) P Q
      (hamiltonCGHLimitOfSmoothCGH (I := I) (M := M) X hsource.origIndex hsource.strictMono
        hsource.toOrig L subseq hsubseq hconv hcomplete) := by
  classical
  have hscalar := hconv.scalar_converges 0 h0 L.basepoint
  refine hscalar.congr' ?_
  filter_upwards with k
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  letI : T2Space (X.term (subseq k)).M :=
    (X.term (subseq k)).t2
  calc
    (X.term (subseq k)).S.scalar 0 (hconv.spatial.maps.map k (L.atTime 0).basepoint)
        = (X.term (subseq k)).S.scalar 0 (X.term (subseq k)).basepoint := by
          simp [PointedCGHMaps.map, hconv.spatial.maps.basepoint_map k]
    _ = hamiltonRescaledScalar (I := I) P Q (hsource.origIndex (subseq k)) 0
        (Q.point (hsource.origIndex (subseq k))) := by
          simpa using hsource.baseScalar (subseq k)

omit [NeZero (Module.finrank ℝ E)] in
theorem tracefree_ricci_decay_at_zero_of_smooth_cgh
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hscalar :
      forall t : Real, t ∈ P.D.carrier ->
        forall x : M, 0 < P.S.scalar t x)
    (hpinch : hamiltonPinchingEstimate (I := I) P)
    (L : HamiltonCGHLimit (I := I) M)
    (h0 : (0 : Real) ∈ L.D.carrier)
    (hreal : HamiltonSourceRealization (I := I) (M := M) P Q hsel L) :
    limitTracefreeRicciDecayAt (I := I) L 0 := by
  classical
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  rcases hamilton_rescaled_tracefree_ricci_norm_sq_at_zero_bound (I := I) P Q hsel hscalar hpinch with
    ⟨epsilon, C, hepsilon, _hepsilon1, _hC, hbound⟩
  have hconv :
      FunctionPullbackTendsto (I := I) L.cgh.spatial.maps
        (fun k _t x =>
          letI : TopologicalSpace (L.sourceTerm (L.cghSubseq k)).M :=
            (L.sourceTerm (L.cghSubseq k)).topology
          letI : ChartedSpace H (L.sourceTerm (L.cghSubseq k)).M :=
            (L.sourceTerm (L.cghSubseq k)).charted
          letI : IsManifold I ∞ (L.sourceTerm (L.cghSubseq k)).M :=
            (L.sourceTerm (L.cghSubseq k)).smooth
          letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
              (L.sourceTerm (L.cghSubseq k)).M := by
            change IsManifold I ∞ (L.sourceTerm (L.cghSubseq k)).M
            infer_instance
          letI : SigmaCompactSpace (L.sourceTerm (L.cghSubseq k)).M :=
            (L.sourceTerm (L.cghSubseq k)).sigmaCompact
          letI : T2Space (L.sourceTerm (L.cghSubseq k)).M :=
            (L.sourceTerm (L.cghSubseq k)).t2
          DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq
            (L.sourceTerm (L.cghSubseq k)).S.scalar
            (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
              (L.sourceTerm (L.cghSubseq k)).S) 0 x)
        (fun _t x =>
          DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq
            L.S.scalar
            (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) L.S)
            0 x) := by
    intro _t _ht x
    have hsc := L.cgh.scalar_converges 0 h0 x
    have hric := L.cgh.ricciNorm_converges 0 h0 x
    simpa only [
      DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq,
      DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqOf,
      DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqAtOf] using
      hric.sub ((hsc.pow 2).div_const 3)
  have hdecay :=
    hamilton_rescaled_pinching_error_tendsto_zero (I := I) h0omega P hD Q hsel L
      (C := C) hepsilon
  have hsmall :=
    FunctionPullbackTendsto.le_of_bound0 (I := I) hconv
      (fun _t _x k =>
        C * hamiltonBlowupScale (I := I) P Q (L.subseq k) ^ (-epsilon))
      (by
        intro _t x
        refine ⟨hdecay, Filter.Eventually.of_forall ?_⟩
        intro k
        let i : Nat := L.cghSubseq k
        letI : TopologicalSpace (L.sourceTerm i).M :=
          (L.sourceTerm i).topology
        letI : ChartedSpace H (L.sourceTerm i).M :=
          (L.sourceTerm i).charted
        letI : IsManifold I ∞ (L.sourceTerm i).M :=
          (L.sourceTerm i).smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
            (L.sourceTerm i).M := by
          change IsManifold I ∞ (L.sourceTerm i).M
          infer_instance
        letI : SigmaCompactSpace (L.sourceTerm i).M :=
          (L.sourceTerm i).sigmaCompact
        letI : T2Space (L.sourceTerm i).M :=
          (L.sourceTerm i).t2
        have hcross :
            DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq
                (L.sourceTerm i).S.scalar
                (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
                  (L.sourceTerm i).S)
                0 (L.cgh.spatial.maps.map k x) =
              DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq
                (hamiltonRescaledSolution (I := I) P Q hsel (L.origIndex i)).scalar
                (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
                (hamiltonRescaledSolution (I := I) P Q hsel (L.origIndex i)))
                0
                (L.sourceToOrig i (L.cgh.spatial.maps.map k x)) := by
          simp only [
            DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq,
            DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqOf,
            DifferentialGeometry.PDE.RicciFlow.ricciNorm,
            DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar,
            DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricci,
            DifferentialGeometry.PDE.RicciFlow.SolutionOn.family_metric,
            DifferentialGeometry.PDE.RicciFlow.SolutionFamily.scalar,
            DifferentialGeometry.PDE.RicciFlow.SolutionFamily.ricci]
          rw [hreal.metric_eq i 0 h0]
          exact
            trace_free_ricci_norm_sq_cross (I := I) (J := I)
              ((hamiltonRescaledSolution (I := I) P Q hsel
                (L.origIndex i)).base.metric 0)
              (L.sourceToOrig i) (L.cgh.spatial.maps.map k x)
        rw [hcross]
        simpa [i, HamiltonCGHLimit.subseq] using
          hbound (L.origIndex i)
            (L.sourceToOrig i (L.cgh.spatial.maps.map k x)))
  exact hsmall 0 h0

omit [NeZero (Module.finrank ℝ E)] in
theorem round_at_zero_of_smooth_cgh
    {omega : Real} (h0omega : 0 < omega)
    (hdim : Module.finrank Real E = 3)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hscalar :
      forall t : Real, t ∈ P.D.carrier ->
        forall x : M, 0 < P.S.scalar t x)
    (hpinch : hamiltonPinchingEstimate (I := I) P)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (hsource : HamiltonSourceLink (I := I) (M := M) P Q hsel X)
    (h0 : (0 : Real) ∈ X.D.carrier)
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (subseq : Nat -> Nat) (hsubseq : StrictMono subseq)
    (hconv : SmoothCGHConverges (I := I) X L subseq)
    (hcomplete : forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) (L.atTime (I := I) t))
    (hconnected :
      letI : TopologicalSpace L.M := L.topology
      ConnectedSpace L.M) :
    let Lh := hamiltonCGHLimitOfSmoothCGH (I := I) (M := M) X hsource.origIndex
      hsource.strictMono hsource.toOrig L subseq hsubseq hconv hcomplete
    limitRoundAt (I := I) (M := M) Lh 0 := by
  classical
  let Lh := hamiltonCGHLimitOfSmoothCGH (I := I) (M := M) X hsource.origIndex
    hsource.strictMono hsource.toOrig L subseq hsubseq hconv hcomplete
  have h0h : (0 : Real) ∈ Lh.D.carrier := by
    simpa [Lh, hamiltonCGHLimitOfSmoothCGH] using h0
  have hreal : HamiltonSourceRealization (I := I) (M := M) P Q hsel Lh := by
    simpa [Lh] using
      (HamiltonSourceLink.realizes (I := I) (M := M) P Q hsel hsource
        L subseq hsubseq hconv hcomplete)
  have hdecay : limitTracefreeRicciDecayAt (I := I) (M := M) Lh 0 :=
    tracefree_ricci_decay_at_zero_of_smooth_cgh (I := I) (M := M) h0omega P hD Q hsel hscalar
      hpinch Lh h0h hreal
  have htf : limitTracefreeRicciZeroAt (I := I) (M := M) Lh 0 :=
    tracefree_zero_of_decay (I := I) (M := M) hdim hdecay
  have heinstein : limitEinsteinAt (I := I) (M := M) Lh 0 :=
    limit_einstein_of_tracefree_ricci_zero (I := I) (M := M) hdim htf
  have hbaseConv : hamiltonLimitBaseScalarConvergence (I := I) (M := M) P Q Lh := by
    simpa [Lh] using
      (base_scalar_convergence_of_smooth_cgh (I := I) (M := M) P Q hsel hsource
        h0 hsubseq hconv hcomplete)
  have hbaseOne : limitBaseScalarOne (I := I) (M := M) Lh :=
    limit_base_scalar_one (I := I) (M := M) P Q hsel hbaseConv
  letI : TopologicalSpace Lh.N := Lh.topology
  letI : ChartedSpace H Lh.N := Lh.charted
  letI : IsManifold I ∞ Lh.N := Lh.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) Lh.N := Lh.smooth_plus
  letI : SigmaCompactSpace Lh.N := Lh.sigmaCompact
  letI : T2Space Lh.N := Lh.t2
  letI : T2Space (TangentBundle I Lh.N) := Lh.t2TangentBundle
  have hbaseEq : Lh.S.scalar 0 Lh.basepoint = 1 := by
    simpa [limitBaseScalarOne] using hbaseOne
  have hbasePos : 0 < Lh.S.scalar 0 Lh.basepoint := by
    rw [hbaseEq]
    exact one_pos
  have hconn : hamiltonLimitConnected (I := I) (M := M) Lh := by
    simpa [Lh, hamiltonCGHLimitOfSmoothCGH, hamiltonLimitConnected] using hconnected
  have hbdry : hamiltonLimitBoundaryless (I := I) := by
    simpa [Lh, hamiltonCGHLimitOfSmoothCGH, hamiltonLimitBoundaryless] using
      (inferInstance : I.Boundaryless)
  exact limit_round_base (I := I) (M := M) hdim hconn hbdry
    hbasePos heinstein

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem flow_upgrade_data_connected
    {X : PointedFlowSeq (I := I)}
    {mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I))}
    (d : FlowUpgrade (I := I) X mc)
    (hconn : letI : TopologicalSpace mc.limit.M := mc.limit.topology
      ConnectedSpace mc.limit.M) :
    letI : TopologicalSpace d.data.L.M := d.data.L.topology
    ConnectedSpace d.data.L.M := by
  have hAt0 : letI : TopologicalSpace (d.data.L.atTime (I := I) 0).M :=
      (d.data.L.atTime (I := I) 0).topology
      ConnectedSpace (d.data.L.atTime (I := I) 0).M := by
    rw [d.data.hL0]
    exact hconn
  simpa only [PointedFlowData.atTime] using hAt0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem flow_upgrade_data_converges
    {X : PointedFlowSeq (I := I)}
    {mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I))}
    (d : FlowUpgrade (I := I) X mc) :
    Nonempty (SmoothCGHConverges (I := I) X d.data.L
      (mc.compSubseq d.φ d.hφ).subseq) :=
  ⟨SmoothCGHConverges.ofRestrictPullback (I := I)
    d.data.maps d.data.scalar d.data.ricciNorm d.data.hσsrc
    d.data.refMetric
    (letI : TopologicalSpace d.data.L.M := d.data.L.topology
     letI : ChartedSpace H d.data.L.M := d.data.L.charted
     letI : IsManifold I ∞ d.data.L.M := d.data.L.smooth
     letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) d.data.L.M := by
       change IsManifold I ∞ d.data.L.M
       infer_instance
     letI : SigmaCompactSpace d.data.L.M := d.data.L.sigmaCompact
     letI : T2Space d.data.L.M := d.data.L.t2
     d.data.L.S.family.metric) d.data.conv⟩

theorem constant_positive_sectional_curvature_of_smooth_cgh
    {omega : Real} (h0omega : 0 < omega)
    (hM : isClosedThreeManifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hscalar :
      forall t : Real, t ∈ P.D.carrier ->
        forall x : M, 0 < P.S.scalar t x)
    (hpinch : hamiltonPinchingEstimate (I := I) P)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (hsource : HamiltonSourceLink (I := I) (M := M) P Q hsel X)
    (h0 : (0 : Real) ∈ X.D.carrier)
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (subseq : Nat -> Nat) (hsubseq : StrictMono subseq)
    (hconv : SmoothCGHConverges (I := I) X L subseq)
    (hcomplete : forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) (L.atTime (I := I) t))
    (hconnected :
      letI : TopologicalSpace L.M := L.topology
      ConnectedSpace L.M) :
    admitsConstantPositiveSectionalCurvature (I := I) (M := M) := by
  let Lh := hamiltonCGHLimitOfSmoothCGH (I := I) (M := M) X hsource.origIndex
    hsource.strictMono hsource.toOrig L subseq hsubseq hconv hcomplete
  have hround : limitRoundAt (I := I) (M := M) Lh 0 := by
    simpa only [Lh] using
      (round_at_zero_of_smooth_cgh (I := I) (M := M) h0omega hM.2.2.2 P hD Q hsel
        hscalar hpinch hsource h0 L subseq hsubseq hconv hcomplete hconnected)
  have h0h : (0 : Real) ∈ Lh.D.carrier := by
    change (0 : Real) ∈ X.D.carrier
    exact h0
  have hconn : hamiltonLimitConnected (I := I) (M := M) Lh := by
    change (letI : TopologicalSpace L.M := L.topology; ConnectedSpace L.M)
    exact hconnected
  simpa only [admitsConstantPositiveSectionalCurvature] using
    (limit_to_orig (I := I) (M := M) hM h0h hconn hround)


end HamiltonPositiveRicci
end RicciFlow
end PDE
end DifferentialGeometry
