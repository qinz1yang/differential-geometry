import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.PositiveRicci.Flow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Definitions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.TraceFreeRicciHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.QuotientEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.HamiltonReaction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.TraceFreeRicciEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.SolutionEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.IntrinsicEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Estimate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Local
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.RicciPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Defs
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityCross
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Topology.ThreeManifold

set_option autoImplicit false

noncomputable section

universe u

namespace DifferentialGeometry.PDE.RicciFlow
namespace HamiltonPositiveRicci

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

def hamiltonScalarBlowup
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) : Prop :=
  forall A : Real, exists t : Real, exists x : M,
    t ∈ P.D.carrier /\ A < hamiltonScalar (I := I) P t x

def hamiltonBlowupPointSelection
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) : Prop :=
  (forall i : Nat, 0 < hamiltonBlowupScale (I := I) P Q i) /\
    (forall i : Nat, 0 < Q.time i) /\
    (forall i : Nat, Q.time i ∈ P.D.carrier) /\
    (forall A : Real, exists N : Nat,
      forall i : Nat, N <= i ->
        A <= hamiltonBlowupScale (I := I) P Q i * Q.time i) /\
    (forall i : Nat, hamiltonRescaledScalar (I := I) P Q i 0 (Q.point i) = 1) /\
    (forall (i : Nat) (s : Real) (x : M),
      -(hamiltonBlowupScale (I := I) P Q i * Q.time i) <= s -> s <= 0 ->
        hamiltonRescaledScalar (I := I) P Q i s x <= 1)

noncomputable def hamiltonRescaledSolution
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : hamiltonBlowupPointSelection (I := I) P Q) (i : Nat) :
    SolutionOn (I := I) (M := M)
      (paraInterval P.D (Q.time i) (hamiltonBlowupScale (I := I) P Q i)
        (hsel.2.2.1 i)) :=
  paraSolution (I := I) P.S (Q.time i) (hamiltonBlowupScale (I := I) P Q i)
    (hsel.1 i) (hsel.2.2.1 i)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_rescaled_tracefree_ricci_norm_sq_identity
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : hamiltonBlowupPointSelection (I := I) P Q) (i : Nat) :
    DifferentialGeometry.PDE.RicciFlow.ParabolicTraceFreeRicciNormSqScaling (M := M)
      (DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq P.S.scalar
        (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) P.S))
      (DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq
        (hamiltonRescaledSolution (I := I) P Q hsel i).scalar
        (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
          (hamiltonRescaledSolution (I := I) P Q hsel i)))
      (Q.time i) (hamiltonBlowupScale (I := I) P Q i) := by
  intro s x
  simp only [hamiltonRescaledSolution,
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq,
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqOf,
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqAtOf,
    DifferentialGeometry.PDE.RicciFlow.paraSolution_scalar,
    DifferentialGeometry.PDE.RicciFlow.paraSolution_ricciNorm]
  ring

structure HamiltonSourceRealization
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (L : HamiltonCGHLimit (I := I) M) : Prop where
  time_mem : forall (i : Nat) (t : Real), t ∈ L.D.carrier ->
    t ∈ (paraInterval P.D (Q.time (L.origIndex i))
      (hamiltonBlowupScale (I := I) P Q (L.origIndex i))
      (hsel.2.2.1 (L.origIndex i))).carrier
  basepoint_map : forall i : Nat,
    letI : TopologicalSpace (L.sourceTerm i).M := (L.sourceTerm i).topology
    letI : ChartedSpace H (L.sourceTerm i).M := (L.sourceTerm i).charted
    L.sourceToOrig i (L.sourceTerm i).basepoint = Q.point (L.origIndex i)
  metric_eq : forall i : Nat,
    letI : TopologicalSpace (L.sourceTerm i).M := (L.sourceTerm i).topology
    letI : ChartedSpace H (L.sourceTerm i).M := (L.sourceTerm i).charted
    letI : IsManifold I ∞ (L.sourceTerm i).M := (L.sourceTerm i).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (L.sourceTerm i).M := by
      change IsManifold I ∞ (L.sourceTerm i).M
      infer_instance
    letI : SigmaCompactSpace (L.sourceTerm i).M := (L.sourceTerm i).sigmaCompact
    letI : T2Space (L.sourceTerm i).M := (L.sourceTerm i).t2
    forall t : Real, t ∈ L.D.carrier ->
      (L.sourceTerm i).S.base.metric t =
        Diffeomorph.pullbackMetricCross
          ((hamiltonRescaledSolution (I := I) P Q hsel (L.origIndex i)).base.metric t)
          (L.sourceToOrig i)

def hamiltonRescaledRicciNonnegative
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) : Prop :=
  forall (i : Nat) (s : Real) (x : M) (v : TangentSpace I x),
    -(hamiltonBlowupScale (I := I) P Q i * Q.time i) <= s -> s <= 0 ->
      0 <= P.S.ricciAt (hamiltonRescaledTime (I := I) P Q i s) x
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)

def hamiltonFixedPinching
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) (omega : Real) : Prop :=
  exists delta : Real,
    0 < delta /\ delta < (1 : Real) / 3 /\
      forall T : Real, 0 <= T -> T < omega ->
        DifferentialGeometry.PDE.RicciFlow.PinchPres (I := I) (M := M)
          (fun t : Real => P.S.base.metric t)
          (DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M)
            P.S.ricci)
          P.S.scalar T delta

def hamiltonRicciNonnegative
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) (omega : Real) : Prop :=
  forall T : Real, 0 <= T -> T < omega ->
    DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M) P.S.ricci)
      (Set.Icc 0 T)

def hamiltonPinchingEstimate
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) : Prop :=
  exists epsilon C : Real,
    0 < epsilon /\ epsilon < 1 /\ 0 <= C /\
      DifferentialGeometry.PDE.RicciFlow.PinchEstimateOn (M := M)
        (DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq P.S.scalar
          (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) P.S))
        P.S.scalar
        (DifferentialGeometry.PDE.RicciFlow.pinchWeight (M := M) P.S.scalar epsilon)
        C P.D.carrier

private theorem scaled_pinch_le
    {q R r C epsilon : Real}
    (hR : 0 < R) (hr : 0 < r) (hr1 : r ≤ 1)
    (hC : 0 ≤ C) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hpinch : q / r ^ 2 ≤ C * (R * r) ^ (-epsilon)) :
    q ≤ C * R ^ (-epsilon) := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hmain :
      q ≤ (C * (R * r) ^ (-epsilon)) * r ^ 2 :=
    (div_le_iff₀ hr2).mp hpinch
  have hrewrite :
      (C * (R * r) ^ (-epsilon)) * r ^ 2 =
        (C * R ^ (-epsilon)) * r ^ (2 - epsilon) := by
    rw [Real.mul_rpow hR.le hr.le, ← Real.rpow_two r]
    calc
      C * (R ^ (-epsilon) * r ^ (-epsilon)) * r ^ (2 : Real) =
          (C * R ^ (-epsilon)) *
            (r ^ (-epsilon) * r ^ (2 : Real)) := by ring
      _ = (C * R ^ (-epsilon)) * r ^ (2 - epsilon) := by
        rw [← Real.rpow_add hr]
        congr 2
        ring
  rw [hrewrite] at hmain
  have hrpow : r ^ (2 - epsilon) ≤ 1 :=
    Real.rpow_le_one hr.le hr1 (by linarith)
  have hcoef : 0 ≤ C * R ^ (-epsilon) :=
    mul_nonneg hC (Real.rpow_nonneg hR.le _)
  exact hmain.trans (by simpa using mul_le_mul_of_nonneg_left hrpow hcoef)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_rescaled_tracefree_ricci_norm_sq_at_zero_bound
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hscalar :
      ∀ t : Real, t ∈ P.D.carrier -> ∀ x : M, 0 < P.S.scalar t x)
    (hpinch : hamiltonPinchingEstimate (I := I) P) :
    ∃ epsilon C : Real,
      0 < epsilon ∧ epsilon < 1 ∧ 0 ≤ C ∧
        ∀ i : Nat, ∀ x : M,
          DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq
              (hamiltonRescaledSolution (I := I) P Q hsel i).scalar
              (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
                (hamiltonRescaledSolution (I := I) P Q hsel i)) 0 x ≤
            C * hamiltonBlowupScale (I := I) P Q i ^ (-epsilon) := by
  rcases hpinch with ⟨epsilon, C, hepsilon0, hepsilon1, hC, hest⟩
  refine ⟨epsilon, C, hepsilon0, hepsilon1, hC, ?_⟩
  intro i x
  let R : Real := hamiltonBlowupScale (I := I) P Q i
  let r : Real := (hamiltonRescaledSolution (I := I) P Q hsel i).scalar 0 x
  let q : Real :=
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq
      (hamiltonRescaledSolution (I := I) P Q hsel i).scalar
      (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
        (hamiltonRescaledSolution (I := I) P Q hsel i)) 0 x
  have hR : 0 < R := hsel.1 i
  have htime : 0 < Q.time i := hsel.2.1 i
  have htimeMem : Q.time i ∈ P.D.carrier := hsel.2.2.1 i
  have hscalarOld : 0 < P.S.scalar (Q.time i) x :=
    hscalar (Q.time i) htimeMem x
  have hr_eq :
      r = R⁻¹ * P.S.scalar (Q.time i) x := by
    simp only [r, R, hamiltonRescaledSolution,
      DifferentialGeometry.PDE.RicciFlow.paraSolution_scalar,
      DifferentialGeometry.PDE.RicciFlow.paraTime_zero]
  have hr : 0 < r := by
    rw [hr_eq]
    exact mul_pos (inv_pos.mpr hR) hscalarOld
  have hleft : -(R * Q.time i) ≤ (0 : Real) := by
    have : 0 < R * Q.time i := mul_pos hR htime
    linarith
  have hr1 : r ≤ 1 := by
    have hmax := hsel.2.2.2.2.2 i 0 x
      (by simpa only [R] using hleft) le_rfl
    have hr_display :
        r = hamiltonRescaledScalar (I := I) P Q i 0 x := by
      simpa only [R, hamiltonRescaledScalar, hamiltonRescaledTime, hamiltonScalar,
        hamiltonSolution, zero_div, add_zero] using hr_eq
    rwa [← hr_display] at hmax
  have hscalarOld_eq : P.S.scalar (Q.time i) x = R * r := by
    rw [hr_eq]
    field_simp [ne_of_gt hR]
  have hscalarDisplay :
      DifferentialGeometry.PDE.RicciFlow.ParabolicScalarCurvatureScaling (M := M)
        P.S.scalar
        (hamiltonRescaledSolution (I := I) P Q hsel i).scalar
        (Q.time i) R := by
    intro s y
    simpa only [R, hamiltonRescaledSolution] using
      congrFun
        (congrFun
          (DifferentialGeometry.PDE.RicciFlow.paraSolution_scalar
            (I := I) P.S (Q.time i) R hR htimeMem) s) y
  have hratio :=
    DifferentialGeometry.PDE.RicciFlow.para_tracefree_ratio_invariant
      (M := M)
      (scalar := P.S.scalar)
      (scalarR := (hamiltonRescaledSolution (I := I) P Q hsel i).scalar)
      (q := DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq P.S.scalar
        (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) P.S))
      (qR := DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq
        (hamiltonRescaledSolution (I := I) P Q hsel i).scalar
        (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
          (hamiltonRescaledSolution (I := I) P Q hsel i)))
      (τ := Q.time i) (R := R) hR hscalarDisplay
      (by simpa only [R] using hamilton_rescaled_tracefree_ricci_norm_sq_identity (I := I) P Q hsel i)
      0 x
  have hratio_le :
      q / r ^ 2 ≤ C * (R * r) ^ (-epsilon) := by
    rw [hratio]
    simpa only [q, r, R,
      DifferentialGeometry.PDE.RicciFlow.paraTime_zero, hscalarOld_eq,
      DifferentialGeometry.PDE.RicciFlow.pinchWeight] using
      hest (Q.time i) htimeMem x
  exact scaled_pinch_le hR hr hr1 hC hepsilon0 hepsilon1 hratio_le

def hamiltonWindow
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (r : Real) : Prop :=
  exists N : Nat, forall i : Nat, N <= i ->
    forall s : Real, -(r ^ 2) <= s -> s <= 0 ->
      -(hamiltonBlowupScale (I := I) P Q i * Q.time i) <= s /\ s <= 0

def hamiltonRiemannCurvatureBound
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) : Prop :=
  forall (i : Nat) (s : Real) (x : M),
    -(hamiltonBlowupScale (I := I) P Q i * Q.time i) <= s -> s <= 0 ->
      hamiltonRiemannNormSq (I := I) (M := M) P
          (hamiltonRescaledTime (I := I) P Q i s) x <=
        (100 : Real) ^ 2 * (hamiltonBlowupScale (I := I) P Q i) ^ 2

def hamiltonRescaledInitialTime
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : hamiltonBlowupPointSelection (I := I) P Q) (i : Nat) :
    (paraInterval P.D (Q.time i) (hamiltonBlowupScale (I := I) P Q i)
      (hsel.2.2.1 i)).FlowTime :=
  ⟨0, (paraInterval P.D (Q.time i) (hamiltonBlowupScale (I := I) P Q i)
    (hsel.2.2.1 i)).initial_mem⟩

def hamiltonRescaledBall
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (i : Nat) (r : Real) (hr : 0 < r) :
    Perelman.FlowMetricBall (hamiltonRescaledSolution (I := I) P Q hsel i)
      (hamiltonRescaledInitialTime (I := I) P Q hsel i) where
  center := Q.point i
  radius := r
  radius_pos := hr

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem hamilton_rm_scalar_ctl
    {omega : Real} (h0ω : 0 < omega)
    (hM : isClosedThreeManifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
    (hnonnegative : hamiltonRicciNonnegative (I := I) P omega)
    {t : Real} {x : M} (htD : t ∈ P.D.carrier) :
    0 <= hamiltonScalar (I := I) P t x ∧
      hamiltonRiemannNormSq (I := I) (M := M) P t x <=
        (100 : Real) ^ 2 * (hamiltonScalar (I := I) P t x) ^ 2 := by
  classical
  rcases hM with ⟨_hcompact, _hconnected, _hboundaryless, hdim⟩
  have htD' : t ∈ (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega
    h0ω).carrier := by
    simpa [hD] using htD
  have ht0 : 0 <= t := htD'.1
  have htω : t < omega := htD'.2
  have hricOn := hnonnegative t ht0 htω
  have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  have hricNonneg :
      DifferentialGeometry.Geometry.Curvature.RicciNonnegAt (I := I) (P.S.ricciAt t x) := by
    intro v
    simpa [DifferentialGeometry.Geometry.Curvature.vec2,
      DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricciAt] using
      hricOn t ⟨ht0, le_rfl⟩ x v
  have hricSym :
      DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I) (P.S.ricciAt t x) :=
    DifferentialGeometry.PDE.RicciFlow.ricci_is_symmetric (I := I) (M := M) P.S t x
  have hRmScalar :
      hamiltonRiemannNormSq (I := I) (M := M) P t x <=
        (100 : Real) ^ 2 * (hamiltonScalar (I := I) P t x) ^ 2 := by
    have hpoint :=
      DifferentialGeometry.Geometry.Curvature.normSqLeOfFirstTrace
        (I := I) (M := M) (g := P.S.base.metric t)
        (Ric := P.S.ricciAt t x) (scalar := P.S.scalar t x)
        (Rm04 := P.S.base.rm04 t x) hdimT hricSym hricNonneg
        (fun basis horth =>
          DifferentialGeometry.PDE.RicciFlow.riemann_from_ricci_trace_data (I := I) (M := M) P.S horth)
    simpa [hamiltonRiemannNormSq, hamiltonScalar, hamiltonSolution] using hpoint
  have hscalarNonneg : 0 <= hamiltonScalar (I := I) P t x := by
    rcases DifferentialGeometry.Geometry.Curvature.ricciEigenBasis3
        (I := I) (M := M) (P.S.base.metric t) (P.S.ricciAt t x)
        hdimT hricSym hricNonneg with
      ⟨basis, l1, l2, l3, horth, hdiag, h1, h2, h3⟩
    have hScalarTrace :
        DifferentialGeometry.Geometry.Curvature.ScalarRealizesRicciTraceAt (I := I)
          (P.S.scalar t x) (P.S.ricciAt t x) DifferentialGeometry.Geometry.Curvature.delta3
            basis := by
      have htr :=
        DifferentialGeometry.PDE.RicciFlow.scalarTrace_delta (I := I) (P.S.base.metric t)
          (P.S.ricciAt t x) horth
      simpa [DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_eq_metricTrace] using htr
    have hscalar_eq :
        P.S.scalar t x = DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 :=
      DifferentialGeometry.PDE.RicciFlow.scalar_eq_diag (I := I) hScalarTrace hdiag
    change 0 <= P.S.scalar t x
    rw [hscalar_eq]
    unfold DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3
    nlinarith
  exact ⟨hscalarNonneg, hRmScalar⟩

private theorem scalar_pos_of_rm {R rm : Real}
    (hR : 0 <= R) (hctl : rm <= (100 : Real) ^ 2 * R ^ 2)
    (hrm : 0 < rm) :
    0 < R := by
  by_contra hnot
  have hRle : R <= 0 := le_of_not_gt hnot
  have hR0 : R = 0 := le_antisymm hRle hR
  nlinarith

private theorem scalar_gt_of_rm {A R rm : Real}
    (hA : 0 < A) (hR : 0 <= R)
    (hctl : rm <= (100 : Real) ^ 2 * R ^ 2)
    (hrm : (100 : Real) ^ 2 * A ^ 2 < rm) :
    A < R := by
  have hsq : A ^ 2 < R ^ 2 := by
    nlinarith
  by_contra hnot
  have hRleA : R <= A := le_of_not_gt hnot
  have hdiff : 0 <= A - R := by linarith
  have hsum : 0 <= A + R := by linarith
  have hprod : 0 <= (A - R) * (A + R) :=
    mul_nonneg hdiff hsum
  nlinarith

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem hamilton_scalar_cont_slab
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
    (T : Real) :
    T < omega ->
    ContinuousOn
      (fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
      (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) := by
  intro hTω
  exact hamilton_scalar_slab_continuous_on (I := I) (M := M) h0ω P hD T hTω

omit [SigmaCompactSpace M] [T2Space M] in
private theorem slab_max_of_continuousOn
    [CompactSpace M]
    {f : Real × M -> Real}
    {T t : Real} {x : M}
    (hcont : ContinuousOn f (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T))
    (ht : t ∈ Set.Icc 0 T) :
    ∃ tmax : Real, ∃ xmax : M,
      tmax ∈ Set.Icc 0 T ∧
        ∀ s : Real, s ∈ Set.Icc 0 T -> ∀ y : M,
          f (s, y) <= f (tmax, xmax) := by
  classical
  let slab := DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T
  have hcompact : IsCompact slab := by
    unfold slab DifferentialGeometry.Analysis.Parabolic.spacetimeSlab
    exact isCompact_Icc.prod isCompact_univ
  have hnonempty : slab.Nonempty := ⟨(t, x), ⟨ht, trivial⟩⟩
  rcases hcompact.exists_isMaxOn hnonempty hcont with ⟨p, hp, hmax⟩
  rcases p with ⟨tmax, xmax⟩
  refine ⟨tmax, xmax, hp.1, ?_⟩
  intro s hs y
  exact hmax ⟨hs, trivial⟩

private def hamiltonPointLevel (B : Real) (i : Nat) : Real :=
  max B 0 + ((i : Real) + 1)

private theorem hamiltonPointLevel_pos (B : Real) (i : Nat) :
    0 < hamiltonPointLevel B i := by
  unfold hamiltonPointLevel
  have hmax0 : 0 <= max B 0 := le_max_right B 0
  have hi : 0 < (i : Real) + 1 := by positivity
  linarith

private theorem hamiltonPointLevel_gt_bound (B : Real) (i : Nat) :
    B < hamiltonPointLevel B i := by
  unfold hamiltonPointLevel
  have hB : B <= max B 0 := le_max_left B 0
  have hi : 0 < (i : Real) + 1 := by positivity
  linarith

private theorem hamiltonPointLevel_ge_index (B : Real) (i : Nat) :
    ((i : Real) + 1) <= hamiltonPointLevel B i := by
  unfold hamiltonPointLevel
  have hmax0 : 0 <= max B 0 := le_max_right B 0
  linarith

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_blowup
    {omega : Real} (h0ω : 0 < omega)
    (hM : isClosedThreeManifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
    (hnonnegative : hamiltonRicciNonnegative (I := I) P omega) :
    hamiltonScalarBlowup (I := I) P := by
  intro A
  by_cases hA : 0 < A
  · rcases P.curvUnbounded ((100 : Real) ^ 2 * A ^ 2) with
      ⟨t, x, htD, hRm⟩
    refine ⟨t, x, htD, ?_⟩
    have hRm' :
        (100 : Real) ^ 2 * A ^ 2 <
          hamiltonRiemannNormSq (I := I) (M := M) P t x := by
      simpa [hamiltonRiemannNormSq, hamiltonSolution] using hRm
    have hctl :=
      hamilton_rm_scalar_ctl (I := I) (M := M) h0ω hM P hD hnonnegative
        (t := t) (x := x) htD
    exact scalar_gt_of_rm hA hctl.1 hctl.2 hRm'
  · rcases P.curvUnbounded 0 with ⟨t, x, htD, hRm⟩
    refine ⟨t, x, htD, ?_⟩
    have hRm' : 0 < hamiltonRiemannNormSq (I := I) (M := M) P t x := by
      simpa [hamiltonRiemannNormSq, hamiltonSolution] using hRm
    have hctl :=
      hamilton_rm_scalar_ctl (I := I) (M := M) h0ω hM P hD hnonnegative
        (t := t) (x := x) htD
    have hRpos :
        0 < hamiltonScalar (I := I) P t x :=
      scalar_pos_of_rm hctl.1 hctl.2 hRm'
    exact lt_of_le_of_lt (le_of_not_gt hA) hRpos

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_exists_blowup_point_sequence
    [CompactSpace M]
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
    (hscalarBlowup : hamiltonScalarBlowup (I := I) P) :
    exists Q : HamiltonBlowup M, hamiltonBlowupPointSelection (I := I) P Q := by
  classical
  let half : Real := omega / 2
  have hhalf_pos : 0 < half := by
    dsimp [half]
    linarith
  have hhalf_nonneg : 0 <= half := le_of_lt hhalf_pos
  have hhalf_lt_omega : half < omega := by
    dsimp [half]
    linarith
  have hcont_half :
      ContinuousOn
        (fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
        (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) half) :=
    hamilton_scalar_cont_slab (I := I) (M := M) h0ω P hD half hhalf_lt_omega
  have hbounded_half :
      DifferentialGeometry.PDE.RicciFlow.ScalarBoundedAboveOnSlab
        (M := M) (hamiltonScalar (I := I) P) half :=
    DifferentialGeometry.PDE.RicciFlow.ScalarBoundedAboveOnSlab.of_continuousOn
      (M := M) hcont_half
  rcases hbounded_half with ⟨Bhalf, hBhalf⟩
  let level : Nat -> Real := fun i => hamiltonPointLevel Bhalf i
  have hraw : ∀ i : Nat, ∃ t : Real, ∃ x : M,
      t ∈ P.D.carrier /\ level i < hamiltonScalar (I := I) P t x := by
    intro i
    exact hscalarBlowup (level i)
  let rawTime : Nat -> Real := fun i => Classical.choose (hraw i)
  let rawPoint : Nat -> M := fun i =>
    Classical.choose (Classical.choose_spec (hraw i))
  have hraw_spec : ∀ i : Nat,
      rawTime i ∈ P.D.carrier /\
        level i < hamiltonScalar (I := I) P (rawTime i) (rawPoint i) := by
    intro i
    simpa [rawTime, rawPoint] using
      Classical.choose_spec (Classical.choose_spec (hraw i))
  have hraw_nonneg : ∀ i : Nat, 0 <= rawTime i := by
    intro i
    have hmem : rawTime i ∈
        (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega
          h0ω).carrier := by
      simpa [hD] using (hraw_spec i).1
    exact hmem.1
  have hraw_lt_omega : ∀ i : Nat, rawTime i < omega := by
    intro i
    have hmem : rawTime i ∈
        (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega
          h0ω).carrier := by
      simpa [hD] using (hraw_spec i).1
    exact hmem.2
  have hmax_exists : ∀ i : Nat, ∃ tmax : Real, ∃ xmax : M,
      tmax ∈ Set.Icc 0 (rawTime i) ∧
        ∀ s : Real, s ∈ Set.Icc 0 (rawTime i) -> ∀ y : M,
          hamiltonScalar (I := I) P s y <=
            hamiltonScalar (I := I) P tmax xmax := by
    intro i
    exact slab_max_of_continuousOn (M := M)
      (f := fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
      (T := rawTime i) (t := rawTime i) (x := rawPoint i)
      (hamilton_scalar_cont_slab (I := I) (M := M) h0ω P hD (rawTime i) (hraw_lt_omega i))
      ⟨hraw_nonneg i, le_rfl⟩
  let qTime : Nat -> Real := fun i => Classical.choose (hmax_exists i)
  let qPoint : Nat -> M := fun i =>
    Classical.choose (Classical.choose_spec (hmax_exists i))
  have hq_spec : ∀ i : Nat,
      qTime i ∈ Set.Icc 0 (rawTime i) ∧
        ∀ s : Real, s ∈ Set.Icc 0 (rawTime i) -> ∀ y : M,
          hamiltonScalar (I := I) P s y <=
            hamiltonScalar (I := I) P (qTime i) (qPoint i) := by
    intro i
    simpa [qTime, qPoint] using
      Classical.choose_spec (Classical.choose_spec (hmax_exists i))
  let Q : HamiltonBlowup M := ⟨qPoint, qTime⟩
  refine ⟨Q, ?_⟩
  have hscale_lower : ∀ i : Nat,
      level i < hamiltonBlowupScale (I := I) P Q i := by
    intro i
    have hraw_le :=
      (hq_spec i).2 (rawTime i) ⟨hraw_nonneg i, le_rfl⟩ (rawPoint i)
    exact lt_of_lt_of_le (hraw_spec i).2 hraw_le
  have hscale_pos : ∀ i : Nat, 0 < hamiltonBlowupScale (I := I) P Q i := by
    intro i
    exact lt_trans (hamiltonPointLevel_pos Bhalf i) (hscale_lower i)
  have hq_gt_half : ∀ i : Nat, half < Q.time i := by
    intro i
    by_contra hnot
    have hle : Q.time i <= half := le_of_not_gt hnot
    have hmem_half : Q.time i ∈ Set.Icc 0 half :=
      ⟨(hq_spec i).1.1, hle⟩
    have hupper := hBhalf (Q.time i) hmem_half (Q.point i)
    have hB_lt_level : Bhalf < level i :=
      hamiltonPointLevel_gt_bound Bhalf i
    exact not_lt_of_ge hupper (lt_trans hB_lt_level (hscale_lower i))
  have htime_pos : ∀ i : Nat, 0 < Q.time i := by
    intro i
    exact lt_trans hhalf_pos (hq_gt_half i)
  have htime_mem : ∀ i : Nat, Q.time i ∈ P.D.carrier := by
    intro i
    rw [hD]
    exact ⟨(hq_spec i).1.1,
      lt_of_le_of_lt (hq_spec i).1.2 (hraw_lt_omega i)⟩
  refine ⟨hscale_pos, htime_pos, htime_mem, ?_, ?_, ?_⟩
  · intro A
    obtain ⟨N, hN⟩ := exists_nat_ge (A / half)
    refine ⟨N, ?_⟩
    intro i hi
    have hNi : (N : Real) <= i := by exact_mod_cast hi
    have hA_le_Nhalf : A <= (N : Real) * half := by
      have hm := mul_le_mul_of_nonneg_right hN hhalf_nonneg
      simpa [div_mul_cancel₀ A (ne_of_gt hhalf_pos)] using hm
    have hNhalf_le_ihalf : (N : Real) * half <= (i : Real) * half :=
      mul_le_mul_of_nonneg_right hNi hhalf_nonneg
    have hihalf_le_i1half : (i : Real) * half <= ((i : Real) + 1) * half := by
      nlinarith [hhalf_nonneg]
    have hi1half_le_levelhalf :
        ((i : Real) + 1) * half <= level i * half :=
      mul_le_mul_of_nonneg_right
        (hamiltonPointLevel_ge_index Bhalf i) hhalf_nonneg
    have hprod_gt : level i * half <
        hamiltonBlowupScale (I := I) P Q i * Q.time i := by
      nlinarith [hscale_lower i, hq_gt_half i,
        le_of_lt (hamiltonPointLevel_pos Bhalf i), hhalf_pos]
    exact le_of_lt
      (lt_of_le_of_lt
        (le_trans hA_le_Nhalf
          (le_trans hNhalf_le_ihalf
            (le_trans hihalf_le_i1half hi1half_le_levelhalf)))
        hprod_gt)
  · intro i
    have hscale_ne : hamiltonBlowupScale (I := I) P Q i ≠ 0 :=
      ne_of_gt (hscale_pos i)
    have htime0 : hamiltonRescaledTime (I := I) P Q i 0 = Q.time i := by
      dsimp [hamiltonRescaledTime]
      field_simp [hscale_ne]
      ring
    have hscalar0 :
        hamiltonScalar (I := I) P
            (hamiltonRescaledTime (I := I) P Q i 0) (Q.point i) =
          hamiltonBlowupScale (I := I) P Q i := by
      rw [htime0]
      rfl
    dsimp [hamiltonRescaledScalar]
    rw [hscalar0]
    field_simp [hscale_ne]
  · intro i s x hsleft hsright
    have hscale_ne : hamiltonBlowupScale (I := I) P Q i ≠ 0 :=
      ne_of_gt (hscale_pos i)
    have htau_mem : hamiltonRescaledTime (I := I) P Q i s ∈
        Set.Icc 0 (Q.time i) := by
      constructor
      · dsimp [hamiltonRescaledTime]
        have hdiv :
            -Q.time i <= s / hamiltonBlowupScale (I := I) P Q i := by
          have hdiv' :
              -(hamiltonBlowupScale (I := I) P Q i * Q.time i) /
                  hamiltonBlowupScale (I := I) P Q i <=
                s / hamiltonBlowupScale (I := I) P Q i :=
            div_le_div_of_nonneg_right hsleft (le_of_lt (hscale_pos i))
          have hleft :
              -(hamiltonBlowupScale (I := I) P Q i * Q.time i) /
                  hamiltonBlowupScale (I := I) P Q i = -Q.time i := by
            field_simp [hscale_ne]
          simpa [hleft] using hdiv'
        linarith
      · dsimp [hamiltonRescaledTime]
        have hdiv : s / hamiltonBlowupScale (I := I) P Q i <= 0 := by
          exact div_nonpos_of_nonpos_of_nonneg hsright (le_of_lt (hscale_pos i))
        linarith
    have htau_raw : hamiltonRescaledTime (I := I) P Q i s ∈
        Set.Icc 0 (rawTime i) :=
      ⟨htau_mem.1, le_trans htau_mem.2 (hq_spec i).1.2⟩
    have hscalar_le :
        hamiltonScalar (I := I) P (hamiltonRescaledTime (I := I) P Q i s) x <=
          hamiltonBlowupScale (I := I) P Q i :=
      (hq_spec i).2 (hamiltonRescaledTime (I := I) P Q i s) htau_raw x
    dsimp [hamiltonRescaledScalar]
    have hmul :=
      mul_le_mul_of_nonneg_left hscalar_le
        (inv_nonneg.mpr (le_of_lt (hscale_pos i)))
    have hone :
        (hamiltonBlowupScale (I := I) P Q i)⁻¹ *
            hamiltonBlowupScale (I := I) P Q i = 1 := by
      field_simp [hscale_ne]
    simpa [hone] using hmul

omit [NeZero (Module.finrank ℝ E)] in
theorem hamilton_fixed_pinching
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : isClosedThreeManifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (hpos : positiveRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    hamiltonFixedPinching (I := I) P omega := by
  rcases hM with ⟨hcompact, hconnected, hboundaryless, hdim⟩
  let : CompactSpace M := hcompact
  let : ConnectedSpace M := hconnected
  let : I.Boundaryless := hboundaryless
  let : Nonempty M := inferInstance
  have hpos0 :
      DifferentialGeometry.PDE.RicciFlow.RicciPosInit (I := I) (M := M)
        (DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M)
          P.S.ricci) :=
    hamilton_initial_ricci_positive (I := I) (M := M) h0ω hpos P hD
  have hinit : DifferentialGeometry.PDE.RicciFlow.PinchInitLt (I := I) (M := M)
      (fun t : Real => P.S.base.metric t)
      (DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M) P.S.ricci)
      P.S.scalar :=
    DifferentialGeometry.PDE.RicciFlow.pinchInitLt_pos (I := I) (M := M)
      (G := fun t : Real => P.S.base.metric t)
      (Ric := DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M)
        P.S.ricci)
      (scalar := P.S.scalar)
      (DifferentialGeometry.PDE.RicciFlow.initialMetricRicciDataOfSolution
        (I := I) (M := M) P.S)
      (DifferentialGeometry.PDE.RicciFlow.initial_metric_ricci_data_positive
        (I := I) (M := M) P.S hpos0)
      (DifferentialGeometry.PDE.RicciFlow.initial_scalar_curvature_continuous_of_solution
        (I := I) (M := M) P.S
        P.isSmooth.isSolution
        (by
          rw [hD]
          exact ⟨le_rfl, h0ω⟩))
  rcases hinit with ⟨delta, hdelta0, hdelta13, hpinch0⟩
  refine ⟨delta, hdelta0, hdelta13, ?_⟩
  intro T hT hTω
  have hdimT : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3 := by
    intro x
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  have hTsub : Set.Icc 0 T ⊆ P.D.carrier := by
    intro t ht
    rw [hD]
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩
  have hTreg : Set.Ioc 0 T ⊆ P.D.regular := by
    intro t ht
    rw [hD]
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩
  exact DifferentialGeometry.PDE.RicciFlow.pinch_sol_closed (I := I) (M := M) (S := P.S)
    P.isSmooth hT hdelta13 hdimT hTsub hTreg hpinch0

omit [NeZero (Module.finrank ℝ E)] in
theorem hamilton_ricci_nonnegative
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : isClosedThreeManifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (hpos : positiveRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    hamiltonRicciNonnegative (I := I) P omega := by
  rcases hM with ⟨hcompact, hconnected, hboundaryless, hdim⟩
  let : CompactSpace M := hcompact
  let : ConnectedSpace M := hconnected
  let : I.Boundaryless := hboundaryless
  let : Nonempty M := inferInstance
  have hpos0 := hamilton_initial_ricci_positive (I := I) (M := M) h0ω hpos P hD
  have hinit : DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyNonnegativeAtTime
      (I := I) (M := M)
      (DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M) P.S.ricci)
        0 := by
    intro x v
    by_cases hv : v = 0
    · subst v
      have hbilin := DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily_bilin
        (I := I) (M := M) P.S.ricci 0 x
      have hzero :
          (DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M)
            P.S.ricci)
              0 x 0 0 = 0 := by
        have h := hbilin.smul_left 0
          (0 : TangentSpace I x) (0 : TangentSpace I x)
        simpa using h
      rw [hzero]
    · exact le_of_lt (hpos0 x v hv)
  intro T hT hTω
  have hdimT : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3 := by
    intro x
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  have hTsub : Set.Icc 0 T ⊆ P.D.carrier := by
    intro t ht
    rw [hD]
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩
  have hTreg : Set.Ioc 0 T ⊆ P.D.regular := by
    intro t ht
    rw [hD]
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩
  exact DifferentialGeometry.PDE.RicciFlow.ricci_nonnegative_of_closed_solution_wmp_data
    (I := I) (M := M) (S := P.S)
    P.isSmooth hT hdimT hTsub hTreg hinit

omit [NeZero (Module.finrank ℝ E)] in
theorem hamilton_rescaled_ricci_nonnegative
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : isClosedThreeManifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : positiveRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q) :
    hamiltonRescaledRicciNonnegative (I := I) P Q := by
  rcases hsel with ⟨hscale, htime, htimeMem, _hprod, _hbase, _hscalarMax⟩
  have hricOn : hamiltonRicciNonnegative (I := I) P omega :=
    hamilton_ricci_nonnegative (I := I) (M := M) h0ω hM hpos P hD
  intro i s x v hsleft hsright
  have hQiω : Q.time i < omega := by
    have hmem := htimeMem i
    rw [hD] at hmem
    exact hmem.2
  have hnonneg :=
    hricOn (Q.time i) (le_of_lt (htime i)) hQiω
  have hscale_ne : hamiltonBlowupScale (I := I) P Q i ≠ 0 :=
    ne_of_gt (hscale i)
  have hsdiv :
      -Q.time i <= s / hamiltonBlowupScale (I := I) P Q i := by
    have hdiv := div_le_div_of_nonneg_right hsleft (le_of_lt (hscale i))
    have hcancel :
        -(hamiltonBlowupScale (I := I) P Q i * Q.time i) /
            hamiltonBlowupScale (I := I) P Q i = -Q.time i := by
      field_simp [hscale_ne]
    rwa [hcancel] at hdiv
  have htau0 :
      0 <= hamiltonRescaledTime (I := I) P Q i s := by
    dsimp [hamiltonRescaledTime]
    linarith
  have htauT :
      hamiltonRescaledTime (I := I) P Q i s <= Q.time i := by
    dsimp [hamiltonRescaledTime]
    have hsdiv_nonpos :
        s / hamiltonBlowupScale (I := I) P Q i <= 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hsright (le_of_lt (hscale i))
    linarith
  have htau : hamiltonRescaledTime (I := I) P Q i s ∈ Set.Icc 0 (Q.time i) :=
    ⟨htau0, htauT⟩
  have hraw := hnonneg (hamiltonRescaledTime (I := I) P Q i s) htau x v
  simpa [DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily,
    DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricci,
    DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricciAt,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.ricci,
    DifferentialGeometry.PDE.RicciFlow.SolutionFamily.ricciAt] using hraw

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_positive
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {omega : Real} (h0ω : 0 < omega)
    (hM : isClosedThreeManifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : positiveRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    ∀ t : Real, t ∈ P.D.carrier -> ∀ x : M, 0 < P.S.scalar t x := by
  classical
  rcases hM with ⟨hcompact, _hconnected, hboundaryless, hdim⟩
  let : CompactSpace M := hcompact
  let : I.Boundaryless := hboundaryless
  let : Nonempty M := inferInstance
  rcases hamilton_initial_scalar_minimum (I := I) (M := M) hdim h0ω hpos P hD with
    ⟨c0, hinit_min, hinit_pos⟩
  have hcont :
      forall T : Real, 0 <= T -> T < omega ->
        ContinuousOn (fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
          (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) := by
    intro T _hT hTω
    exact hamilton_scalar_slab_continuous_on (I := I) (M := M) h0ω P hD T hTω
  have hc0 : 0 < c0 :=
    DifferentialGeometry.PDE.RicciFlow.InitialScalarMinimum.pos_of_forall_pos
      (M := M) hinit_min hinit_pos
  rcases hamilton_scalar_slab_lipschitz (I := I) (M := M) (omega := omega) P c0 hc0 hcont with
    ⟨K, hK⟩
  have hreg :
      ∀ T : Real, 0 < T -> T < omega ->
        T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
          DifferentialGeometry.PDE.RicciFlow.ScalarLowerBoundWMPRegularity
            (I := I) (hamiltonMetricConnectionFamily (I := I) P) T 3 c0
            (hamiltonScalar (I := I) P) (K T) := by
    intro T _hT hTω hPole
    exact hamilton_scalar_weak_maximum_principle_regularity
      (I := I) (M := M) h0ω P hD c0 hc0 K T hTω hPole
  have hevol :
      DifferentialGeometry.PDE.RicciFlow.ScalarEvolutionEquationOn
        (D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
        (hamiltonScalar (I := I) P)
        (hamiltonScalarLaplacian (I := I) P)
        (hamiltonRicciNormSq (I := I) P) :=
    hamilton_scalar_evolution_equation (I := I) (M := M) h0ω P hD
  have hlap :
      ∀ T : Real, 0 < T -> T < omega ->
        T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
          DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn
            (I := I) (hamiltonMetricConnectionFamily (I := I) P) T
            (hamiltonScalar (I := I) P)
            (hamiltonScalarLaplacian (I := I) P) := by
    intro T _hT _hTω _hPole
    exact hamilton_scalar_laplacian_realizes_heat (I := I) (M := M) P T
  have hricci :
      ∀ T : Real, 0 < T -> T < omega ->
        T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
          ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
            (1 / 3 : Real) * (hamiltonScalar (I := I) P t x) ^ 2 <=
              hamiltonRicciNormSq (I := I) P t x := by
    intro _T _hT _hTω _hPole t _ht x
    exact hamilton_scalar_sq_le_three_ricci_norm_sq (I := I) (M := M) hdim P t x
  have hF :
      ∀ T : Real, 0 < T -> T < omega ->
        T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
          ∀ t : Real, t ∈ Set.Icc 0 T ->
            LipschitzOnWith (K T)
              (fun a : Real => DifferentialGeometry.PDE.RicciFlow.scalarLowerReaction 3 a)
              (DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet (M := M) T
                (hamiltonScalar (I := I) P)
                (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0)) := by
    intro T hT hTω hPole
    exact hK T hT hTω hPole
  have hfinite :
      omega <= DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 := by
    have hfin := DifferentialGeometry.PDE.RicciFlow.finiteTime3D (I := I) (M := M)
      h0ω (hamiltonMetricConnectionFamily (I := I) P) c0
      (hamiltonScalar (I := I) P) (hamiltonScalarLaplacian (I := I) P)
      (hamiltonRicciNormSq (I := I) P) K hinit_min hinit_pos hcont
      hreg hevol hlap hricci hF
    simpa [DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime] using hfin.2
  have hlower :
      DifferentialGeometry.PDE.RicciFlow.ScalarLowerBarrierBoundUpToPole
        (M := M) (hamiltonScalar (I := I) P) 3 c0 omega :=
    DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrierBoundUpToPole_of_scalarEvolution_closedOpen
      (I := I) h0ω (hamiltonMetricConnectionFamily (I := I) P) 3 c0 (by norm_num)
      hc0 (hamiltonScalar (I := I) P) (hamiltonScalarLaplacian (I := I) P)
      (hamiltonRicciNormSq (I := I) P) K hreg hevol hlap hricci
      (DifferentialGeometry.PDE.RicciFlow.InitialScalarMinimum.lowerBound (M := M) hinit_min) hF
  intro t htD x
  have ht_closed :
      t ∈ (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega
        h0ω).carrier := by
    simpa [hD] using htD
  rcases ht_closed with ⟨ht0, htω⟩
  by_cases ht_zero : t = 0
  · have h0 := hinit_pos x
    simpa [hamiltonScalar, hamiltonSolution, ht_zero] using h0
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_zero)
    have htblow : t < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 :=
      lt_of_lt_of_le htω hfinite
    have hbound :
        DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0 t <=
          hamiltonScalar (I := I) P t x :=
      hlower t htpos htω htblow x
    have hden :
        0 < 1 - (2 / (3 : Real)) * c0 * t :=
      DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier_denominator_pos_of_lt_blowup
        (n := 3) (c0 := c0) (by norm_num) hc0 htblow
    have hpos_t :
        0 < hamiltonScalar (I := I) P t x :=
      DifferentialGeometry.PDE.RicciFlow.scalar_curvature_positive_of_lower_barrier
        (n := 3) (c0 := c0) (t := t) hbound hc0 hden
    simpa [hamiltonScalar, hamiltonSolution] using hpos_t

omit [NeZero (Module.finrank ℝ E)] in
theorem hamilton_pinching_implies_pinch_estimate
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : isClosedThreeManifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : positiveRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    hamiltonPinchingEstimate (I := I) P := by
  rcases hM with ⟨hcompact, hconnected, hboundaryless, hdim⟩
  let : CompactSpace M := hcompact
  let : ConnectedSpace M := hconnected
  let : I.Boundaryless := hboundaryless
  let : Nonempty M := inferInstance
  have hdimT : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3 := by
    intro x
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  have hfixed : hamiltonFixedPinching (I := I) P omega :=
    hamilton_fixed_pinching (I := I) (M := M) h0ω
      ⟨hcompact, hconnected, hboundaryless, hdim⟩ hpos P hD
  have hnonneg : hamiltonRicciNonnegative (I := I) P omega :=
    hamilton_ricci_nonnegative (I := I) (M := M) h0ω
      ⟨hcompact, hconnected, hboundaryless, hdim⟩ hpos P hD
  have hscalar :
      ∀ t : Real, t ∈ P.D.carrier -> ∀ x : M, 0 < P.S.scalar t x :=
    hamilton_scalar_positive (I := I) (M := M) h0ω
      ⟨hcompact, hconnected, hboundaryless, hdim⟩ g0 hpos P hD
  rcases DifferentialGeometry.PDE.RicciFlow.exists_pinching_estimate_of_smooth_solution (I := I) (M := M)
      P.S P.isSmooth h0ω hD hdimT hscalar hfixed hnonneg with
    ⟨epsilon, C, heps0, heps1, hC0, hest⟩
  exact ⟨epsilon, C, heps0, heps1, hC0, hest⟩

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_rescaled_curvature_bound
    (hM : isClosedThreeManifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hric : hamiltonRescaledRicciNonnegative (I := I) P Q) :
    hamiltonRiemannCurvatureBound (I := I) P Q := by
  classical
  rcases hM with ⟨_hcompact, _hconnected, _hboundaryless, hdim⟩
  rcases hsel with ⟨hscale, _htime, _htimeMem, _hprod, _hbase, hscalarMax⟩
  intro i s x hsleft hsright
  let τ : Real := hamiltonRescaledTime (I := I) P Q i s
  have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  have hricNonneg :
      DifferentialGeometry.Geometry.Curvature.RicciNonnegAt (I := I) (P.S.ricciAt τ x) := by
    intro v
    simpa [τ, DifferentialGeometry.Geometry.Curvature.vec2,
      DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricciAt] using
      hric i s x v hsleft hsright
  have hricSym :
      DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I) (P.S.ricciAt τ x) :=
    DifferentialGeometry.PDE.RicciFlow.ricci_is_symmetric (I := I) (M := M) P.S τ x
  have hRmScalar :
      hamiltonRiemannNormSq (I := I) (M := M) P τ x <=
        (100 : Real) ^ 2 * (hamiltonScalar (I := I) P τ x) ^ 2 := by
    have hpoint :=
      DifferentialGeometry.Geometry.Curvature.normSqLeOfFirstTrace
        (I := I) (M := M) (g := P.S.base.metric τ)
        (Ric := P.S.ricciAt τ x) (scalar := P.S.scalar τ x)
        (Rm04 := P.S.base.rm04 τ x) hdimT hricSym hricNonneg
        (fun basis horth =>
          DifferentialGeometry.PDE.RicciFlow.riemann_from_ricci_trace_data (I := I) (M := M) P.S horth)
    simpa [hamiltonRiemannNormSq, hamiltonScalar, hamiltonSolution, τ] using hpoint
  have hscalarNonneg : 0 <= hamiltonScalar (I := I) P τ x := by
    rcases DifferentialGeometry.Geometry.Curvature.ricciEigenBasis3
        (I := I) (M := M) (P.S.base.metric τ) (P.S.ricciAt τ x)
        hdimT hricSym hricNonneg with
      ⟨basis, l1, l2, l3, horth, hdiag, h1, h2, h3⟩
    have hScalarTrace :
        DifferentialGeometry.Geometry.Curvature.ScalarRealizesRicciTraceAt (I := I)
          (P.S.scalar τ x) (P.S.ricciAt τ x) DifferentialGeometry.Geometry.Curvature.delta3
            basis := by
      have htr :=
        DifferentialGeometry.PDE.RicciFlow.scalarTrace_delta (I := I) (P.S.base.metric τ)
          (P.S.ricciAt τ x) horth
      simpa [DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_eq_metricTrace] using htr
    have hscalar_eq :
        P.S.scalar τ x = DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 :=
      DifferentialGeometry.PDE.RicciFlow.scalar_eq_diag (I := I) hScalarTrace hdiag
    change 0 <= P.S.scalar τ x
    rw [hscalar_eq]
    unfold DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3
    nlinarith
  have hscalarUpper :
      hamiltonScalar (I := I) P τ x <= hamiltonBlowupScale (I := I) P Q i := by
    have hraw := hscalarMax i s x hsleft hsright
    have hmul :=
      mul_le_mul_of_nonneg_left hraw (le_of_lt (hscale i))
    have hleft :
        hamiltonBlowupScale (I := I) P Q i *
            hamiltonRescaledScalar (I := I) P Q i s x =
          hamiltonScalar (I := I) P τ x := by
      dsimp [hamiltonRescaledScalar, τ]
      field_simp [ne_of_gt (hscale i)]
    have hright :
        hamiltonBlowupScale (I := I) P Q i * (1 : Real) =
          hamiltonBlowupScale (I := I) P Q i := by
      ring
    simpa [hleft, hright] using hmul
  have hscalarSq :
      (hamiltonScalar (I := I) P τ x) ^ 2 <=
        (hamiltonBlowupScale (I := I) P Q i) ^ 2 := by
    have hdiff :
        0 <= hamiltonBlowupScale (I := I) P Q i -
          hamiltonScalar (I := I) P τ x := by
      linarith
    have hsum :
        0 <= hamiltonBlowupScale (I := I) P Q i +
          hamiltonScalar (I := I) P τ x := by
      nlinarith [hscalarNonneg, le_of_lt (hscale i)]
    have hprod :
        0 <=
          (hamiltonBlowupScale (I := I) P Q i -
              hamiltonScalar (I := I) P τ x) *
            (hamiltonBlowupScale (I := I) P Q i +
              hamiltonScalar (I := I) P τ x) :=
      mul_nonneg hdiff hsum
    nlinarith
  have hscaled :
      (100 : Real) ^ 2 * (hamiltonScalar (I := I) P τ x) ^ 2 <=
        (100 : Real) ^ 2 * (hamiltonBlowupScale (I := I) P Q i) ^ 2 :=
    mul_le_mul_of_nonneg_left hscalarSq (by norm_num)
  exact le_trans hRmScalar hscaled

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_reference_radius_window
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q) :
    hamiltonWindow (I := I) P Q hamiltonReferenceRadius := by
  rcases hsel with ⟨_hscale, _htime, _htimeMem, hprod, _hbase, _hscalarMax⟩
  rcases hprod (hamiltonReferenceRadius ^ 2) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i hi s hsleft hsright
  have hprod_i :
      hamiltonReferenceRadius ^ 2 <= hamiltonBlowupScale (I := I) P Q i * Q.time i := hN i hi
  constructor
  · linarith
  · exact hsright

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_blowup_scale_tendsto_at_top
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
      0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q) :
    Filter.Tendsto (hamiltonBlowupScale (I := I) P Q)
      Filter.atTop Filter.atTop := by
  rcases hsel with ⟨hscale, _htime, htimeMem, hprod, _hbase, _hscalarMax⟩
  rw [Filter.tendsto_atTop]
  intro A
  rcases hprod (A * omega) with ⟨N, hN⟩
  filter_upwards [Filter.eventually_atTop.2 ⟨N, fun i hi => hi⟩] with i hi
  have hprod_i :
      A * omega ≤ hamiltonBlowupScale (I := I) P Q i * Q.time i :=
    hN i hi
  have htime_i := htimeMem i
  rw [hD] at htime_i
  have hlt :
      hamiltonBlowupScale (I := I) P Q i * Q.time i <
        hamiltonBlowupScale (I := I) P Q i * omega :=
    mul_lt_mul_of_pos_left htime_i.2 (hscale i)
  exact le_of_lt
    (lt_of_mul_lt_mul_right (lt_of_le_of_lt hprod_i hlt) h0omega.le)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_rescaled_pinching_error_tendsto_zero
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
      0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (L : HamiltonCGHLimit (I := I) M)
    {epsilon C : Real} (hepsilon : 0 < epsilon) :
    Filter.Tendsto
      (fun k : Nat =>
        C * hamiltonBlowupScale (I := I) P Q (L.subseq k) ^ (-epsilon))
      Filter.atTop (nhds 0) := by
  have hscale :
      Filter.Tendsto
        (fun k : Nat => hamiltonBlowupScale (I := I) P Q (L.subseq k))
        Filter.atTop Filter.atTop :=
    (hamilton_blowup_scale_tendsto_at_top (I := I) h0omega P hD Q hsel).comp
      L.subseq_strict.tendsto_atTop
  have hpow :
      Filter.Tendsto
        (fun k : Nat =>
          hamiltonBlowupScale (I := I) P Q (L.subseq k) ^ (-epsilon))
        Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hepsilon).comp hscale
  simpa only [mul_zero] using tendsto_const_nhds.mul hpow

end HamiltonPositiveRicci
end DifferentialGeometry.PDE.RicciFlow
