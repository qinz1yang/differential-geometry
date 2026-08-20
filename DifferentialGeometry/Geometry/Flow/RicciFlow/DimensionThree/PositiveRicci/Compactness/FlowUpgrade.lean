import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.RicciFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Construction
import DifferentialGeometry.Geometry.Metric.Convergence.PullbackCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.TracefreeRicciPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.Estimate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CurvatureTowerBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.Local
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.FlowUniformEquivalence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.FixedDomainBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.NoncollapseInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.BoundedGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.SourceCovariantLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.SourceCovariantLipschitzBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Completeness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Limit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.WindowEquivalence
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.PositiveRicci.Blowup
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.EarlyTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ScaleTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.CanonicalCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.BoundedGeometryCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
private theorem srm_eq_of_inner
    {g g' : SmoothRiemannianMetric I M}
    (h : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = g'.inner x v w) :
    g = g' := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g'
  have hi : i₁ = i₂ :=
    funext fun x =>
      ContinuousLinearMap.ext fun v =>
        ContinuousLinearMap.ext fun w => h x v w
  subst hi
  rfl

private def hamiltonCommonD :
    DifferentialGeometry.Geometry.Curvature.RealTimeInterval :=
  DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closed
    (-(hamilton_reference_radius ^ 2)) 0 (neg_nonpos.mpr (sq_nonneg hamilton_reference_radius))

private def hamiltonShiLeft : Real :=
  -(2 * hamilton_reference_radius ^ 2)

private noncomputable def hamiltonWinStart
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius) : Nat :=
  Classical.choose hwindow

private noncomputable def hamiltonBufStart
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q) : Nat :=
  Classical.choose (hsel.2.2.2.1 (2 * hamilton_reference_radius ^ 2))

private noncomputable def hamiltonStart
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius) : Nat :=
  max (hamiltonWinStart (I := I) P Q hwindow) (hamiltonBufStart (I := I) P Q hsel)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem hamiltonStart_spec
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius) :
    ∀ i : Nat, hamiltonStart (I := I) P Q hsel hwindow ≤ i →
      ∀ s : Real, -(hamilton_reference_radius ^ 2) ≤ s → s ≤ 0 →
        -(hamiltonBlowupScale (I := I) P Q i * Q.time i) ≤ s ∧ s ≤ 0 :=
  fun i hi s hs h0 =>
    Classical.choose_spec hwindow i
      (le_trans (Nat.le_max_left _ _) hi) s hs h0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem hamiltonBuf_spec
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius) :
    ∀ i : Nat, hamiltonStart (I := I) P Q hsel hwindow ≤ i →
      2 * hamilton_reference_radius ^ 2 ≤
        hamiltonBlowupScale (I := I) P Q i * Q.time i :=
  fun i hi =>
    Classical.choose_spec (hsel.2.2.2.1 (2 * hamilton_reference_radius ^ 2)) i
      (le_trans (Nat.le_max_right _ _) hi)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem hamilton_car_subset
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius)
    (i : Nat) :
    hamiltonCommonD.carrier ⊆
      (DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
        (Q.time (hamiltonStart (I := I) P Q hsel hwindow + i))
        (hamiltonBlowupScale (I := I) P Q
          (hamiltonStart (I := I) P Q hsel hwindow + i))
        (hsel.1 (hamiltonStart (I := I) P Q hsel hwindow + i))
        (hsel.2.2.1 (hamiltonStart (I := I) P Q hsel hwindow + i))).carrier := by
  intro s hs
  change s ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 at hs
  let j := hamiltonStart (I := I) P Q hsel hwindow + i
  have hj : hamiltonStart (I := I) P Q hsel hwindow ≤ j := by
    simpa only [j] using
      Nat.le_add_right (hamiltonStart (I := I) P Q hsel hwindow) i
  have hw := hamiltonStart_spec (I := I) P Q hsel hwindow j hj s hs.1 hs.2
  rw [DifferentialGeometry.PDE.RicciFlow.paraInterval_carrier]
  change hamiltonRescaledTime (I := I) P Q j s ∈ P.D.carrier
  rw [hD]
  have hscale := hsel.1 j
  have htimeMem := hsel.2.2.1 j
  rw [hD] at htimeMem
  have hnum : 0 ≤ hamiltonBlowupScale (I := I) P Q j * Q.time j + s := by
    linarith [hw.1]
  have hlo : 0 ≤ hamiltonRescaledTime (I := I) P Q j s := by
    rw [show hamiltonRescaledTime (I := I) P Q j s =
        (hamiltonBlowupScale (I := I) P Q j * Q.time j + s) /
          hamiltonBlowupScale (I := I) P Q j by
      unfold hamiltonRescaledTime
      field_simp [ne_of_gt hscale]]
    exact div_nonneg hnum hscale.le
  have hsdiv : s / hamiltonBlowupScale (I := I) P Q j ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hw.2 hscale.le
  have hhi : hamiltonRescaledTime (I := I) P Q j s < omega := by
    unfold hamiltonRescaledTime
    linarith [htimeMem.2, hsdiv]
  exact ⟨hlo, hhi⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem hamilton_reg_subset
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius)
    (i : Nat) :
    hamiltonCommonD.regular ⊆
      (DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
        (Q.time (hamiltonStart (I := I) P Q hsel hwindow + i))
        (hamiltonBlowupScale (I := I) P Q
          (hamiltonStart (I := I) P Q hsel hwindow + i))
        (hsel.1 (hamiltonStart (I := I) P Q hsel hwindow + i))
        (hsel.2.2.1 (hamiltonStart (I := I) P Q hsel hwindow + i))).regular := by
  intro s hs
  change s ∈ Set.Ioo (-(hamilton_reference_radius ^ 2)) 0 at hs
  let j := hamiltonStart (I := I) P Q hsel hwindow + i
  have hj : hamiltonStart (I := I) P Q hsel hwindow ≤ j := by
    simpa only [j] using
      Nat.le_add_right (hamiltonStart (I := I) P Q hsel hwindow) i
  have hw0 :=
    hamiltonStart_spec (I := I) P Q hsel hwindow j hj (-(hamilton_reference_radius ^ 2))
      le_rfl (neg_nonpos.mpr (sq_nonneg hamilton_reference_radius))
  rw [DifferentialGeometry.PDE.RicciFlow.paraInterval_regular]
  change hamiltonRescaledTime (I := I) P Q j s ∈ P.D.regular
  rw [hD]
  have hscale := hsel.1 j
  have htimeMem := hsel.2.2.1 j
  rw [hD] at htimeMem
  have hnum : 0 < hamiltonBlowupScale (I := I) P Q j * Q.time j + s := by
    linarith [hw0.1, hs.1]
  have hlo : 0 < hamiltonRescaledTime (I := I) P Q j s := by
    rw [show hamiltonRescaledTime (I := I) P Q j s =
        (hamiltonBlowupScale (I := I) P Q j * Q.time j + s) /
          hamiltonBlowupScale (I := I) P Q j by
      unfold hamiltonRescaledTime
      field_simp [ne_of_gt hscale]]
    exact div_pos hnum hscale
  have hsdiv : s / hamiltonBlowupScale (I := I) P Q j < 0 :=
    div_neg_of_neg_of_pos hs.2 hscale
  have hhi : hamiltonRescaledTime (I := I) P Q j s < omega := by
    unfold hamiltonRescaledTime
    linarith [htimeMem.2, hsdiv]
  exact ⟨hlo, hhi⟩

noncomputable def hamiltonSourceSequence
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius) :
    PointedFlowSeq.{u, uE, uH} (I := I) where
  D := hamiltonCommonD
  term := fun i =>
    { M := M
      topology := inferInstance
      charted := inferInstance
      smooth := inferInstance
      sigmaCompact := inferInstance
      t2 := inferInstance
      t2TangentBundle := inferInstance
      basepoint := Q.point (hamiltonStart (I := I) P Q hsel hwindow + i)
      S :=
        (hamiltonRescaledSolution (I := I) P Q hsel
          (hamiltonStart (I := I) P Q hsel hwindow + i)).timeRestrict hamiltonCommonD
      isSolution :=
        DifferentialGeometry.PDE.RicciFlow.isSoln_timeRestrict (I := I)
          (DifferentialGeometry.PDE.RicciFlow.paraSol (I := I) P.S
            P.isSmooth.isSolution
            (Q.time (hamiltonStart (I := I) P Q hsel hwindow + i))
            (hamiltonBlowupScale (I := I) P Q
              (hamiltonStart (I := I) P Q hsel hwindow + i))
            (hsel.1 (hamiltonStart (I := I) P Q hsel hwindow + i))
            (hsel.2.2.1 (hamiltonStart (I := I) P Q hsel hwindow + i)))
          (hamilton_car_subset (I := I) h0omega P hD Q hsel hwindow i)
          (hamilton_reg_subset (I := I) h0omega P hD Q hsel hwindow i) }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem sourceSeq_carrier
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius) :
    (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow).D.carrier =
      Set.Icc (-(hamilton_reference_radius ^ 2)) 0 := by
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem sourceSeq_regular
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius) :
    (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow).D.regular =
      Set.Ioo (-(hamilton_reference_radius ^ 2)) 0 := by
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem hamilton_shi_car
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius)
    (i : Nat) :
    Set.Icc hamiltonShiLeft 0 ⊆
      (DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
        (Q.time (hamiltonStart (I := I) P Q hsel hwindow + i))
        (hamiltonBlowupScale (I := I) P Q
          (hamiltonStart (I := I) P Q hsel hwindow + i))
        (hsel.1 (hamiltonStart (I := I) P Q hsel hwindow + i))
        (hsel.2.2.1 (hamiltonStart (I := I) P Q hsel hwindow + i))).carrier := by
  intro s hs
  let j := hamiltonStart (I := I) P Q hsel hwindow + i
  have hj : hamiltonStart (I := I) P Q hsel hwindow ≤ j := by
    simpa only [j] using
      Nat.le_add_right (hamiltonStart (I := I) P Q hsel hwindow) i
  have hbuf := hamiltonBuf_spec (I := I) P Q hsel hwindow j hj
  rw [DifferentialGeometry.PDE.RicciFlow.paraInterval_carrier]
  change hamiltonRescaledTime (I := I) P Q j s ∈ P.D.carrier
  rw [hD]
  have hscale := hsel.1 j
  have htimeMem := hsel.2.2.1 j
  rw [hD] at htimeMem
  have hsleft : -(2 * hamilton_reference_radius ^ 2) ≤ s := by
    simpa only [hamiltonShiLeft] using hs.1
  have hnum : 0 ≤ hamiltonBlowupScale (I := I) P Q j * Q.time j + s := by
    linarith [hsleft]
  have hlo : 0 ≤ hamiltonRescaledTime (I := I) P Q j s := by
    rw [show hamiltonRescaledTime (I := I) P Q j s =
        (hamiltonBlowupScale (I := I) P Q j * Q.time j + s) /
          hamiltonBlowupScale (I := I) P Q j by
      unfold hamiltonRescaledTime
      field_simp [ne_of_gt hscale]]
    exact div_nonneg hnum hscale.le
  have hsdiv : s / hamiltonBlowupScale (I := I) P Q j ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hs.2 hscale.le
  have hhi : hamiltonRescaledTime (I := I) P Q j s < omega := by
    unfold hamiltonRescaledTime
    linarith [htimeMem.2, hsdiv]
  exact ⟨hlo, hhi⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem hamilton_shi_reg
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius)
    (i : Nat) :
    Set.Ioc hamiltonShiLeft 0 ⊆
      (DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
        (Q.time (hamiltonStart (I := I) P Q hsel hwindow + i))
        (hamiltonBlowupScale (I := I) P Q
          (hamiltonStart (I := I) P Q hsel hwindow + i))
        (hsel.1 (hamiltonStart (I := I) P Q hsel hwindow + i))
        (hsel.2.2.1 (hamiltonStart (I := I) P Q hsel hwindow + i))).regular := by
  intro s hs
  let j := hamiltonStart (I := I) P Q hsel hwindow + i
  have hj : hamiltonStart (I := I) P Q hsel hwindow ≤ j := by
    simpa only [j] using
      Nat.le_add_right (hamiltonStart (I := I) P Q hsel hwindow) i
  have hbuf := hamiltonBuf_spec (I := I) P Q hsel hwindow j hj
  rw [DifferentialGeometry.PDE.RicciFlow.paraInterval_regular]
  change hamiltonRescaledTime (I := I) P Q j s ∈ P.D.regular
  rw [hD]
  have hscale := hsel.1 j
  have htimeMem := hsel.2.2.1 j
  rw [hD] at htimeMem
  have hsleft : -(2 * hamilton_reference_radius ^ 2) < s := by
    simpa only [hamiltonShiLeft] using hs.1
  have hnum : 0 < hamiltonBlowupScale (I := I) P Q j * Q.time j + s := by
    linarith [hsleft]
  have hlo : 0 < hamiltonRescaledTime (I := I) P Q j s := by
    rw [show hamiltonRescaledTime (I := I) P Q j s =
        (hamiltonBlowupScale (I := I) P Q j * Q.time j + s) /
          hamiltonBlowupScale (I := I) P Q j by
      unfold hamiltonRescaledTime
      field_simp [ne_of_gt hscale]]
    exact div_pos hnum hscale
  have hsdiv : s / hamiltonBlowupScale (I := I) P Q j ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hs.2 hscale.le
  have hhi : hamiltonRescaledTime (I := I) P Q j s < omega := by
    unfold hamiltonRescaledTime
    linarith [htimeMem.2, hsdiv]
  exact ⟨hlo, hhi⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem hamilton_shi_rm
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius)
    (hrm : hamiltonRiemannCurvatureBound (I := I) P Q)
    (i : Nat) :
    ∀ s ∈ Set.Icc hamiltonShiLeft 0, ∀ x : M,
      Tensor0SBundle.normSq0S (I := I)
          ((hamiltonRescaledSolution (I := I) P Q hsel
            (hamiltonStart (I := I) P Q hsel hwindow + i)).base.metric s) x 4
          ((hamiltonRescaledSolution (I := I) P Q hsel
            (hamiltonStart (I := I) P Q hsel hwindow + i)).base.rm04 s x) ≤
        (100 : Real) ^ 2 := by
  intro s hs x
  let j := hamiltonStart (I := I) P Q hsel hwindow + i
  have hj : hamiltonStart (I := I) P Q hsel hwindow ≤ j := by
    simpa only [j] using
      Nat.le_add_right (hamiltonStart (I := I) P Q hsel hwindow) i
  have hbuf := hamiltonBuf_spec (I := I) P Q hsel hwindow j hj
  have hsleft : -(2 * hamilton_reference_radius ^ 2) ≤ s := by
    simpa only [hamiltonShiLeft] using hs.1
  have hleft :
      -(hamiltonBlowupScale (I := I) P Q j * Q.time j) ≤ s := by
    linarith
  have hold := hrm j s x hleft hs.2
  have hold' :
      Tensor0SBundle.normSq0S (I := I)
          (P.S.base.metric (DifferentialGeometry.PDE.RicciFlow.paraTime
            (Q.time j) (hamiltonBlowupScale (I := I) P Q j) s)) x 4
          (P.S.base.rm04 (DifferentialGeometry.PDE.RicciFlow.paraTime
            (Q.time j) (hamiltonBlowupScale (I := I) P Q j) s) x) ≤
        (100 : Real) ^ 2 *
          (hamiltonBlowupScale (I := I) P Q j) ^ 2 := by
    simpa [hamiltonRiemannNormSq, hamiltonSolution, hamiltonRescaledTime] using hold
  have hscale := hsel.1 j
  have hmul := mul_le_mul_of_nonneg_left hold'
    (sq_nonneg (hamiltonBlowupScale (I := I) P Q j)⁻¹)
  change Tensor0SBundle.normSq0S (I := I)
      ((hamiltonRescaledSolution (I := I) P Q hsel j).base.metric s) x 4
      ((hamiltonRescaledSolution (I := I) P Q hsel j).base.rm04 s x) ≤
    (100 : Real) ^ 2
  unfold hamiltonRescaledSolution
  rw [DifferentialGeometry.PDE.RicciFlow.paraRmNormSq]
  calc
    (hamiltonBlowupScale (I := I) P Q j)⁻¹ ^ 2 *
        Tensor0SBundle.normSq0S (I := I)
          (P.S.base.metric (DifferentialGeometry.PDE.RicciFlow.paraTime
            (Q.time j) (hamiltonBlowupScale (I := I) P Q j) s)) x 4
          (P.S.base.rm04 (DifferentialGeometry.PDE.RicciFlow.paraTime
            (Q.time j) (hamiltonBlowupScale (I := I) P Q j) s) x) ≤
      (hamiltonBlowupScale (I := I) P Q j)⁻¹ ^ 2 *
        ((100 : Real) ^ 2 *
          (hamiltonBlowupScale (I := I) P Q j) ^ 2) := hmul
    _ = (100 : Real) ^ 2 := by
      field_simp [ne_of_gt hscale]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem hamilton_ball_rm
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius)
    (hrm : hamiltonRiemannCurvatureBound (I := I) P Q)
    {r : Real} (hr : 0 < r) (hrle : r ≤ hamilton_reference_radius)
    (i : Nat) :
    (hamiltonRescaledBall (I := I) P Q hsel
      (hamiltonStart (I := I) P Q hsel hwindow + i) r hr).IsRmControlled := by
  let j := hamiltonStart (I := I) P Q hsel hwindow + i
  let B := hamiltonRescaledBall (I := I) P Q hsel j r hr
  change B.IsRmControlled
  unfold PDE.RicciFlow.Perelman.FlowMetricBall.IsRmControlled
  dsimp only [B, hamiltonRescaledBall, hamiltonRescaledInitialTime]
  have hrsq : r ^ 2 ≤ hamilton_reference_radius ^ 2 := by
    nlinarith
      [mul_nonneg (sub_nonneg.mpr hrle)
        (add_nonneg hr.le hamilton_reference_radius_pos.le)]
  constructor
  · intro t ht
    apply hamilton_shi_car (I := I) h0omega P hD Q hsel hwindow i
    refine ⟨?_, ht.2⟩
    dsimp only [hamiltonShiLeft]
    nlinarith [ht.1, hrsq, sq_nonneg hamilton_reference_radius]
  · intro t ht x _hx
    have htShi : t ∈ Set.Icc hamiltonShiLeft 0 := by
      refine ⟨?_, ht.2⟩
      dsimp only [hamiltonShiLeft]
      nlinarith [ht.1, hrsq, sq_nonneg hamilton_reference_radius]
    have hsq :=
      hamilton_shi_rm (I := I) P Q hsel hwindow hrm i t htShi x
    change r ^ 4 *
        Tensor0SBundle.normSq0S (I := I)
          ((hamiltonRescaledSolution (I := I) P Q hsel j).base.metric t) x 4
          ((hamiltonRescaledSolution (I := I) P Q hsel j).base.rm04 t x) ≤ 1
    have hmul :=
      mul_le_mul_of_nonneg_left hsq (pow_nonneg hr.le 4)
    calc
      r ^ 4 *
            Tensor0SBundle.normSq0S (I := I)
              ((hamiltonRescaledSolution (I := I) P Q hsel j).base.metric t) x 4
              ((hamiltonRescaledSolution (I := I) P Q hsel j).base.rm04 t x)
          ≤ r ^ 4 * (100 : Real) ^ 2 := hmul
      _ ≤ hamilton_reference_radius ^ 4 * (100 : Real) ^ 2 := by
        gcongr
      _ = 1 := by
        norm_num [hamilton_reference_radius]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem hamilton_win_equiv
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius)
    (hrm : hamiltonRiemannCurvatureBound (I := I) P Q) :
    ∃ A Bmax : Real, 0 ≤ A ∧ 1 ≤ Bmax ∧
      (∀ t : Real, t ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 →
        metricEquivalenceFactor 1 A t 0 ≤ Bmax) ∧
      ∀ i : Nat,
        MetricUniformEquivalentOnWindow (I := I) Set.univ
          (-(hamilton_reference_radius ^ 2)) 0
          ((hamiltonRescaledSolution (I := I) P Q hsel
            (hamiltonStart (I := I) P Q hsel hwindow + i)).family.metric 0)
          (fun _ t ↦
            (hamiltonRescaledSolution (I := I) P Q hsel
              (hamiltonStart (I := I) P Q hsel hwindow + i)).family.metric t)
          (fun t ↦ metricEquivalenceFactor 1 A t 0) := by
  let C : Real := (100 : Real) ^ 2
  let A : Real := (Module.finrank Real E : Real) ^ 2 * Real.sqrt C
  let timeRadius : Real := hamilton_reference_radius ^ 2
  let Bmax : Real := Real.exp (2 * A * timeRadius)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hRadius : 0 ≤ timeRadius := by
    dsimp only [timeRadius]
    positivity
  have hBmax : 1 ≤ Bmax := by
    dsimp only [Bmax]
    exact Real.one_le_exp
      (mul_nonneg (mul_nonneg (by norm_num) hA) hRadius)
  have habs : ∀ t : Real, t ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 →
      |t| ≤ timeRadius := by
    intro t ht
    rw [abs_of_nonpos ht.2]
    dsimp only [timeRadius]
    nlinarith [ht.1]
  have hB : ∀ t : Real, t ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 →
      metricEquivalenceFactor 1 A t 0 ≤ Bmax := by
    intro t ht
    rw [metricEquivalenceFactor]
    simp only [one_mul, sub_zero]
    dsimp only [Bmax]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (habs t ht)
      (mul_nonneg (by norm_num) hA)
  refine ⟨A, Bmax, hA, hBmax, hB, ?_⟩
  intro i
  let j := hamiltonStart (I := I) P Q hsel hwindow + i
  let Draw := DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
    (Q.time j) (hamiltonBlowupScale (I := I) P Q j)
    (hsel.1 j) (hsel.2.2.1 j)
  let Sraw : DifferentialGeometry.PDE.RicciFlow.SolutionOn
      (I := I) (M := M) Draw :=
    hamiltonRescaledSolution (I := I) P Q hsel j
  have hraw : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn
      (I := I) Sraw := by
    exact DifferentialGeometry.PDE.RicciFlow.paraSol (I := I) P.S
      P.isSmooth.isSolution (Q.time j)
      (hamiltonBlowupScale (I := I) P Q j)
      (hsel.1 j) (hsel.2.2.1 j)
  let Sseq : Nat → DifferentialGeometry.PDE.RicciFlow.SolutionOn
      (I := I) (M := M) Draw := fun _ ↦ Sraw
  have hSseq : ∀ n : Nat,
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) (Sseq n) :=
    fun _ ↦ hraw
  have hcarrier : Set.Icc (-(hamilton_reference_radius ^ 2)) 0 ⊆ Draw.carrier := by
    intro t ht
    apply hamilton_shi_car (I := I) h0omega P hD Q hsel hwindow i
    refine ⟨?_, ht.2⟩
    dsimp only [hamiltonShiLeft]
    nlinarith [sq_pos_of_pos hamilton_reference_radius_pos, ht.1]
  have hregular : Set.Icc (-(hamilton_reference_radius ^ 2)) 0 ⊆ Draw.regular := by
    intro t ht
    apply hamilton_shi_reg (I := I) h0omega P hD Q hsel hwindow i
    refine ⟨?_, ht.2⟩
    dsimp only [hamiltonShiLeft]
    nlinarith [sq_pos_of_pos hamilton_reference_radius_pos, ht.1]
  have hquad :=
    DifferentialGeometry.Geometry.Curvature.twoTensorQuadBound_of_solutions
      (I := I)
      Sseq Set.univ (-(hamilton_reference_radius ^ 2)) 0 C
    (fun _ t ht x _hx ↦ by
      simpa only [Sseq, Sraw, C, j] using
        hamilton_shi_rm (I := I) P Q hsel hwindow hrm i t
          (by
            refine ⟨?_, ht.2⟩
            dsimp only [hamiltonShiLeft]
            nlinarith [sq_pos_of_pos hamilton_reference_radius_pos, ht.1])
          x)
  have hequiv0 : ∀ n : Nat,
      MetricUniformEquivalentOn (I := I) Set.univ
        (Sraw.family.metric 0) ((Sseq n).family.metric 0) 1 := by
    intro n
    refine ⟨le_rfl, ?_⟩
    intro x _hx v
    simp only [Sseq, inv_one, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  have hzero : (0 : Real) ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 :=
    ⟨neg_nonpos.mpr (sq_nonneg hamilton_reference_radius), le_rfl⟩
  have hequiv :=
    metric_uniform_equivalent_on_window_of_solutions (I := I)
      Sseq hSseq Set.univ (-(hamilton_reference_radius ^ 2)) 0 0 1 A
      (Sraw.family.metric 0) hregular hzero le_rfl hA hequiv0 hquad.2
  simpa only [Sseq, Sraw, j] using hequiv

private theorem hamilton_win_shi
    {omega : Real} (h0omega : 0 < omega)
    (hcompact : CompactSpace M)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius)
    (hrm : hamiltonRiemannCurvatureBound (I := I) P Q) :
    ∀ N : Nat, ∃ KShi : Real, 0 ≤ KShi ∧
      ∀ i : Nat,
        MovingShiBoundOn (I := I) Set.univ
          (-(hamilton_reference_radius ^ 2)) 0
          (fun _ t ↦
            (hamiltonRescaledSolution (I := I) P Q hsel
              (hamiltonStart (I := I) P Q hsel hwindow + i)).family.metric t)
          N KShi := by
  letI : CompactSpace M := hcompact
  intro N
  let KShi : Real :=
    shiOpenConst (Module.finrank Real E) ((100 : Real) ^ 2)
      hamiltonShiLeft (-(hamilton_reference_radius ^ 2)) 0 N
  refine ⟨KShi, shiOpenConst_nonneg _ _ _ _ _ _, ?_⟩
  intro i
  let j := hamiltonStart (I := I) P Q hsel hwindow + i
  let Draw := DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
    (Q.time j) (hamiltonBlowupScale (I := I) P Q j)
    (hsel.1 j) (hsel.2.2.1 j)
  let Sraw : DifferentialGeometry.PDE.RicciFlow.SolutionOn
      (I := I) (M := M) Draw :=
    hamiltonRescaledSolution (I := I) P Q hsel j
  have hraw : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn
      (I := I) Sraw := by
    exact DifferentialGeometry.PDE.RicciFlow.paraSol (I := I) P.S
      P.isSmooth.isSolution (Q.time j)
      (hamiltonBlowupScale (I := I) P Q j)
      (hsel.1 j) (hsel.2.2.1 j)
  let Fraw : PointedFlowData (I := I) Draw :=
    { M := M
      topology := inferInstance
      charted := inferInstance
      smooth := inferInstance
      sigmaCompact := inferInstance
      t2 := inferInstance
      t2TangentBundle := inferInstance
      basepoint := Q.point j
      S := Sraw
      isSolution := hraw }
  have hcomplete :
      MetricComplete (I := I) (Fraw.atTime (I := I) hamiltonShiLeft) := by
    dsimp only [MetricComplete, PointedFlowData.atTime]
    refine @complete_of_compact Fraw.M ?_ ?_
    simpa only [Fraw] using hcompact
  have halphaBeta : hamiltonShiLeft < -(hamilton_reference_radius ^ 2) := by
    dsimp only [hamiltonShiLeft]
    nlinarith [sq_pos_of_pos hamilton_reference_radius_pos]
  have hbetaZero : -(hamilton_reference_radius ^ 2) ≤ (0 : Real) :=
    neg_nonpos.mpr (sq_nonneg hamilton_reference_radius)
  have hShi := movingShi_of_bound (I := I) Fraw
    halphaBeta hbetaZero
    (hamilton_shi_car (I := I) h0omega P hD Q hsel hwindow i)
    (hamilton_shi_reg (I := I) h0omega P hD Q hsel hwindow i)
    hcomplete (by positivity : (0 : Real) ≤ (100 : Real) ^ 2)
    (by
      intro t ht x
      change Tensor0SBundle.normSq0S (I := I)
          (Sraw.family.metric t) x 4 (Sraw.base.rm04 t x) ≤
        (100 : Real) ^ 2
      simpa only [Sraw, j] using
        hamilton_shi_rm (I := I) P Q hsel hwindow hrm i t ht x)
    N
  simpa only [Fraw, Sraw, j, KShi] using hShi

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem hamilton_src_rm
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius)
    (hrm : hamiltonRiemannCurvatureBound (I := I) P Q)
    {r : Real} (hr : 0 < r) (hrle : r ≤ hamilton_reference_radius)
    (i : Nat) :
    let X := hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow
    let hzero : (0 : Real) ∈ X.D.carrier := by
      change (0 : Real) ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0
      exact ⟨neg_nonpos.mpr (sq_nonneg hamilton_reference_radius), le_rfl⟩
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I 1 (X.term i).M :=
      IsManifold.of_le (I := I) (M := (X.term i).M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    (PointedFlowData.baseFlowBall (I := I) (X.term i)
      hzero r hr).IsRmControlled := by
  let X := hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow
  let hzero : (0 : Real) ∈ X.D.carrier := by
    change (0 : Real) ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0
    exact ⟨neg_nonpos.mpr (sq_nonneg hamilton_reference_radius), le_rfl⟩
  letI : TopologicalSpace (X.term i).M := (X.term i).topology
  letI : ChartedSpace H (X.term i).M := (X.term i).charted
  letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
  letI : IsManifold I 1 (X.term i).M :=
    IsManifold.of_le (I := I) (M := (X.term i).M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
    change IsManifold I ∞ (X.term i).M
    infer_instance
  letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
  letI : T2Space (X.term i).M := (X.term i).t2
  let B := PointedFlowData.baseFlowBall (I := I) (X.term i)
    hzero r hr
  change B.IsRmControlled
  unfold PDE.RicciFlow.Perelman.FlowMetricBall.IsRmControlled
  have hrsq : r ^ 2 ≤ hamilton_reference_radius ^ 2 := by
    nlinarith
      [mul_nonneg (sub_nonneg.mpr hrle)
        (add_nonneg hr.le hamilton_reference_radius_pos.le)]
  constructor
  · intro t ht
    have ht' : t ∈ Set.Icc ((0 : Real) - r ^ 2) 0 := by
      simpa only [B, PointedFlowData.baseFlowBall] using ht
    change t ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0
    exact ⟨by linarith [ht'.1, hrsq], ht'.2⟩
  · intro t ht x _hx
    have ht' : t ∈ Set.Icc ((0 : Real) - r ^ 2) 0 := by
      simpa only [B, PointedFlowData.baseFlowBall] using ht
    let j := hamiltonStart (I := I) P Q hsel hwindow + i
    have htShi : t ∈ Set.Icc hamiltonShiLeft 0 := by
      refine ⟨?_, ht'.2⟩
      dsimp only [hamiltonShiLeft]
      linarith [ht'.1, hrsq, sq_nonneg hamilton_reference_radius]
    have hsq :=
      hamilton_shi_rm (I := I) P Q hsel hwindow hrm i t htShi x
    change r ^ 4 *
        Tensor0SBundle.normSq0S (I := I)
          ((hamiltonRescaledSolution (I := I) P Q hsel j).base.metric t) x 4
          ((hamiltonRescaledSolution (I := I) P Q hsel j).base.rm04 t x) ≤ 1
    have hmul :=
      mul_le_mul_of_nonneg_left hsq (pow_nonneg hr.le 4)
    calc
      r ^ 4 *
            Tensor0SBundle.normSq0S (I := I)
              ((hamiltonRescaledSolution (I := I) P Q hsel j).base.metric t) x 4
              ((hamiltonRescaledSolution (I := I) P Q hsel j).base.rm04 t x)
          ≤ r ^ 4 * (100 : Real) ^ 2 := hmul
      _ ≤ hamilton_reference_radius ^ 4 * (100 : Real) ^ 2 := by
        gcongr
      _ = 1 := by
        norm_num [hamilton_reference_radius]

omit [NeZero (Module.finrank Real E)] in
theorem hamilton_source_chart_jet_bound
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius)
    {P₀ : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    (Φ : PointedCGHMaps (I := I)
      (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow) P₀ subseq)
    {R : letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      SmoothRiemannianMetric I P₀.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    (k r : Nat) (x₀ : P₀.M) (i j : Fin (Module.finrank Real E))
    {C : Set E}
    (hCtarget : letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      C ⊆ (extChartAt I x₀).target)
    (hCgrow : letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      (extChartAt I x₀).symm '' C ⊆ bf.grow k) :
    letI : TopologicalSpace P₀.M := P₀.topology
    letI : ChartedSpace H P₀.M := P₀.charted
    letI : T2Space P₀.M := P₀.t2
    letI : IsManifold I ∞ P₀.M := P₀.smooth
    ContinuousOn
      (fun p : Real × E =>
        iteratedFDeriv Real r
          (DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I)
            (gSeqExt (I := I) Φ R bf hsrc htgt k p.1) x₀ i j) p.2)
      (Set.Icc (-(hamilton_reference_radius ^ 2)) 0 ×ˢ C) := by
  let X := hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow
  change PointedCGHMaps (I := I) X P₀ subseq at Φ
  letI : TopologicalSpace P₀.M := P₀.topology
  letI : ChartedSpace H P₀.M := P₀.charted
  letI : T2Space P₀.M := P₀.t2
  letI : IsManifold I ∞ P₀.M := P₀.smooth
  letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : IsManifold I 1 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M)
      (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M)
      (n := (∞ : WithTop ℕ∞)) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
    sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
    sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) :=
    sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
    sourceDomSmooth (I := I) Φ k
  letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  letI : SigmaCompactSpace ↥(targetOpen (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k (htgt k)
  letI : T2Space ↥(targetOpen (I := I) Φ k) :=
    targetDomT2 (I := I) Φ k
  letI : IsManifold I 1 ↥(targetOpen (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := ↥(targetOpen (I := I) Φ k))
      (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      ↥(targetOpen (I := I) Φ k) := by
    change IsManifold I ∞ ↥(targetOpen (I := I) Φ k)
    infer_instance
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) :=
    targetDomTop (I := I) Φ k
  letI : ChartedSpace H (TargetDomain (I := I) Φ k) :=
    targetDomCharted (I := I) Φ k
  letI : T2Space (TargetDomain (I := I) Φ k) :=
    targetDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (TargetDomain (I := I) Φ k) :=
    targetDomSmooth (I := I) Φ k
  letI : IsManifold I 1 (TargetDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := TargetDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 (TargetDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := TargetDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      (TargetDomain (I := I) Φ k) := by
    change IsManifold I ∞ (TargetDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (TargetDomain (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k (htgt k)
  let j₀ := hamiltonStart (I := I) P Q hsel hwindow + subseq k
  let Draw := DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
    (Q.time j₀) (hamiltonBlowupScale (I := I) P Q j₀)
    (hsel.1 j₀) (hsel.2.2.1 j₀)
  let Sraw : DifferentialGeometry.PDE.RicciFlow.SolutionOn
      (I := I) (M := (X.term (subseq k)).M) Draw := by
    change DifferentialGeometry.PDE.RicciFlow.SolutionOn
      (I := I) (M := M) Draw
    exact hamiltonRescaledSolution (I := I) P Q hsel j₀
  have hraw : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) Sraw := by
    change DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
      (hamiltonRescaledSolution (I := I) P Q hsel j₀)
    exact DifferentialGeometry.PDE.RicciFlow.paraSol (I := I) P.S
      P.isSmooth.isSolution (Q.time j₀)
      (hamiltonBlowupScale (I := I) P Q j₀)
      (hsel.1 j₀) (hsel.2.2.1 j₀)
  let S := DifferentialGeometry.PDE.RicciFlow.solutionOn_pullback (I := I)
    (solutionOn_restrictOpen (I := I) Sraw (targetOpen (I := I) Φ k))
    (sourceTargetDiff (I := I) Φ k)
  have hS : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S := by
    exact DifferentialGeometry.PDE.RicciFlow.isSolutionOn_pullback (I := I)
      (solutionOn_restrictOpen (I := I) Sraw (targetOpen (I := I) Φ k))
      (isSolutionOn_restrictOpen (I := I) Sraw hraw
        (targetOpen (I := I) Φ k))
      (sourceTargetDiff (I := I) Φ k)
  have hreg : Set.Icc (-(hamilton_reference_radius ^ 2)) 0 ⊆
      Draw.regular := by
    intro t ht
    apply hamilton_shi_reg (I := I) h0omega P hD Q hsel hwindow (subseq k)
    refine ⟨?_, ht.2⟩
    dsimp only [hamiltonShiLeft]
    have htleft := ht.1
    nlinarith [sq_pos_of_pos hamilton_reference_radius_pos]
  apply ConvOut.gSeqJet_of_soln (Φ := Φ) (R := R) (bf := bf)
    (hsrc := hsrc) (htgt := htgt) k S hS hreg
  · intro t x v w
    rfl
  · exact hCtarget
  · exact hCgrow

omit [NeZero (Module.finrank Real E)] in
theorem hamilton_limit_chart_jets_continuous
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius)
    {P₀ : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    (Φ : PointedCGHMaps (I := I)
      (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow) P₀ subseq)
    {R : letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      SmoothRiemannianMetric I P₀.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    (co : ConvOut (I := I) Φ R bf hsrc htgt (-(hamilton_reference_radius ^ 2)) 0) :
    letI : TopologicalSpace P₀.M := P₀.topology
    letI : ChartedSpace H P₀.M := P₀.charted
    letI : T2Space P₀.M := P₀.t2
    letI : IsManifold I ∞ P₀.M := P₀.smooth
    ∀ (r : Nat) (x₀ : P₀.M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × E =>
          iteratedFDeriv Real r
            (DifferentialGeometry.Geometry.Operator.chartGramOnE
              (I := I) (co.gInf p.1) x₀ i j) p.2)
        (Set.Icc (-(hamilton_reference_radius ^ 2)) 0 ×ˢ
          interior (extChartAt I x₀).target) := by
  letI : TopologicalSpace P₀.M := P₀.topology
  letI : ChartedSpace H P₀.M := P₀.charted
  letI : T2Space P₀.M := P₀.t2
  letI : IsManifold I ∞ P₀.M := P₀.smooth
  letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
  apply ConvOut.gramJets_of_stage (I := I) (Φ := Φ) co
  intro r x₀ i j C hCc hCtgt
  let K : Set P₀.M := (extChartAt I x₀).symm '' C
  have hKc : IsCompact K := by
    dsimp only [K]
    exact hCc.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) x₀).mono hCtgt)
  obtain ⟨kgrow, hkgrow⟩ := bf.grow_cover K hKc
  filter_upwards [Filter.eventually_ge_atTop kgrow] with k hk
  apply hamilton_source_chart_jet_bound (I := I) h0omega P hD Q hsel hwindow Φ
    (co.φ k) r x₀ i j hCtgt
  simpa only [K] using hkgrow (co.φ k) (hk.trans (co.hφ.id_le k))

theorem hamilton_limit_chart_gram_smooth
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius)
    {P₀ : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    (Φ : PointedCGHMaps (I := I)
      (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow) P₀ subseq)
    {R : letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      SmoothRiemannianMetric I P₀.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    (co : ConvOut (I := I) Φ R bf hsrc htgt (-(hamilton_reference_radius ^ 2)) 0) :
    letI : TopologicalSpace P₀.M := P₀.topology
    letI : ChartedSpace H P₀.M := P₀.charted
    letI : T2Space P₀.M := P₀.t2
    letI : IsManifold I ∞ P₀.M := P₀.smooth
    ∀ (x₀ : P₀.M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × P₀.M =>
          DifferentialGeometry.Integral.Measure.chartGramMatrix
            (I := I) (co.gInf p.1) x₀ p.2 i j)
        (Set.Icc (-(hamilton_reference_radius ^ 2)) 0 ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  letI : TopologicalSpace P₀.M := P₀.topology
  letI : ChartedSpace H P₀.M := P₀.charted
  letI : T2Space P₀.M := P₀.t2
  letI : IsManifold I ∞ P₀.M := P₀.smooth
  letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
  apply ConvOut.gramSmoothIcc (I := I) (Φ := Φ)
    (neg_lt_zero.mpr (sq_pos_of_pos hamilton_reference_radius_pos))
  · exact Set.Subset.rfl
  · exact Set.Subset.rfl
  · exact hamilton_limit_chart_jets_continuous (I := I) h0omega P hD Q hsel hwindow Φ co

theorem hamilton_limit_is_solution
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius)
    {P₀ : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    (Φ : PointedCGHMaps (I := I)
      (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow) P₀ subseq)
    {R : letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      SmoothRiemannianMetric I P₀.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    (co : ConvOut (I := I) Φ R bf hsrc htgt (-(hamilton_reference_radius ^ 2)) 0) :
    letI : TopologicalSpace P₀.M := P₀.topology
    letI : ChartedSpace H P₀.M := P₀.charted
    letI : T2Space P₀.M := P₀.t2
    letI : IsManifold I ∞ P₀.M := P₀.smooth
    letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
    DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
      ({ base := { metric := co.gInf } } :
        DifferentialGeometry.PDE.RicciFlow.SolutionOn
          (I := I) (M := P₀.M)
          (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow).D) := by
  letI : TopologicalSpace P₀.M := P₀.topology
  letI : ChartedSpace H P₀.M := P₀.charted
  letI : T2Space P₀.M := P₀.t2
  letI : IsManifold I ∞ P₀.M := P₀.smooth
  letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
  let J : Set Real := Set.Icc (-(hamilton_reference_radius ^ 2)) 0
  have hJlt : -(hamilton_reference_radius ^ 2) < (0 : Real) :=
    neg_lt_zero.mpr (sq_pos_of_pos hamilton_reference_radius_pos)
  have hJ : UniqueDiffOn Real J := by
    simpa only [J] using uniqueDiffOn_Icc hJlt
  have hcarrier :
      (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow).D.carrier = J := by
    simpa only [J] using sourceSeq_carrier (I := I) h0omega P hD Q hsel hwindow
  have hcarrierSub :
      (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow).D.carrier ⊆ J := by
    simpa only [hcarrier] using (Set.Subset.rfl : J ⊆ J)
  have hjoint := hamilton_limit_chart_gram_smooth (I := I) h0omega P hD Q hsel hwindow Φ co
  have hsmooth :=
    ConvOut.metricSmooth (I := I) (Φ := Φ) hcarrier co
  have hpde : ∀ t ∈
      (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow).D.regular,
      ∀ (x : P₀.M) (v w : TangentSpace I x),
        HasDerivAt (fun s : Real => (co.gInf s).inner x v w)
          ((-2 : Real) *
            DifferentialGeometry.Geometry.Curvature.ricciTensor
              (I := I) (co.gInf t) x v w) t := by
    intro t ht x v w
    exact ConvOut.metricPDE_regular (I := I) (Φ := Φ)
      hcarrierSub co ht x v w
  have hscalarCont :
      ContinuousOn
        (fun q : Real × P₀.M =>
          DifferentialGeometry.Geometry.Curvature.metricScalarAt
            (I := I) (co.gInf q.1) q.2)
        ((hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow).D.carrier ×ˢ
          (Set.univ : Set P₀.M)) := by
    simpa only [hcarrier, J] using
      DifferentialGeometry.PDE.RicciFlow.scalarCont_of_joint
        (I := I) co.gInf J hJ hjoint
  have hscalarTime : ∀ t ∈
      (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow).D.carrier,
      ∀ x : P₀.M,
        DifferentiableWithinAt Real
          (fun s : Real =>
            DifferentialGeometry.Geometry.Curvature.metricScalarAt
              (I := I) (co.gInf s) x)
          (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow).D.carrier t := by
    intro t ht x
    have htJ : t ∈ J := hcarrier ▸ ht
    have htime :=
      DifferentialGeometry.PDE.RicciFlow.scalarTime_of_joint
        (I := I) co.gInf J hJ hjoint t htJ x
    simpa only [hcarrier] using htime
  have hricciCont := DifferentialGeometry.PDE.RicciFlow.ricciCont_of_joint
    (I := I) co.gInf J hJ hjoint
  have hrm04Cont := DifferentialGeometry.PDE.RicciFlow.rm04Cont_of_joint
    (I := I) co.gInf J hJ hjoint
  apply DifferentialGeometry.PDE.RicciFlow.isSolutionOn_of_reg
    (I := I) co.gInf hsmooth hpde hscalarCont hscalarTime
  · simpa only [hcarrier] using hricciCont
  · simpa only [hcarrier] using hrm04Cont

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem nablaK_restrict
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (k : Nat) (t : Real) (x : M) :
    DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic
        (I := I) (S.timeRestrict D') k t x =
      DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic
        (I := I) S k t x := by
  have hfield :
      DifferentialGeometry.PDE.RicciFlow.nablaKRm04Field
          (I := I) (S.timeRestrict D') t k =
        DifferentialGeometry.PDE.RicciFlow.nablaKRm04Field (I := I) S t k := by
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [DifferentialGeometry.PDE.RicciFlow.nablaKRm04Field_succ,
          DifferentialGeometry.PDE.RicciFlow.nablaKRm04Field_succ, ih]
        simp only [
          DifferentialGeometry.PDE.RicciFlow.SolutionOn.family_connection,
          DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_base]
  unfold DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic
  rw [hfield]
  simp only [
    DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_base]

noncomputable def hamiltonSourceDerivativeInput
    {omega : Real} (h0omega : 0 < omega)
    (hcompact : CompactSpace M)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hrm : hamiltonRiemannCurvatureBound (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius) :
    FlowDerivativeInput (I := I)
      (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow) := by
  classical
  letI : CompactSpace M := hcompact
  let X := hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow
  let Cderiv : Nat -> Real := fun k =>
    Real.sqrt
      (rmOpenBound (Module.finrank Real E) ((100 : Real) ^ 2)
        hamiltonShiLeft (-(hamilton_reference_radius ^ 2)) 0 k k)
  have halphaBeta : hamiltonShiLeft < -(hamilton_reference_radius ^ 2) := by
    dsimp only [hamiltonShiLeft]
    nlinarith [sq_pos_of_pos hamilton_reference_radius_pos]
  have hbetaZero : -(hamilton_reference_radius ^ 2) ≤ (0 : Real) :=
    neg_nonpos.mpr (sq_nonneg hamilton_reference_radius)
  have hsp : FlowDerivBounds (I := I) X := by
    refine
      { C := Cderiv
        nonneg := fun k => Real.sqrt_nonneg _
        bound := ?_ }
    intro i k
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    let j := hamiltonStart (I := I) P Q hsel hwindow + i
    let Draw := DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
      (Q.time j) (hamiltonBlowupScale (I := I) P Q j)
      (hsel.1 j) (hsel.2.2.1 j)
    let Sraw : DifferentialGeometry.PDE.RicciFlow.SolutionOn
        (I := I) (M := M) Draw :=
      hamiltonRescaledSolution (I := I) P Q hsel j
    have hraw : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn
        (I := I) Sraw := by
      exact DifferentialGeometry.PDE.RicciFlow.paraSol (I := I) P.S
        P.isSmooth.isSolution (Q.time j)
        (hamiltonBlowupScale (I := I) P Q j)
        (hsel.1 j) (hsel.2.2.1 j)
    let Fraw : PointedFlowData (I := I) Draw :=
      { M := M
        topology := inferInstance
        charted := inferInstance
        smooth := inferInstance
        sigmaCompact := inferInstance
        t2 := inferInstance
        t2TangentBundle := inferInstance
        basepoint := Q.point j
        S := Sraw
        isSolution := hraw }
    have hcomplete :
        MetricComplete (I := I) (Fraw.atTime (I := I) hamiltonShiLeft) := by
      dsimp only [MetricComplete, PointedFlowData.atTime]
      refine @complete_of_compact Fraw.M ?_ ?_
      simpa only [Fraw] using hcompact
    have hsq := movingRm_of_bound (I := I) Fraw
      halphaBeta hbetaZero
      (hamilton_shi_car (I := I) h0omega P hD Q hsel hwindow i)
      (hamilton_shi_reg (I := I) h0omega P hD Q hsel hwindow i)
      hcomplete (by positivity : (0 : Real) ≤ (100 : Real) ^ 2)
      (by
        intro t ht x
        change Tensor0SBundle.normSq0S (I := I)
            (Sraw.family.metric t) x 4 (Sraw.base.rm04 t x) ≤
          (100 : Real) ^ 2
        simpa only [Sraw, j] using
          hamilton_shi_rm (I := I) P Q hsel hwindow hrm i t ht x)
      k
    unfold HasSpacetimeCurvDerivBound
    intro t ht x
    have ht' : t ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 := by
      change t ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 at ht
      exact ht
    unfold curvDerivNorm Cderiv
    change Real.sqrt
        (curvDerivNormSq k ((X.term i).S.base.metric t) x) ≤
      Real.sqrt
        (rmOpenBound (Module.finrank Real E) ((100 : Real) ^ 2)
          hamiltonShiLeft (-(hamilton_reference_radius ^ 2)) 0 k k)
    rw [curvNormSq_eq (S := (X.term i).S)]
    apply Real.sqrt_le_sqrt
    change DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic
        (I := I)
        ((hamiltonRescaledSolution (I := I) P Q hsel j).timeRestrict hamiltonCommonD)
        k t x ≤
      rmOpenBound (Module.finrank Real E) ((100 : Real) ^ 2)
        hamiltonShiLeft (-(hamilton_reference_radius ^ 2)) 0 k k
    rw [nablaK_restrict]
    simpa only [Fraw, Sraw, j] using hsq k le_rfl t ht' x
  have hzero : (0 : Real) ∈ X.D.carrier := by
    change (0 : Real) ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0
    exact ⟨hbetaZero, le_rfl⟩
  exact
    { spacetime := hsp
      at_zero_geom := hsp.at_time hzero }

omit [NeZero (Module.finrank Real E)] in
theorem hamilton_source_covariant_lipschitz_bound
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius)
    {P₀ : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    (Φ : PointedCGHMaps (I := I)
      (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow) P₀ subseq)
    (R : letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      SmoothRiemannianMetric I P₀.M)
    (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (Bmax : Real) (hBmax : 1 ≤ Bmax)
    (hequiv :
      letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : T2Space P₀.M := P₀.t2
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
      ∀ k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) :=
          sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        ∀ t : Real, t ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 →
          MetricUniformEquivalentOn (I := I)
            (Set.univ : Set (SourceDomain (I := I) Φ k))
            (refRes (I := I) Φ R hsrc k)
            (srcMetric (I := I) Φ hsrc htgt k t) Bmax)
    (hShi :
      letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : T2Space P₀.M := P₀.t2
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
      ∀ N : Nat, ∃ KShi : Real, 0 ≤ KShi ∧
        ∀ k : Nat,
          letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
            sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
            sourceDomCharted (I := I) Φ k
          letI : T2Space (SourceDomain (I := I) Φ k) :=
            sourceDomT2 (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
            sourceDomSmooth (I := I) Φ k
          letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
            sourceDomSigmaOf (I := I) Φ k (hsrc k)
          MovingShiBoundOn (I := I)
            (Set.univ : Set (SourceDomain (I := I) Φ k))
            (-(hamilton_reference_radius ^ 2)) 0
            (fun _ t ↦ srcMetric (I := I) Φ hsrc htgt k t) N KShi)
    (hinit :
      letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : T2Space P₀.M := P₀.t2
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
      ∀ q : Nat, ∃ Cq : Real, 0 ≤ Cq ∧
        ∀ k : Nat,
          letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
            sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
            sourceDomCharted (I := I) Φ k
          letI : T2Space (SourceDomain (I := I) Φ k) :=
            sourceDomT2 (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
            sourceDomSmooth (I := I) Φ k
          letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
            sourceDomSigmaOf (I := I) Φ k (hsrc k)
          ∀ y : SourceDomain (I := I) Φ k,
            metricCovDerivNorm (I := I) q
                (srcMetric (I := I) Φ hsrc htgt k 0)
                (refRes (I := I) Φ R hsrc k) y ≤ Cq) :
    SrcCovLipData (I := I) Φ R hsrc htgt (-(hamilton_reference_radius ^ 2)) 0 := by
  refine srcCovLip_of_flow (I := I)
    (β := -(hamilton_reference_radius ^ 2)) (ψ := 0) (t₀ := 0)
    Φ R hsrc htgt
    (fun k ↦
      DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
        (Q.time (hamiltonStart (I := I) P Q hsel hwindow + subseq k))
        (hamiltonBlowupScale (I := I) P Q
          (hamiltonStart (I := I) P Q hsel hwindow + subseq k))
        (hsel.1 (hamiltonStart (I := I) P Q hsel hwindow + subseq k))
        (hsel.2.2.1
          (hamiltonStart (I := I) P Q hsel hwindow + subseq k)))
    (fun k ↦ sourceFlowOf (I := I) Φ k (hsrc k) (htgt k)
      (hamiltonRescaledSolution (I := I) P Q hsel
        (hamiltonStart (I := I) P Q hsel hwindow + subseq k)))
    (fun k ↦ isSoln_sourceFlowOf (I := I) Φ k (hsrc k) (htgt k)
      (hamiltonRescaledSolution (I := I) P Q hsel
        (hamiltonStart (I := I) P Q hsel hwindow + subseq k))
      (DifferentialGeometry.PDE.RicciFlow.paraSol (I := I) P.S
        P.isSmooth.isSolution
        (Q.time (hamiltonStart (I := I) P Q hsel hwindow + subseq k))
        (hamiltonBlowupScale (I := I) P Q
          (hamiltonStart (I := I) P Q hsel hwindow + subseq k))
        (hsel.1 (hamiltonStart (I := I) P Q hsel hwindow + subseq k))
        (hsel.2.2.1
          (hamiltonStart (I := I) P Q hsel hwindow + subseq k))))
    ?_ ?_ ?_ ?_ Bmax hBmax hequiv hShi hinit
  · intro k r
    rfl
  · exact neg_nonpos.mpr (sq_nonneg hamilton_reference_radius)
  · exact ⟨neg_nonpos.mpr (sq_nonneg hamilton_reference_radius), le_rfl⟩
  · intro k s hs
    apply hamilton_shi_reg (I := I) h0omega P hD Q hsel hwindow (subseq k)
    refine ⟨?_, hs.2⟩
    dsimp only [hamiltonShiLeft]
    nlinarith [sq_pos_of_pos hamilton_reference_radius_pos, hs.1]

theorem hamilton_flow_upgrade_of_metric_compactness
    {omega : Real} (h0omega : 0 < omega)
    (hcompact : CompactSpace M)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hrm : hamiltonRiemannCurvatureBound (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius)
    (canon : CanonicalMetricCompactness (I := I)
      ((hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow).atZero
        (I := I))) :
    ∃ d : FlowUpgrade (I := I)
        (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow) canon.compactness,
      ∀ t : Real,
        t ∈ (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow).D.carrier →
          MetricComplete (I := I) (d.data.L.atTime (I := I) t) := by
  classical
  letI : CompactSpace M := hcompact
  let X := hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow
  let mc := canon.compactness
  let Phi := pointedCGHMaps_of_manifold (I := I) X
    mc.limit mc.subseq mc.maps
  letI : TopologicalSpace mc.limit.M := mc.limit.topology
  letI : ChartedSpace H mc.limit.M := mc.limit.charted
  letI : T2Space mc.limit.M := mc.limit.t2
  letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
  letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
  have hsrc : SrcSigma (I := I) Phi := by
    intro k
    exact Geometry.isSigmaCompact_of_isOpen I
      (PointedCGHMaps.source_open (I := I) Phi k)
  have htgt : TgtSigma (I := I) Phi := by
    intro k
    letI : TopologicalSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).topology
    letI : ChartedSpace H (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).charted
    letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).sigmaCompact
    exact Geometry.isSigmaCompact_of_isOpen I
      (PointedCGHMaps.target_open (I := I) Phi k)
  let bf := Classical.choice (nonempty_bumpFamily (I := I) Phi)
  let gRefT : ∀ k : Nat,
      letI : TopologicalSpace (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).charted
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).smooth
      SmoothRiemannianMetric I (X.term (mc.subseq k)).M :=
    fun k =>
      letI : TopologicalSpace (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).charted
      letI : T2Space (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).t2
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).smooth
      letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).sigmaCompact
      (X.term (mc.subseq k)).S.family.metric 0
  have hcanonRel := CanonicalMetricCompactness.metric_uniformly_equivalent (I := I) canon hsrc htgt
  dsimp only at hcanonRel
  obtain ⟨Crel, hCrel, hrelZero⟩ := hcanonRel
  have hsrcZero (k : Nat) :
      tgtRefSrc (I := I) Phi gRefT hsrc htgt k =
        srcMetric (I := I) Phi hsrc htgt k 0 := by
    letI : TopologicalSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).topology
    letI : ChartedSpace H (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).charted
    letI : T2Space (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).t2
    letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).smooth
    letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).sigmaCompact
    rfl
  have hrel : ∀ k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
        sourceDomTop (I := I) Phi k
      letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
        sourceDomCharted (I := I) Phi k
      letI : T2Space (SourceDomain (I := I) Phi k) :=
        sourceDomT2 (I := I) Phi k
      letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
        sourceDomSmooth (I := I) Phi k
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (SourceDomain (I := I) Phi k))
        (refRes (I := I) Phi mc.limit.metric hsrc k)
        (tgtRefSrc (I := I) Phi gRefT hsrc htgt k) Crel := by
    intro k
    rw [hsrcZero k]
    exact hrelZero k
  have hinit := CanonicalMetricCompactness.metric_covariant_derivatives_bounded (I := I) canon hsrc htgt
  dsimp only at hinit
  have hcp := CanonicalMetricCompactness.metric_converges_on_compact_sets (I := I) canon hsrc htgt
  dsimp only at hcp
  obtain ⟨A, Bmax, hA, hBmax, hBmajor, hwindowRaw⟩ :=
    hamilton_win_equiv (I := I) h0omega P hD Q hsel hwindow hrm
  let B : Real → Real := fun t => metricEquivalenceFactor 1 A t 0
  have hequivT : ∀ k : Nat,
      letI : TopologicalSpace (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).charted
      letI : T2Space (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).t2
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).smooth
      letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).sigmaCompact
      MetricUniformEquivalentOnWindow (I := I) (Phi.target k)
        (-(hamilton_reference_radius ^ 2)) 0 (gRefT k)
        (fun _ t => (X.term (mc.subseq k)).S.family.metric t) B := by
    intro k
    letI : TopologicalSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).topology
    letI : ChartedSpace H (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).charted
    letI : T2Space (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).t2
    letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).smooth
    letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).sigmaCompact
    have hall := hwindowRaw (mc.subseq k)
    have hall' : MetricUniformEquivalentOnWindow (I := I) Set.univ
        (-(hamilton_reference_radius ^ 2)) 0 (gRefT k)
        (fun _ t => (X.term (mc.subseq k)).S.family.metric t) B := by
      simpa only [X, hamiltonSourceSequence,
        DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_metric,
        gRefT, B] using hall
    intro i t ht
    refine ⟨(hall' i t ht).1, ?_⟩
    intro x _hx v
    exact (hall' i t ht).2 x (Set.mem_univ x) v
  have hShiT : ∀ N : Nat, ∃ KShi : Real, 0 ≤ KShi ∧
      ∀ k : Nat,
        letI : TopologicalSpace (X.term (mc.subseq k)).M :=
          (X.term (mc.subseq k)).topology
        letI : ChartedSpace H (X.term (mc.subseq k)).M :=
          (X.term (mc.subseq k)).charted
        letI : T2Space (X.term (mc.subseq k)).M :=
          (X.term (mc.subseq k)).t2
        letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
          (X.term (mc.subseq k)).smooth
        letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
          (X.term (mc.subseq k)).sigmaCompact
        MovingShiBoundOn (I := I) (Phi.target k)
          (-(hamilton_reference_radius ^ 2)) 0
          (fun _ t => (X.term (mc.subseq k)).S.family.metric t) N KShi := by
    intro N
    obtain ⟨KShi, hKShi, hShiAll⟩ :=
      hamilton_win_shi (I := I) h0omega hcompact P hD Q hsel hwindow hrm N
    refine ⟨KShi, hKShi, ?_⟩
    intro k
    letI : TopologicalSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).topology
    letI : ChartedSpace H (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).charted
    letI : T2Space (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).t2
    letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).smooth
    letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).sigmaCompact
    intro s hs i t ht x _hx
    simpa only [X, hamiltonSourceSequence,
      DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_metric] using
      hShiAll (mc.subseq k) s hs i t ht x (Set.mem_univ x)
  have hShiSrc : ∀ N : Nat, ∃ KShi : Real, 0 ≤ KShi ∧
      ∀ k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
          sourceDomTop (I := I) Phi k
        letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
          sourceDomCharted (I := I) Phi k
        letI : T2Space (SourceDomain (I := I) Phi k) :=
          sourceDomT2 (I := I) Phi k
        letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
          sourceDomSmooth (I := I) Phi k
        letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
          sourceDomSigmaOf (I := I) Phi k (hsrc k)
        MovingShiBoundOn (I := I)
          (Set.univ : Set (SourceDomain (I := I) Phi k))
          (-(hamilton_reference_radius ^ 2)) 0
          (fun _ t => srcMetric (I := I) Phi hsrc htgt k t) N KShi := by
    intro N
    obtain ⟨KShi, hKShi, hShi⟩ := hShiT N
    exact ⟨KShi, hKShi, fun k =>
      srcShi (I := I) Phi hsrc htgt (-(hamilton_reference_radius ^ 2)) 0
        N KShi hShi k⟩
  have hBsrc : 1 ≤ Crel * Bmax :=
    one_le_mul_of_one_le_of_one_le hCrel hBmax
  have hequivSrc : ∀ k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
        sourceDomTop (I := I) Phi k
      letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
        sourceDomCharted (I := I) Phi k
      letI : T2Space (SourceDomain (I := I) Phi k) :=
        sourceDomT2 (I := I) Phi k
      letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
        sourceDomSmooth (I := I) Phi k
      letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
        sourceDomSigmaOf (I := I) Phi k (hsrc k)
      ∀ t : Real, t ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 →
        MetricUniformEquivalentOn (I := I)
          (Set.univ : Set (SourceDomain (I := I) Phi k))
          (refRes (I := I) Phi mc.limit.metric hsrc k)
          (srcMetric (I := I) Phi hsrc htgt k t) (Crel * Bmax) := by
    intro k t ht
    letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
      sourceDomTop (I := I) Phi k
    letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
      sourceDomCharted (I := I) Phi k
    letI : T2Space (SourceDomain (I := I) Phi k) :=
      sourceDomT2 (I := I) Phi k
    letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
      sourceDomSmooth (I := I) Phi k
    letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
      sourceDomSigmaOf (I := I) Phi k (hsrc k)
    have hEq := srcEquivOn (I := I) Phi mc.limit.metric hsrc htgt
      (-(hamilton_reference_radius ^ 2)) 0 gRefT B Crel hequivT hrel k t ht
    exact metricUniformEquivalentOn_of_le (I := I) hEq
      (mul_le_mul_of_nonneg_left (hBmajor t ht)
        (zero_le_one.trans hCrel))
  have srcData : SrcCovLipData (I := I) Phi mc.limit.metric hsrc htgt
      (-(hamilton_reference_radius ^ 2)) 0 :=
    hamilton_source_covariant_lipschitz_bound (I := I) h0omega P hD Q hsel hwindow
      Phi mc.limit.metric hsrc htgt (Crel * Bmax) hBsrc
      hequivSrc hShiSrc hinit
  let cLow : Real := (Crel * Bmax)⁻¹
  have hcLow : 0 < cLow :=
    inv_pos.mpr (zero_lt_one.trans_le hBsrc)
  have hbound :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 →
        ∀ (y : SourceDomain (I := I) Phi k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
                sourceDomTop (I := I) Phi k
            letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
                sourceDomCharted (I := I) Phi k
            TangentSpace I y),
          cLow * mc.limit.metric.inner (y : mc.limit.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
              sourceDomSmooth (I := I) Phi k
            (srcMetric (I := I) Phi hsrc htgt k t).inner y v v := by
    intro k t ht y v
    simpa only [cLow] using
      ((hequivSrc k t ht).2 y (Set.mem_univ y) v).1
  have hcovTail :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : T2Space mc.limit.M := mc.limit.t2
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      ∀ q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real),
        t ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 →
          ∀ z : mc.limit.M, z ∈ bf.grow k →
            metricCovDerivNorm (I := I) q
              (gSeqExt (I := I) Phi mc.limit.metric bf hsrc htgt k t)
              mc.limit.metric z ≤ C := by
    have hcovSrc : ∀ q : Nat, ∃ C : Real, 0 ≤ C ∧
        ∀ (k : Nat) (t : Real), t ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 →
          ∀ y : SourceDomain (I := I) Phi k,
            (y : mc.limit.M) ∈ bf.grow k →
              letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
                sourceDomTop (I := I) Phi k
              letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
                sourceDomCharted (I := I) Phi k
              letI : T2Space (SourceDomain (I := I) Phi k) :=
                sourceDomT2 (I := I) Phi k
              letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
                sourceDomSmooth (I := I) Phi k
              letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
                sourceDomSigmaOf (I := I) Phi k (hsrc k)
              metricCovDerivNorm (I := I) q
                (srcMetric (I := I) Phi hsrc htgt k t)
                (refRes (I := I) Phi mc.limit.metric hsrc k) y ≤ C := by
      intro q
      obtain ⟨C, hC, hcov⟩ := srcData.cov q
      exact ⟨C, hC, fun k t ht y _hy => hcov k t ht y⟩
    exact covTail_of_bounds (I := I) Phi mc.limit.metric bf hsrc htgt
      (-(hamilton_reference_radius ^ 2)) 0 hcovSrc
  let co := convOut_of_src (I := I) Phi mc.limit.metric bf hsrc htgt
    (neg_nonpos.mpr (sq_nonneg hamilton_reference_radius)) hBsrc hequivSrc srcData
  have hcarrier : X.D.carrier ⊆ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 := by
    intro t ht
    change t ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 at ht
    exact ht
  have hzeroMem : (0 : Real) ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 :=
    ⟨neg_nonpos.mpr (sq_nonneg hamilton_reference_radius), le_rfl⟩
  have hzero : co.gInf 0 = mc.limit.metric :=
    gInf_zero_eq (I := I) Phi mc.limit.metric bf hsrc htgt
      (-(hamilton_reference_radius ^ 2)) 0 co hzeroMem mc.limit.metric
      (conv0_of_cp (I := I) Phi mc.limit.metric hsrc htgt
        mc.limit.metric hcp)
  have hsol :=
    hamilton_limit_is_solution (I := I) h0omega P hD Q hsel hwindow Phi co
  let L := flowOfMetric (I := I) X.D mc.limit co.gInf hsol
  have hL0 : L.atTime (I := I) 0 = mc.limit :=
    flowOfMetric_atTime (I := I) X.D mc.limit co.gInf hsol 0 hzero
  have hscalarRaw := ConvOut.scalar_conv (I := I) (Φ := Phi)
    mc.limit.metric bf hsrc htgt (-(hamilton_reference_radius ^ 2)) 0 cLow hcLow
    hbound hcovTail co hcarrier
  have hricRaw := ConvOut.ricNorm_conv (I := I) (Φ := Phi)
    mc.limit.metric bf hsrc htgt (-(hamilton_reference_radius ^ 2)) 0 cLow hcLow
    hbound hcovTail co hcarrier
  have map_cast {P₁ P₂ : PointedRiemannianManifold (I := I)}
      {s : Nat → Nat} (h : P₁ = P₂)
      (maps : PointedCGHMaps (I := I) X P₂ s)
      (k : Nat) (x : P₁.M) :
      HEq ((h.symm ▸ maps : PointedCGHMaps (I := I) X P₁ s).map k x)
        (maps.map k (h ▸ x)) := by
    cases h
    rfl
  have hmap (k : Nat) (x : mc.limit.M) :
      (hL0.symm ▸ (Phi.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X
          (L.atTime (I := I) 0) (mc.subseq ∘ co.φ)).map k x =
        (Phi.compSubseq co.φ co.hφ).map k x := by
    have hx : hL0 ▸ x = x :=
      eq_of_heq ((eqRec_heq
        (φ := fun Q₀ : PointedRiemannianManifold (I := I) => Q₀.M) hL0) x)
    exact
      (eq_of_heq (map_cast hL0 (Phi.compSubseq co.φ co.hφ) k x)).trans
        (congrArg (fun y => (Phi.compSubseq co.φ co.hφ).map k y) hx)
  have scalar : ScalarPullbackTendsto (I := I)
      (hL0.symm ▸ (Phi.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X
          (L.atTime (I := I) 0) (mc.subseq ∘ co.φ)) := by
    unfold ScalarPullbackTendsto FunctionPullbackTendsto
    intro t ht x
    change mc.limit.M at x
    change Filter.Tendsto _ Filter.atTop
      (nhds (DifferentialGeometry.Geometry.Curvature.metricScalarAt
        (I := I) (co.gInf t) x))
    refine Filter.Tendsto.congr'
      (Filter.Eventually.of_forall (fun k => ?_)) (hscalarRaw t ht x)
    letI : TopologicalSpace (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).topology
    letI : ChartedSpace H (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).charted
    letI : IsManifold I ∞ (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).smooth
    letI : SigmaCompactSpace (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).sigmaCompact
    letI : T2Space (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).t2
    letI : IsManifold I 1 (X.term ((mc.subseq ∘ co.φ) k)).M :=
      IsManifold.of_le (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
        (X.term ((mc.subseq ∘ co.φ) k)).M := by
      change IsManifold I ∞ (X.term ((mc.subseq ∘ co.φ) k)).M
      infer_instance
    exact congrArg
      (fun y => (X.term ((mc.subseq ∘ co.φ) k)).S.scalar t y)
      (hmap k x).symm
  have ricciNorm : RicNormPullback (I := I)
      (hL0.symm ▸ (Phi.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X
          (L.atTime (I := I) 0) (mc.subseq ∘ co.φ)) := by
    unfold RicNormPullback FunctionPullbackTendsto
    intro t ht x
    change mc.limit.M at x
    change Filter.Tendsto _ Filter.atTop
      (nhds (Tensor0SBundle.normSq0S (I := I) (co.gInf t) x 2
        (DifferentialGeometry.Geometry.Curvature.metricRicci
          (I := I) (co.gInf t) x)))
    refine Filter.Tendsto.congr'
      (Filter.Eventually.of_forall (fun k => ?_)) (hricRaw t ht x)
    letI : TopologicalSpace (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).topology
    letI : ChartedSpace H (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).charted
    letI : IsManifold I ∞ (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).smooth
    letI : SigmaCompactSpace (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).sigmaCompact
    letI : T2Space (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).t2
    letI : IsManifold I 1 (X.term ((mc.subseq ∘ co.φ) k)).M :=
      IsManifold.of_le (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
        (X.term ((mc.subseq ∘ co.φ) k)).M := by
      change IsManifold I ∞ (X.term ((mc.subseq ∘ co.φ) k)).M
      infer_instance
    exact congrArg
      (fun y => DifferentialGeometry.PDE.RicciFlow.ricciNorm
        (I := I) (X.term ((mc.subseq ∘ co.φ) k)).S t y)
      (hmap k x).symm
  let d := flowUpgrade_of_maps (I := I) (X := X) mc L mc.limit rfl hL0
    Phi mc.limit.metric bf hsrc htgt (-(hamilton_reference_radius ^ 2)) 0 hcarrier co
    (fun _ _ => HEq.rfl) scalar ricciNorm
  refine ⟨d, ?_⟩
  intro t ht
  have htWindow : t ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 := hcarrier ht
  have hseq : ∀ (k : Nat) (s : Real),
      s ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0 →
        ∀ (x : mc.limit.M) (v : TangentSpace I x),
          min cLow 1 * mc.limit.metric.inner x v v ≤
            (gSeqExt (I := I) Phi mc.limit.metric bf hsrc htgt
              (co.φ k) s).inner x v v := by
    intro k s hs x v
    exact gSeqExt_lower (I := I) Phi mc.limit.metric bf hsrc htgt
      cLow (-(hamilton_reference_radius ^ 2)) 0 hcLow hbound (co.φ k) s hs x v
  have hcomplete := ConvOut.complete_at (I := I) Phi mc.limit_complete co
    (lt_min hcLow one_pos) hseq htWindow
  have hdL : d.data.L = L :=
    flowUpgrade_maps_L (I := I) (X := X) mc L mc.limit rfl hL0
      Phi mc.limit.metric bf hsrc htgt (-(hamilton_reference_radius ^ 2)) 0 hcarrier co
      (fun _ _ => HEq.rfl) scalar ricciNorm
  rw [hdL]
  change MetricComplete (I := I)
    ({ mc.limit with metric := co.gInf t } :
      PointedRiemannianManifold (I := I))
  exact hcomplete

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_hamilton_vol
    {omega : Real} (h0omega : 0 < omega)
    (hM : isClosedThreeManifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hrm : hamiltonRiemannCurvatureBound (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius) :
    ∃ V : FlowerScaleVolData (I := I)
        (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow),
      IsFlowerScaleVolBound (I := I) V := by
  classical
  letI : CompactSpace M := hM.1
  letI : ConnectedSpace M := hM.2.1
  letI : I.Boundaryless := hM.2.2.1
  letI : NeZero (Module.finrank Real E) := ⟨by
    rw [hM.2.2.2]
    norm_num⟩
  have hsol : PDE.RicciFlow.IsSolutionOn (I := I) P.S :=
    P.isSmooth.isSolution
  have hnlc :
      PDE.RicciFlow.Perelman.NoLocalCollapsing P.S hamilton_reference_radius := by
    have htransport :
        ∀ (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
          (hD' : D =
            DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
              0 omega h0omega)
          (S : PDE.RicciFlow.SolutionOn (I := I) (M := M) D),
          PDE.RicciFlow.IsSolutionOn (I := I) S →
            PDE.RicciFlow.Perelman.NoLocalCollapsing S hamilton_reference_radius := by
      intro D hD' S hS
      subst D
      exact PDE.RicciFlow.Perelman.no_local_open
        (I := I) (M := M) h0omega S hS hM.2.2.2 hamilton_reference_radius_pos
    exact htransport P.D hD P.S hsol
  rcases hnlc with ⟨kappa, hkappa, hbelow⟩
  let X := hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow
  have hzero : (0 : Real) ∈ X.D.carrier := by
    change (0 : Real) ∈ Set.Icc (-(hamilton_reference_radius ^ 2)) 0
    exact ⟨neg_nonpos.mpr (sq_nonneg hamilton_reference_radius), le_rfl⟩
  let c : Real := (2 * hamilton_reference_radius ^ 2) / omega
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos
      (mul_pos (by norm_num) (sq_pos_of_pos hamilton_reference_radius_pos)) h0omega
  let r : Real := min hamilton_reference_radius (Real.sqrt c * hamilton_reference_radius)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min hamilton_reference_radius_pos
      (mul_pos (Real.sqrt_pos.2 hc) hamilton_reference_radius_pos)
  have hrle : r ≤ hamilton_reference_radius := by
    exact min_le_left _ _
  let V : FlowerScaleVolData (I := I) X :=
    { zero_mem := hzero
      kappa := kappa
      kappa_pos := hkappa
      radius := r
      radius_pos := hr }
  refine ⟨V, ?_⟩
  refine ⟨?_, ?_⟩
  · intro i
    simpa only [V, X] using
      (hamilton_src_rm (I := I) h0omega P hD Q hsel hwindow hrm
        hr hrle i)
  · intro i
    let j := hamiltonStart (I := I) P Q hsel hwindow + i
    have hj : hamiltonStart (I := I) P Q hsel hwindow ≤ j := by
      simpa only [j] using
        Nat.le_add_right (hamiltonStart (I := I) P Q hsel hwindow) i
    have hbuf := hamiltonBuf_spec (I := I) P Q hsel hwindow j hj
    have hscale : 0 < hamiltonBlowupScale (I := I) P Q j := hsel.1 j
    have htime := hsel.2.2.1 j
    rw [hD] at htime
    have hcscale : c ≤ hamiltonBlowupScale (I := I) P Q j := by
      apply (div_le_iff₀ h0omega).2
      have hlt :
          hamiltonBlowupScale (I := I) P Q j * Q.time j <
            hamiltonBlowupScale (I := I) P Q j * omega :=
        mul_lt_mul_of_pos_left htime.2 hscale
      linarith
    have hsqrt :
        Real.sqrt c ≤
          Real.sqrt (hamiltonBlowupScale (I := I) P Q j) :=
      Real.sqrt_le_sqrt hcscale
    have hradius :
        r ≤ Real.sqrt (hamiltonBlowupScale (I := I) P Q j) * hamilton_reference_radius := by
      exact (min_le_right _ _).trans
        (mul_le_mul_of_nonneg_right hsqrt hamilton_reference_radius_pos.le)
    let B := hamiltonRescaledBall (I := I) P Q hsel j r hr
    have hRmB : B.IsRmControlled := by
      simpa only [B, j] using
        (hamilton_ball_rm (I := I) h0omega P hD Q hsel hwindow hrm
          hr hrle i)
    have hbelow_i :=
      PDE.RicciFlow.Perelman.para_noncollapse
        (I := I) P.S (Q.time j)
        (hamiltonBlowupScale (I := I) P Q j) hscale (hsel.2.2.1 j)
        kappa hamilton_reference_radius hbelow
    have hkB : B.IsKappaNoncollapsed kappa :=
      hbelow_i.2 (hamiltonRescaledInitialTime (I := I) P Q hsel j) B
        hradius hRmB
    simpa only [V, X, B, j, hamiltonSourceSequence,
      PointedFlowData.baseFlowBall, hamiltonRescaledBall,
      PDE.RicciFlow.Perelman.FlowMetricBall.IsKappaNoncollapsed,
      PDE.RicciFlow.Perelman.FlowMetricBall.volume,
      PDE.RicciFlow.Perelman.FlowMetricBall.set,
      PDE.RicciFlow.Perelman.FlowMetricBall.setAt,
      PDE.RicciFlow.SolutionOn.timeRestrict_metric] using hkB


structure HamiltonSourceLink
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  origIndex : Nat -> Nat
  strictMono : StrictMono origIndex
  toOrig : forall i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    (X.term i).M ≃ₘ⟮I, I⟯ M
  time_mem : forall (i : Nat) (t : Real), t ∈ X.D.carrier ->
    t ∈ (DifferentialGeometry.PDE.RicciFlow.paraInterval P.D (Q.time (origIndex i))
      (hamiltonBlowupScale (I := I) P Q (origIndex i))
      (hsel.1 (origIndex i)) (hsel.2.2.1 (origIndex i))).carrier
  basepoint_map : forall i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    toOrig i (X.term i).basepoint = Q.point (origIndex i)
  metric_eq : forall i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    forall t : Real, t ∈ X.D.carrier ->
      (X.term i).S.base.metric t =
        Diffeomorph.pullbackMetricCross
          ((hamiltonRescaledSolution (I := I) P Q hsel (origIndex i)).base.metric t)
          (toOrig i)
  baseScalar : forall i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    (X.term i).S.scalar 0 (X.term i).basepoint =
      hamiltonRescaledScalar (I := I) P Q (origIndex i) 0 (Q.point (origIndex i))

noncomputable def hamiltonSourceLink
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    (hwindow : hamiltonWindow (I := I) P Q hamilton_reference_radius) :
    HamiltonSourceLink (I := I) (M := M) P Q hsel
      (hamiltonSourceSequence (I := I) h0omega P hD Q hsel hwindow) := by
  refine
    { origIndex := fun i => hamiltonStart (I := I) P Q hsel hwindow + i
      strictMono := ?_
      toOrig := fun _ => _root_.Diffeomorph.refl I M ∞
      time_mem := ?_
      basepoint_map := ?_
      metric_eq := ?_
      baseScalar := ?_ }
  · intro i j hij
    exact Nat.add_lt_add_left hij (hamiltonStart (I := I) P Q hsel hwindow)
  · intro i t ht
    exact hamilton_car_subset (I := I) h0omega P hD Q hsel hwindow i ht
  · intro i
    rfl
  · intro i t _ht
    change
      (hamiltonRescaledSolution (I := I) P Q hsel
          (hamiltonStart (I := I) P Q hsel hwindow + i)).base.metric t =
        Diffeomorph.pullbackMetricCross
          ((hamiltonRescaledSolution (I := I) P Q hsel
            (hamiltonStart (I := I) P Q hsel hwindow + i)).base.metric t)
          (_root_.Diffeomorph.refl I M ∞)
    apply srm_eq_of_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    have hmfd :
        mfderiv I I
            (_root_.Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) x =
          ContinuousLinearMap.id ℝ (TangentSpace I x) := by
      have h1 :
          mfderiv I I
              (fun y : M =>
                (_root_.Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) y) x =
            mfderiv I I (id : M → M) x := rfl
      rw [h1]
      exact mfderiv_id
    rw [hmfd]
    rfl
  · intro i
    change
      (hamiltonRescaledSolution (I := I) P Q hsel
        (hamiltonStart (I := I) P Q hsel hwindow + i)).scalar 0
          (Q.point (hamiltonStart (I := I) P Q hsel hwindow + i)) =
        hamiltonRescaledScalar (I := I) P Q
          (hamiltonStart (I := I) P Q hsel hwindow + i) 0
          (Q.point (hamiltonStart (I := I) P Q hsel hwindow + i))
    simp only [hamiltonRescaledSolution,
      DifferentialGeometry.PDE.RicciFlow.paraSolution_scalar,
      DifferentialGeometry.PDE.RicciFlow.paraTime,
      hamiltonRescaledScalar, hamiltonRescaledTime, hamiltonScalar, hamiltonSolution]



end HamiltonPositiveRicci
end RicciFlow
end PDE
end DifferentialGeometry
