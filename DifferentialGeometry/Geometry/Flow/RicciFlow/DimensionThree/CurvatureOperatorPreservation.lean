import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorReactionPreservation
import DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureOperatorConeMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RicciPreservation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RicciPinchingPreservation

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

noncomputable def ricciUpperBoundSec
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    TwoTensorSecFamily (I := I) (M := M) :=
  fun t => (-1 : Real) • pinchSec (I := I) S (1 / 2) t

theorem ricciUpperBoundSec_at_point
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    (ricciUpperBoundSec S) t x =
      ((1 / 2) * S.scalar t x) •
        metricTensorField (I := I) (S.base.metric t) x - S.ricci t x := by
  unfold ricciUpperBoundSec
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [pinchSec_at_trace (I := I) (M := M) S (1 / 2) t x]
  have hsc :
      S.scalar t x =
        metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) := by
    simp [SolutionOn.scalar_eq_metricTrace, SolutionOn.ricci,
      SolutionFamily.ricci, SolutionOn.ricciAt, SolutionFamily.ricciAt]
  rw [hsc]
  apply ContinuousMultilinearMap.ext
  intro slots
  let A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x := S.ricci t x
  let B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    (1 / 2 * metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x)) •
      metricTensorField (I := I) (S.base.metric t) x
  calc
    ((-1 : Real) • (A - B)) slots = (-1 : Real) * ((A - B) slots) := by
      rw [show ((-1 : Real) • (A - B)) slots = (-1 : Real) * ((A - B) slots) from
        Tensor0SSpace.smul_apply 2 x (-1 : Real) (A - B) slots]
    _ = -1 * (A slots - B slots) := by
      rw [show (A - B) slots = A slots - B slots from
        Tensor0SSpace.sub_apply 2 x A B slots]
    _ = B slots - A slots := by ring

@[simp]
theorem ricciUpperBoundSec_apply
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v w : TangentSpace I x) :
    ((ricciUpperBoundSec S) t x) (vec2 (I := I) v w) =
      (1 / 2) * S.scalar t x * (S.base.metric t).inner x v w -
        S.ricciAt t x (vec2 (I := I) v w) := by
  rw [ricciUpperBoundSec_at_point (I := I) S t x]
  calc
    ((1 / 2 * S.scalar t x) • metricTensorField (I := I) (S.base.metric t) x - S.ricci t x)
        (vec2 (I := I) v w)
        = ((1 / 2 * S.scalar t x) • metricTensorField (I := I) (S.base.metric t) x)
            (vec2 (I := I) v w) - (S.ricci t x) (vec2 (I := I) v w) :=
          Tensor0SSpace.sub_apply 2 x
            ((1 / 2 * S.scalar t x) • metricTensorField (I := I) (S.base.metric t) x)
            (S.ricci t x) (vec2 (I := I) v w)
    _ = (1 / 2 * S.scalar t x) * (S.base.metric t).inner x v w -
          S.ricciAt t x (vec2 (I := I) v w) := by
          rw [show ((1 / 2 * S.scalar t x) • metricTensorField (I := I) (S.base.metric t) x)
                  (vec2 (I := I) v w) =
                (1 / 2 * S.scalar t x) *
                  metricTensorField (I := I) (S.base.metric t) x (vec2 (I := I) v w) from
            Tensor0SSpace.smul_apply 2 x (1 / 2 * S.scalar t x)
              (metricTensorField (I := I) (S.base.metric t) x) (vec2 (I := I) v w)]
          simp only [metricTensorField_apply]
          have h0 : vec2 (I := I) v w 0 = v := by
            unfold DifferentialGeometry.Geometry.Curvature.vec2
            simp
          have h1 : vec2 (I := I) v w 1 = w := by
            unfold DifferentialGeometry.Geometry.Curvature.vec2
            norm_num
          rw [h0, h1]
          simp [SolutionOn.ricciAt, SolutionFamily.ricciAt]

theorem ricciUpperBoundSec_symm
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (U : Set Real) :
    TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S)) U := by
  intro t _ht x v w
  have hRic := ricciAt_symm (I := I) S t x v w
  have hg := (S.base.metric t).symm x v w
  change (ricciUpperBoundSec S) t x (vec2 (I := I) v w) =
    (ricciUpperBoundSec S) t x (vec2 (I := I) w v)
  rw [ricciUpperBoundSec_apply (I := I) S t x v w,
    ricciUpperBoundSec_apply (I := I) S t x w v, hRic, hg]

noncomputable def ricciUpperBoundNablaModel
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    TensorNabla1SecFamily (I := I) (M := M) :=
  fun t => -pinchNablaModel (I := I) S (1 / 2) t

noncomputable def ricciUpperBoundNab2ModelSec
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    TensorNabla2SecFamily (I := I) (M := M) :=
  fun t => -pinchNab2ModelSec (I := I) S (1 / 2) t

private def ricciUpperBoundCoordTime
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v : TangentSpace I x) : Real :=
  -(ricciCoordQuadRHS (I := I) S t x v) +
    (1 / 2) *
      ((DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
            (S.scalar t) x +
          2 * normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x)) *
          (S.family.metric t).inner x v v +
        S.scalar t x *
          ((-2 : Real) * S.ricciAt t x (vec2 (I := I) v v)))

private def ricciUpperBoundCoordReact
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v : TangentSpace I x) : Real :=
  normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x) *
      (S.family.metric t).inner x v v -
    S.scalar t x * S.ricciAt t x (vec2 (I := I) v v) -
      ricciCoordReact (I := I) S t x v

noncomputable def ricciUpperBoundReactAt
    (g : SmoothRiemannianMetric I M) {x : M}
    (A : Tensor02At (I := I) (M := M) x) :
    Tensor02At (I := I) (M := M) x :=
  let trA := metricTracePair0SAt (I := I) g A
  let Ric := trA • metricTensorField (I := I) g x - A
  let sc := metricTracePair0SAt (I := I) g Ric
  inner0S (I := I) g x 2 Ric Ric • metricTensorField (I := I) g x -
    sc • Ric - ricciReaction3At (I := I) (M := M) g Ric

noncomputable def ricciUpperBoundReact : TwoTensorReaction (I := I) (M := M) :=
  Tensor02ReactionAt.toRawSymm (I := I) (M := M)
    (fun _t g _x A => ricciUpperBoundReactAt (I := I) g A)

private theorem ricciUpperBoundReact_eval
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v : TangentSpace I x) :
    (ricciUpperBoundReact t (S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t)) x v v =
      ricciUpperBoundReactAt (S.base.metric t) ((ricciUpperBoundSec S) t x)
        (vec2 (I := I) v v) := by
  let Araw : RawTwoTensorField (I := I) (M := M) :=
    twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t
  have hbilin : TwoTensorBilinearAt (I := I) (M := M) Araw x := by
    simpa [Araw] using
      twoTensorSecToFamily_bilin (I := I) (M := M) (ricciUpperBoundSec S) t x
  have hsym : TwoTensorSymmetricAt (I := I) (M := M) Araw x := by
    simpa [Araw] using
      (ricciUpperBoundSec_symm (I := I) S Set.univ) t (by simp) x
  rw [show
      twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t = Araw by rfl]
  rw [ricciUpperBoundReact, Tensor02ReactionAt.toRawSymm_eval_of_bilin
    (I := I) (M := M) (fun _t g x A => ricciUpperBoundReactAt (I := I) g A)
    t (S.base.metric t) Araw x hbilin]
  have hrealSec :
      Tensor02RealizesRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) Araw) x
        ((ricciUpperBoundSec S) t x) := by
    intro X Y
    rw [rawSym2_eq_of_symm (I := I) (M := M) hsym X Y]
    rfl
  have hrealBundled :
      Tensor02RealizesRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) Araw) x
        (tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Araw) x
          (rawSym2_bilin (I := I) (M := M) hbilin)) :=
    tensor02OfRawAt_realizes (I := I) (M := M)
      (rawSym2 (I := I) (M := M) Araw) x
      (rawSym2_bilin (I := I) (M := M) hbilin)
  have hT :
      tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Araw) x
          (rawSym2_bilin (I := I) (M := M) hbilin) =
        (ricciUpperBoundSec S) t x :=
    tensor02_realizes_ext (I := I) (M := M) hrealBundled hrealSec
  rw [hT]

private theorem ricciUpperBoundReactAt_eq_neg_shift
    (g : SmoothRiemannianMetric I M) {x : M}
    (A : Tensor02At (I := I) (M := M) x) (v : TangentSpace I x) :
    ricciUpperBoundReactAt (I := I) g A (vec2 (I := I) v v) =
      -shiftNAt (I := I) (M := M) (1 / 2) 0 g x (-A) (vec2 (I := I) v v) := by
  have hscalar :
      shiftScalar3At (I := I) (M := M) (1 / 2) g (-A) =
        2 * metricTracePair0SAt (I := I) g A := by
    unfold shiftScalar3At
    rw [metricTracePair0SAt_neg (I := I) g A]
    field_simp
    ring
  have hshift :
      shiftRic3At (I := I) (M := M) (1 / 2) g (-A) =
        metricTracePair0SAt (I := I) g A • metricTensorField (I := I) g x - A := by
    unfold shiftRic3At
    rw [hscalar]
    have hsc :
        (1 / 2 * (2 * metricTracePair0SAt (I := I) g A)) =
          metricTracePair0SAt (I := I) g A := by
      ring
    rw [hsc]
    rw [sub_eq_add_neg, add_comm]
    rfl
  unfold ricciUpperBoundReactAt shiftNAt
  rw [hshift]
  let trA : Real := metricTracePair0SAt (I := I) g A
  let Ric : Tensor02At (I := I) (M := M) x := trA • metricTensorField (I := I) g x - A
  let P : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    inner0S (I := I) g x 2 Ric Ric • metricTensorField (I := I) g x
  let Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    metricTracePair0SAt (I := I) g Ric • Ric
  let R : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    ricciReaction3At (I := I) (M := M) g Ric
  let Y : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x := P - Q
  calc
    (P - Q - R) (vec2 (I := I) v v)
        = (P - Q) (vec2 (I := I) v v) - R (vec2 (I := I) v v) :=
          Tensor0SSpace.sub_apply 2 x (P - Q) R (vec2 (I := I) v v)
    _ = (P (vec2 (I := I) v v) - Q (vec2 (I := I) v v)) - R (vec2 (I := I) v v) := by
          rw [show (P - Q) (vec2 (I := I) v v) = P (vec2 (I := I) v v) - Q (vec2 (I := I) v v) from
            Tensor0SSpace.sub_apply 2 x P Q (vec2 (I := I) v v)]
    _ = -(R (vec2 (I := I) v v) - (P (vec2 (I := I) v v) - Q (vec2 (I := I) v v))) := by
          ring
    _ = -(R (vec2 (I := I) v v) - ((2 : Real) * (1 / 2)) * (P (vec2 (I := I) v v) - Q (vec2
      (I := I) v v))) := by
          ring_nf
    _ = -((R - ((2 : Real) * (1 / 2)) • Y) (vec2 (I := I) v v)) := by
          congr 1

private theorem ricciUpperBoundReactAt_of_solution
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (v : TangentSpace I x) :
    ricciUpperBoundReactAt (S.base.metric t) ((ricciUpperBoundSec S) t x)
        (vec2 (I := I) v v) =
      ricciUpperBoundCoordReact S t x v := by
  have hshift :=
    ricciUpperBoundReactAt_eq_neg_shift (I := I) (S.base.metric t)
      ((ricciUpperBoundSec S) t x) v
  rw [hshift]
  have hP : -((ricciUpperBoundSec S) t x) = pinchSec (I := I) S (1 / 2) t x := by
    unfold ricciUpperBoundSec
    simp
  rw [hP]
  rw [pinchSec_at_trace (I := I) (M := M) S (1 / 2) t x]
  obtain ⟨basis, horth⟩ :=
    exists_orthonormalBasisAt (I := I) (S.base.metric t) x hdim
  have hshiftNAt :=
    shiftNAt_pinch (I := I) (M := M) (t := 0) basis horth
      (by norm_num : (1 : Real) - 3 * (1 / 2) ≠ 0) (S.ricci t x)
  have hsc :
      S.scalar t x =
        metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) := by
    simp [SolutionOn.scalar_eq_metricTrace, SolutionOn.ricci,
      SolutionFamily.ricci, SolutionOn.ricciAt, SolutionFamily.ricciAt]
  have hreact := ricciCoordReact_eq_reaction3 (I := I) S hdim (t := t) (x := x) v
  rw [show -shiftNAt (I := I) (M := M) (1 / 2) 0 (S.base.metric t) x
            (S.ricci t x -
              (1 / 2 * metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x)) •
                metricTensorField (I := I) (S.base.metric t) x) (vec2 (I := I) v v) =
        (-shiftNAt (I := I) (M := M) (1 / 2) 0 (S.base.metric t) x
            (S.ricci t x -
              (1 / 2 * metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x)) •
                metricTensorField (I := I) (S.base.metric t) x)) (vec2 (I := I) v v) from
      (Tensor0SSpace.neg_apply 2 x (shiftNAt (I := I) (M := M) (1 / 2) 0 (S.base.metric t) x
            (S.ricci t x -
              (1 / 2 * metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x)) •
                metricTensorField (I := I) (S.base.metric t) x)) (vec2 (I := I) v v)).symm]
  rw [hshiftNAt]
  change -(ricciReaction3At (I := I) (M := M) (S.base.metric t) (S.ricci t x)
        (vec2 (I := I) v v) -
      (2 * (1 / 2)) *
        (inner0S (I := I) (S.base.metric t) x 2 (S.ricci t x) (S.ricci t x) *
            (S.base.metric t).inner x v v -
          metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) *
            (S.ricci t x) (vec2 (I := I) v v))) =
    ricciUpperBoundCoordReact S t x v
  rw [← hreact]
  simp [ricciUpperBoundCoordReact, normSq0S_eq_inner,
    SolutionOn.ricciAt, SolutionFamily.ricciAt]

private theorem ricciUpperBoundNab2ModelSec_neg
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    (ricciUpperBoundNab2ModelSec S t) x = -pinchNab2Model S (1 / 2) t x := by
  simp [ricciUpperBoundNab2ModelSec, pinchNab2ModelSec_apply]

private theorem ricciUpperBoundHeat_coord
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v : TangentSpace I x) :
    tensorHeatWithDrift2QuadMetricAt (I := I) (S.base.metric t)
        (fun _y : M => 0)
        (ricciUpperBoundNab2ModelSec S t x) (ricciUpperBoundNablaModel S t x) v =
      (1 / 2) *
          (DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
            (S.scalar t) x) * (S.base.metric t).inner x v v -
        ricciCoordRough S t x v := by
  classical
  rw [tensorHeatWithDrift2QuadMetricAt_zero_drift]
  rw [ricciUpperBoundNab2ModelSec_neg (I := I) S t x]
  rw [metricTraceFirstTwo0SAt_neg (I := I) (S.base.metric t)
    (pinchNab2Model S (1 / 2) t x) (vec2 (I := I) v v)]
  classical
  let basis :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv :
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) (S.base.metric t) x k l (extChartAt I x x)
  have hinv :
      MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis gInv := by
    simpa [basis, gInv] using
      Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) (S.base.metric t) x
  rw [pinchNab2Model_trace (I := I) S (1 / 2) t basis gInv hinv v]
  rw [ricciRoughTrace_coord (I := I) S t x v]
  rw [scalarHessTrace_eq_lap (I := I) S t x]
  unfold ricciCoordRough
  ring

private theorem ricciUpperBoundQuadDeriv_coord
    [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x : M) (v : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real =>
        twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) s x v v)
      (ricciUpperBoundCoordTime S (t : Real) x v)
      D.carrier (t : Real) := by
  have hP :=
    pinchQuadDeriv_coord (I := I) (M := M) S hS (delta := 1 / 2) t x v
  have hfun :
      (fun s : Real => -(twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S (1 / 2)) s x v v)) =
        fun s : Real =>
          twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) s x v v := by
    funext s
    change -(pinchSec (I := I) S (1 / 2) s x (vec2 (I := I) v v)) =
      (ricciUpperBoundSec S) s x (vec2 (I := I) v v)
    rw [ricciUpperBoundSec_apply (I := I) S s x v v]
    rw [pinchSec_at_trace (I := I) (M := M) S (1 / 2) s x]
    have hsc :
        S.scalar s x =
          metricTracePair0SAt (I := I) (S.base.metric s) (S.ricci s x) := by
      simp [SolutionOn.scalar_eq_metricTrace, SolutionOn.ricci,
        SolutionFamily.ricci, SolutionOn.ricciAt, SolutionFamily.ricciAt]
    rw [hsc]
    simp only [one_div, SolutionOn.ricci_eq, SolutionFamily.ricci_apply, SolutionOn.ricciAt_eq]
    let A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
      metricRicciAt (S.base.metric s) x
    let c : Real :=
      (2 : ℝ)⁻¹ * metricTracePair0SAt (I := I) (S.base.metric s) A
    change -((A - c • metricTensorField (I := I) (S.base.metric s) x) (vec2 (I := I) v v)) =
      c * (S.base.metric s).inner x v v - A (vec2 (I := I) v v)
    change -(A (vec2 (I := I) v v) - c * (S.base.metric s).inner x v v) =
      c * (S.base.metric s).inner x v v - A (vec2 (I := I) v v)
    ring
  rw [← hfun]
  refine hP.neg.congr_deriv ?_
  simp only [ricciUpperBoundCoordTime]
  unfold ricciCoordQuadRHS
  ring

private theorem ricciUpperBoundParabolic_of_react
    [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hreact :
      ∀ t, t ∈ Set.Ioc 0 T -> ∀ x, ∀ v : TangentSpace I x,
        (ricciUpperBoundReact t (S.base.metric t)
          (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t)) x v v =
          ricciUpperBoundCoordReact S t x v) :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S))
      (fun _t x => (0 : TangentSpace I x))
      ricciUpperBoundReact
      (fun t x => ricciUpperBoundNab2ModelSec S t x)
      (fun t x => ricciUpperBoundNablaModel S t x) T := by
  refine ⟨?_⟩
  refine ⟨fun t x v => ricciUpperBoundCoordTime S t x v, ?_, ?_⟩
  · intro t ht x v
    have htreg : t ∈ D.regular := hTreg ht
    have hderiv :=
      ricciUpperBoundQuadDeriv_coord (I := I) (M := M) S hS ⟨t, htreg⟩ x v
    simpa [ricciUpperBoundCoordTime] using hderiv.mono hTsub
  · intro t ht x v
    have hheat := ricciUpperBoundHeat_coord (I := I) S t x v
    have hN := hreact t ht x v
    apply le_of_eq
    calc
      tensorHeatWithDrift2QuadMetricAt (I := I) (S.base.metric t)
            (fun x => (0 : TangentSpace I x))
            (ricciUpperBoundNab2ModelSec S t x) (ricciUpperBoundNablaModel S t x) v +
          (ricciUpperBoundReact t (S.base.metric t)
            (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t)) x v v =
        ((1 / 2) *
            (DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
              (S.scalar t) x) * (S.base.metric t).inner x v v -
          ricciCoordRough S t x v) + ricciUpperBoundCoordReact S t x v := by
            rw [hheat, hN]
      _ = ricciUpperBoundCoordTime S t x v := by
            simp only [ricciUpperBoundCoordTime, ricciUpperBoundCoordReact, ricciCoordReact,
              ricciCoordQuadRHS, ricciCoordRough]
            simp [SolutionOn.family]
            ring

theorem ricciUpperBoundParabolic
    [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T : Real}
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular) :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S))
      (fun _t x => (0 : TangentSpace I x))
      ricciUpperBoundReact
      (fun t x => ricciUpperBoundNab2ModelSec S t x)
      (fun t x => ricciUpperBoundNablaModel S t x) T :=
  ricciUpperBoundParabolic_of_react (I := I) (M := M) S hS hTsub hTreg
    (fun t _ht x v => by
      rw [ricciUpperBoundReact_eval (I := I) S t x v]
      exact ricciUpperBoundReactAt_of_solution (I := I) S (hdim x) (t := t) (x := x) v)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem twoBlockDet_nonneg
    {A : RawTwoTensorField (I := I) (M := M)} {x : M}
    (hsym : TwoTensorSymmetricAt (I := I) (M := M) A x)
    (hbilin : TwoTensorBilinearAt (I := I) (M := M) A x)
    (hpsd : TwoTensorNonnegativeAt (I := I) (M := M) A x)
    (e1 e2 : TangentSpace I x) (a b c : Real)
    (h11 : A x e1 e1 = a) (h22 : A x e2 e2 = b) (h12 : A x e1 e2 = c) :
    0 ≤ a * b - c ^ 2 := by
  have hb : 0 ≤ b := by
    have h := hpsd e2
    rwa [h22] at h
  have ha : 0 ≤ a := by
    have h := hpsd e1
    rwa [h11] at h
  by_cases ha0 : a = 0
  · subst ha0
    have h21 : A x e2 e1 = c := by
      simpa [h12] using hsym e2 e1
    by_cases hc0 : c = 0
    · subst hc0
      simp
    · have hc : c ≠ 0 := hc0
      let t : Real := -(b + 1) / c
      have hw : 0 ≤ A x (e2 + t • e1) (e2 + t • e1) := hpsd _
      rw [raw_quad_add_smul_eq (I := I) (M := M) hsym hbilin (v := e2) (w := e1) (a := t)] at hw
      rw [h22, h21, h11] at hw
      have hlt : b + 2 * t * c < 0 := by
        dsimp [t]
        field_simp [hc]
        ring_nf
        nlinarith
      nlinarith [hlt, hb]
  · have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h21 : A x e2 e1 = c := by
      simpa [h12] using hsym e2 e1
    have hw : 0 ≤ A x ((-c) • e1 + a • e2) ((-c) • e1 + a • e2) := hpsd _
    have hquad := raw_quad_add_smul_eq (I := I) (M := M) hsym hbilin
      (v := (-c) • e1) (w := e2) (a := a)
    rw [hquad] at hw
    have hvc : A x ((-c) • e1) ((-c) • e1) = c ^ 2 * a := by
      rw [hbilin.smul_left (-c) e1 ((-c) • e1),
        hbilin.smul_right (-c) e1 e1, h11]
      ring
    have hvw : A x ((-c) • e1) e2 = -c * c := by
      rw [hbilin.smul_left (-c) e1 e2, h12]
    have hx : 0 ≤ a * (a * b - c ^ 2) := by
      rw [hvc, hvw, h22] at hw
      nlinarith
    have hx2 : 0 ≤ (a * (a * b - c ^ 2)) * a⁻¹ :=
      mul_nonneg hx (inv_nonneg.mpr (le_of_lt hpos))
    have hcancel : (a * (a * b - c ^ 2)) * a⁻¹ = a * b - c ^ 2 := by
      field_simp [ha0]
    rwa [hcancel] at hx2

private theorem ricciUpperBoundReactAt_block
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (a b c : Real) (A : Tensor02At (I := I) (M := M) x)
    (hA : ∀ i j : Fin 3,
      A (vec2 (I := I) (basis i) (basis j)) = shiftBlockS3 a b c i j) :
    ricciUpperBoundReactAt (I := I) g A (vec2 (I := I) (basis 0) (basis 0)) =
      2 * (a * b - c ^ 2) := by
  let trA := metricTracePair0SAt (I := I) g A
  let Ric : Tensor02At (I := I) (M := M) x := trA • metricTensorField (I := I) g x - A
  let RicComp : Fin 3 → Fin 3 → Real := fun i j =>
    (a + b) * DifferentialGeometry.Geometry.Curvature.delta3 i j - shiftBlockS3 a b c i j
  have htrA : trA = a + b := by
    dsimp [trA]
    rw [metricTrace_comp_orthonormal (I := I) (M := M) basis horth A]
    simp_rw [hA, ricciScal3]
    simp [Fin.sum_univ_three, shiftBlockS3]
  have hRicComp : ∀ i j : Fin 3,
      Ric (vec2 (I := I) (basis i) (basis j)) = RicComp i j := by
    intro i j
    dsimp [Ric, RicComp]
    rw [htrA]
    have hmetric :
        metricTensorField (I := I) g x (vec2 (I := I) (basis i) (basis j)) =
          DifferentialGeometry.Geometry.Curvature.delta3 i j := by
      simp [metricTensorField_apply, horth i j,
        vec2, DifferentialGeometry.Geometry.Curvature.vec2]
    calc
      ((a + b) • metricTensorField (I := I) g x - A) (vec2 (I := I) (basis i) (basis j))
          = ((a + b) • metricTensorField (I := I) g x) (vec2 (I := I) (basis i) (basis j)) -
              A (vec2 (I := I) (basis i) (basis j)) :=
            Tensor0SSpace.sub_apply 2 x ((a + b) • metricTensorField (I := I) g x) A
              (vec2 (I := I) (basis i) (basis j))
      _ = (a + b) * DifferentialGeometry.Geometry.Curvature.delta3 i j -
              shiftBlockS3 a b c i j := by
            rw [show ((a + b) • metricTensorField (I := I) g x) (vec2 (I := I) (basis i)
              (basis j)) =
                  (a + b) * metricTensorField (I := I) g x (vec2 (I := I) (basis i) (basis j)) from
              Tensor0SSpace.smul_apply 2 x (a + b) (metricTensorField (I := I) g x)
                (vec2 (I := I) (basis i) (basis j))]
            rw [hmetric, hA]
  have hsc : metricTracePair0SAt (I := I) g Ric = 2 * (a + b) := by
    rw [metricTrace_comp_orthonormal (I := I) (M := M) basis horth Ric]
    simp_rw [hRicComp, ricciScal3]
    simp [RicComp, Fin.sum_univ_three, shiftBlockS3,
      DifferentialGeometry.Geometry.Curvature.delta3]
    ring
  have hnorm : inner0S (I := I) g x 2 Ric Ric = ricciNorm3 RicComp := by
    rw [ricciNorm3_comp_orthonormal (I := I) (M := M) basis horth Ric]
    simp_rw [hRicComp]
  have hreact :
      ricciReaction3At (I := I) (M := M) g Ric (vec2 (I := I) (basis 0) (basis 0)) =
        ricciPresReact (stdRmOfRic3 RicComp) RicComp 0 0 := by
    rw [ricciReaction3At_comp_orthonormal (I := I) (M := M) basis horth Ric]
    have hRm : ∀ p q r s : Fin 3,
        rm04OfRic3At (I := I) (M := M) g Ric
            (vec4 (I := I) (basis p) (basis q) (basis r) (basis s)) =
          stdRmOfRic3 RicComp p q r s := by
      intro p q r s
      rw [rm04OfRic3At_comp_orthonormal (I := I) (M := M) basis horth Ric]
      simp_rw [hRicComp]
    simp [hRicComp, hRm]
  have hmetric00 :
      metricTensorField (I := I) g x (vec2 (I := I) (basis 0) (basis 0)) = 1 := by
    simp [metricTensorField_apply, horth 0 0,
      vec2, DifferentialGeometry.Geometry.Curvature.vec2,
      DifferentialGeometry.Geometry.Curvature.delta3]
  have hmain :
      ricciUpperBoundReactAt (I := I) g A (vec2 (I := I) (basis 0) (basis 0)) =
        inner0S (I := I) g x 2 Ric Ric * 1 -
          metricTracePair0SAt (I := I) g Ric * Ric (vec2 (I := I) (basis 0) (basis 0)) -
          ricciReaction3At (I := I) (M := M) g Ric (vec2 (I := I) (basis 0) (basis 0)) := by
    unfold ricciUpperBoundReactAt
    dsimp
    calc
      (inner0S (I := I) g x 2 (trA • metricTensorField (I := I) g x - A)
            (trA • metricTensorField (I := I) g x - A) •
          metricTensorField (I := I) g x -
        metricTracePair0SAt (I := I) g (trA • metricTensorField (I := I) g x - A) •
            (trA • metricTensorField (I := I) g x - A) -
        ricciReaction3At (I := I) (M := M) g (trA • metricTensorField (I := I) g x - A))
        (vec2 (I := I) (basis 0) (basis 0))
          = (inner0S (I := I) g x 2 (trA • metricTensorField (I := I) g x - A)
                (trA • metricTensorField (I := I) g x - A) •
              metricTensorField (I := I) g x -
            metricTracePair0SAt (I := I) g (trA • metricTensorField (I := I) g x - A) •
                (trA • metricTensorField (I := I) g x - A))
              (vec2 (I := I) (basis 0) (basis 0)) -
            ricciReaction3At (I := I) (M := M) g (trA • metricTensorField (I := I) g x - A)
              (vec2 (I := I) (basis 0) (basis 0)) :=
          Tensor0SSpace.sub_apply 2 x
            (inner0S (I := I) g x 2 (trA • metricTensorField (I := I) g x - A)
                (trA • metricTensorField (I := I) g x - A) •
              metricTensorField (I := I) g x -
            metricTracePair0SAt (I := I) g (trA • metricTensorField (I := I) g x - A) •
                (trA • metricTensorField (I := I) g x - A))
            (ricciReaction3At (I := I) (M := M) g (trA • metricTensorField (I := I) g x - A))
            (vec2 (I := I) (basis 0) (basis 0))
      _ = (inner0S (I := I) g x 2 (trA • metricTensorField (I := I) g x - A)
              (trA • metricTensorField (I := I) g x - A) •
            metricTensorField (I := I) g x) (vec2 (I := I) (basis 0) (basis 0)) -
            (metricTracePair0SAt (I := I) g (trA • metricTensorField (I := I) g x - A) •
                (trA • metricTensorField (I := I) g x - A)) (vec2 (I := I) (basis 0) (basis 0)) -
            ricciReaction3At (I := I) (M := M) g (trA • metricTensorField (I := I) g x - A)
              (vec2 (I := I) (basis 0) (basis 0)) := by
          rw [show (inner0S (I := I) g x 2 (trA • metricTensorField (I := I) g x - A)
                (trA • metricTensorField (I := I) g x - A) •
              metricTensorField (I := I) g x -
            metricTracePair0SAt (I := I) g (trA • metricTensorField (I := I) g x - A) •
                (trA • metricTensorField (I := I) g x - A)) (vec2 (I := I) (basis 0) (basis 0)) =
              (inner0S (I := I) g x 2 (trA • metricTensorField (I := I) g x - A)
                    (trA • metricTensorField (I := I) g x - A) •
                metricTensorField (I := I) g x) (vec2 (I := I) (basis 0) (basis 0)) -
                (metricTracePair0SAt (I := I) g (trA • metricTensorField (I := I) g x - A) •
                    (trA • metricTensorField (I := I) g x - A)) (vec2 (I := I) (basis 0)
                      (basis 0)) from
            Tensor0SSpace.sub_apply 2 x
              (inner0S (I := I) g x 2 (trA • metricTensorField (I := I) g x - A)
                  (trA • metricTensorField (I := I) g x - A) •
                metricTensorField (I := I) g x)
              (metricTracePair0SAt (I := I) g (trA • metricTensorField (I := I) g x - A) •
                (trA • metricTensorField (I := I) g x - A)) (vec2 (I := I) (basis 0) (basis 0))]
      _ = inner0S (I := I) g x 2 (trA • metricTensorField (I := I) g x - A)
              (trA • metricTensorField (I := I) g x - A) * 1 -
            metricTracePair0SAt (I := I) g (trA • metricTensorField (I := I) g x - A) *
                (trA • metricTensorField (I := I) g x - A) (vec2 (I := I) (basis 0) (basis 0)) -
            ricciReaction3At (I := I) (M := M) g (trA • metricTensorField (I := I) g x - A)
              (vec2 (I := I) (basis 0) (basis 0)) := by
          rw [show (inner0S (I := I) g x 2 (trA • metricTensorField (I := I) g x - A)
                    (trA • metricTensorField (I := I) g x - A) •
                metricTensorField (I := I) g x) (vec2 (I := I) (basis 0) (basis 0)) =
              inner0S (I := I) g x 2 (trA • metricTensorField (I := I) g x - A)
                  (trA • metricTensorField (I := I) g x - A) *
                metricTensorField (I := I) g x (vec2 (I := I) (basis 0) (basis 0)) from
            Tensor0SSpace.smul_apply 2 x
              (inner0S (I := I) g x 2 (trA • metricTensorField (I := I) g x - A)
                (trA • metricTensorField (I := I) g x - A))
              (metricTensorField (I := I) g x) (vec2 (I := I) (basis 0) (basis 0))]
          rw [show (metricTracePair0SAt (I := I) g (trA • metricTensorField (I := I) g x - A) •
                (trA • metricTensorField (I := I) g x - A)) (vec2 (I := I) (basis 0) (basis 0)) =
              metricTracePair0SAt (I := I) g (trA • metricTensorField (I := I) g x - A) *
                (trA • metricTensorField (I := I) g x - A) (vec2 (I := I) (basis 0) (basis 0)) from
            Tensor0SSpace.smul_apply 2 x
              (metricTracePair0SAt (I := I) g (trA • metricTensorField (I := I) g x - A))
              (trA • metricTensorField (I := I) g x - A) (vec2 (I := I) (basis 0) (basis 0))]
          rw [hmetric00]
  calc
    ricciUpperBoundReactAt (I := I) g A (vec2 (I := I) (basis 0) (basis 0))
        = inner0S (I := I) g x 2 Ric Ric * 1 -
            metricTracePair0SAt (I := I) g Ric * Ric (vec2 (I := I) (basis 0) (basis 0)) -
            ricciReaction3At (I := I) (M := M) g Ric (vec2 (I := I) (basis 0) (basis 0)) := hmain
    _ = ricciNorm3 RicComp * 1 -
          (2 * (a + b)) * RicComp 0 0 -
          ricciPresReact (stdRmOfRic3 RicComp) RicComp 0 0 := by
          rw [hnorm, hsc, hRicComp 0 0, hreact]
    _ = 2 * (a * b - c ^ 2) := by
          simp [RicComp, ricciNorm3, ricciPresReact, ricciSq3, ricciScal3,
            shiftBlockS3, stdRmOfRic3, DifferentialGeometry.Geometry.Curvature.delta3,
            Fin.sum_univ_three]
          ring

private theorem ricciUpperBoundReact_realizes_block
    {t : Real} {g : SmoothRiemannianMetric I M} {x : M}
    {Araw : RawTwoTensorField (I := I) (M := M)}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (hbilin : TwoTensorBilinearAt (I := I) (M := M) Araw x) :
    (ricciUpperBoundReact t g Araw) x (basis 0) (basis 0) =
      ricciUpperBoundReactAt (I := I) g
        (tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Araw) x
          (rawSym2_bilin (I := I) (M := M) hbilin)) (vec2 (I := I) (basis 0) (basis 0)) := by
  rw [ricciUpperBoundReact, Tensor02ReactionAt.toRawSymm_eval_of_bilin
    (I := I) (M := M) (fun _t g x A => ricciUpperBoundReactAt (I := I) g A)
    t g Araw x hbilin]

private theorem ricciUpperBoundReactAt_block_of_raw
    (g : SmoothRiemannianMetric I M) {x : M}
    {Araw : RawTwoTensorField (I := I) (M := M)}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {a b c : Real}
    (hsym : TwoTensorSymmetricAt (I := I) (M := M) Araw x)
    (hbilin : TwoTensorBilinearAt (I := I) (M := M) Araw x)
    (hblock : ShiftBlockAt (I := I) (M := M) g Araw x basis a b c) :
    ricciUpperBoundReactAt (I := I) g
        (tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Araw) x
          (rawSym2_bilin (I := I) (M := M) hbilin)) (vec2 (I := I) (basis 0) (basis 0)) =
      2 * (a * b - c ^ 2) := by
  let T : Tensor02At (I := I) (M := M) x :=
    tensor02OfRawAt (I := I) (M := M)
      (rawSym2 (I := I) (M := M) Araw) x
      (rawSym2_bilin (I := I) (M := M) hbilin)
  have hreal : Tensor02RealizesRawAt (I := I) (M := M) Araw x T := by
    intro v w
    change tensor02OfRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) Araw) x
        (rawSym2_bilin (I := I) (M := M) hbilin) (vec2 (I := I) v w) = Araw x v w
    rw [tensor02OfRawAt_realizes (I := I) (M := M)]
    exact rawSym2_eq_of_symm (I := I) (M := M) hsym v w
  change ricciUpperBoundReactAt (I := I) g T (vec2 (I := I) (basis 0) (basis 0)) =
    2 * (a * b - c ^ 2)
  exact ricciUpperBoundReactAt_block (I := I) g basis hblock.orthonormal a b c T
    (fun i j => by
      rw [hreal (basis i) (basis j)]
      exact hblock.components i j)

private theorem ricciUpperBoundReact_null_symm
    (G : Real → SmoothRiemannianMetric I M) (U : Set Real)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3) :
    TensorNullEigenvectorConditionSymm (I := I) (M := M) G ricciUpperBoundReact U := by
  intro t ht A x hsym hbilin hpsd v hv
  have hBout : TwoTensorBilinearAt (I := I) (M := M)
      (ricciUpperBoundReact t (G t) A) x := by
    simpa [ricciUpperBoundReact] using
      (Tensor02ReactionAt.toRawSymm_output_bilin (I := I) (M := M) G
        (fun _t g x A => ricciUpperBoundReactAt (I := I) g A) U t ht A x)
  by_cases hv0 : v = 0
  · subst v
    have hzero : (ricciUpperBoundReact t (G t) A) x 0 0 = 0 := by
      have h := hBout.smul_left 0 (0 : TangentSpace I x) (0 : TangentSpace I x)
      simpa using h
    rw [hzero]
  · obtain ⟨nb⟩ :=
      exists_nullOrthonormalBasis3At (I := I) (M := M) (G t)
        (x := x) (v := v) (hdim x) hv0
    rcases nb.scale with ⟨r, hr, hscale⟩
    let a : Real := A x (nb.basis 1) (nb.basis 1)
    let b : Real := A x (nb.basis 2) (nb.basis 2)
    let c : Real := A x (nb.basis 1) (nb.basis 2)
    have hblock : ShiftBlockAt (I := I) (M := M) (G t) A x nb.basis a b c :=
      shiftBlockOfNull (I := I) (M := M) nb.orthonormal hsym hbilin hpsd hv hscale hr
    have hdet : 0 ≤ a * b - c ^ 2 := by
      exact twoBlockDet_nonneg (I := I) (M := M) hsym hbilin hpsd
        (nb.basis 1) (nb.basis 2) a b c (by dsimp [a]) (by dsimp [b])
        (by dsimp [c])
    have heval :
        (ricciUpperBoundReact t (G t) A) x v v = r ^ 2 * (2 * (a * b - c ^ 2)) := by
      rw [hscale]
      rw [hBout.smul_left r (nb.basis 0) (r • nb.basis 0)]
      rw [hBout.smul_right r (nb.basis 0) (nb.basis 0)]
      rw [ricciUpperBoundReact_realizes_block (I := I) (M := M) hbilin]
      rw [ricciUpperBoundReactAt_block_of_raw (I := I) (G t) hsym hbilin hblock]
      ring
    rw [heval]
    exact mul_nonneg (sq_nonneg r)
      (mul_nonneg (by norm_num : (0 : Real) ≤ 2) hdet)

private theorem ricciUpperBoundReact_symmInputOn
    (G : Real → SmoothRiemannianMetric I M) (U : Set Real) :
    TensorReactionSymmInputOn (I := I) (M := M) G ricciUpperBoundReact U :=
  Tensor02ReactionAt.toRawSymm_symmInputOn (I := I) (M := M) G
    (fun _t g _x A => ricciUpperBoundReactAt (I := I) g A) U

theorem ricciUpperBoundReact_null
    (G : Real → SmoothRiemannianMetric I M) (U : Set Real)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3) :
    TensorNullEigenvectorCondition (I := I) (M := M) G ricciUpperBoundReact U :=
  null_of_symm (I := I) (M := M) (ricciUpperBoundReact_symmInputOn (I := I) G U)
    (ricciUpperBoundReact_null_symm (I := I) G U hdim)

private theorem ricciUpperBoundReactAt_shift_invariant
    (g : SmoothRiemannianMetric I M) {x : M}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (A : Tensor02At (I := I) (M := M) x) (c : Real) (v : TangentSpace I x) :
    ricciUpperBoundReactAt (I := I) g (A + c • metricTensorField (I := I) g x)
        (vec2 (I := I) v v) =
      ricciUpperBoundReactAt (I := I) g A (vec2 (I := I) v v) := by
  have h1 := ricciUpperBoundReactAt_eq_neg_shift (I := I) g (A + c • metricTensorField
    (I := I) g x) v
  have h2 := ricciUpperBoundReactAt_eq_neg_shift (I := I) g A v
  have hneg :
      -(A + c • metricTensorField (I := I) g x) =
        -A + (-c) • metricTensorField (I := I) g x := by
    rw [neg_add]
    rw [neg_smul]
  have hshift' :
      shiftNAt (I := I) (M := M) (1 / 2) 0 g x (-A + (-c) • metricTensorField (I := I) g x)
          (vec2 (I := I) v v) =
        shiftNAt (I := I) (M := M) (1 / 2) 0 g x (-A) (vec2 (I := I) v v) := by
    have h := shiftNAt_add_g_quad (I := I) (M := M) (delta := 1 / 2) (c := -c) (t := 0) (g := g)
      (by norm_num : (1 : Real) - 3 * (1 / 2) ≠ 0) hdim (-A) v
    have hzero :
        ((-c) / (1 - 3 * (1 / 2))) * (2 * (1 / 2) - 1) *
            ((3 : Real) • shiftRic3At (I := I) (M := M) (1 / 2) g (-A) -
              metricTracePair0SAt (I := I) g (shiftRic3At (I := I) (M := M) (1 / 2) g (-A)) •
                metricTensorField (I := I) g x) (vec2 (I := I) v v) = 0 := by
      norm_num
    linarith
  rw [h1, h2, hneg]
  exact congrArg Neg.neg hshift'

private theorem ricciUpperBoundReact_barrier_eq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {x : M}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (epsilon d t0 t : Real) (v : TangentSpace I x) :
    (ricciUpperBoundReact t (S.base.metric t)
        (tensorBarrierFamily (fun s : Real => S.base.metric s)
          (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S))
          epsilon d t0 t)) x v v =
      (ricciUpperBoundReact t (S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t)) x v v := by
  let Araw : RawTwoTensorField (I := I) (M := M) :=
    twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t
  let Barr : RawTwoTensorField (I := I) (M := M) :=
    tensorBarrierFamily (fun s : Real => S.base.metric s)
      (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S))
      epsilon d t0 t
  let c : Real := epsilon * (d + t - t0)
  have hBarr : Barr = fun x v w => Araw x v w + c * (S.base.metric t).inner x v w := by
    funext x v w
    simp [Barr, Araw, c, tensorBarrierFamily_apply]
  have hbilinA : TwoTensorBilinearAt (I := I) (M := M) Araw x := by
    simpa [Araw] using
      twoTensorSecToFamily_bilin (I := I) (M := M) (ricciUpperBoundSec S) t x
  have hbilinB : TwoTensorBilinearAt (I := I) (M := M) Barr x := by
    simpa [Barr] using
      barrierBilinearAt (I := I) (M := M)
        (G := fun s : Real => S.base.metric s)
        (S := twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S))
        (epsilon := epsilon) (delta := d) (t0 := t0) (t := t) (x := x)
        (twoTensorSecToFamily_bilin (I := I) (M := M) (ricciUpperBoundSec S) t x)
  have hsymB : TwoTensorSymmetricAt (I := I) (M := M) Barr x := by
    exact barrierSymmAt (I := I) (M := M)
      (G := fun s : Real => S.base.metric s)
      (S := twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S))
      (epsilon := epsilon) (delta := d) (t0 := t0) (t := t) (x := x)
      ((ricciUpperBoundSec_symm (I := I) S Set.univ) t (by simp) x)
  have hrealB :
      Tensor02RealizesRawAt (I := I) (M := M) (rawSym2 (I := I) (M := M) Barr) x
        ((ricciUpperBoundSec S) t x + c • metricTensorField (I := I) (S.base.metric t) x) := by
    intro X Y
    rw [rawSym2_eq_of_symm (I := I) (M := M) hsymB X Y]
    rw [hBarr]
    have hadd :
        ((ricciUpperBoundSec S) t x + c • metricTensorField (I := I) (S.base.metric t) x)
            (vec2 (I := I) X Y) =
          (ricciUpperBoundSec S) t x (vec2 (I := I) X Y) +
            (c • metricTensorField (I := I) (S.base.metric t) x) (vec2 (I := I) X Y) :=
      Tensor0SSpace.add_apply 2 x ((ricciUpperBoundSec S) t x)
        (c • metricTensorField (I := I) (S.base.metric t) x) (vec2 (I := I) X Y)
    rw [hadd]
    rw [show (c • metricTensorField (I := I) (S.base.metric t) x) (vec2 (I := I) X Y) =
          c * metricTensorField (I := I) (S.base.metric t) x (vec2 (I := I) X Y) from
        Tensor0SSpace.smul_apply 2 x c (metricTensorField (I := I) (S.base.metric t) x)
          (vec2 (I := I) X Y)]
    simp only [metricTensorField_apply]
    have h0 : vec2 (I := I) X Y 0 = X := by
      unfold DifferentialGeometry.Geometry.Curvature.vec2
      simp
    have h1 : vec2 (I := I) X Y 1 = Y := by
      unfold DifferentialGeometry.Geometry.Curvature.vec2
      norm_num
    rw [h0, h1]
    dsimp [Araw]
    rw [twoTensorSecToFamily_apply]
  have hrealBundled :
      Tensor02RealizesRawAt (I := I) (M := M) (rawSym2 (I := I) (M := M) Barr) x
        (tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Barr) x
          (rawSym2_bilin (I := I) (M := M) hbilinB)) :=
    tensor02OfRawAt_realizes (I := I) (M := M)
      (rawSym2 (I := I) (M := M) Barr) x
      (rawSym2_bilin (I := I) (M := M) hbilinB)
  have hB : tensor02OfRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) Barr) x
        (rawSym2_bilin (I := I) (M := M) hbilinB) =
      (ricciUpperBoundSec S) t x + c • metricTensorField (I := I) (S.base.metric t) x :=
    tensor02_realizes_ext (I := I) (M := M) hrealBundled hrealB
  rw [ricciUpperBoundReact, Tensor02ReactionAt.toRawSymm_eval_of_bilin
    (I := I) (M := M) (fun _t g x A => ricciUpperBoundReactAt (I := I) g A)
    t (S.base.metric t) Barr x hbilinB]
  rw [hB]
  rw [ricciUpperBoundReactAt_shift_invariant (I := I) (S.base.metric t) hdim
    ((ricciUpperBoundSec S) t x) c v]
  rw [← ricciUpperBoundReact_eval (I := I) S t x v]
  rfl

private theorem ricciUpperBoundSpatialModel
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    TensorSpatialDerivs (I := I) (M := M)
      (fun t : Real => S.base.connection t) (ricciUpperBoundSec S)
      (ricciUpperBoundNablaModel S) (ricciUpperBoundNab2ModelSec S) := by
  constructor
  · intro t
    have h := (pinchSpatialModel (I := I) S (1 / 2)).first t
    have hneg := TotalNabla0SRealizes.smul (I := I) (M := M) (-1 : Real) h
    simpa [ricciUpperBoundSec, ricciUpperBoundNablaModel, pinchNablaModel] using hneg
  · intro t
    have h := (pinchSpatialModel (I := I) S (1 / 2)).second t
    have hneg := TotalNabla0SRealizes.smul (I := I) (M := M) (-1 : Real) h
    simpa [ricciUpperBoundNablaModel, ricciUpperBoundNab2ModelSec, pinchNab2ModelSec,
      pinchNab2Model, pinchNablaModel] using hneg

private theorem ricciUpperBoundSec_neg_pinch_eval
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (v w : TangentSpace I x) :
    twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t x v w =
      -(twoTensorSecToFamily (I := I) (M := M) (pinchSec (I := I) S (1 / 2)) t x v w) := by
  rw [twoTensorSecToFamily_apply, ricciUpperBoundSec_apply (I := I) S t x v w]
  simp only [twoTensorSecToFamily]
  rw [pinchSec_at_trace (I := I) (M := M) S (1 / 2) t x]
  have hsc :
      S.scalar t x =
        metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) := by
    simp [SolutionOn.scalar_eq_metricTrace, SolutionOn.ricci,
      SolutionFamily.ricci, SolutionOn.ricciAt, SolutionFamily.ricciAt]
  rw [hsc]
  simp only [one_div, SolutionOn.ricci_eq, SolutionFamily.ricci_apply, SolutionOn.ricciAt_eq]
  let A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    metricRicciAt (S.base.metric t) x
  let c : Real :=
    (2 : ℝ)⁻¹ * metricTracePair0SAt (I := I) (S.base.metric t) A
  change (2 : ℝ)⁻¹ * metricTracePair0SAt (I := I) (S.base.metric t) A *
        (S.base.metric t).inner x v w - A (vec2 (I := I) v w) =
    -(A (vec2 (I := I) v w) - c * (S.base.metric t).inner x v w)
  ring

private theorem ricciUpperBoundSecFamilyContinuousOnSet
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Set.Icc 0 T)
      (fun t x => (ricciUpperBoundSec S) t x) := by
  have hP := pinchSecFamilyContinuousOnSet (I := I) (M := M) S hS (1 / 2)
  have hneg := Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
    (s := 2) (K := D.carrier)
    (A := fun t x => (pinchSec (I := I) S (1 / 2)) t x) (-1 : Real) hP
  have hmono := Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M) hneg hTsub
  simpa [ricciUpperBoundSec] using hmono

private theorem ricciUpperBoundSec_tangentBundle_cont
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval} {K : Set Real}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hK : K ⊆ Set.Icc 0 T) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
        ((ricciUpperBoundSec S) q.1.1 q.2.proj)) := by
  exact Tensor0SFamilyContinuousOnSet.tangentBundle (I := I) (M := M)
    (Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
      (ricciUpperBoundSecFamilyContinuousOnSet (I := I) S hS hTsub) hK)

private theorem ricciUpperBoundBarrierReg
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T : Real}
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular) :
    TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S))
      (fun _t x => (0 : TangentSpace I x))
      ricciUpperBoundReact T where
  tensor_eval_continuous := by
    intro x v w
    have hP := pinchEval_contOn (I := I) (M := M) S hS (delta := 1 / 2) hTsub x v w
    convert hP.neg using 1
    ext t
    rw [ricciUpperBoundSec_neg_pinch_eval (I := I) S]
  metric_eval_continuous := by
    intro x v w
    simpa [SolutionOn.family] using
      ((hS.smoothMetric.coeff_cont x v w).mono hTsub)
  barrier_eval_continuous := by
    intro epsilon d t0 hsub x v w
    have hScont :
        ContinuousOn
          (fun t : Real =>
            twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t x v w)
          (Set.Icc t0 (t0 + d)) := by
      convert ((pinchEval_contOn (I := I) (M := M) S hS
        (delta := 1 / 2) hTsub x v w).neg).mono hsub using 1
      ext t
      rw [ricciUpperBoundSec_neg_pinch_eval (I := I) S]
    have hGcont :
        ContinuousOn
          (fun t : Real => (S.base.metric t).inner x v w)
          (Set.Icc t0 (t0 + d)) := by
      exact
        (by
          simpa [SolutionOn.family] using
            ((hS.smoothMetric.coeff_cont x v w).mono hTsub) :
          ContinuousOn
            (fun t : Real => (S.base.metric t).inner x v w)
            (Set.Icc 0 T)).mono hsub
    have hcoef :
        ContinuousOn (fun t : Real => epsilon * (d + t - t0))
          (Set.Icc t0 (t0 + d)) := by
      have hlin : Continuous (fun t : Real => d + t - t0) :=
        (continuous_const.add continuous_id).sub continuous_const
      exact (continuous_const.mul hlin).continuousOn
    simpa [tensorBarrierFamily] using hScont.add (hcoef.mul hGcont)
  metricGainControl :=
    pinchMetricGain (I := I) (M := M) S hS hTsub hTreg
  smallBarrierLip := by
    intro delta0 t0 hdelta0 hsub0
    refine ⟨0, le_rfl, ?_⟩
    intro epsilon d hepsilon hd hdle t ht x v
    have heq := ricciUpperBoundReact_barrier_eq (I := I) S (hdim x)
      (epsilon := epsilon) (d := d) (t0 := t0) (t := t) v
    rw [heq]
    simp

private theorem ricciUpperBoundSecCore
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T : Real}
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular) :
    TensorWMPSectionCore (I := I) (M := M)
      (fun t : Real => S.base.metric t) (ricciUpperBoundSec S)
      (fun _t x => (0 : TangentSpace I x)) ricciUpperBoundReact T := by
  exact TensorWMPSectionCore.ofSmoothMetric (I := I) (M := M)
    (G := S.family) (S := ricciUpperBoundSec S)
    (X := fun _t x => (0 : TangentSpace I x)) (N := ricciUpperBoundReact) (T := T)
    hTsub hS.smoothMetric
    (ricciUpperBoundSec_symm (I := I) S (Set.Icc 0 T))
    (by simpa [SolutionOn.family] using ricciUpperBoundBarrierReg (I := I) S hS hdim hTsub hTreg)
    (fun d t0 _hd hsub =>
      ricciUpperBoundSec_tangentBundle_cont (I := I) S hS hTsub hsub)
    (fun epsilon d t0 _hepsilon _hd hsub x v =>
      (ricciUpperBoundBarrierReg (I := I) S hS hdim hTsub hTreg).barrier_eval_continuous
        epsilon d t0 hsub x v v)

theorem ricciUpperBoundPreserved
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T : Real}
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hT : 0 ≤ T)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S)) 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S)) (Set.Icc 0 T) := by
  exact tensor_wmp (I := I) (M := M)
    { hT := hT
      reg := ricciUpperBoundSecCore (I := I) S hS.isSolution hdim hTsub hTreg
      parabolic := ricciUpperBoundParabolic (I := I) S hS hdim hTsub hTreg
      null := ricciUpperBoundReact_null (fun t : Real => S.base.metric t) (Set.Icc 0 T) hdim
      initial := hinit
      hcov1 := fun t => ricciCov1 (I := I) S t
      hcovInf := fun t => ricciCovInf (I := I) S t
      hmc := fun t => ricciMetricComp (I := I) S t
      spatial := ricciUpperBoundSpatialModel (I := I) S }

theorem ricci_upper_bound_of_metricCurvatureOperatorNonnegative
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hcone : DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
      DifferentialGeometry.Geometry.Curvature.algebraicCurvatureOperatorNonnegativeCone) :
    ∀ v : TangentSpace I x,
      S.ricciAt t x (vec2 (I := I) v v) ≤
        (S.scalar t x / 2) * (S.base.metric t).inner x v v := by
  have hsymm : DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I) (S.ricciAt t x) :=
    ricciAt_symm (I := I) S t x
  have htrace : ∀ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      OrthonormalBasisAt (I := I) (S.base.metric t) x basis →
        RiemannFromRicci3DTraceDataAt (I := I) (S.base.metric t) (-(S.ricciAt t x))
          (-(S.scalar t x))
          (DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt
            (I := I) (M := M) (S.base.metric t) x :
              DifferentialGeometry.Geometry.Curvature.Tensor04At (I := I) (M := M) x) basis := by
    intro basis horth
    have htd := traceData_metricTrace (I := I) (M := M) S (t := t) (x := x) horth
    have hsc : S.scalar t x =
        DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I)
          (S.base.metric t) (S.ricciAt t x) := by
      simp
    have hrm : S.base.rm04 t x =
        DifferentialGeometry.Geometry.Curvature.metricRm04At (I := I) (M := M)
          (S.base.metric t) x := by
      rfl
    rw [hrm] at htd
    simpa [hsc] using htd
  intro v
  exact (DifferentialGeometry.Geometry.Curvature.algebraicCurvatureOperatorNonnegative_iff_ricci_upper_bound3
    (I := I) (M := M) (g := S.base.metric t) (Ric := S.ricciAt t x) (scalar := S.scalar t x)
    (A := DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt
      (I := I) (M := M) (S.base.metric t) x)
    (hdim := hdim) (hsymm := hsymm) (htrace := htrace)).mp hcone v

theorem metricCurvatureOperatorNonnegative_of_ricci_upper_bound_at
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hUpper : ∀ v : TangentSpace I x,
      S.ricciAt t x (vec2 (I := I) v v) ≤
        (S.scalar t x / 2) * (S.base.metric t).inner x v v) :
    DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
      DifferentialGeometry.Geometry.Curvature.algebraicCurvatureOperatorNonnegativeCone := by
  have hsymm : DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I) (S.ricciAt t x) :=
    ricciAt_symm (I := I) S t x
  have htrace : ∀ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      OrthonormalBasisAt (I := I) (S.base.metric t) x basis →
        RiemannFromRicci3DTraceDataAt (I := I) (S.base.metric t) (-(S.ricciAt t x))
          (-(S.scalar t x))
          (DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt
            (I := I) (M := M) (S.base.metric t) x :
              DifferentialGeometry.Geometry.Curvature.Tensor04At (I := I) (M := M) x) basis := by
    intro basis horth
    have htd := traceData_metricTrace (I := I) (M := M) S (t := t) (x := x) horth
    have hsc : S.scalar t x =
        DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I)
          (S.base.metric t) (S.ricciAt t x) := by
      simp
    have hrm : S.base.rm04 t x =
        DifferentialGeometry.Geometry.Curvature.metricRm04At (I := I) (M := M)
          (S.base.metric t) x := by
      rfl
    rw [hrm] at htd
    simpa [hsc] using htd
  exact (DifferentialGeometry.Geometry.Curvature.algebraicCurvatureOperatorNonnegative_iff_ricci_upper_bound3
    (I := I) (M := M) (g := S.base.metric t) (Ric := S.ricciAt t x) (scalar := S.scalar t x)
    (A := DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt
      (I := I) (M := M) (S.base.metric t) x)
    (hdim := hdim) (hsymm := hsymm) (htrace := htrace)).mpr hUpper

theorem metricCurvatureOperatorNonnegative_of_ricci_upper_bound
    [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hdim : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3)
    (hUpper : ∀ (t : ℝ) (x : M) (v : TangentSpace I x),
      S.ricciAt t x (vec2 (I := I) v v) ≤
        (S.scalar t x / 2) * (S.base.metric t).inner x v v) :
    ∀ (t : ℝ) (x : M),
      DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          DifferentialGeometry.Geometry.Curvature.algebraicCurvatureOperatorNonnegativeCone :=
  fun t x =>
    metricCurvatureOperatorNonnegative_of_ricci_upper_bound_at (I := I) S (hdim x)
      (t := t) (x := x) (fun v => hUpper t x v)

theorem metricCurvatureOperatorNonnegative_preserved
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T : Real}
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hT : 0 ≤ T)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hinit : ∀ x : M,
      DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric 0) x ∈
      DifferentialGeometry.Geometry.Curvature.algebraicCurvatureOperatorNonnegativeCone) :
    ∀ t, t ∈ Set.Icc 0 T -> ∀ x : M,
      DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
      DifferentialGeometry.Geometry.Curvature.algebraicCurvatureOperatorNonnegativeCone := by
  have hinitUpper :
      TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S)) 0 := by
    intro x v
    rw [twoTensorSecToFamily_apply, ricciUpperBoundSec_apply (I := I) S 0 x v v]
    have hb := ricci_upper_bound_of_metricCurvatureOperatorNonnegative (I := I) S (hdim x)
      (t := 0) (x := x) (hinit x) v
    linarith
  have hnonneg := ricciUpperBoundPreserved (I := I) hS (T := T) hdim hT hTsub hTreg hinitUpper
  intro t ht x
  exact metricCurvatureOperatorNonnegative_of_ricci_upper_bound_at (I := I) S (hdim x)
    (t := t) (x := x) (by
      intro v
      have hTv := hnonneg t ht x v
      rw [twoTensorSecToFamily_apply, ricciUpperBoundSec_apply (I := I) S t x v v] at hTv
      linarith)
end DifferentialGeometry.PDE.RicciFlow
