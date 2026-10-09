import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.NonnegativeCurvatureOperator

/-!
# Preservation of a time-dependent shift of the three-dimensional Ricci upper bound

For a smooth Ricci flow on a compact boundaryless 3-manifold let
`A = ricciUpperBoundSec S = (R / 2) g - Ric`. For a differentiable `f` with
`2 f(t) Ric ≤ f'(t) g` on `[0, T]`, the tensor `A + f(t) g(t)` stays nonnegative on `[0, T]` if it
is nonnegative at `t = 0`.

The proof is the weak tensor maximum principle (`tensor_weak_maximum_principle`) applied to the
section family `A + f(t) g(t)` with reaction `N(A) + f'(t) g - 2 f(t) Ric`, where `N` is the
reaction `ricciUpperBoundReact` of `NonnegativeCurvatureOperator.lean`. Its quadratic form is
invariant under adding multiples of the metric (re-proved here for an arbitrary shift), which
gives the null-eigenvector condition, the parabolic inequality and a zero Lipschitz constant for
the maximum principle's internal barrier. With `f ≡ 0` this is `ricci_upper_bound_preserved`.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

/-! ### Quadratic shift invariance of the reaction -/

private theorem reactAt_eq_neg_shiftNAt
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

private theorem reactAt_add_smul_metric
    (g : SmoothRiemannianMetric I M) {x : M}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (A : Tensor02At (I := I) (M := M) x) (c : Real) (v : TangentSpace I x) :
    ricciUpperBoundReactAt (I := I) g (A + c • metricTensorField (I := I) g x)
        (vec2 (I := I) v v) =
      ricciUpperBoundReactAt (I := I) g A (vec2 (I := I) v v) := by
  have h1 := reactAt_eq_neg_shiftNAt (I := I) g (A + c • metricTensorField (I := I) g x) v
  have h2 := reactAt_eq_neg_shiftNAt (I := I) g A v
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

/-- The quadratic form of `ricciUpperBoundReact` is unchanged when a multiple of the metric is
added to a symmetric bilinear input. -/
theorem ricciUpperBoundReact_add_smul_metric
    (t : Real) (g : SmoothRiemannianMetric I M)
    {A : RawTwoTensorField (I := I) (M := M)} {x : M}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hsym : TwoTensorSymmetricAt (I := I) (M := M) A x)
    (hbilin : TwoTensorBilinearAt (I := I) (M := M) A x)
    (c : Real) (v : TangentSpace I x) :
    ricciUpperBoundReact t g (fun y a b => A y a b + c * g.inner y a b) x v v =
      ricciUpperBoundReact t g A x v v := by
  let Ash : RawTwoTensorField (I := I) (M := M) := fun y a b => A y a b + c * g.inner y a b
  have hg := metricInner_bilinAt (I := I) (M := M) (fun _ : Real => g) 0 x
  have hbilinSh : TwoTensorBilinearAt (I := I) (M := M) Ash x := by
    constructor
    · intro X Y Z
      simp only [Ash, hbilin.add_left X Y Z, hg.add_left X Y Z]
      ring
    · intro a X Z
      simp only [Ash, hbilin.smul_left a X Z, hg.smul_left a X Z]
      ring
    · intro X Y Z
      simp only [Ash, hbilin.add_right X Y Z, hg.add_right X Y Z]
      ring
    · intro a X Z
      simp only [Ash, hbilin.smul_right a X Z, hg.smul_right a X Z]
      ring
  let TA : Tensor02At (I := I) (M := M) x :=
    tensor02OfRawAt (I := I) (M := M) (rawSym2 (I := I) (M := M) A) x
      (rawSym2_bilin (I := I) (M := M) hbilin)
  have hrealA : Tensor02RealizesRawAt (I := I) (M := M) A x TA := by
    intro X Y
    change tensor02OfRawAt (I := I) (M := M) (rawSym2 (I := I) (M := M) A) x
        (rawSym2_bilin (I := I) (M := M) hbilin) (vec2 (I := I) X Y) = A x X Y
    rw [tensor02OfRawAt_realizes (I := I) (M := M)]
    exact rawSym2_eq_of_symm (I := I) (M := M) hsym X Y
  have hrealSh :
      Tensor02RealizesRawAt (I := I) (M := M) (rawSym2 (I := I) (M := M) Ash) x
        (TA + c • metricTensorField (I := I) g x) := by
    intro X Y
    have hsymSh : TwoTensorSymmetricAt (I := I) (M := M) Ash x := by
      intro a b
      simp only [Ash, hsym a b, g.symm x a b]
    rw [rawSym2_eq_of_symm (I := I) (M := M) hsymSh X Y]
    rw [show (TA + c • metricTensorField (I := I) g x) (vec2 (I := I) X Y) =
        TA (vec2 (I := I) X Y) + (c • metricTensorField (I := I) g x) (vec2 (I := I) X Y) from
      Tensor0SSpace.add_apply 2 x TA (c • metricTensorField (I := I) g x) (vec2 (I := I) X Y)]
    rw [show (c • metricTensorField (I := I) g x) (vec2 (I := I) X Y) =
        c * metricTensorField (I := I) g x (vec2 (I := I) X Y) from
      Tensor0SSpace.smul_apply 2 x c (metricTensorField (I := I) g x) (vec2 (I := I) X Y)]
    rw [hrealA X Y, metricTensorField_apply]
    have h0 : vec2 (I := I) X Y 0 = X := by
      unfold DifferentialGeometry.Geometry.Curvature.vec2
      simp
    have h1 : vec2 (I := I) X Y 1 = Y := by
      unfold DifferentialGeometry.Geometry.Curvature.vec2
      norm_num
    rw [h0, h1]
  have hT : tensor02OfRawAt (I := I) (M := M) (rawSym2 (I := I) (M := M) Ash) x
        (rawSym2_bilin (I := I) (M := M) hbilinSh) =
      TA + c • metricTensorField (I := I) g x :=
    tensor02_realizes_ext (I := I) (M := M)
      (tensor02OfRawAt_realizes (I := I) (M := M) (rawSym2 (I := I) (M := M) Ash) x
        (rawSym2_bilin (I := I) (M := M) hbilinSh)) hrealSh
  change ricciUpperBoundReact t g Ash x v v = ricciUpperBoundReact t g A x v v
  rw [ricciUpperBoundReact, Tensor02ReactionAt.toRawSymm_eval_of_bilin
      (I := I) (M := M) (fun _ g _ A => ricciUpperBoundReactAt (I := I) g A)
      t g Ash x hbilinSh,
    Tensor02ReactionAt.toRawSymm_eval_of_bilin
      (I := I) (M := M) (fun _ g _ A => ricciUpperBoundReactAt (I := I) g A)
      t g A x hbilin]
  rw [hT]
  exact reactAt_add_smul_metric (I := I) g hdim TA c v

/-! ### The shifted family and its reaction -/

private noncomputable def shiftSec
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (f : Real → Real) :
    TwoTensorSecFamily (I := I) (M := M) :=
  fun t =>
    letI := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
    ricciUpperBoundSec S t + f t • Tensor0SBundle.metricTensorField (I := I) (S.base.metric t)

private theorem shiftSec_apply
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (f : Real → Real)
    (t : Real) (x : M) (v w : TangentSpace I x) :
    twoTensorSecToFamily (I := I) (M := M) (shiftSec S f) t x v w =
      twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t x v w +
        f t * (S.base.metric t).inner x v w := by
  simp only [twoTensorSecToFamily, shiftSec, ContMDiffSection.coe_add, Pi.add_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply]
  change
    ((ricciUpperBoundSec S) t x (vec2 (I := I) v w) +
        f t * (Tensor0SBundle.metricTensorField (I := I) (S.base.metric t) x)
          (vec2 (I := I) v w)) =
      (ricciUpperBoundSec S) t x (vec2 (I := I) v w) + f t * (S.base.metric t).inner x v w
  rw [Tensor0SBundle.metricTensorField_apply]
  have h0 : vec2 (I := I) v w 0 = v := by
    simp [DifferentialGeometry.Geometry.Curvature.vec2]
  have h1 : vec2 (I := I) v w 1 = w := by
    simp [DifferentialGeometry.Geometry.Curvature.vec2]
  rw [h0, h1]

private theorem shiftSec_raw
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (f : Real → Real) (t : Real) :
    twoTensorSecToFamily (I := I) (M := M) (shiftSec S f) t =
      fun y a b => twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t y a b +
        f t * (S.base.metric t).inner y a b := by
  funext y a b
  exact shiftSec_apply (I := I) S f t y a b

private noncomputable def shiftReact (f : Real → Real) : TwoTensorReaction (I := I) (M := M) :=
  fun t g A x v w =>
    ricciUpperBoundReact t g A x v w +
      (deriv f t * g.inner x v w -
        2 * f t * metricRicciAt (I := I) (M := M) g x (vec2 (I := I) v w))

private theorem shiftReact_shiftSec
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {x : M} (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (t c : Real) (v : TangentSpace I x) :
    ricciUpperBoundReact t (S.base.metric t)
        (fun y a b => twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t y a b +
          c * (S.base.metric t).inner y a b) x v v =
      ricciUpperBoundReact t (S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t) x v v :=
  ricciUpperBoundReact_add_smul_metric (I := I) t (S.base.metric t) hdim
    ((ricci_upper_bound_sec_symm (I := I) S Set.univ) t (Set.mem_univ t) x)
    (twoTensorSecToFamily_bilin (I := I) (M := M) (ricciUpperBoundSec S) t x) c v

/-! ### Regularity of the shifted family -/

private theorem shiftSec_symm
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (f : Real → Real) (U : Set Real) :
    TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) (shiftSec S f)) U := by
  intro t _ x v w
  rw [shiftSec_apply (I := I) S f t x v w, shiftSec_apply (I := I) S f t x w v,
    (ricci_upper_bound_sec_symm (I := I) S Set.univ) t (Set.mem_univ t) x v w,
    (S.base.metric t).symm x v w]

private theorem shiftSec_familyCont
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {f : Real → Real} (hf : Continuous f) {T : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Set.Icc 0 T)
      (fun t x => (shiftSec S f) t x) := by
  have hP := pinchSecFamilyContinuousOnSet (I := I) (M := M) S hS (1 / 2)
  have hneg := tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
    (s := 2) (K := D.carrier)
    (A := fun t x => (pinchSec (I := I) S (1 / 2)) t x) (-1 : Real) hP
  have hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Set.Icc 0 T)
      (fun t x => (ricciUpperBoundSec S) t x) := by
    have hmono := tensor0SFamilyContinuousOnSet.mono (I := I) (M := M) hneg hTsub
    simpa [ricciUpperBoundSec] using hmono
  have hG : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Set.Icc 0 T)
      (fun t x => metricTensorField (I := I) (S.base.metric t) x) :=
    tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
      (by simpa [SolutionOn.family] using hS.smoothMetric.metricTensor_cont) hTsub
  have hfc : Continuous (fun q : {t : Real // t ∈ Set.Icc 0 T} × M => f q.1.1) :=
    hf.comp (continuous_subtype_val.comp continuous_fst)
  have hsum := hA.add (tensor0SFamilyContinuousOnSet.smul (I := I) (M := M) (f := fun t _ => f t) hfc hG)
  simpa [shiftSec] using hsum

private theorem shiftSec_barrierRegularity
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T : Real}
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    {f : Real → Real} (hf : Continuous f) :
    TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (shiftSec S f))
      (fun _ x => (0 : TangentSpace I x))
      (shiftReact f) T where
  tensor_eval_continuous := by
    intro x v w
    have h := tensorEval_contOn (I := I) (M := M)
      (shiftSec_familyCont (I := I) S hS hf hTsub) x v w
    simpa [twoTensorSecToFamily] using h
  metric_eval_continuous := by
    intro x v w
    simpa [SolutionOn.family] using
      ((hS.smoothMetric.coeff_cont x v w).mono hTsub)
  barrier_eval_continuous := by
    intro epsilon d t0 hsub x v w
    have hScont :
        ContinuousOn
          (fun t : Real => twoTensorSecToFamily (I := I) (M := M) (shiftSec S f) t x v w)
          (Set.Icc t0 (t0 + d)) := by
      have h := tensorEval_contOn (I := I) (M := M)
        (shiftSec_familyCont (I := I) S hS hf hTsub) x v w
      exact (by simpa [twoTensorSecToFamily] using h :
        ContinuousOn
          (fun t : Real => twoTensorSecToFamily (I := I) (M := M) (shiftSec S f) t x v w)
          (Set.Icc 0 T)).mono hsub
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
    have hadd := hScont.add (hcoef.mul hGcont)
    have hfun :
        (fun t : Real => twoTensorSecToFamily (I := I) (M := M) (shiftSec S f) t x v w) +
          (fun t : Real => epsilon * (d + t - t0)) *
            (fun t : Real => (S.base.metric t).inner x v w) =
          fun t => tensorBarrierFamily (I := I) (M := M) S.base.metric
            (twoTensorSecToFamily (I := I) (M := M) (shiftSec S f))
            epsilon d t0 t x v w := by
      funext t
      rw [Pi.add_apply, Pi.mul_apply, tensorBarrierFamily_apply]
    rw [hfun] at hadd
    exact hadd
  metricGainControl :=
    pinchMetricGain (I := I) (M := M) S hS hTsub hTreg
  smallBarrierLip := by
    intro delta0 t0 _ _
    refine ⟨0, le_rfl, ?_⟩
    intro epsilon d _ _ _ t _ x v
    have hbar :
        tensorBarrierFamily (I := I) (M := M) (fun s : Real => S.base.metric s)
            (twoTensorSecToFamily (I := I) (M := M) (shiftSec S f)) epsilon d t0 t =
          fun y a b => twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t y a b +
            (f t + epsilon * (d + t - t0)) * (S.base.metric t).inner y a b := by
      funext y a b
      rw [tensorBarrierFamily_apply, shiftSec_apply (I := I) S f t y a b]
      ring
    have hS1 := shiftReact_shiftSec (I := I) S (hdim x) t (f t) v
    have hS2 := shiftReact_shiftSec (I := I) S (hdim x) t (f t + epsilon * (d + t - t0)) v
    simp only [shiftReact]
    rw [hbar, shiftSec_raw (I := I) S f t, hS1, hS2]
    simp

/-! ### Parabolic inequality, null condition and spatial derivatives -/

private theorem shiftSec_parabolic
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T : Real}
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    {f : Real → Real} (hf : Differentiable Real f) :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M) (shiftSec S f))
      (fun _ x => (0 : TangentSpace I x))
      (shiftReact f)
      (fun t x => ricciUpperBoundNab2ModelSec S t x)
      (fun t x => ricciUpperBoundNablaModel S t x) T := by
  obtain ⟨⟨timeDerivA, hderivA, hineqA⟩⟩ :=
    ricci_upper_bound_parabolic (I := I) S hS hdim hTsub hTreg
  refine ⟨⟨fun t x v => timeDerivA t x v +
    (deriv f t * (S.base.metric t).inner x v v +
      f t * ((-2 : Real) * S.ricciAt t x (vec2 (I := I) v v))), ?_, ?_⟩⟩
  · intro t ht x v
    have h1 := hderivA t ht x v
    have h2 : HasDerivWithinAt f (deriv f t) (Set.Icc 0 T) t :=
      (hf t).hasDerivAt.hasDerivWithinAt
    have h3 : HasDerivWithinAt (fun s : Real => (S.base.metric s).inner x v v)
        ((-2 : Real) * S.ricciAt t x (vec2 (I := I) v v)) (Set.Icc 0 T) t := by
      have h := metric_derivWithin_eq_neg_two_ricci (I := I) S hS.isSolution
        ⟨t, hTreg ht⟩ x v v
      simpa [SolutionOn.family] using h.mono hTsub
    have hsum := h1.add (h2.mul h3)
    have hfun :
        (fun s : Real => twoTensorSecToFamily (I := I) (M := M) (shiftSec S f) s x v v) =
          fun s : Real => twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) s x v v +
            f s * (S.base.metric s).inner x v v := by
      funext s
      exact shiftSec_apply (I := I) S f s x v v
    rw [hfun]
    exact hsum
  · intro t ht x v
    have hA := hineqA t ht x v
    have hN : shiftReact f t (S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M) (shiftSec S f) t) x v v =
          ricciUpperBoundReact t (S.base.metric t)
            (twoTensorSecToFamily (I := I) (M := M) (ricciUpperBoundSec S) t) x v v +
          (deriv f t * (S.base.metric t).inner x v v -
            2 * f t * S.ricciAt t x (vec2 (I := I) v v)) := by
      simp only [shiftReact]
      rw [shiftSec_raw (I := I) S f t, shiftReact_shiftSec (I := I) S (hdim x) t (f t) v]
      rfl
    rw [hN]
    linarith

private theorem shiftReact_null
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) {T : Real}
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    {f : Real → Real}
    (hgain : ∀ t ∈ Set.Icc 0 T, ∀ (x : M) (v : TangentSpace I x),
      2 * f t * S.ricciAt t x (vec2 (I := I) v v) ≤ deriv f t * (S.base.metric t).inner x v v) :
    TensorNullEigenvectorCondition (I := I) (M := M) (fun t : Real => S.base.metric t)
      (shiftReact f) (Set.Icc 0 T) := by
  intro t ht A x hsym hbilin hA v hv
  have h1 := ricci_upper_bound_reaction_null (I := I) (fun t : Real => S.base.metric t)
    (Set.Icc 0 T) hdim t ht A x hsym hbilin hA v hv
  have h2 := hgain t ht x v
  change 0 ≤ ricciUpperBoundReact t (S.base.metric t) A x v v +
    (deriv f t * (S.base.metric t).inner x v v -
      2 * f t * S.ricciAt t x (vec2 (I := I) v v))
  linarith

private theorem upperSpatial
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
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

private theorem shiftSpatial
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (f : Real → Real) :
    TensorSpatialDerivs (I := I) (M := M)
      (fun t : Real => S.base.connection t) (shiftSec S f)
      (ricciUpperBoundNablaModel S) (ricciUpperBoundNab2ModelSec S) := by
  have hA := upperSpatial (I := I) S
  constructor
  · intro t
    let := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
    let := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3
    have hmetric :
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 (S.base.connection t) (Tensor0SBundle.metricTensorField (I := I) (S.base.metric t))
          (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (n := (∞ : WithTop ℕ∞)) 3) :=
      Tensor0SBundle.zero_realizes_metric (I := I) (S.base.connection t) (S.base.metric t)
        (ricciMetricComp (I := I) S t)
    have hscaled :
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 (S.base.connection t)
          (f t • Tensor0SBundle.metricTensorField (I := I) (S.base.metric t))
          (f t • (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (n := (∞ : WithTop ℕ∞)) 3)) :=
      TotalNabla0SRealizes.smul (I := I) (M := M) (f t) hmetric
    have hadd := TotalNabla0SRealizes.add (I := I) (M := M) (hA.first t) hscaled
    simpa [shiftSec] using hadd
  · intro t
    exact hA.second t

/-! ### The preservation theorem -/

/-- Preservation of `(R / 2) g - Ric + f(t) g ≥ 0` along a smooth Ricci flow on a compact
boundaryless 3-manifold, for a differentiable `f` with `2 f(t) Ric ≤ f'(t) g` on `[0, T]`. -/
theorem ricci_upper_bound_add_smul_metric_preserved
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T : Real}
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    {f : Real → Real} (hf : Differentiable Real f)
    (hgain : ∀ t ∈ Set.Icc 0 T, ∀ (x : M) (v : TangentSpace I x),
      2 * f t * S.ricciAt t x (vec2 (I := I) v v) ≤ deriv f t * (S.base.metric t).inner x v v)
    (hinit : ∀ (x : M) (v : TangentSpace I x),
      0 ≤ (ricciUpperBoundSec S) 0 x (vec2 (I := I) v v) +
        f 0 * (S.base.metric 0).inner x v v) :
    ∀ t ∈ Set.Icc 0 T, ∀ (x : M) (v : TangentSpace I x),
      0 ≤ (ricciUpperBoundSec S) t x (vec2 (I := I) v v) +
        f t * (S.base.metric t).inner x v v := by
  intro t ht x v
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hbar := shiftSec_barrierRegularity (I := I) S hS.isSolution hdim hTsub hTreg hf.continuous
  have hreg :
      TensorWeakMaximumPrincipleSectionCompactness (I := I) (M := M)
        (fun t : Real => S.base.metric t) (shiftSec S f)
        (fun _ x => (0 : TangentSpace I x)) (shiftReact f) T :=
    TensorWeakMaximumPrincipleSectionCompactness.ofSmoothMetric (I := I) (M := M)
      (G := S.family) (S := shiftSec S f)
      (X := fun _ x => (0 : TangentSpace I x)) (N := shiftReact f) (T := T)
      hTsub hS.isSolution.smoothMetric
      (shiftSec_symm (I := I) S f (Set.Icc 0 T))
      (by simpa [SolutionOn.family] using hbar)
      (fun _ _ _ hsub =>
        tensor0SFamilyContinuousOnSet.tangentBundle (I := I) (M := M)
          (tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
            (shiftSec_familyCont (I := I) S hS.isSolution hf.continuous hTsub) hsub))
      (fun epsilon d t0 _ _ hsub x v =>
        hbar.barrier_eval_continuous epsilon d t0 hsub x v v)
  have hinit' : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) (shiftSec S f)) 0 := by
    intro y w
    rw [shiftSec_apply (I := I) S f 0 y w w, twoTensorSecToFamily_apply]
    exact hinit y w
  have hnonneg := tensor_weak_maximum_principle (I := I) (M := M)
    { time_nonneg := hT
      regularity := hreg
      parabolic := shiftSec_parabolic (I := I) S hS hdim hTsub hTreg hf
      null := shiftReact_null (I := I) S hdim hgain
      initial := hinit'
      connection_contMDiff_one := fun t => ricciCov1 (I := I) S t
      connection_contMDiff_infty := fun t => ricciCovInf (I := I) S t
      metricCompatible := fun t => ricciMetricComp (I := I) S t
      spatial := shiftSpatial (I := I) S f }
  have h := hnonneg t ht x v
  rw [shiftSec_apply (I := I) S f t x v v, twoTensorSecToFamily_apply] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow
