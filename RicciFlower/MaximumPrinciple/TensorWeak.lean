import RicciFlower.Realized.Curvature
import RicciFlower.Realized.TensorOperators
import RicciFlower.Tensor.RSTensor.MetricCompatibility
import RicciFlower.Tensor.RSTensor.QuadraticBounds
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Connection.OneJet
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Connection.Tangent
import RicciFlower.Tensor.RicciIdentity.Tensor0S.Realization
import RicciFlower.Operators.HessianTrace
import RicciFlower.Operators.LaplacianMinimum
import RicciFlower.Metric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Hamilton Weak Maximum Principle For Symmetric Two-Tensors

This file records the RicciFlower-native interface for Hamilton's weak maximum
principle for symmetric two-tensors.  The analytic proof itself is kept as one
explicit frontier: it is the barrier and first-null-vector maximum-principle
argument, not a Ricci-algebra or curvature-identity issue.
-/

namespace RicciFlower
namespace Realized

noncomputable section

open Bundle Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- A time-dependent covariant two-tensor field. -/
abbrev TwoTensorFamily : Type _ :=
  Real -> RawTwoTensorField (I := I) (M := M)

/-- A time-dependent vector field used for drift terms. -/
abbrev TimeDependentVectorField : Type _ :=
  Real -> (x : M) -> TangentSpace I x

/-- A time-dependent quadratic-form evaluation on tangent vectors. -/
abbrev TensorQuadraticFormFamily : Type _ :=
  Real -> (x : M) -> TangentSpace I x -> Real

/-- Supplied first covariant derivative tensors for a time-dependent two-tensor. -/
abbrev TensorNabla1Family : Type _ :=
  Real -> (x : M) ->
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x

/-- Supplied second covariant derivative tensors for a time-dependent two-tensor. -/
abbrev TensorNabla2Family : Type _ :=
  Real -> (x : M) ->
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x

/-- A fiberwise algebraic reaction term for the tensor maximum principle. -/
abbrev TwoTensorReaction : Type _ :=
  Real -> SmoothRiemannianMetric I M -> RawTwoTensorField (I := I) (M := M) ->
    RawTwoTensorField (I := I) (M := M)

/-- Pointwise symmetry of a covariant two-tensor. -/
def TwoTensorSymmetricAt (A : RawTwoTensorField (I := I) (M := M)) (x : M) : Prop :=
  ∀ X Y : TangentSpace I x, A x X Y = A x Y X

/-- Pointwise nonnegativity of a covariant two-tensor as a quadratic form. -/
def TwoTensorNonnegativeAt (A : RawTwoTensorField (I := I) (M := M)) (x : M) : Prop :=
  ∀ v : TangentSpace I x, 0 ≤ A x v v

/-- Pointwise positive definiteness of a covariant two-tensor as a quadratic form. -/
def TwoTensorPositiveDefiniteAt (A : RawTwoTensorField (I := I) (M := M)) (x : M) : Prop :=
  ∀ v : TangentSpace I x, v ≠ 0 -> 0 < A x v v

/-- Symmetry of a tensor family on a set of times. -/
def TwoTensorFamilySymmetricOn (S : TwoTensorFamily (I := I) (M := M))
    (U : Set Real) : Prop :=
  ∀ t, t ∈ U -> ∀ x, TwoTensorSymmetricAt (I := I) (M := M) (S t) x

/-- Nonnegativity of a tensor family on a set of times. -/
def TwoTensorFamilyNonnegativeOn (S : TwoTensorFamily (I := I) (M := M))
    (U : Set Real) : Prop :=
  ∀ t, t ∈ U -> ∀ x, TwoTensorNonnegativeAt (I := I) (M := M) (S t) x

/-- Nonnegativity of a tensor family at one time. -/
def TwoTensorFamilyNonnegativeAtTime (S : TwoTensorFamily (I := I) (M := M))
    (t : Real) : Prop :=
  ∀ x, TwoTensorNonnegativeAt (I := I) (M := M) (S t) x

/--
Hamilton's positive barrier
`S_epsilon = S + epsilon * (delta + t - t0) * g`.
-/
def tensorBarrierFamily
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) : TwoTensorFamily (I := I) (M := M) :=
  fun t x v w => S t x v w + epsilon * (delta + t - t0) * (G t).inner x v w

@[simp] theorem tensorBarrierFamily_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (v w : TangentSpace I x) :
    tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t x v w =
      S t x v w + epsilon * (delta + t - t0) * (G t).inner x v w := by
  rfl

/-- A time-dependent smooth covariant two-tensor section. -/
abbrev TwoTensorSecFamily : Type _ :=
  Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 2

/-- A time-dependent smooth covariant three-tensor section used as `∇S`. -/
abbrev TensorNabla1SecFamily : Type _ :=
  Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 3

/-- A time-dependent smooth covariant four-tensor section used as `∇²S`. -/
abbrev TensorNabla2SecFamily : Type _ :=
  Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 4

/-- Convert a section-backed two-tensor family to the pointwise quadratic-form
style used by the tensor WMP statement. -/
def twoTensorSecToFamily
    (S : TwoTensorSecFamily (I := I) (M := M)) :
    TwoTensorFamily (I := I) (M := M) :=
  fun t x v w => S t x (vec2 (I := I) v w)

@[simp]
theorem twoTensorSecToFamily_apply
    (S : TwoTensorSecFamily (I := I) (M := M))
    (t : Real) (x : M) (v w : TangentSpace I x) :
    twoTensorSecToFamily (I := I) (M := M) S t x v w =
      S t x (vec2 (I := I) v w) := by
  rfl

/-- Section-backed positive barrier.  This is the smooth-section version of
`tensorBarrierFamily`; it is used only as a producer bridge for spatial
covariant derivative data. -/
noncomputable def tensorBarrierSecFamily
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real) :
    TwoTensorSecFamily (I := I) (M := M) :=
  fun t =>
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
    S t + (epsilon * (delta + t - t0)) •
      Tensor0SBundle.metricTensorField (I := I) (G t)

@[simp]
theorem tensorBarrierSec_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (v w : TangentSpace I x) :
    twoTensorSecToFamily (I := I) (M := M)
        (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0)
        t x v w =
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x v w := by
  simp only [twoTensorSecToFamily, tensorBarrierSecFamily, tensorBarrierFamily,
    ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
    Pi.smul_apply]
  change
    (S t x (vec2 (I := I) v w) +
        (epsilon * (delta + t - t0)) *
          (Tensor0SBundle.metricTensorField (I := I) (G t) x)
            (vec2 (I := I) v w)) =
      S t x (vec2 (I := I) v w) +
        epsilon * (delta + t - t0) * (G t).inner x v w
  rw [Tensor0SBundle.metricTensorField_apply]
  have h0 : vec2 (I := I) v w 0 = v := by
    unfold vec2 Curvature.vec2
    simp
  have h1 : vec2 (I := I) v w 1 = w := by
    unfold vec2 Curvature.vec2
    norm_num
  rw [h0, h1]

private theorem eval02_sec_eq
    (S : TwoTensorSecFamily (I := I) (M := M))
    (t : Real) (x : M) (v w : TangentSpace I x) :
    eval02 (I := I) (M := M) (S t x) v w =
      twoTensorSecToFamily (I := I) (M := M) S t x v w := by
  rfl

private theorem quad02_sec_eq
    (S : TwoTensorSecFamily (I := I) (M := M))
    (t : Real) (x : M) (v : TangentSpace I x) :
    quad02 (I := I) (M := M) (S t x) v =
      twoTensorSecToFamily (I := I) (M := M) S t x v v := by
  calc
    quad02 (I := I) (M := M) (S t x) v =
        eval02 (I := I) (M := M) (S t x) v v := by
          rw [eval02_self]
    _ = twoTensorSecToFamily (I := I) (M := M) S t x v v :=
          eval02_sec_eq (I := I) (M := M) S t x v v

/-- The positive metric barrier preserves pointwise symmetry. -/
theorem barrierSymmAt
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 t : Real} {x : M}
    (hS : TwoTensorSymmetricAt (I := I) (M := M) (S t) x) :
    TwoTensorSymmetricAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t) x := by
  intro v w
  simp [tensorBarrierFamily, hS v w, (G t).symm x v w]

private theorem vec2_self_eq_const {x : M} (v : TangentSpace I x) :
    vec2 (I := I) v v = fun _ : Fin 2 => v := by
  funext i
  fin_cases i <;> simp [vec2, Curvature.vec2]

/-- Section-backed barriers are quadratic in the repeated tangent vector. -/
theorem barrierSec_smul2
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (a : Real)
    (v : TangentSpace I x) :
    twoTensorSecToFamily (I := I) (M := M)
        (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0)
        t x (a • v) (a • v) =
      a * a *
        twoTensorSecToFamily (I := I) (M := M)
          (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0)
          t x v v := by
  have hscale := tensor02_smul2 (I := I) (M := M)
    ((tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0) t x)
    a v
  simpa [quad02, twoTensorSecToFamily, vec2_self_eq_const] using hscale

/-- A section-backed raw barrier keeps the same quadratic scaling. -/
theorem barrierFamily_smul2
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (a : Real)
    (v : TangentSpace I x) :
    tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x (a • v) (a • v) =
      a * a *
        tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0 t x v v := by
  rw [← tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0 t x
      (a • v) (a • v),
    ← tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0 t x v v]
  exact barrierSec_smul2 (I := I) (M := M) G S epsilon delta t0 t x a v

/-- A negative section-backed barrier value can be normalized to a metric-unit
tangent vector at the same time and base point. -/
theorem negBarrier_unit
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (v : TangentSpace I x)
    (hneg :
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x v v < 0) :
    ∃ u : TangentSpace I x,
      (G t).inner x u u = 1 ∧
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x u u < 0 := by
  let B : TwoTensorFamily (I := I) (M := M) :=
    tensorBarrierFamily (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0
  have hv : v ≠ 0 := by
    intro hv0
    have hzero : B t x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by
      have hscale := barrierFamily_smul2 (I := I) (M := M)
        G S epsilon delta t0 t x 0 (0 : TangentSpace I x)
      simpa [B] using hscale
    have hnegB : B t x v v < 0 := by
      simpa [B] using hneg
    have hvzero : B t x v v = 0 := by
      simpa [hv0] using hzero
    rw [hvzero] at hnegB
    linarith
  let r : Real := (G t).inner x v v
  have hrpos : 0 < r := (G t).pos x v hv
  let s : Real := Real.sqrt r
  have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  let a : Real := s⁻¹
  let u : TangentSpace I x := a • v
  have hss : s * s = r := by
    simpa [sq] using (Real.sq_sqrt (le_of_lt hrpos))
  have hunit : (G t).inner x u u = 1 := by
    have haa : a * a * r = 1 := by
      have hmul : (s * s) * (s⁻¹ * s⁻¹) = 1 := by
        field_simp [hsne]
      calc
        a * a * r = (s⁻¹ * s⁻¹) * (s * s) := by
          rw [hss]
        _ = (s * s) * (s⁻¹ * s⁻¹) := by ring
        _ = 1 := hmul
    calc
      (G t).inner x u u = a * a * r := by
        simpa [u, r] using metric_smul2 (I := I) (M := M) (G t) a v
      _ = 1 := haa
  have hcoeff_pos : 0 < a * a := mul_pos (inv_pos.mpr hspos) (inv_pos.mpr hspos)
  have hquad :
      B t x u u = a * a * B t x v v := by
    simpa [B, u, a] using
      barrierFamily_smul2 (I := I) (M := M) G S epsilon delta t0 t x a v
  refine ⟨u, hunit, ?_⟩
  change B t x u u < 0
  rw [hquad]
  have hnegB : B t x v v < 0 := by
    simpa [B] using hneg
  exact mul_neg_of_pos_of_neg hcoeff_pos hnegB

/-- The scalar barrier quadratic form on a metric unit-tangent time slab. -/
def barrierUnitQuad
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 tA tB : Real)
    (p : MetricUnitTangentSlab (I := I) (M := M) G tA tB) : Real :=
  tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 p.1.1
    (MetricUnitTangent.base (I := I) (M := M) p.2)
    (MetricUnitTangent.vec (I := I) (M := M) p.2)
    (MetricUnitTangent.vec (I := I) (M := M) p.2)

@[simp]
theorem barrierUnitQuad_mk
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 tA tB t : Real) (ht : t ∈ Set.Icc tA tB)
    (x : M) (v : TangentSpace I x)
    (hunit : (G t).inner x v v = 1) :
    barrierUnitQuad (I := I) (M := M) G S epsilon delta t0 tA tB
      (⟨⟨t, ht⟩,
        (⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩ :
          MetricUnitTangent (I := I) (M := M) (G t))⟩ :
        MetricUnitTangentSlab (I := I) (M := M) G tA tB) =
      tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t x v v := by
  rfl

/-- A negative section-backed barrier value gives a negative point on the
metric unit-tangent slab at the same time. -/
theorem negBarrier_unitSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 tA tB t : Real) (ht : t ∈ Set.Icc tA tB)
    (x : M) (v : TangentSpace I x)
    (hneg :
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x v v < 0) :
    ∃ p : MetricUnitTangentSlab (I := I) (M := M) G tA tB,
      p.1.1 = t ∧
      barrierUnitQuad (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 tA tB p < 0 := by
  obtain ⟨u, hunit, hneg_u⟩ :=
    negBarrier_unit (I := I) (M := M) G S epsilon delta t0 t x v hneg
  refine ⟨⟨⟨t, ht⟩,
      (⟨(⟨x, u⟩ : TangentBundle I M), hunit⟩ :
        MetricUnitTangent (I := I) (M := M) (G t))⟩, rfl, ?_⟩
  simpa using hneg_u

/-- Failure of nonnegativity for a section-backed barrier produces a negative
point on the metric unit-tangent time slab. -/
theorem failure_unitSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 tA tB : Real)
    (hfail :
      ¬ TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0)
        (Set.Icc tA tB)) :
    ∃ p : MetricUnitTangentSlab (I := I) (M := M) G tA tB,
      barrierUnitQuad (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 tA tB p < 0 := by
  classical
  unfold TwoTensorFamilyNonnegativeOn TwoTensorNonnegativeAt at hfail
  push Not at hfail
  obtain ⟨t, ht, x, v, hneg⟩ := hfail
  obtain ⟨p, _hpt, hpneg⟩ :=
    negBarrier_unitSlab (I := I) (M := M) G S epsilon delta t0 tA tB
      t ht x v hneg
  exact ⟨p, hpneg⟩

private theorem metricUnitSlab_time_cont
    (G : Real -> SmoothRiemannianMetric I M) (tA tB : Real) :
    Continuous (fun p : MetricUnitTangentSlab (I := I) (M := M) G tA tB =>
      (p.1 : {t : Real // t ∈ Set.Icc tA tB})) := by
  change Continuous
    (fun p :
      (Σ t : {t : Real // t ∈ Set.Icc tA tB},
        MetricUnitTangent (I := I) (M := M) (G t.1)) => p.1)
  rw [continuous_def]
  intro s hs
  exact isOpen_sigma_fst_preimage s

private theorem metricUnitSlab_timeVal_cont
    (G : Real -> SmoothRiemannianMetric I M) (tA tB : Real) :
    Continuous (fun p : MetricUnitTangentSlab (I := I) (M := M) G tA tB =>
      p.1.1) :=
  continuous_subtype_val.comp
    (metricUnitSlab_time_cont (I := I) (M := M) G tA tB)

/-- Metric quadratic evaluation on an ambient time/tangent-bundle product. -/
def metricBundleQuad
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (q : {t : Real // t ∈ K} × TangentBundle I M) : Real :=
  metricTimeBundleQuad (I := I) (M := M) G K q

/-- Section-backed two-tensor quadratic evaluation on an ambient
time/tangent-bundle product. -/
def tensorSecBundleQuad
    (S : TwoTensorSecFamily (I := I) (M := M)) (K : Set Real)
    (q : {t : Real // t ∈ K} × TangentBundle I M) : Real :=
  S q.1.1 q.2.proj (fun _ : Fin 2 => q.2.2)

/-- Metric-family quadratic continuity from continuity of the corresponding
metric `(0,2)` tensor section over the time/tangent-bundle product. -/
theorem metricFamQuadCont
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (hG :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        TotalSpace.mk' (Tensor0SModel 2 Real E)
          (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
          (metricTensorField (I := I) (G q.1.1) q.2.proj))) :
    Continuous (metricBundleQuad (I := I) (M := M) G K) := by
  let P := {t : Real // t ∈ K} × TangentBundle I M
  let b : P -> M := fun q => q.2.proj
  let T : (q : P) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (b q) :=
    fun q => metricTensorField (I := I) (G q.1.1) (b q)
  let v : Fin 2 -> (q : P) -> TangentSpace I (b q) :=
    fun _ q => q.2.2
  have hb : Continuous b := by
    dsimp [b]
    exact (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_snd
  have hT : Continuous (fun q : P =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) (b q) (T q)) := by
    simpa [P, b, T] using hG
  have hv : ∀ i : Fin 2, Continuous (fun q : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b q) (v i q)) := by
    intro i
    simpa [P, b, v] using (continuous_snd :
      Continuous (fun q : P => (q.2 : TangentBundle I M)))
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := Real) (I := I) (M := M) (P := P) (n := 2)
    b hb T hT v hv
  simpa [metricBundleQuad, metricTimeBundleQuad, T, b, v,
    Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply,
    metricTensorField_apply, vec2_self_eq_const] using hEval

/-- Section-backed two-tensor quadratic continuity from continuity of the
two-tensor section over the time/tangent-bundle product. -/
theorem tensorQuadCont
    (S : TwoTensorSecFamily (I := I) (M := M)) (K : Set Real)
    (hS :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        TotalSpace.mk' (Tensor0SModel 2 Real E)
          (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
          (S q.1.1 q.2.proj))) :
    Continuous (tensorSecBundleQuad (I := I) (M := M) S K) := by
  let P := {t : Real // t ∈ K} × TangentBundle I M
  let b : P -> M := fun q => q.2.proj
  let T : (q : P) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (b q) :=
    fun q => S q.1.1 (b q)
  let v : Fin 2 -> (q : P) -> TangentSpace I (b q) :=
    fun _ q => q.2.2
  have hb : Continuous b := by
    dsimp [b]
    exact (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_snd
  have hT : Continuous (fun q : P =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) (b q) (T q)) := by
    simpa [P, b, T] using hS
  have hv : ∀ i : Fin 2, Continuous (fun q : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b q) (v i q)) := by
    intro i
    simpa [P, b, v] using (continuous_snd :
      Continuous (fun q : P => (q.2 : TangentBundle I M)))
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := Real) (I := I) (M := M) (P := P) (n := 2)
    b hb T hT v hv
  simpa [tensorSecBundleQuad, T, b, v, vec2_self_eq_const,
    Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using hEval

/-- Raw barrier quadratic evaluation on an ambient time/tangent-bundle product. -/
def barrierBundleQuad
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) (K : Set Real)
    (q : {t : Real // t ∈ K} × TangentBundle I M) : Real :=
  tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
    q.1.1 q.2.proj q.2.2 q.2.2

/-- The section-backed ambient barrier quadratic form is continuous if the
metric and two-tensor quadratic evaluations are continuous. -/
theorem barrierBundleCont
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real) (K : Set Real)
    (hS : Continuous (tensorSecBundleQuad (I := I) (M := M) S K))
    (hG : Continuous (metricBundleQuad (I := I) (M := M) G K)) :
    Continuous (barrierBundleQuad (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0 K) := by
  have htime :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        (q.1.1 : Real)) :=
    continuous_subtype_val.comp continuous_fst
  have hcoef :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        epsilon * (delta + q.1.1 - t0)) := by
    exact continuous_const.mul ((continuous_const.add htime).sub continuous_const)
  have hmain :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        tensorSecBundleQuad (I := I) (M := M) S K q +
          (epsilon * (delta + q.1.1 - t0)) *
            metricBundleQuad (I := I) (M := M) G K q) :=
    hS.add (hcoef.mul hG)
  refine hmain.congr ?_
  intro q
  simp [barrierBundleQuad, tensorSecBundleQuad, metricBundleQuad,
    metricTimeBundleQuad, tensorBarrierFamily, twoTensorSecToFamily,
    vec2_self_eq_const, mul_assoc]

/-- The scalar barrier quadratic form on the geometric metric unit-tangent
time slab. -/
def barrierTimeSlabQuad
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) (K : Set Real)
    (p : MetricUnitTangentTimeSlab (I := I) (M := M) G K) : Real :=
  tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
    (MetricUnitTangentTimeSlab.time (I := I) (M := M) p)
    (MetricUnitTangentTimeSlab.base (I := I) (M := M) p)
    (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)
    (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)

theorem barrierTimeSlabQuad_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) (K : Set Real)
    (p : MetricUnitTangentTimeSlab (I := I) (M := M) G K) :
    barrierTimeSlabQuad (I := I) (M := M) G S epsilon delta t0 K p =
      tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
        (MetricUnitTangentTimeSlab.time (I := I) (M := M) p)
        (MetricUnitTangentTimeSlab.base (I := I) (M := M) p)
        (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)
        (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p) :=
  rfl

@[simp]
theorem barrierTimeSlabQuad_mk
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (K : Set Real) (ht : t ∈ K)
    (x : M) (v : TangentSpace I x)
    (hunit : (G t).inner x v v = 1) :
    barrierTimeSlabQuad (I := I) (M := M) G S epsilon delta t0 K
      (⟨(⟨t, ht⟩, (⟨x, v⟩ : TangentBundle I M)), hunit⟩ :
        MetricUnitTangentTimeSlab (I := I) (M := M) G K) =
      tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t x v v := by
  rfl

/-- The geometric time-slab barrier quadratic form is continuous if the
ambient metric and section-backed tensor quadratic evaluations are continuous. -/
theorem barrierTimeCont
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real) (K : Set Real)
    (hS : Continuous (tensorSecBundleQuad (I := I) (M := M) S K))
    (hG : Continuous (metricBundleQuad (I := I) (M := M) G K)) :
    Continuous
      (barrierTimeSlabQuad (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0 K) := by
  have hbundle := barrierBundleCont (I := I) (M := M)
    G S epsilon delta t0 K hS hG
  have hsub :
      Continuous (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
        (p.1 : {t : Real // t ∈ K} × TangentBundle I M)) :=
    continuous_subtype_val
  simpa [barrierTimeSlabQuad, barrierBundleQuad,
    MetricUnitTangentTimeSlab.time, MetricUnitTangentTimeSlab.base,
    MetricUnitTangentTimeSlab.vec, MetricUnitTangentTimeSlab.bundlePoint]
    using hbundle.comp hsub

/-- A negative section-backed barrier value gives a negative point on the
geometric metric unit-tangent time slab at the same time. -/
theorem negBarrier_timeSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) {K : Set Real} (ht : t ∈ K)
    (x : M) (v : TangentSpace I x)
    (hneg :
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x v v < 0) :
    ∃ p : MetricUnitTangentTimeSlab (I := I) (M := M) G K,
      MetricUnitTangentTimeSlab.time (I := I) (M := M) p = t ∧
      barrierTimeSlabQuad (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 K p < 0 := by
  obtain ⟨u, hunit, hneg_u⟩ :=
    negBarrier_unit (I := I) (M := M) G S epsilon delta t0 t x v hneg
  refine ⟨⟨(⟨t, ht⟩, (⟨x, u⟩ : TangentBundle I M)), hunit⟩, rfl, ?_⟩
  simpa using hneg_u

/-- Failure of nonnegativity for a section-backed barrier produces a negative
point on the geometric metric unit-tangent time slab. -/
theorem failure_timeSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real) {K : Set Real}
    (hfail :
      ¬ TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0) K) :
    ∃ p : MetricUnitTangentTimeSlab (I := I) (M := M) G K,
      barrierTimeSlabQuad (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 K p < 0 := by
  classical
  unfold TwoTensorFamilyNonnegativeOn TwoTensorNonnegativeAt at hfail
  push Not at hfail
  obtain ⟨t, ht, x, v, hneg⟩ := hfail
  obtain ⟨p, _hpt, hpneg⟩ :=
    negBarrier_timeSlab (I := I) (M := M) G S epsilon delta t0 t ht x v hneg
  exact ⟨p, hpneg⟩

private theorem metricUnitTimeSlab_timeVal_cont
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real) :
    Continuous (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
      MetricUnitTangentTimeSlab.time (I := I) (M := M) p) := by
  have htime :
      Continuous (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
        (p.1.1 : {t : Real // t ∈ K})) :=
    continuous_fst.comp continuous_subtype_val
  exact continuous_subtype_val.comp htime

private theorem exists_left_neg_of_continuousOn
    {f : Real -> Real} {a b c : Real}
    (hab : a < b) (hbc : b ≤ c)
    (hcont : ContinuousOn f (Set.Icc a c)) (hneg : f b < 0) :
    ∃ s : Real, s ∈ Set.Icc a c ∧ s < b ∧ f s < 0 := by
  have hbmem : b ∈ Set.Icc a c := ⟨le_of_lt hab, hbc⟩
  have hpre :
      {s : Real | f s < 0} ∈ nhdsWithin b (Set.Icc a c) :=
    (hcont.continuousWithinAt hbmem).preimage_mem_nhdsWithin
      (isOpen_Iio.mem_nhds hneg)
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre with
    ⟨u, hu_nhds, hu_subset⟩
  rcases exists_Ioc_subset_of_mem_nhds' hu_nhds hab with
    ⟨l, hlb, hlu⟩
  let s : Real := (max a l + b) / 2
  have hmax_lt : max a l < b := max_lt hab hlb.2
  have hmax_lt_s : max a l < s := by
    dsimp [s]
    linarith
  have hmax_le_s : max a l ≤ s := le_of_lt hmax_lt_s
  have hs_lt : s < b := by
    dsimp [s]
    linarith
  have ha_le_s : a ≤ s := le_trans (le_max_left a l) hmax_le_s
  have hl_lt_s : l < s := lt_of_le_of_lt (le_max_right a l) hmax_lt_s
  have hs_mem_u : s ∈ u := hlu ⟨hl_lt_s, le_of_lt hs_lt⟩
  have hs_mem_Icc : s ∈ Set.Icc a c := ⟨ha_le_s, le_trans (le_of_lt hs_lt) hbc⟩
  exact ⟨s, hs_mem_Icc, hs_lt, hu_subset ⟨hs_mem_u, hs_mem_Icc⟩⟩

/-- Spatial first and second covariant derivative realizations for a
section-backed two-tensor family. -/
structure TensorSpatialDerivs
    (cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (S : TwoTensorSecFamily (I := I) (M := M))
    (nablaS : TensorNabla1SecFamily (I := I) (M := M))
    (nabla2S : TensorNabla2SecFamily (I := I) (M := M)) : Prop where
  first :
    ∀ t : Real,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (cov t) (S t) (nablaS t)
  second :
    ∀ t : Real,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (cov t) (nablaS t) (nabla2S t)

/-- The section-backed barrier has the same spatial covariant derivative data
as `S`, because the metric addend has zero covariant derivative for a
metric-compatible connection. -/
theorem barrierDerivs
    [T2Space M]
    (cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (nablaS : TensorNabla1SecFamily (I := I) (M := M))
    (nabla2S : TensorNabla2SecFamily (I := I) (M := M))
    (epsilon delta t0 : Real)
    (hmc : ∀ t : Real,
      RicciFlower.Connection.IsMetricCompatible (I := I) (cov t) (G t))
    (hS : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S) :
    TensorSpatialDerivs (I := I) (M := M) cov
      (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0)
      nablaS nabla2S := by
  constructor
  · intro t
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3
    have hmetric :
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 (cov t) (Tensor0SBundle.metricTensorField (I := I) (G t))
          (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (n := (∞ : WithTop ℕ∞)) 3) :=
      Tensor0SBundle.zero_realizes_metric (I := I) (cov t) (G t) (hmc t)
    have hscaled :
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 (cov t)
          ((epsilon * (delta + t - t0)) •
            Tensor0SBundle.metricTensorField (I := I) (G t))
          ((epsilon * (delta + t - t0)) •
            (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) 3)) :=
      TotalNabla0SRealizes.smul (I := I) (M := M)
        (epsilon * (delta + t - t0)) hmetric
    have hadd := TotalNabla0SRealizes.add (I := I) (M := M)
      (hS.first t) hscaled
    simpa [tensorBarrierSecFamily] using hadd
  · intro t
    exact hS.second t

/-- Barrier sizes used in the final tensor-WMP epsilon limit. -/
def SmallBarrierEps (epsilon : Real) : Prop :=
  0 < epsilon ∧ epsilon ≤ 1

/--
Hamilton's null-eigenvector condition for the reaction term.

At each point, whenever any symmetric two-tensor input is nonnegative and has a
null vector, the reaction term is nonnegative on that null vector.  This
reaction-wide shape is needed because Hamilton's barrier argument applies the
condition to `S_epsilon`, not only to the original tensor family.
-/
def TensorNullEigenvectorCondition
    (G : Real -> SmoothRiemannianMetric I M)
    (N : TwoTensorReaction (I := I) (M := M))
    (U : Set Real) : Prop :=
  ∀ t, t ∈ U -> ∀ A : RawTwoTensorField (I := I) (M := M), ∀ x,
    TwoTensorNonnegativeAt (I := I) (M := M) A x ->
    ∀ v : TangentSpace I x,
      A x v v = 0 ->
      0 ≤ N t (G t) A x v v

/--
Analytic regularity predicate for the tensor WMP barrier argument.

This records the concrete scalar-evaluation regularity and uniform small-barrier
reaction Lipschitz control needed by the barrier estimate.  The compact
first-null extraction and tensor heat-operator realization remain separate
frontiers.
-/
structure TensorBarrierRegularityOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  tensor_eval_continuous :
    ∀ x, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : Real => S t x v w) (Set.Icc 0 T)
  metric_eval_continuous :
    ∀ x, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : Real => (G t).inner x v w) (Set.Icc 0 T)
  barrier_eval_continuous :
    ∀ epsilon delta t0 : Real,
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ x, ∀ v w : TangentSpace I x,
        ContinuousOn
          (fun t : Real =>
            tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t x v w)
          (Set.Icc t0 (t0 + delta))
  metricGainControl :
    ∀ t0 : Real,
      t0 ∈ Set.Icc 0 T ->
      t0 < T ->
      ∃ delta0 : Real,
        0 < delta0 ∧ t0 + delta0 ≤ T ∧
          ∀ delta : Real,
            0 < delta ->
            delta ≤ delta0 ->
            ∀ epsilon : Real,
              SmallBarrierEps epsilon ->
              ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
                (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    HasDerivWithinAt (fun s : Real => (G s).inner x v v)
                      (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
                (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    (epsilon / 2) * (G t).inner x v v ≤
                      epsilon * ((G t).inner x v v +
                        (delta + t - t0) * metricDeriv t x v))
  smallBarrierLip :
    ∀ delta0 t0 : Real,
      0 < delta0 ->
      Set.Icc t0 (t0 + delta0) ⊆ Set.Icc 0 T ->
      ∃ K : Real, 0 ≤ K ∧
        ∀ epsilon delta : Real,
          SmallBarrierEps epsilon ->
          0 < delta ->
          delta ≤ delta0 ->
          ∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
            ∀ x, ∀ v : TangentSpace I x,
              |N t (G t) (S t) x v v -
                N t (G t)
                  (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
                  x v v| ≤
              K * |epsilon * (delta + t - t0) * (G t).inner x v v|

/--
Analytic predicate for the evaluated drifted parabolic supersolution
inequality.

The heat-with-drift term is evaluated by the direct tensor operator
`tensorHeatWithDrift2QuadMetricAt` from supplied first and second covariant
derivative tensors.
-/
def TensorParabolicInequalityWithDriftOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (nabla2S : TensorNabla2Family (I := I) (M := M))
    (nablaS : TensorNabla1Family (I := I) (M := M))
    (T : Real) : Prop :=
  ∃ timeDeriv : TensorQuadraticFormFamily (I := I) (M := M),
    (∀ t, t ∈ Set.Ioc 0 T ->
      ∀ x, ∀ v : TangentSpace I x,
        HasDerivWithinAt
          (fun s : Real => S s x v v)
          (timeDeriv t x v)
          (Set.Icc 0 T) t) ∧
    (∀ t, t ∈ Set.Ioc 0 T ->
      ∀ x, ∀ v : TangentSpace I x,
        tensorHeatWithDrift2QuadMetricAt (I := I) (G t) (X t)
            (nabla2S t x) (nablaS t x) v +
          N t (G t) (S t) x v v ≤ timeDeriv t x v)

/-- Strict evaluated drifted parabolic inequality for the positive barrier on a time set. -/
def TensorParabolicStrictInequalityWithDriftOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (nabla2S : TensorNabla2Family (I := I) (M := M))
    (nablaS : TensorNabla1Family (I := I) (M := M))
    (U : Set Real) : Prop :=
  ∃ timeDeriv : TensorQuadraticFormFamily (I := I) (M := M),
    (∀ t, t ∈ U ->
      ∀ x, ∀ v : TangentSpace I x,
        HasDerivWithinAt
          (fun s : Real => S s x v v)
          (timeDeriv t x v)
          U t) ∧
    (∀ t, t ∈ U ->
      ∀ x, ∀ v : TangentSpace I x,
        v ≠ 0 ->
        tensorHeatWithDrift2QuadMetricAt (I := I) (G t) (X t)
            (nabla2S t x) (nablaS t x) v +
          N t (G t) (S t) x v v < timeDeriv t x v)

/--
Local comparison estimates that turn the base parabolic inequality for `S`
into the strict parabolic inequality for the positive barrier.

The analytic work is concentrated in producing these estimates.  The order
argument consuming them is `strictBarrier_of_est` below.
-/
def TensorBarrierLocalEst
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (nabla2S : TensorNabla2Family (I := I) (M := M))
    (nablaS : TensorNabla1Family (I := I) (M := M))
    (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
    (nablaBarrier : TensorNabla1Family (I := I) (M := M))
    (epsilon delta t0 : Real)
    (U : Set Real)
    (timeDerivS timeDerivBarrier :
      TensorQuadraticFormFamily (I := I) (M := M)) : Prop :=
  (∀ t, t ∈ U ->
    ∀ x, ∀ v : TangentSpace I x,
      HasDerivWithinAt
        (fun s : Real =>
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 s x v v)
        (timeDerivBarrier t x v) U t) ∧
  (∀ t, t ∈ U ->
    ∀ x, ∀ v : TangentSpace I x,
      ∃ heatErr reactionErr metricGain : Real,
        timeDerivS t x v + metricGain ≤ timeDerivBarrier t x v ∧
        tensorHeatWithDrift2QuadMetricAt (I := I) (G t) (X t)
            (nabla2Barrier t x) (nablaBarrier t x) v ≤
          tensorHeatWithDrift2QuadMetricAt (I := I) (G t) (X t)
              (nabla2S t x) (nablaS t x) v + heatErr ∧
        N t (G t)
            (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
            x v v ≤
        N t (G t) (S t) x v v + reactionErr ∧
        (v ≠ 0 -> heatErr + reactionErr < metricGain))

/-- Reduced local estimate when the barrier spatial derivative tensors are the
same supplied tensors as for `S`.  The remaining analytic inputs are the
barrier time derivative, the positive metric gain, and the reaction error. -/
def BarrierLocalCore
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (epsilon delta t0 : Real)
    (U : Set Real)
    (timeDerivS timeDerivBarrier :
      TensorQuadraticFormFamily (I := I) (M := M)) : Prop :=
  (∀ t, t ∈ U ->
    ∀ x, ∀ v : TangentSpace I x,
      HasDerivWithinAt
        (fun s : Real =>
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 s x v v)
        (timeDerivBarrier t x v) U t) ∧
  (∀ t, t ∈ U ->
    ∀ x, ∀ v : TangentSpace I x,
      ∃ reactionErr metricGain : Real,
        timeDerivS t x v + metricGain ≤ timeDerivBarrier t x v ∧
        N t (G t)
            (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
            x v v ≤
        N t (G t) (S t) x v v + reactionErr ∧
        (v ≠ 0 -> reactionErr < metricGain))

/-- Product rule for the pointwise time derivative of the barrier quadratic
form.  The derivative of the metric quadratic form is still supplied by the
caller; this lemma only packages the affine barrier coefficient calculation. -/
theorem hasDerivWithinAt_barrier_quad
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 t dS dg : Real} {U : Set Real}
    {x : M} {v : TangentSpace I x}
    (hS : HasDerivWithinAt (fun s : Real => S s x v v) dS U t)
    (hG : HasDerivWithinAt (fun s : Real => (G s).inner x v v) dg U t) :
    HasDerivWithinAt
      (fun s : Real =>
        tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 s x v v)
      (dS + epsilon * ((G t).inner x v v + (delta + t - t0) * dg))
      U t := by
  have hid : HasDerivWithinAt (fun s : Real => s) 1 U t := by
    simpa using (hasDerivWithinAt_id t U)
  have hlin : HasDerivWithinAt (fun s : Real => delta + s - t0) 1 U t := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      ((hid.const_add delta).sub_const t0)
  have hprod :
      HasDerivWithinAt
        (fun s : Real => (delta + s - t0) * (G s).inner x v v)
        ((G t).inner x v v + (delta + t - t0) * dg)
        U t := by
    have h := hlin.mul hG
    simpa [one_mul, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hmetric :
      HasDerivWithinAt
        (fun s : Real => epsilon * ((delta + s - t0) * (G s).inner x v v))
        (epsilon * ((G t).inner x v v + (delta + t - t0) * dg))
        U t := by
    exact hprod.const_mul epsilon
  have htotal := hS.add hmetric
  simpa [tensorBarrierFamily, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using htotal

/-- Build the reduced barrier core from the time derivatives of `S(t)(v,v)`
and `g(t)(v,v)`.  The remaining hypotheses are exactly the local gain,
reaction-error, and positive-margin estimates. -/
theorem barrierCore_deriv
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {epsilon delta t0 : Real} {U : Set Real}
    {timeDerivS metricDeriv reactionErr metricGain :
      TensorQuadraticFormFamily (I := I) (M := M)}
    (hS :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => S s x v v)
            (timeDerivS t x v) U t)
    (hG :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => (G s).inner x v v)
            (metricDeriv t x v) U t)
    (hGain :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          metricGain t x v ≤
            epsilon * ((G t).inner x v v +
              (delta + t - t0) * metricDeriv t x v))
    (hReaction :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          N t (G t)
              (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
              x v v ≤
            N t (G t) (S t) x v v + reactionErr t x v)
    (hMargin :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          v ≠ 0 -> reactionErr t x v < metricGain t x v) :
    BarrierLocalCore (I := I) (M := M) G S N epsilon delta t0 U
      timeDerivS
      (fun t x v =>
        timeDerivS t x v +
          epsilon * ((G t).inner x v v +
            (delta + t - t0) * metricDeriv t x v)) := by
  constructor
  · intro t ht x v
    exact hasDerivWithinAt_barrier_quad
      (I := I) (M := M) (hS t ht x v) (hG t ht x v)
  · intro t ht x v
    refine ⟨reactionErr t x v, metricGain t x v, ?_, hReaction t ht x v,
      hMargin t ht x v⟩
    have h := hGain t ht x v
    linarith

/-- Direct constructor for the reduced local barrier estimate from pointwise
time-derivative, reaction-error, and margin inequalities. -/
theorem barrierCore_of_pt
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {epsilon delta t0 : Real} {U : Set Real}
    {timeDerivS timeDerivBarrier :
      TensorQuadraticFormFamily (I := I) (M := M)}
    (reactionErr metricGain : TensorQuadraticFormFamily (I := I) (M := M))
    (hDerivB :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt
            (fun s : Real =>
              tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 s x v v)
            (timeDerivBarrier t x v) U t)
    (hTime :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          timeDerivS t x v + metricGain t x v ≤ timeDerivBarrier t x v)
    (hReaction :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          N t (G t)
              (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
              x v v ≤
            N t (G t) (S t) x v v + reactionErr t x v)
    (hMargin :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          v ≠ 0 -> reactionErr t x v < metricGain t x v) :
    BarrierLocalCore (I := I) (M := M) G S N epsilon delta t0 U
      timeDerivS timeDerivBarrier := by
  constructor
  · exact hDerivB
  · intro t ht x v
    exact ⟨reactionErr t x v, metricGain t x v,
      hTime t ht x v, hReaction t ht x v, hMargin t ht x v⟩

/-- If the metric barrier contributes no spatial heat-with-drift error, the
reduced time/reaction estimates produce the full local estimate expected by the
strict-barrier theorem. -/
theorem localEst_of_core
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real} {U : Set Real}
    {timeDerivS timeDerivBarrier :
      TensorQuadraticFormFamily (I := I) (M := M)}
    (hcore : BarrierLocalCore (I := I) (M := M) G S N epsilon delta t0 U
      timeDerivS timeDerivBarrier) :
    TensorBarrierLocalEst (I := I) (M := M) G S X N
      nabla2S nablaS nabla2S nablaS epsilon delta t0 U
      timeDerivS timeDerivBarrier := by
  constructor
  · exact hcore.1
  · intro t ht x v
    rcases hcore.2 t ht x v with
      ⟨reactionErr, metricGain, htime, hreaction, hmargin⟩
    refine ⟨0, reactionErr, metricGain, htime, ?_, hreaction, ?_⟩
    · linarith
    · intro hv
      have h := hmargin hv
      linarith

/-- Full local barrier estimate from pointwise time derivatives of `S` and
the metric quadratic form, when the metric barrier has already been eliminated
from the spatial heat term. -/
theorem localEst_deriv
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real} {U : Set Real}
    {timeDerivS metricDeriv reactionErr metricGain :
      TensorQuadraticFormFamily (I := I) (M := M)}
    (hS :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => S s x v v)
            (timeDerivS t x v) U t)
    (hG :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => (G s).inner x v v)
            (metricDeriv t x v) U t)
    (hGain :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          metricGain t x v ≤
            epsilon * ((G t).inner x v v +
              (delta + t - t0) * metricDeriv t x v))
    (hReaction :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          N t (G t)
              (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
              x v v ≤
            N t (G t) (S t) x v v + reactionErr t x v)
    (hMargin :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          v ≠ 0 -> reactionErr t x v < metricGain t x v) :
    TensorBarrierLocalEst (I := I) (M := M) G S X N
      nabla2S nablaS nabla2S nablaS epsilon delta t0 U
      timeDerivS
      (fun t x v =>
        timeDerivS t x v +
          epsilon * ((G t).inner x v v +
            (delta + t - t0) * metricDeriv t x v)) :=
  localEst_of_core (I := I) (M := M)
    (barrierCore_deriv (I := I) (M := M)
      hS hG hGain hReaction hMargin)

theorem strictBarrier_of_derivEst
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 T : Real}
    (hsub : Set.Ioc t0 (t0 + delta) ⊆ Set.Ioc 0 T)
    (hbase : TensorParabolicInequalityWithDriftOn (I := I) (M := M)
      G S X N nabla2S nablaS T)
    (metricDeriv reactionErr metricGain :
      TensorQuadraticFormFamily (I := I) (M := M))
    (hG :
      ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => (G s).inner x v v)
            (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t)
    (hGain :
      ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          metricGain t x v ≤
            epsilon * ((G t).inner x v v +
              (delta + t - t0) * metricDeriv t x v))
    (hReaction :
      ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          N t (G t)
              (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
              x v v ≤
            N t (G t) (S t) x v v + reactionErr t x v)
    (hMargin :
      ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          v ≠ 0 -> reactionErr t x v < metricGain t x v) :
    TensorParabolicStrictInequalityWithDriftOn (I := I) (M := M) G
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0) X N
      nabla2S nablaS (Set.Ioc t0 (t0 + delta)) := by
  rcases hbase with ⟨timeDerivS, hSbase, hbase_ineq⟩
  let timeDerivBarrier : TensorQuadraticFormFamily (I := I) (M := M) :=
    fun t x v =>
      timeDerivS t x v +
        epsilon * ((G t).inner x v v +
          (delta + t - t0) * metricDeriv t x v)
  have hSlocal :
      ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => S s x v v)
            (timeDerivS t x v) (Set.Ioc t0 (t0 + delta)) t := by
    intro t ht x v
    have hsub_closed : Set.Ioc t0 (t0 + delta) ⊆ Set.Icc 0 T := by
      intro s hs
      exact ⟨le_of_lt (hsub hs).1, (hsub hs).2⟩
    exact (hSbase t (hsub ht) x v).mono hsub_closed
  have hGlocal :
      ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => (G s).inner x v v)
            (metricDeriv t x v) (Set.Ioc t0 (t0 + delta)) t := by
    intro t ht x v
    exact (hG t ht x v).mono (by
      intro s hs
      exact ⟨le_of_lt hs.1, hs.2⟩)
  have hest :
      TensorBarrierLocalEst (I := I) (M := M) G S X N
        nabla2S nablaS nabla2S nablaS epsilon delta t0
        (Set.Ioc t0 (t0 + delta)) timeDerivS timeDerivBarrier :=
    localEst_deriv (I := I) (M := M)
      (G := G) (S := S) (X := X) (N := N)
      (nabla2S := nabla2S) (nablaS := nablaS)
      (epsilon := epsilon) (delta := delta) (t0 := t0)
      (U := Set.Ioc t0 (t0 + delta))
      (timeDerivS := timeDerivS) (metricDeriv := metricDeriv)
      (reactionErr := reactionErr) (metricGain := metricGain)
      hSlocal hGlocal hGain hReaction hMargin
  refine ⟨timeDerivBarrier, hest.1, ?_⟩
  intro t ht x v hv
  rcases hest.2 t ht x v with
    ⟨heatErr, reactionErr', metricGain', htime, hheat, hreaction, hmargin⟩
  have hbase_t := hbase_ineq t (hsub ht) x v
  have hmargin_t := hmargin hv
  linarith

theorem strictParabolic_of_est
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 T : Real} {U : Set Real}
    (hsub : U ⊆ Set.Ioc 0 T)
    (hbase : TensorParabolicInequalityWithDriftOn (I := I) (M := M)
      G S X N nabla2S nablaS T)
    (hest : ∀ timeDerivS : TensorQuadraticFormFamily (I := I) (M := M),
      ∃ timeDerivBarrier : TensorQuadraticFormFamily (I := I) (M := M),
        TensorBarrierLocalEst (I := I) (M := M) G S X N
          nabla2S nablaS nabla2Barrier nablaBarrier epsilon delta t0 U
          timeDerivS timeDerivBarrier) :
    TensorParabolicStrictInequalityWithDriftOn (I := I) (M := M) G
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0) X N
      nabla2Barrier nablaBarrier U := by
  rcases hbase with ⟨timeDerivS, _hbase_deriv, hbase_ineq⟩
  rcases hest timeDerivS with ⟨timeDerivBarrier, hbarrier_deriv, hcompare⟩
  refine ⟨timeDerivBarrier, hbarrier_deriv, ?_⟩
  intro t ht x v hv
  rcases hcompare t ht x v with
    ⟨heatErr, reactionErr, metricGain, htime, hheat, hreaction, hmargin⟩
  have hbase_t := hbase_ineq t (hsub ht) x v
  have hmargin_t := hmargin hv
  linarith

/--
Data at the first point where the positive barrier develops a null vector.

The vector is normalized with respect to the metric at the first null time.
This is the shape supplied by compactness of the unit tangent bundle.
-/
structure TensorFirstNullData
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) : Type _ where
  t1 : Real
  x1 : M
  v : TangentSpace I x1
  t1_mem : t1 ∈ Set.Ioc t0 (t0 + delta)
  v_ne_zero : v ≠ 0
  unit : (G t1).inner x1 v v = 1
  nonnegative_until :
    ∀ t, t ∈ Set.Icc t0 t1 ->
      ∀ x, TwoTensorNonnegativeAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t) x
  null :
    tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t1 x1 v v = 0

/-- At a section-backed first-null point, positive semidefiniteness plus
symmetry makes the null vector a left-kernel vector for the barrier tensor. -/
theorem firstNullKernel_left
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S)
        (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) :
    ∀ w : TangentSpace I d.x1,
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 d.t1 d.x1 d.v w = 0 := by
  let Bsec : TwoTensorSecFamily (I := I) (M := M) :=
    tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0
  let A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 d.x1 :=
    Bsec d.t1 d.x1
  have ht1_slab : d.t1 ∈ Set.Icc t0 (t0 + delta) :=
    ⟨le_of_lt d.t1_mem.1, d.t1_mem.2⟩
  have hBsym :
      TwoTensorSymmetricAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0 d.t1) d.x1 :=
    barrierSymmAt (I := I) (M := M)
      (G := G) (S := twoTensorSecToFamily (I := I) (M := M) S)
      (epsilon := epsilon) (delta := delta) (t0 := t0)
      (t := d.t1) (x := d.x1)
      (hsym d.t1 ht1_slab d.x1)
  have hAsym :
      ∀ u w : TangentSpace I d.x1,
        eval02 (I := I) (M := M) A u w =
          eval02 (I := I) (M := M) A w u := by
    intro u w
    calc
      eval02 (I := I) (M := M) A u w =
          twoTensorSecToFamily (I := I) (M := M) Bsec d.t1 d.x1 u w := by
            exact eval02_sec_eq (I := I) (M := M) Bsec d.t1 d.x1 u w
      _ =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 u w := by
            exact tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
              d.t1 d.x1 u w
      _ =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 w u := hBsym u w
      _ =
          twoTensorSecToFamily (I := I) (M := M) Bsec d.t1 d.x1 w u := by
            exact (tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
              d.t1 d.x1 w u).symm
      _ = eval02 (I := I) (M := M) A w u := by
            exact (eval02_sec_eq (I := I) (M := M) Bsec d.t1 d.x1 w u).symm
  have hApsd : ∀ u : TangentSpace I d.x1,
      0 ≤ quad02 (I := I) (M := M) A u := by
    intro u
    have hraw := d.nonnegative_until d.t1
      ⟨le_of_lt d.t1_mem.1, le_rfl⟩ d.x1 u
    calc
      0 ≤
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 u u := hraw
      _ = quad02 (I := I) (M := M) A u := by
          rw [← tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
            d.t1 d.x1 u u]
          exact (quad02_sec_eq (I := I) (M := M) Bsec d.t1 d.x1 u).symm
  have hAnull : quad02 (I := I) (M := M) A d.v = 0 := by
    calc
      quad02 (I := I) (M := M) A d.v =
          twoTensorSecToFamily (I := I) (M := M) Bsec d.t1 d.x1 d.v d.v :=
            quad02_sec_eq (I := I) (M := M) Bsec d.t1 d.x1 d.v
      _ =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 d.v d.v :=
            tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
              d.t1 d.x1 d.v d.v
      _ = 0 := d.null
  have hkernel :=
    psd_null_left (I := I) (M := M) A hAsym hApsd hAnull
  intro w
  calc
    tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 d.t1 d.x1 d.v w =
        twoTensorSecToFamily (I := I) (M := M) Bsec d.t1 d.x1 d.v w := by
          exact (tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
            d.t1 d.x1 d.v w).symm
    _ = eval02 (I := I) (M := M) A d.v w := by
          exact (eval02_sec_eq (I := I) (M := M) Bsec d.t1 d.x1 d.v w).symm
    _ = 0 := hkernel w

/-- Right-kernel version of `firstNullKernel_left`, using barrier symmetry. -/
theorem firstNullKernel_right
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S)
        (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) :
    ∀ w : TangentSpace I d.x1,
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 d.t1 d.x1 w d.v = 0 := by
  have ht1_slab : d.t1 ∈ Set.Icc t0 (t0 + delta) :=
    ⟨le_of_lt d.t1_mem.1, d.t1_mem.2⟩
  have hBsym :
      TwoTensorSymmetricAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0 d.t1) d.x1 :=
    barrierSymmAt (I := I) (M := M)
      (G := G) (S := twoTensorSecToFamily (I := I) (M := M) S)
      (epsilon := epsilon) (delta := delta) (t0 := t0)
      (t := d.t1) (x := d.x1)
      (hsym d.t1 ht1_slab d.x1)
  intro w
  rw [hBsym w d.v]
  exact firstNullKernel_left (I := I) (M := M) hsym d w

/-- Transfer the first-null left-kernel fact from the raw barrier evaluator to
a local `(0,2)` tensor field whose left-null evaluations agree with it. -/
private theorem firstNullFieldKerL
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S)
        (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0)
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    (hB :
      ∀ w : TangentSpace I d.x1,
        B d.x1 (vec2 (I := I) d.v w) =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 d.v w) :
    ∀ w : TangentSpace I d.x1,
      B d.x1 (vec2 (I := I) d.v w) = 0 := by
  intro w
  rw [hB w]
  exact firstNullKernel_left (I := I) (M := M) hsym d w

/-- Transfer the first-null right-kernel fact from the raw barrier evaluator to
a local `(0,2)` tensor field whose right-null evaluations agree with it. -/
private theorem firstNullFieldKerR
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S)
        (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0)
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    (hB :
      ∀ w : TangentSpace I d.x1,
        B d.x1 (vec2 (I := I) w d.v) =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 w d.v) :
    ∀ w : TangentSpace I d.x1,
      B d.x1 (vec2 (I := I) w d.v) = 0 := by
  intro w
  rw [hB w]
  exact firstNullKernel_right (I := I) (M := M) hsym d w

/-- One-dimensional derivative sign at a right-end minimum.

If `phi` is nonnegative on `[a,t]`, vanishes at `t`, and has derivative `d`
within a larger open interval `(a,b]` at `t`, then `d <= 0`. -/
private theorem deriv_nonpos_of_nonneg_left
    {phi : Real -> Real} {a b t d : Real}
    (hat : a < t) (htb : t ≤ b)
    (hnonneg : ∀ s : Real, s ∈ Set.Icc a t -> 0 ≤ phi s)
    (hzero : phi t = 0)
    (hderiv : HasDerivWithinAt phi d (Set.Ioc a b) t) :
    d ≤ 0 := by
  let m : Real := (a + t) / 2
  have ham : a < m := by
    dsimp [m]
    linarith
  have hmt : m < t := by
    dsimp [m]
    linarith
  have hsubset : Set.Icc m t ⊆ Set.Ioc a b := by
    intro y hy
    exact ⟨lt_of_lt_of_le ham hy.1, hy.2.trans htb⟩
  have hderiv_m : HasDerivWithinAt phi d (Set.Icc m t) t :=
    hderiv.mono hsubset
  have hmin : IsMinOn phi (Set.Icc m t) t := by
    intro y hy
    rw [hzero]
    exact hnonneg y ⟨(le_of_lt ham).trans hy.1, hy.2⟩
  have hlocal : IsLocalMinOn phi (Set.Icc m t) t := hmin.localize
  have hdir : m - t ∈ posTangentConeAt (Set.Icc m t) t := by
    have hseg : segment Real t m ⊆ Set.Icc m t := by
      rw [segment_symm, segment_eq_Icc (le_of_lt hmt)]
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonneg_deriv :
      0 ≤ (fderivWithin Real phi (Set.Icc m t) t : Real →L[Real] Real) (m - t) :=
    hlocal.fderivWithin_nonneg hdir
  have huniq :
      UniqueDiffWithinAt Real (Set.Icc m t) t :=
    (uniqueDiffOn_Icc hmt).uniqueDiffWithinAt ⟨le_of_lt hmt, le_rfl⟩
  have hderiv_eq : derivWithin phi (Set.Icc m t) t = d :=
    hderiv_m.derivWithin huniq
  have hlin :
      (fderivWithin Real phi (Set.Icc m t) t : Real →L[Real] Real) (m - t) =
        (m - t) * derivWithin phi (Set.Icc m t) t := by
    rw [← fderivWithin_derivWithin (𝕜 := Real) (f := phi)
      (s := Set.Icc m t) (x := t)]
    simpa [smul_eq_mul] using
      ((fderivWithin Real phi (Set.Icc m t) t : Real →L[Real] Real).map_smul
        (m - t) (1 : Real))
  rw [hlin, hderiv_eq] at hnonneg_deriv
  exact nonpos_of_mul_nonneg_right hnonneg_deriv (sub_neg.mpr hmt)

/-- The fixed-vector time derivative at a first-null point is nonpositive. -/
theorem firstNullTime_nonpos
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (timeDeriv : TensorQuadraticFormFamily (I := I) (M := M))
    (hderiv :
      ∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt
            (fun s : Real =>
              tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
                s x v v)
            (timeDeriv t x v) (Set.Ioc t0 (t0 + delta)) t) :
    timeDeriv d.t1 d.x1 d.v ≤ 0 := by
  exact deriv_nonpos_of_nonneg_left
    (a := t0) (b := t0 + delta) (t := d.t1)
    (d := timeDeriv d.t1 d.x1 d.v)
    d.t1_mem.1 d.t1_mem.2
    (fun s hs => d.nonnegative_until s hs d.x1 d.v)
    d.null
    (hderiv d.t1 d.t1_mem d.x1 d.v)

/-- Drift-slot cancellation for a scalar test `phi = B(V,V)`.

This is the first-derivative product rule specialized to a point where the
moving test vector fields have zero covariant derivative. -/
theorem nablaEval_extDeriv
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : ∀ q : Fin 2, V q x = v)
    (hcovV :
      ∀ q : Fin 2, ((cov (fun p : M => V q p) x) (Y x)) = 0) :
    nablaB x (Fin.cons (Y x) (vec2 (I := I) v v)) =
      extDerivFun (I := I) (fun p : M => B p (fun q : Fin 2 => V q p))
        x (Y x) := by
  have hslots : (fun q : Fin 2 => V q x) = vec2 (I := I) v v := by
    funext q
    rw [hV q]
    fin_cases q <;> simp [vec2, Curvature.vec2]
  have h :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I)
      hreal Y V x
  rw [hslots] at h
  rw [h]
  have hsum :
      (∑ a : Fin 2,
        B x
          (Function.update (vec2 (I := I) v v) a
            ((cov (fun p : M => V a p) x) (Y x)))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _ha
    rw [hcovV a]
    exact (B x).map_update_zero (vec2 (I := I) v v) a
  rw [hsum]
  simp

/--
First-derivative product rule at a null vector in the kernel of the two-tensor.

This variant does not require the moving test vector fields to have zero
covariant derivative in the differentiating direction.  The two correction
terms in the tensor product rule vanish because the null vector is in the left
and right kernel of `B x`.
-/
private theorem nablaEval_ker
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : ∀ q : Fin 2, V q x = v)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0) :
    nablaB x (Fin.cons (Y x) (vec2 (I := I) v v)) =
      extDerivFun (I := I) (fun p : M => B p (fun q : Fin 2 => V q p))
        x (Y x) := by
  have hslots : (fun q : Fin 2 => V q x) = vec2 (I := I) v v := by
    funext q
    rw [hV q]
    fin_cases q <;> simp [vec2, Curvature.vec2]
  have h :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I)
      hreal Y V x
  rw [hslots] at h
  rw [h]
  have hsum :
      (∑ a : Fin 2,
        B x
          (Function.update (vec2 (I := I) v v) a
            ((cov (fun p : M => V a p) x) (Y x)))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _ha
    fin_cases a
    · change
        B x
          (Function.update (vec2 (I := I) v v) (0 : Fin 2)
            ((cov (fun p : M => V 0 p) x) (Y x))) = 0
      let A : TangentSpace I x := (cov (fun p : M => V 0 p) x) (Y x)
      have hupdate :
          Function.update (vec2 (I := I) v v) (0 : Fin 2) A =
            vec2 (I := I) A v := by
        funext q
        fin_cases q <;> simp [vec2, Curvature.vec2, Function.update, A]
      rw [hupdate]
      exact hkerR A
    · change
        B x
          (Function.update (vec2 (I := I) v v) (1 : Fin 2)
            ((cov (fun p : M => V 1 p) x) (Y x))) = 0
      let A : TangentSpace I x := (cov (fun p : M => V 1 p) x) (Y x)
      have hupdate :
          Function.update (vec2 (I := I) v v) (1 : Fin 2) A =
            vec2 (I := I) v A := by
        funext q
        fin_cases q <;> simp [vec2, Curvature.vec2, Function.update, A]
      rw [hupdate]
      exact hkerL A
  rw [hsum]
  simp

/--
Pointwise version of `nablaEval_ker` for an arbitrary tangent direction.

The required smooth direction field is chosen internally; this is useful when
the direction is a correction term such as `(∇_X Y)_x`.
-/
private theorem nablaEval_ker_tangent
    [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (Vsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : Vsec x = v)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0)
    (A : TangentSpace I x) :
    nablaB x (Fin.cons A (vec2 (I := I) v v)) =
      extDerivFun (I := I)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) x A := by
  obtain ⟨Ysec, hYsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A
  let V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun _ => Vsec
  have hV' : ∀ q : Fin 2, V q x = v := by
    intro q
    exact hV
  have hcalc :=
    nablaEval_ker (I := I) (M := M) hreal Ysec V hV' hkerL hkerR
  simpa [V, hYsec, vec2_self_eq_const] using hcalc

/-- The derivative of a correction term `B(A,V)` vanishes when `A` vanishes at
the point and `V` is a right-null vector for `B` there. -/
private theorem deriv_eval_zero_left
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (X A V : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hA : A x = 0)
    (hV : V x = v)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0) :
    extDerivFun (I := I)
      (fun p : M => B p (vec2 (I := I) (A p) (V p))) x (X x) = 0 := by
  let U : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Fin.cons A (fun _ : Fin 1 => V)
  have hslots : (fun q : Fin 2 => U q x) =
      vec2 (I := I) (0 : TangentSpace I x) v := by
    funext q
    fin_cases q <;> simp [U, hA, hV, vec2, Curvature.vec2]
  have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) hreal X U x
  rw [hslots] at h
  have hfun :
      (fun p : M => B p (fun a : Fin 2 => U a p)) =
        (fun p : M => B p (vec2 (I := I) (A p) (V p))) := by
    funext p
    congr
    funext q
    fin_cases q <;> simp [U, vec2, Curvature.vec2]
  rw [hfun] at h
  have hlhs :
      nablaB x (Fin.cons (X x) (vec2 (I := I) (0 : TangentSpace I x) v)) = 0 := by
    exact (nablaB x).map_coord_zero (1 : Fin 3)
      (by
        change (vec2 (I := I) (0 : TangentSpace I x) v) (0 : Fin 2) = 0
        simp [vec2, Curvature.vec2])
  have hsum :
      (∑ a : Fin 2,
        B x
          (Function.update (vec2 (I := I) (0 : TangentSpace I x) v) a
            ((cov (fun p : M => U a p) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_two]
    have h0 :
        B x
          (Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (0 : Fin 2)
            ((cov (fun p : M => U 0 p) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (fun p : M => U 0 p) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (0 : Fin 2) W =
            vec2 (I := I) W v := by
        funext q
        fin_cases q <;> simp [vec2, Curvature.vec2, Function.update, W]
      rw [hupdate]
      exact hkerR W
    have h1 :
        B x
          (Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (1 : Fin 2)
            ((cov (fun p : M => U 1 p) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (fun p : M => U 1 p) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (1 : Fin 2) W =
            vec2 (I := I) (0 : TangentSpace I x) W := by
        funext q
        fin_cases q <;> simp [vec2, Curvature.vec2, Function.update, W]
      have hzero :
          B x (vec2 (I := I) (0 : TangentSpace I x) W) = 0 := by
        exact (B x).map_coord_zero (0 : Fin 2)
          (by simp [vec2, Curvature.vec2])
      rw [hupdate]
      exact hzero
    rw [h0, h1]
    simp
  rw [hlhs, hsum] at h
  simpa using h.symm

/-- The derivative of a correction term `B(V,A)` vanishes when `A` vanishes at
the point and `V` is a left-null vector for `B` there. -/
private theorem deriv_eval_zero_right
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (X V A : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : V x = v)
    (hA : A x = 0)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0) :
    extDerivFun (I := I)
      (fun p : M => B p (vec2 (I := I) (V p) (A p))) x (X x) = 0 := by
  let U : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Fin.cons V (fun _ : Fin 1 => A)
  have hslots : (fun q : Fin 2 => U q x) =
      vec2 (I := I) v (0 : TangentSpace I x) := by
    funext q
    fin_cases q <;> simp [U, hA, hV, vec2, Curvature.vec2]
  have h := TotalNabla0SRealizes.eval_smooth_slots (I := I) hreal X U x
  rw [hslots] at h
  have hfun :
      (fun p : M => B p (fun a : Fin 2 => U a p)) =
        (fun p : M => B p (vec2 (I := I) (V p) (A p))) := by
    funext p
    congr
    funext q
    fin_cases q <;> simp [U, vec2, Curvature.vec2]
  rw [hfun] at h
  have hlhs :
      nablaB x (Fin.cons (X x) (vec2 (I := I) v (0 : TangentSpace I x))) = 0 := by
    exact (nablaB x).map_coord_zero (2 : Fin 3)
      (by
        change (vec2 (I := I) v (0 : TangentSpace I x)) (1 : Fin 2) = 0
        simp [vec2, Curvature.vec2])
  have hsum :
      (∑ a : Fin 2,
        B x
          (Function.update (vec2 (I := I) v (0 : TangentSpace I x)) a
            ((cov (fun p : M => U a p) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_two]
    have h0 :
        B x
          (Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (0 : Fin 2)
            ((cov (fun p : M => U 0 p) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (fun p : M => U 0 p) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (0 : Fin 2) W =
            vec2 (I := I) W (0 : TangentSpace I x) := by
        funext q
        fin_cases q <;> simp [vec2, Curvature.vec2, Function.update, W]
      have hzero :
          B x (vec2 (I := I) W (0 : TangentSpace I x)) = 0 := by
        exact (B x).map_coord_zero (1 : Fin 2)
          (by simp [vec2, Curvature.vec2])
      rw [hupdate]
      exact hzero
    have h1 :
        B x
          (Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (1 : Fin 2)
            ((cov (fun p : M => U 1 p) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (fun p : M => U 1 p) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (1 : Fin 2) W =
            vec2 (I := I) v W := by
        funext q
        fin_cases q <;> simp [vec2, Curvature.vec2, Function.update, W]
      rw [hupdate]
      exact hkerL W
    rw [h0, h1]
    simp
  rw [hlhs, hsum] at h
  simpa using h.symm

/-- C¹-slot version of `deriv_eval_zero_left`.  The moved slot need only be a
locally `C¹` tangent field near the evaluation point. -/
private theorem deriv_eval_zero_left_C1
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (X V : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (A : (p : M) -> TangentSpace I p)
    {x : M} {v : TangentSpace I x}
    (hA_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M => (⟨p, A p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x)
    (hA : A x = 0)
    (hV : V x = v)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0) :
    extDerivFun (I := I)
      (fun p : M => B p (vec2 (I := I) (A p) (V p))) x (X x) = 0 := by
  let U : Fin 2 -> (p : M) -> TangentSpace I p :=
    Fin.cons A (fun _ : Fin 1 => fun p : M => V p)
  have hV_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    have htop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x :=
      V.contMDiff.contMDiffAt
    exact htop.of_le (by simp)
  have hU_at : ∀ a : Fin 2,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, U a p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    intro a
    fin_cases a
    · simpa [U] using hA_at
    · simpa [U] using hV_at
  have hslots : (fun q : Fin 2 => U q x) =
      vec2 (I := I) (0 : TangentSpace I x) v := by
    funext q
    fin_cases q <;> simp [U, hA, hV, vec2, Curvature.vec2]
  have h := TotalNabla0SRealizes.eval_C1_slots (I := I) hreal X U x hU_at
  rw [hslots] at h
  have hfun :
      (fun p : M => B p (fun a : Fin 2 => U a p)) =
        (fun p : M => B p (vec2 (I := I) (A p) (V p))) := by
    funext p
    congr
    funext q
    fin_cases q <;> simp [U, vec2, Curvature.vec2]
  rw [hfun] at h
  have hlhs :
      nablaB x (Fin.cons (X x) (vec2 (I := I) (0 : TangentSpace I x) v)) = 0 := by
    exact (nablaB x).map_coord_zero (1 : Fin 3)
      (by
        change (vec2 (I := I) (0 : TangentSpace I x) v) (0 : Fin 2) = 0
        simp [vec2, Curvature.vec2])
  have hsum :
      (∑ a : Fin 2,
        B x
          (Function.update (vec2 (I := I) (0 : TangentSpace I x) v) a
            ((cov (U a) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_two]
    have h0 :
        B x
          (Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (0 : Fin 2)
            ((cov (U 0) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (U 0) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (0 : Fin 2) W =
            vec2 (I := I) W v := by
        funext q
        fin_cases q <;> simp [vec2, Curvature.vec2, Function.update, W]
      rw [hupdate]
      exact hkerR W
    have h1 :
        B x
          (Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (1 : Fin 2)
            ((cov (U 1) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (U 1) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) (0 : TangentSpace I x) v) (1 : Fin 2) W =
            vec2 (I := I) (0 : TangentSpace I x) W := by
        funext q
        fin_cases q <;> simp [vec2, Curvature.vec2, Function.update, W]
      have hzero :
          B x (vec2 (I := I) (0 : TangentSpace I x) W) = 0 := by
        exact (B x).map_coord_zero (0 : Fin 2)
          (by simp [vec2, Curvature.vec2])
      rw [hupdate]
      exact hzero
    rw [h0, h1]
    simp
  rw [hlhs, hsum] at h
  simpa using h.symm

/-- C¹-slot version of `deriv_eval_zero_right`.  The moved slot need only be a
locally `C¹` tangent field near the evaluation point. -/
private theorem deriv_eval_zero_right_C1
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (X V : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (A : (p : M) -> TangentSpace I p)
    {x : M} {v : TangentSpace I x}
    (hA_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M => (⟨p, A p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x)
    (hV : V x = v)
    (hA : A x = 0)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0) :
    extDerivFun (I := I)
      (fun p : M => B p (vec2 (I := I) (V p) (A p))) x (X x) = 0 := by
  let U : Fin 2 -> (p : M) -> TangentSpace I p :=
    Fin.cons (fun p : M => V p) (fun _ : Fin 1 => A)
  have hV_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    have htop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x :=
      V.contMDiff.contMDiffAt
    exact htop.of_le (by simp)
  have hU_at : ∀ a : Fin 2,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, U a p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    intro a
    fin_cases a
    · simpa [U] using hV_at
    · simpa [U] using hA_at
  have hslots : (fun q : Fin 2 => U q x) =
      vec2 (I := I) v (0 : TangentSpace I x) := by
    funext q
    fin_cases q <;> simp [U, hA, hV, vec2, Curvature.vec2]
  have h := TotalNabla0SRealizes.eval_C1_slots (I := I) hreal X U x hU_at
  rw [hslots] at h
  have hfun :
      (fun p : M => B p (fun a : Fin 2 => U a p)) =
        (fun p : M => B p (vec2 (I := I) (V p) (A p))) := by
    funext p
    congr
    funext q
    fin_cases q <;> simp [U, vec2, Curvature.vec2]
  rw [hfun] at h
  have hlhs :
      nablaB x (Fin.cons (X x) (vec2 (I := I) v (0 : TangentSpace I x))) = 0 := by
    exact (nablaB x).map_coord_zero (2 : Fin 3)
      (by
        change (vec2 (I := I) v (0 : TangentSpace I x)) (1 : Fin 2) = 0
        simp [vec2, Curvature.vec2])
  have hsum :
      (∑ a : Fin 2,
        B x
          (Function.update (vec2 (I := I) v (0 : TangentSpace I x)) a
            ((cov (U a) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_two]
    have h0 :
        B x
          (Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (0 : Fin 2)
            ((cov (U 0) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (U 0) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (0 : Fin 2) W =
            vec2 (I := I) W (0 : TangentSpace I x) := by
        funext q
        fin_cases q <;> simp [vec2, Curvature.vec2, Function.update, W]
      have hzero :
          B x (vec2 (I := I) W (0 : TangentSpace I x)) = 0 := by
        exact (B x).map_coord_zero (1 : Fin 2)
          (by simp [vec2, Curvature.vec2])
      rw [hupdate]
      exact hzero
    have h1 :
        B x
          (Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (1 : Fin 2)
            ((cov (U 1) x) (X x))) = 0 := by
      let W : TangentSpace I x := (cov (U 1) x) (X x)
      have hupdate :
          Function.update (vec2 (I := I) v (0 : TangentSpace I x)) (1 : Fin 2) W =
            vec2 (I := I) v W := by
        funext q
        fin_cases q <;> simp [vec2, Curvature.vec2, Function.update, W]
      rw [hupdate]
      exact hkerL W
    rw [h0, h1]
    simp
  rw [hlhs, hsum] at h
  simpa using h.symm

/-- Second-derivative moving-slot product rule at a point where all moved
slots have zero covariant derivative in the differentiating direction. -/
theorem nabla2Eval_extDeriv
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : ∀ q : Fin 2, V q x = v)
    (hcovY : ((cov (fun p : M => Y p) x) (X x)) = 0)
    (hcovV :
      ∀ q : Fin 2, ((cov (fun p : M => V q p) x) (X x)) = 0) :
    nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v))) =
      extDerivFun (I := I)
        (fun p : M => nablaB p (Fin.cons (Y p) (fun q : Fin 2 => V q p)))
        x (X x) := by
  let W : Fin 3 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Fin.cons Y V
  have hslots :
      (fun q : Fin 3 => W q x) =
        Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
          (Y x) (vec2 (I := I) v v) := by
    funext q
    cases q using Fin.cases with
    | zero =>
        simp [W]
    | succ q =>
        simp [W, hV q, vec2, Curvature.vec2, Fin.cons_succ]
  have h :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I)
      hreal X W x
  rw [hslots] at h
  rw [h]
  have hsum :
      (∑ a : Fin 3,
        nablaB x
          (Function.update
            (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
              (Y x) (vec2 (I := I) v v))
            a ((cov (fun p : M => W a p) x) (X x)))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _ha
    have hz : ((cov (fun p : M => W a p) x) (X x)) = 0 := by
      cases a using Fin.cases with
      | zero =>
          simpa [W, Fin.cons_zero] using hcovY
      | succ a =>
          simpa [W, Fin.cons_succ] using hcovV a
    rw [hz]
    exact (nablaB x).map_update_zero
      (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
        (Y x) (vec2 (I := I) v v)) a
  have hfun :
      (fun p : M => nablaB p (fun a : Fin 3 => W a p)) =
        (fun p : M => nablaB p (Fin.cons (Y p) (fun q : Fin 2 => V q p))) := by
    funext p
    congr
    funext a
    cases a using Fin.cases with
    | zero =>
        simp [W, Fin.cons_zero]
    | succ a =>
        simp [W, Fin.cons_succ]
  rw [hfun, hsum]
  simp

/--
Second-derivative moving-slot product rule with the `∇_X Y` correction kept.

This is the form that matches the covariant Hessian definition.  The repeated
test vector section has zero covariant derivative at the point, so only the
correction from the middle slot `Y` remains.
-/
private theorem nabla2Eval_extDeriv_oneSec_corr
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (X Y Vsec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : Vsec x = v)
    (hcovV : ((cov (fun p : M => Vsec p) x) (X x)) = 0) :
    nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v))) =
      extDerivFun (I := I)
        (fun p : M => nablaB p (Fin.cons (Y p) (vec2 (I := I) (Vsec p) (Vsec p))))
        x (X x) -
      nablaB x
        (Fin.cons ((cov (fun p : M => Y p) x) (X x)) (vec2 (I := I) v v)) := by
  let W : Fin 3 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Fin.cons Y (fun _ : Fin 2 => Vsec)
  have hslots :
      (fun q : Fin 3 => W q x) =
        Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
          (Y x) (vec2 (I := I) v v) := by
    funext q
    cases q using Fin.cases with
    | zero =>
        simp [W]
    | succ q =>
        simp [W, hV, vec2, Curvature.vec2, Fin.cons_succ]
  have h :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I)
      hreal X W x
  rw [hslots] at h
  rw [h]
  have hsum :
      (∑ a : Fin 3,
        nablaB x
          (Function.update
            (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
              (Y x) (vec2 (I := I) v v))
            a ((cov (fun p : M => W a p) x) (X x)))) =
      nablaB x
        (Fin.cons ((cov (fun p : M => Y p) x) (X x)) (vec2 (I := I) v v)) := by
    rw [Fin.sum_univ_three]
    have h0 :
        nablaB x
          (Function.update
            (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
              (Y x) (vec2 (I := I) v v))
            0 ((cov (fun p : M => W 0 p) x) (X x))) =
        nablaB x
          (Fin.cons ((cov (fun p : M => Y p) x) (X x)) (vec2 (I := I) v v)) := by
      congr
      funext q
      cases q using Fin.cases with
      | zero =>
          simp [W, Function.update, Fin.cons_zero]
      | succ q =>
          simp [Function.update, Fin.cons_succ]
    have h1 :
        nablaB x
          (Function.update
            (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
              (Y x) (vec2 (I := I) v v))
            1 ((cov (fun p : M => W 1 p) x) (X x))) = 0 := by
      have hz : ((cov (fun p : M => W 1 p) x) (X x)) = 0 := by
        simpa [W, Fin.cons_succ] using hcovV
      rw [hz]
      exact (nablaB x).map_update_zero
        (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
          (Y x) (vec2 (I := I) v v)) 1
    have h2 :
        nablaB x
          (Function.update
            (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
              (Y x) (vec2 (I := I) v v))
            2 ((cov (fun p : M => W 2 p) x) (X x))) = 0 := by
      have hz : ((cov (fun p : M => W 2 p) x) (X x)) = 0 := by
        simpa [W, Fin.cons_succ] using hcovV
      rw [hz]
      exact (nablaB x).map_update_zero
        (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
          (Y x) (vec2 (I := I) v v)) 2
    rw [h0, h1, h2]
    simp
  have hfun :
      (fun p : M => nablaB p (fun a : Fin 3 => W a p)) =
        (fun p : M => nablaB p
          (Fin.cons (Y p) (vec2 (I := I) (Vsec p) (Vsec p)))) := by
    funext p
    congr
    funext a
    cases a using Fin.cases with
    | zero =>
        simp [W, Fin.cons_zero]
    | succ a =>
        simp [W, vec2_self_eq_const, Fin.cons_succ]
  rw [hfun, hsum]

/--
Second-derivative product rule with the correction term rewritten as the
directional derivative of the scalar test function `phi = B(V,V)`.

This is the local calc matching the covariant Hessian formula: the `∇_X Y`
correction in the tensor derivative becomes the corresponding `d phi` term by
the first-null kernel product rule.
-/
private theorem nabla2Eval_extDeriv_oneSec_corr_phi
    [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    (hreal1 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (hreal2 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (X Y Vsec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : Vsec x = v)
    (hcovV : ((cov (fun p : M => Vsec p) x) (X x)) = 0)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0) :
    nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v))) =
      extDerivFun (I := I)
        (fun p : M => nablaB p (Fin.cons (Y p) (vec2 (I := I) (Vsec p) (Vsec p))))
        x (X x) -
      extDerivFun (I := I)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) x
        ((cov (fun p : M => Y p) x) (X x)) := by
  let A : TangentSpace I x := (cov (fun p : M => Y p) x) (X x)
  have hA :
      nablaB x (Fin.cons A (vec2 (I := I) v v)) =
        extDerivFun (I := I)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) x A :=
    nablaEval_ker_tangent (I := I) (M := M) hreal1 Vsec hV hkerL hkerR A
  calc
    nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v)))
        =
      extDerivFun (I := I)
        (fun p : M => nablaB p (Fin.cons (Y p) (vec2 (I := I) (Vsec p) (Vsec p))))
        x (X x) -
      nablaB x
        (Fin.cons ((cov (fun p : M => Y p) x) (X x)) (vec2 (I := I) v v)) := by
          exact nabla2Eval_extDeriv_oneSec_corr (I := I) (M := M)
            hreal2 X Y Vsec hV hcovV
    _ =
      extDerivFun (I := I)
        (fun p : M => nablaB p (Fin.cons (Y p) (vec2 (I := I) (Vsec p) (Vsec p))))
        x (X x) -
      extDerivFun (I := I)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) x
        ((cov (fun p : M => Y p) x) (X x)) := by
          simpa [A] using congrArg
            (fun z : Real =>
              extDerivFun (I := I)
                (fun p : M =>
                  nablaB p (Fin.cons (Y p) (vec2 (I := I) (Vsec p) (Vsec p))))
                x (X x) - z)
            hA

/--
Corrected second-derivative product rule for the scalar test
`phi = B(V,V)` at a PSD-null vector.

The correction terms in the first derivative of `B(V,V)` are
`B(∇_Y V,V)` and `B(V,∇_Y V)`.  If `V` has zero covariant derivative at the
point, those correction fields vanish there; the left/right kernel hypotheses
make their derivatives vanish in the `X` direction.  This leaves exactly the
covariant scalar Hessian expression.
-/
private theorem nabla2Eval_extDeriv_oneSec_hess
    [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    (hreal1 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (hreal2 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (X Y V : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : V x = v)
    (hcovVX : ((cov (fun p : M => V p) x) (X x)) = 0)
    (hcovVY : ((cov (fun p : M => V p) x) (Y x)) = 0)
    (hA_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, ((cov (fun q : M => V q) p) (Y p))⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0)
    (hdphi :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          extDerivFun (I := I)
            (fun q : M => B q (vec2 (I := I) (V q) (V q))) p (Y p)) x) :
    nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v))) =
      extDerivFun (I := I)
        (fun p : M =>
          extDerivFun (I := I)
            (fun q : M => B q (vec2 (I := I) (V q) (V q))) p (Y p))
        x (X x) -
      extDerivFun (I := I)
        (fun p : M => B p (vec2 (I := I) (V p) (V p))) x
        ((cov (fun p : M => Y p) x) (X x)) := by
  let phi : M -> Real := fun p => B p (vec2 (I := I) (V p) (V p))
  let A : (p : M) -> TangentSpace I p := fun p => ((cov (fun q : M => V q) p) (Y p))
  let dphiY : M -> Real := fun p => extDerivFun (I := I) phi p (Y p)
  let corrL : M -> Real := fun p => B p (vec2 (I := I) (A p) (V p))
  let corrR : M -> Real := fun p => B p (vec2 (I := I) (V p) (A p))
  have hV_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    have htop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x :=
      V.contMDiff.contMDiffAt
    exact htop.of_le (by simp)
  have hA_at' :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M => (⟨p, A p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
    simpa [A] using hA_at
  have hcorrL :
      MDifferentiableAt I 𝓘(Real, Real) corrL x := by
    let Slots : Fin 2 -> (p : M) -> TangentSpace I p :=
      Fin.cons A (fun _ : Fin 1 => fun p : M => V p)
    have hSlots : ∀ a : Fin 2,
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, Slots a p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
      intro a
      fin_cases a
      · simpa [Slots] using hA_at'
      · simpa [Slots] using hV_at
    have hraw := tensor0SField_eval_C1_slots_mdiffAt
      (I := I) (M := M) B Slots x hSlots
    have hfun :
        (fun p : M => B p (fun a : Fin 2 => Slots a p)) = corrL := by
      funext p
      congr
      funext a
      fin_cases a <;> simp [Slots, vec2, Curvature.vec2]
    rw [← hfun]
    exact hraw
  have hcorrR :
      MDifferentiableAt I 𝓘(Real, Real) corrR x := by
    let Slots : Fin 2 -> (p : M) -> TangentSpace I p :=
      Fin.cons (fun p : M => V p) (fun _ : Fin 1 => A)
    have hSlots : ∀ a : Fin 2,
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, Slots a p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x := by
      intro a
      fin_cases a
      · simpa [Slots] using hV_at
      · simpa [Slots] using hA_at'
    have hraw := tensor0SField_eval_C1_slots_mdiffAt
      (I := I) (M := M) B Slots x hSlots
    have hfun :
        (fun p : M => B p (fun a : Fin 2 => Slots a p)) = corrR := by
      funext p
      congr
      funext a
      fin_cases a <;> simp [Slots, vec2, Curvature.vec2]
    rw [← hfun]
    exact hraw
  have hleft_fun :
      (fun p : M =>
        nablaB p (Fin.cons (Y p) (vec2 (I := I) (V p) (V p)))) =
        (fun p : M => dphiY p - corrL p - corrR p) := by
    funext p
    let Slots : Fin 2 ->
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      fun _ => V
    have hprod :=
      TotalNabla0SRealizes.eval_smooth_slots (I := I) hreal1 Y Slots p
    have hslots : (fun a : Fin 2 => Slots a p) =
        vec2 (I := I) (V p) (V p) := by
      funext a
      fin_cases a <;> simp [Slots, vec2, Curvature.vec2]
    rw [hslots] at hprod
    have hfun :
        (fun q : M => B q (fun a : Fin 2 => Slots a q)) = phi := by
      funext q
      simp [phi, Slots, vec2_self_eq_const]
    rw [hfun] at hprod
    have hsum :
        (∑ a : Fin 2,
          B p
            (Function.update (vec2 (I := I) (V p) (V p)) a
              ((cov (fun q : M => Slots a q) p) (Y p)))) =
          corrL p + corrR p := by
      rw [Fin.sum_univ_two]
      have h0 :
          B p
            (Function.update (vec2 (I := I) (V p) (V p)) (0 : Fin 2)
              ((cov (fun q : M => Slots 0 q) p) (Y p))) =
            corrL p := by
        have hcov :
            ((cov (fun q : M => Slots 0 q) p) (Y p)) = A p := by
          rfl
        rw [hcov]
        congr
        funext a
        fin_cases a <;> simp [vec2, Curvature.vec2, Function.update]
      have h1 :
          B p
            (Function.update (vec2 (I := I) (V p) (V p)) (1 : Fin 2)
              ((cov (fun q : M => Slots 1 q) p) (Y p))) =
            corrR p := by
        have hcov :
            ((cov (fun q : M => Slots 1 q) p) (Y p)) = A p := by
          rfl
        rw [hcov]
        congr
        funext a
        fin_cases a <;> simp [vec2, Curvature.vec2, Function.update]
      rw [h0, h1]
    rw [hprod, hsum]
    ring
  have hleft_deriv :
      extDerivFun (I := I)
        (fun p : M =>
          nablaB p (Fin.cons (Y p) (vec2 (I := I) (V p) (V p)))) x (X x) =
      extDerivFun (I := I) dphiY x (X x) := by
    rw [hleft_fun]
    have hsub1 :
        MDifferentiableAt I 𝓘(Real, Real) (fun p : M => dphiY p - corrL p) x :=
      hdphi.sub hcorrL
    rw [extDerivFun_sub_at (I := I) (x := x) (v := X x) hsub1 hcorrR]
    rw [extDerivFun_sub_at (I := I) (x := x) (v := X x) hdphi hcorrL]
    have hA0 : A x = 0 := by
      simp [A, hcovVY]
    have hcorrL_zero :
        extDerivFun (I := I) corrL x (X x) = 0 := by
      simpa [corrL] using
        deriv_eval_zero_left_C1 (I := I) (M := M)
          hreal1 X V A hA_at' hA0 hV hkerR
    have hcorrR_zero :
        extDerivFun (I := I) corrR x (X x) = 0 := by
      simpa [corrR] using
        deriv_eval_zero_right_C1 (I := I) (M := M)
          hreal1 X V A hA_at' hV hA0 hkerL
    rw [hcorrL_zero, hcorrR_zero]
    ring
  have hcorr_phi :=
    nabla2Eval_extDeriv_oneSec_corr_phi (I := I) (M := M)
      hreal1 hreal2 X Y V hV hcovVX hkerL hkerR
  rw [hleft_deriv] at hcorr_phi
  simpa [phi, dphiY] using hcorr_phi

/-- Product-rule bridge from the tensor second derivative to a supplied scalar
Hessian realization for `phi = B(V,V)`. -/
private theorem nabla2Eval_hess
    [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    {du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1}
    {Hess : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y}
    (hreal1 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (hreal2 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (X Y V : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : V x = v)
    (hcovVX : ((cov (fun p : M => V p) x) (X x)) = 0)
    (hcovVY : ((cov (fun p : M => V p) x) (Y x)) = 0)
    (hA_at :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, ((cov (fun q : M => V q) p) (Y p))⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0)
    (hdu :
      DuFieldRealizes (I := I)
        (fun p : M => B p (vec2 (I := I) (V p) (V p))) du)
    (hHess :
      HessianRealizesNablaDuAt (I := I) cov du Hess x)
    (hdphi :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          extDerivFun (I := I)
            (fun q : M => B q (vec2 (I := I) (V q) (V q))) p (Y p)) x) :
    nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v))) =
      Hess x (vec2 (I := I) (X x) (Y x)) := by
  let phi : M -> Real := fun p => B p (vec2 (I := I) (V p) (V p))
  have hprod :
      nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v))) =
        extDerivFun (I := I)
          (fun p : M => extDerivFun (I := I) phi p (Y p)) x (X x) -
        extDerivFun (I := I) phi x ((cov (fun p : M => Y p) x) (X x)) := by
    simpa [phi] using
      nabla2Eval_extDeriv_oneSec_hess (I := I) (M := M)
        hreal1 hreal2 X Y V hV hcovVX hcovVY hA_at hkerL hkerR hdphi
  have hnabla_eval :
      nablaDuAt (I := I) cov X du x (fun _ : Fin 1 => Y x) =
        extDerivFun (I := I) (fun y : M => du y (fun _ : Fin 1 => Y y))
          x (X x) -
        du x (fun _ : Fin 1 => (cov (fun y : M => Y y) x) (X x)) := by
    simpa [nablaDuAt] using
      Coordinates.nabla0SFun_one_eval_smooth_slots (I := I) cov X Y du x
  have hdu_fun :
      (fun y : M => du y (fun _ : Fin 1 => Y y)) =
        (fun y : M => extDerivFun (I := I) phi y (Y y)) := by
    funext y
    rw [hdu y]
    exact differential1FormFun_apply_eq_extDerivFun (I := I) phi y (Y y)
  have hdu_corr :
      du x (fun _ : Fin 1 => (cov (fun y : M => Y y) x) (X x)) =
        extDerivFun (I := I) phi x ((cov (fun y : M => Y y) x) (X x)) := by
    rw [hdu x]
    exact differential1FormFun_apply_eq_extDerivFun
      (I := I) phi x ((cov (fun y : M => Y y) x) (X x))
  have hnabla_phi :
      nablaDuAt (I := I) cov X du x (fun _ : Fin 1 => Y x) =
        extDerivFun (I := I) (fun y : M => extDerivFun (I := I) phi y (Y y))
          x (X x) -
        extDerivFun (I := I) phi x ((cov (fun y : M => Y y) x) (X x)) := by
    rw [hnabla_eval, hdu_fun, hdu_corr]
  calc
    nabla2B x (Fin.cons (X x) (Fin.cons (Y x) (vec2 (I := I) v v)))
        =
      extDerivFun (I := I) (fun y : M => extDerivFun (I := I) phi y (Y y))
        x (X x) -
      extDerivFun (I := I) phi x ((cov (fun y : M => Y y) x) (X x)) := hprod
    _ = nablaDuAt (I := I) cov X du x (fun _ : Fin 1 => Y x) := hnabla_phi.symm
    _ = Hess x (vec2 (I := I) (X x) (Y x)) := (hHess X (Y x)).symm

/-- Slot-level form of `nabla2Eval_hess`, suitable for the metric trace. -/
private theorem nabla2Eval_hess_slots
    [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    {du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1}
    {Hess : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y}
    (hreal1 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (hreal2 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (V : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : V x = v)
    (hcovV :
      ∀ W : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _),
        ((cov (fun p : M => V p) x) (W x)) = 0)
    (hkerL : ∀ w : TangentSpace I x, B x (vec2 (I := I) v w) = 0)
    (hkerR : ∀ w : TangentSpace I x, B x (vec2 (I := I) w v) = 0)
    (hdu :
      DuFieldRealizes (I := I)
        (fun p : M => B p (vec2 (I := I) (V p) (V p))) du)
    (hHess :
      HessianRealizesNablaDuAt (I := I) cov du Hess x)
    (hAreg :
      ∀ Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _),
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, ((cov (fun q : M => V q) p) (Y p))⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) x) :
    ∀ U W : TangentSpace I x,
      nabla2B x (metricTraceInput (I := I) U W (vec2 (I := I) v v)) =
        Hess x (vec2 (I := I) U W) := by
  let phi : M -> Real := fun p => B p (vec2 (I := I) (V p) (V p))
  have hphi :
      ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) phi := by
    let Slots : Fin 2 ->
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      fun _ => V
    have hraw := TensorMultilinear.contMDiff_tensor0SField_apply
      (I := I) (M := M) B Slots
    simpa [phi, Slots, vec2_self_eq_const] using hraw
  intro U W
  obtain ⟨Xsec, hXsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x U
  obtain ⟨Ysec, hYsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x W
  have hA_at := hAreg Ysec
  have hdphi :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          extDerivFun (I := I)
            (fun q : M => B q (vec2 (I := I) (V q) (V q))) p (Ysec p)) x := by
    simpa [phi] using dphi_apply_mdiffAt (I := I) phi hphi Ysec x
  have hcalc :=
    nabla2Eval_hess (I := I) (M := M)
      hreal1 hreal2 Xsec Ysec V hV (hcovV Xsec) (hcovV Ysec)
      hA_at hkerL hkerR hdu hHess hdphi
  have hinput :
      metricTraceInput (I := I) U W (vec2 (I := I) v v) =
        Fin.cons (Xsec x) (Fin.cons (Ysec x) (vec2 (I := I) v v)) := by
    funext q
    cases q using Fin.cases with
    | zero =>
        change U = Xsec x
        exact hXsec.symm
    | succ q =>
        cases q using Fin.cases with
        | zero =>
            change W = Ysec x
            exact hYsec.symm
        | succ q =>
            cases q using Fin.cases with
            | zero =>
                rfl
            | succ q =>
                fin_cases q
                rfl
  calc
    nabla2B x (metricTraceInput (I := I) U W (vec2 (I := I) v v))
        =
      nabla2B x (Fin.cons (Xsec x) (Fin.cons (Ysec x) (vec2 (I := I) v v))) := by
        rw [hinput]
    _ = Hess x (vec2 (I := I) (Xsec x) (Ysec x)) := hcalc
    _ = Hess x (vec2 (I := I) U W) := by
        rw [hXsec, hYsec]

/-- Drift-slot cancellation for a scalar test `phi = B(V,V)`.

This is the first-derivative product rule specialized to a point where the
moving test vector fields have zero covariant derivative and the scalar test
has zero spatial derivative in the drift direction. -/
theorem nablaEval_zero
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    {x : M} {v : TangentSpace I x}
    (hV : ∀ q : Fin 2, V q x = v)
    (hphi :
      extDerivFun (I := I) (fun p : M => B p (fun q : Fin 2 => V q p))
        x (X x) = 0)
    (hcovV :
      ∀ q : Fin 2, ((cov (fun p : M => V q p) x) (X x)) = 0) :
    nablaB x (Fin.cons (X x) (vec2 (I := I) v v)) = 0 := by
  rw [nablaEval_extDeriv (I := I) (M := M) hreal X V hV hcovV]
  exact hphi

/-- The scalar test function obtained by evaluating the first-null barrier on
local repeated vector slots has a spatial local minimum at the first-null base
point. -/
theorem firstNullLocalMin
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hV : ∀ q : Fin 2, V q d.x1 = d.v)
    (hB :
      ∀ p : M,
        B p (fun q : Fin 2 => V q p) =
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
            d.t1 p (V 0 p) (V 0 p)) :
    IsLocalMin (fun p : M => B p (fun q : Fin 2 => V q p)) d.x1 := by
  unfold IsLocalMin IsMinFilter
  filter_upwards [] with p
  have hbase :
      B d.x1 (fun q : Fin 2 => V q d.x1) = 0 := by
    rw [hB d.x1, hV 0]
    exact d.null
  have hp :
      0 ≤ B p (fun q : Fin 2 => V q p) := by
    rw [hB p]
    exact d.nonnegative_until d.t1
      ⟨le_of_lt d.t1_mem.1, le_rfl⟩ p (V 0 p)
  rw [hbase]
  exact hp

/--
Compactness and continuity package for extracting the first null vector of the
positive tensor barrier.

This is the analytic unit-tangent-bundle compactness input: it should be
produced from compactness of `M`, compactness of the unit tangent bundle for the
metric at the first time, and continuity of the barrier quadratic form.
-/
structure TensorFirstNullCompactnessOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) : Prop where
  firstNull_of_failure :
    (∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t0) x) ->
    (¬ TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0)
      (Set.Icc t0 (t0 + delta))) ->
    Nonempty (TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)

namespace TensorFirstNullCompactnessOn

/-- Section-backed first-null compactness.  This is the geometric bridge from
smooth tensor sections to the raw first-null package used by the WMP kernel. -/
theorem of_section
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real)
    (hcompact :
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentSlab (I := I) (M := M) G t0 (t0 + delta))))
    (hunit_cont :
      Continuous
        (barrierUnitQuad (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0 t0 (t0 + delta)))
    (hfixed_cont :
      ∀ x (v : TangentSpace I x),
        ContinuousOn
          (fun t : Real =>
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 t x v v)
          (Set.Icc t0 (t0 + delta))) :
    TensorFirstNullCompactnessOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0 := by
  classical
  let Sraw : TwoTensorFamily (I := I) (M := M) :=
    twoTensorSecToFamily (I := I) (M := M) S
  let B : TwoTensorFamily (I := I) (M := M) :=
    tensorBarrierFamily (I := I) (M := M) G Sraw epsilon delta t0
  let slab := MetricUnitTangentSlab (I := I) (M := M) G t0 (t0 + delta)
  let φ : slab -> Real :=
    barrierUnitQuad (I := I) (M := M) G Sraw epsilon delta t0 t0 (t0 + delta)
  let Z : Set slab := {p | φ p ≤ 0}
  refine ⟨?_⟩
  intro hinit_pos hfail
  have hZclosed : IsClosed Z := by
    have hclosed : IsClosed ((Set.Iic (0 : Real)) : Set Real) := isClosed_Iic
    simpa [Z, φ] using hclosed.preimage hunit_cont
  have hZcompact : IsCompact Z := by
    simpa [Z] using hcompact.inter_right hZclosed
  obtain ⟨pbad, hpbad_neg⟩ :=
    failure_unitSlab (I := I) (M := M) G S epsilon delta t0 t0
      (t0 + delta) hfail
  have hZne : Z.Nonempty := ⟨pbad, le_of_lt hpbad_neg⟩
  obtain ⟨p1, hp1Z, hmin⟩ :=
    hZcompact.exists_isMinOn hZne
      (metricUnitSlab_timeVal_cont (I := I) (M := M) G t0 (t0 + delta)).continuousOn
  let t1 : Real := p1.1.1
  let x1 : M := MetricUnitTangent.base (I := I) (M := M) p1.2
  let v1 : TangentSpace I x1 := MetricUnitTangent.vec (I := I) (M := M) p1.2
  have hp1_time : t1 ∈ Set.Icc t0 (t0 + delta) := by
    simp [t1]
  have hp1_nonpos : φ p1 ≤ 0 := hp1Z
  have hv1_ne : v1 ≠ 0 := by
    intro hv
    have hbad : (0 : Real) = 1 := by
      simpa [v1, hv] using
        (MetricUnitTangent.unit (I := I) (M := M) p1.2)
    norm_num at hbad
  have ht1_ne_t0 : t1 ≠ t0 := by
    intro ht1eq
    have hpos : 0 < φ p1 := by
      have hpos_raw := hinit_pos x1 v1 hv1_ne
      simpa [φ, barrierUnitQuad, Sraw, B, t1, x1, v1, ht1eq] using hpos_raw
    linarith
  have ht1_gt : t0 < t1 := lt_of_le_of_ne hp1_time.1 (Ne.symm ht1_ne_t0)
  have hnonneg_until :
      ∀ t, t ∈ Set.Icc t0 t1 ->
        ∀ x, TwoTensorNonnegativeAt (I := I) (M := M) (B t) x := by
    intro t ht x v
    by_contra hnot
    have hneg : B t x v v < 0 := lt_of_not_ge hnot
    have ht_full : t ∈ Set.Icc t0 (t0 + delta) :=
      ⟨ht.1, le_trans ht.2 hp1_time.2⟩
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · obtain ⟨q, hq_time, hqneg⟩ :=
        negBarrier_unitSlab (I := I) (M := M) G S epsilon delta t0
          t0 (t0 + delta) t ht_full x v (by simpa [B, Sraw] using hneg)
      have hqZ : q ∈ Z := by
        simpa [Z, φ] using le_of_lt hqneg
      have hmin_q := hmin hqZ
      have hqtime : q.1.1 = t := hq_time
      have ht1_le_t : t1 ≤ t := by
        have ht1_le_q : (p1.1.1 : Real) ≤ q.1.1 := by
          exact (Subtype.coe_le_coe).2 hmin_q
        simpa [t1, hqtime] using ht1_le_q
      linarith
    · have hneg_t1 :
          B t1 x v v < 0 := by
        simpa [heq] using hneg
      obtain ⟨s, hs_full, hs_lt, hsneg⟩ :=
        exists_left_neg_of_continuousOn (a := t0) (b := t1)
          (c := t0 + delta) ht1_gt hp1_time.2
          (by simpa [B, Sraw] using hfixed_cont x v)
          hneg_t1
      obtain ⟨q, hq_time, hqneg⟩ :=
        negBarrier_unitSlab (I := I) (M := M) G S epsilon delta t0
          t0 (t0 + delta) s hs_full x v (by simpa [B, Sraw] using hsneg)
      have hqZ : q ∈ Z := by
        simpa [Z, φ] using le_of_lt hqneg
      have hmin_q := hmin hqZ
      have hqtime : q.1.1 = s := hq_time
      have ht1_le_s : t1 ≤ s := by
        have ht1_le_q : (p1.1.1 : Real) ≤ q.1.1 := by
          exact (Subtype.coe_le_coe).2 hmin_q
        simpa [t1, hqtime] using ht1_le_q
      linarith
  have hnonneg_p1 : 0 ≤ φ p1 := by
    have hquad :=
      hnonneg_until t1 ⟨le_of_lt ht1_gt, le_rfl⟩ x1 v1
    simpa [φ, barrierUnitQuad, B, Sraw, t1, x1, v1] using hquad
  have hnullφ : φ p1 = 0 := le_antisymm hp1_nonpos hnonneg_p1
  refine Nonempty.intro
    { t1 := t1
      x1 := x1
      v := v1
      t1_mem := ⟨ht1_gt, hp1_time.2⟩
      v_ne_zero := hv1_ne
      unit := by
        exact MetricUnitTangent.unit (I := I) (M := M) p1.2
      nonnegative_until := ?_
      null := ?_ }
  · intro t ht x
    simpa [B, Sraw] using hnonneg_until t ht x
  · simpa [φ, barrierUnitQuad, B, Sraw, t1, x1, v1] using hnullφ

end TensorFirstNullCompactnessOn

namespace TensorFirstNullCompactnessOn

/-- Section-backed first-null compactness using the geometric time-slab
subtype of `{t // t ∈ K} × TangentBundle`, rather than the dependent sigma
slab with coproduct topology. -/
theorem of_section_timeSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real)
    (hcompact :
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
            (Set.Icc t0 (t0 + delta)))))
    (hunit_cont :
      Continuous
        (barrierTimeSlabQuad (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0 (Set.Icc t0 (t0 + delta))))
    (hfixed_cont :
      ∀ x (v : TangentSpace I x),
        ContinuousOn
          (fun t : Real =>
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 t x v v)
          (Set.Icc t0 (t0 + delta))) :
    TensorFirstNullCompactnessOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0 := by
  classical
  let Sraw : TwoTensorFamily (I := I) (M := M) :=
    twoTensorSecToFamily (I := I) (M := M) S
  let B : TwoTensorFamily (I := I) (M := M) :=
    tensorBarrierFamily (I := I) (M := M) G Sraw epsilon delta t0
  let slab := MetricUnitTangentTimeSlab (I := I) (M := M) G
    (Set.Icc t0 (t0 + delta))
  let φ : slab -> Real :=
    barrierTimeSlabQuad (I := I) (M := M) G Sraw epsilon delta t0
      (Set.Icc t0 (t0 + delta))
  let Z : Set slab := {p | φ p ≤ 0}
  refine ⟨?_⟩
  intro hinit_pos hfail
  have hZclosed : IsClosed Z := by
    have hclosed : IsClosed ((Set.Iic (0 : Real)) : Set Real) := isClosed_Iic
    simpa [Z, φ] using hclosed.preimage hunit_cont
  have hZcompact : IsCompact Z := by
    simpa [Z] using hcompact.inter_right hZclosed
  obtain ⟨pbad, hpbad_neg⟩ :=
    failure_timeSlab (I := I) (M := M) G S epsilon delta t0
      (K := Set.Icc t0 (t0 + delta)) hfail
  have hZne : Z.Nonempty := ⟨pbad, le_of_lt hpbad_neg⟩
  obtain ⟨p1, hp1Z, hmin⟩ :=
    hZcompact.exists_isMinOn hZne
      (metricUnitTimeSlab_timeVal_cont (I := I) (M := M)
        G (Set.Icc t0 (t0 + delta))).continuousOn
  let t1 : Real := MetricUnitTangentTimeSlab.time (I := I) (M := M) p1
  let x1 : M := MetricUnitTangentTimeSlab.base (I := I) (M := M) p1
  let v1 : TangentSpace I x1 :=
    MetricUnitTangentTimeSlab.vec (I := I) (M := M) p1
  have hp1_time : t1 ∈ Set.Icc t0 (t0 + delta) := by
    simpa [t1] using
      (MetricUnitTangentTimeSlab.time_mem (I := I) (M := M) p1)
  have hp1_nonpos : φ p1 ≤ 0 := hp1Z
  have hv1_ne : v1 ≠ 0 := by
    intro hv
    have hbad : (0 : Real) = 1 := by
      simpa [v1, hv] using
        (MetricUnitTangentTimeSlab.unit (I := I) (M := M) p1)
    norm_num at hbad
  have ht1_ne_t0 : t1 ≠ t0 := by
    intro ht1eq
    have hpos : 0 < φ p1 := by
      have hpos_raw := hinit_pos x1 v1 hv1_ne
      simpa [φ, barrierTimeSlabQuad, Sraw, B, t1, x1, v1, ht1eq] using hpos_raw
    linarith
  have ht1_gt : t0 < t1 := lt_of_le_of_ne hp1_time.1 (Ne.symm ht1_ne_t0)
  have hnonneg_until :
      ∀ t, t ∈ Set.Icc t0 t1 ->
        ∀ x, TwoTensorNonnegativeAt (I := I) (M := M) (B t) x := by
    intro t ht x v
    by_contra hnot
    have hneg : B t x v v < 0 := lt_of_not_ge hnot
    have ht_full : t ∈ Set.Icc t0 (t0 + delta) :=
      ⟨ht.1, le_trans ht.2 hp1_time.2⟩
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · obtain ⟨q, hq_time, hqneg⟩ :=
        negBarrier_timeSlab (I := I) (M := M) G S epsilon delta t0 t
          (K := Set.Icc t0 (t0 + delta)) ht_full x v
          (by simpa [B, Sraw] using hneg)
      have hqZ : q ∈ Z := by
        simpa [Z, φ] using le_of_lt hqneg
      have hmin_q := hmin hqZ
      have ht1_le_t : t1 ≤ t := by
        simpa [t1, hq_time] using hmin_q
      linarith
    · have hneg_t1 :
          B t1 x v v < 0 := by
        simpa [heq] using hneg
      obtain ⟨s, hs_full, hs_lt, hsneg⟩ :=
        exists_left_neg_of_continuousOn (a := t0) (b := t1)
          (c := t0 + delta) ht1_gt hp1_time.2
          (by simpa [B, Sraw] using hfixed_cont x v)
          hneg_t1
      obtain ⟨q, hq_time, hqneg⟩ :=
        negBarrier_timeSlab (I := I) (M := M) G S epsilon delta t0 s
          (K := Set.Icc t0 (t0 + delta)) hs_full x v
          (by simpa [B, Sraw] using hsneg)
      have hqZ : q ∈ Z := by
        simpa [Z, φ] using le_of_lt hqneg
      have hmin_q := hmin hqZ
      have ht1_le_s : t1 ≤ s := by
        simpa [t1, hq_time] using hmin_q
      linarith
  have hnonneg_p1 : 0 ≤ φ p1 := by
    have hquad :=
      hnonneg_until t1 ⟨le_of_lt ht1_gt, le_rfl⟩ x1 v1
    simpa [φ, barrierTimeSlabQuad, B, Sraw, t1, x1, v1] using hquad
  have hnullφ : φ p1 = 0 := le_antisymm hp1_nonpos hnonneg_p1
  refine Nonempty.intro
    { t1 := t1
      x1 := x1
      v := v1
      t1_mem := ⟨ht1_gt, hp1_time.2⟩
      v_ne_zero := hv1_ne
      unit := by
        exact MetricUnitTangentTimeSlab.unit (I := I) (M := M) p1
      nonnegative_until := ?_
      null := ?_ }
  · intro t ht x
    simpa [B, Sraw] using hnonneg_until t ht x
  · simpa [φ, barrierTimeSlabQuad, B, Sraw, t1, x1, v1] using hnullφ

end TensorFirstNullCompactnessOn

/--
The strict barrier supersolution inequality produced after adding
`epsilon * (delta + t - t0) * g`.

This is the named target for the estimate that absorbs metric variation and
the local Lipschitz error in `N`.
-/
def TensorBarrierStrictSupersolutionOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
    (nablaBarrier : TensorNabla1Family (I := I) (M := M))
    (epsilon delta t0 : Real) : Prop :=
  TensorParabolicStrictInequalityWithDriftOn (I := I) (M := M) G
    (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0) X N
    nabla2Barrier nablaBarrier
    (Set.Ioc t0 (t0 + delta))

theorem strictBarrier_of_est
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 T : Real}
    (hsub : Set.Ioc t0 (t0 + delta) ⊆ Set.Ioc 0 T)
    (hbase : TensorParabolicInequalityWithDriftOn (I := I) (M := M)
      G S X N nabla2S nablaS T)
    (hest : ∀ timeDerivS : TensorQuadraticFormFamily (I := I) (M := M),
      ∃ timeDerivBarrier : TensorQuadraticFormFamily (I := I) (M := M),
        TensorBarrierLocalEst (I := I) (M := M) G S X N
          nabla2S nablaS nabla2Barrier nablaBarrier epsilon delta t0
          (Set.Ioc t0 (t0 + delta)) timeDerivS timeDerivBarrier) :
    TensorBarrierStrictSupersolutionOn (I := I) (M := M) G S X N
      nabla2Barrier nablaBarrier epsilon delta t0 := by
  exact strictParabolic_of_est (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2S := nabla2S) (nablaS := nablaS)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    (epsilon := epsilon) (delta := delta) (t0 := t0) (T := T)
    (U := Set.Ioc t0 (t0 + delta)) hsub hbase hest

/--
Uniform strict barrier supersolution on a fixed short slab for small barriers.

The time slab is fixed before `epsilon` varies over `0 < epsilon ≤ 1`.  This is
the mathematically usable local estimate for the final `epsilon -> 0` argument.
-/
def TensorBarrierUniformStrictOnSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (delta t0 : Real) : Prop :=
  ∀ epsilon : Real, SmallBarrierEps epsilon ->
    ∃ nabla2Barrier : TensorNabla2Family (I := I) (M := M),
    ∃ nablaBarrier : TensorNabla1Family (I := I) (M := M),
      TensorBarrierStrictSupersolutionOn (I := I) (M := M) G S X N
        nabla2Barrier nablaBarrier epsilon delta t0

/--
Scalar signs obtained by testing the tensor barrier on a locally parallel
extension of the first-null vector.

This is an existential `Prop`, rather than a `Prop` structure with `Real`
fields, because Lean does not generate projections for data fields in
proof-irrelevant structures.
-/
def TensorFirstNullScalarSigns
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (epsilon delta t0 : Real)
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0) : Prop :=
  ∃ timeDeriv laplacian drift reaction : Real,
    timeDeriv ≤ 0 ∧
    0 ≤ laplacian ∧
    drift = 0 ∧
    0 ≤ reaction ∧
    drift + reaction < timeDeriv - laplacian

/-- A strict barrier witness together with the first-null scalar signs proved
for the same first and second spatial derivative witnesses. -/
structure TensorStrictCert
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (epsilon delta t0 : Real) : Type _ where
  nabla2Barrier : TensorNabla2Family (I := I) (M := M)
  nablaBarrier : TensorNabla1Family (I := I) (M := M)
  strict :
    TensorBarrierStrictSupersolutionOn (I := I) (M := M) G S X N
      nabla2Barrier nablaBarrier epsilon delta t0
  signs :
    TensorNullEigenvectorCondition (I := I) (M := M) G N
      (Set.Icc t0 (t0 + delta)) ->
    ∀ d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0,
      TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d

/-- Uniform strict barrier certificates on a fixed short slab. -/
def TensorStrictCertSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (delta t0 : Real) : Prop :=
  ∀ epsilon : Real, SmallBarrierEps epsilon ->
    Nonempty (TensorStrictCert (I := I) (M := M) G S X N
      epsilon delta t0)

/--
Build the first-null scalar-sign package from the transparent local scalar
test-function inputs.

The remaining geometric work for future producers is exactly the hypotheses
here: the scalar test has nonpositive time derivative at the first null point,
nonnegative Laplacian, zero drift, and its heat-with-drift value agrees with
the tensor heat-with-drift quadratic evaluation.  The strict inequality and
reaction nonnegativity are then obtained from the already proved WMP inputs.
-/
theorem scalarSigns_of_eval
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (laplacian drift : Real)
    (htime_nonpos :
      ∀ timeDeriv : TensorQuadraticFormFamily (I := I) (M := M),
        (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
          ∀ x, ∀ v : TangentSpace I x,
            HasDerivWithinAt
              (fun s : Real =>
                tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
                  s x v v)
              (timeDeriv t x v) (Set.Ioc t0 (t0 + delta)) t) ->
        timeDeriv d.t1 d.x1 d.v ≤ 0)
    (hlaplacian_nonneg : 0 ≤ laplacian)
    (hdrift_zero : drift = 0)
    (hheat_eq :
      tensorHeatWithDrift2QuadMetricAt (I := I) (G d.t1) (X d.t1)
          (nabla2Barrier d.t1 d.x1) (nablaBarrier d.t1 d.x1) d.v =
        laplacian + drift) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  rcases hstrict with ⟨timeDeriv, hderiv, hstrict_eval⟩
  let reaction : Real :=
    N d.t1 (G d.t1)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
      d.x1 d.v d.v
  have ht1_mem_slab : d.t1 ∈ Set.Icc t0 (t0 + delta) :=
    ⟨le_of_lt d.t1_mem.1, d.t1_mem.2⟩
  have ht1_mem_until : d.t1 ∈ Set.Icc t0 d.t1 :=
    ⟨le_of_lt d.t1_mem.1, le_rfl⟩
  have hbarrier_nonnegative :
      TwoTensorNonnegativeAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
        d.x1 :=
    d.nonnegative_until d.t1 ht1_mem_until d.x1
  have hreaction_nonneg : 0 ≤ reaction := by
    simpa [reaction] using
      hnull d.t1 ht1_mem_slab
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
        d.x1 hbarrier_nonnegative d.v d.null
  have hstrict_at :
      tensorHeatWithDrift2QuadMetricAt (I := I) (G d.t1) (X d.t1)
          (nabla2Barrier d.t1 d.x1) (nablaBarrier d.t1 d.x1) d.v +
        reaction <
        timeDeriv d.t1 d.x1 d.v := by
    simpa [reaction] using
      hstrict_eval d.t1 d.t1_mem d.x1 d.v d.v_ne_zero
  refine ⟨timeDeriv d.t1 d.x1 d.v, laplacian, drift, reaction,
    htime_nonpos timeDeriv hderiv, hlaplacian_nonneg, hdrift_zero,
    hreaction_nonneg, ?_⟩
  linarith

/--
Version of `scalarSigns_of_eval` for separately identified Laplacian and
drift terms.  This is the form expected from the corrected local test-section
calculation: prove the rough-Laplacian trace identity and the drift
cancellation separately, then assemble the tensor heat-with-drift value.
-/
theorem scalarSigns_of_parts
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (laplacian drift : Real)
    (htime_nonpos :
      ∀ timeDeriv : TensorQuadraticFormFamily (I := I) (M := M),
        (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
          ∀ x, ∀ v : TangentSpace I x,
            HasDerivWithinAt
              (fun s : Real =>
                tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
                  s x v v)
              (timeDeriv t x v) (Set.Ioc t0 (t0 + delta)) t) ->
        timeDeriv d.t1 d.x1 d.v ≤ 0)
    (hlaplacian_nonneg : 0 ≤ laplacian)
    (hdrift_zero : drift = 0)
    (hlap :
      metricTraceFirstTwo0SAt (I := I) (G d.t1)
        (nabla2Barrier d.t1 d.x1) (vec2 d.v d.v) = laplacian)
    (hdrift :
      (nablaBarrier d.t1 d.x1)
        (Fin.cons (X d.t1 d.x1) (vec2 d.v d.v)) = drift) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  exact scalarSigns_of_eval (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    hstrict hnull d laplacian drift htime_nonpos hlaplacian_nonneg
    hdrift_zero
    (heatQuad_eq_parts (I := I) (G d.t1) (X d.t1)
      (nabla2Barrier d.t1 d.x1) (nablaBarrier d.t1 d.x1) d.v
      laplacian drift hlap hdrift)

/--
Zero-drift specialization of `scalarSigns_of_parts`.  This is the expected
shape at a first-null point after extending the null vector locally with
vanishing covariant derivative and using that the scalar test function has zero
spatial derivative.
-/
theorem scalarSigns_of_lap
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (laplacian : Real)
    (htime_nonpos :
      ∀ timeDeriv : TensorQuadraticFormFamily (I := I) (M := M),
        (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
          ∀ x, ∀ v : TangentSpace I x,
            HasDerivWithinAt
              (fun s : Real =>
                tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
                  s x v v)
              (timeDeriv t x v) (Set.Ioc t0 (t0 + delta)) t) ->
        timeDeriv d.t1 d.x1 d.v ≤ 0)
    (hlaplacian_nonneg : 0 ≤ laplacian)
    (hlap :
      metricTraceFirstTwo0SAt (I := I) (G d.t1)
        (nabla2Barrier d.t1 d.x1) (vec2 d.v d.v) = laplacian)
    (hdrift :
      (nablaBarrier d.t1 d.x1)
        (Fin.cons (X d.t1 d.x1) (vec2 d.v d.v)) = 0) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  exact scalarSigns_of_parts (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    hstrict hnull d laplacian 0 htime_nonpos hlaplacian_nonneg rfl hlap hdrift

/--
First-null specialization of `scalarSigns_of_lap`.  The nonpositive time
derivative is supplied directly by `TensorFirstNullData`, so future local
test-section producers only have to prove the spatial Laplacian and drift
facts.
-/
theorem scalarSigns_of_lap_firstNull
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (laplacian : Real)
    (hlaplacian_nonneg : 0 ≤ laplacian)
    (hlap :
      metricTraceFirstTwo0SAt (I := I) (G d.t1)
        (nabla2Barrier d.t1 d.x1) (vec2 d.v d.v) = laplacian)
    (hdrift :
      (nablaBarrier d.t1 d.x1)
        (Fin.cons (X d.t1 d.x1) (vec2 d.v d.v)) = 0) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  exact scalarSigns_of_lap (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    hstrict hnull d laplacian
    (fun timeDeriv hderiv => firstNullTime_nonpos (I := I) (M := M)
      d timeDeriv hderiv)
    hlaplacian_nonneg hlap hdrift

/--
First-null scalar signs from a local smooth test section.  The drift
cancellation is supplied by the first-derivative tensor product rule
`nablaEval_zero`; callers still provide the spatial Laplacian comparison.
-/
theorem scalarSigns_of_local
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (laplacian : Real)
    (hlaplacian_nonneg : 0 ≤ laplacian)
    (hlap :
      metricTraceFirstTwo0SAt (I := I) (G d.t1)
        (nabla2Barrier d.t1 d.x1) (vec2 d.v d.v) = laplacian)
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (Xsec :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hX : X d.t1 d.x1 = Xsec d.x1)
    (hnabla : nablaBarrier d.t1 d.x1 = nablaB d.x1)
    (hV : ∀ q : Fin 2, V q d.x1 = d.v)
    (hphi :
      extDerivFun (I := I) (fun p : M => B p (fun q : Fin 2 => V q p))
        d.x1 (Xsec d.x1) = 0)
    (hcovV :
      ∀ q : Fin 2, ((cov (fun p : M => V q p) d.x1) (Xsec d.x1)) = 0) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  apply scalarSigns_of_lap_firstNull (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    hstrict hnull d laplacian hlaplacian_nonneg hlap
  rw [hnabla, hX]
  exact nablaEval_zero (I := I) (M := M) hreal Xsec V hV hphi hcovV

/--
First-null scalar signs from a local test section and the scalar
minimum-principle Laplacian producer.  This closes the Laplacian sign part of
the first-null scalarization; callers still supply the bridge identifying the
tensor rough-Laplacian trace with the scalar Laplacian of `phi = B(V,V)`.
-/
theorem scalarSigns_of_local_min
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (Xsec :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hlapMin : LaplacianNonnegativeAtSpatialMin (I := I) cov (G d.t1))
    (hlap :
      metricTraceFirstTwo0SAt (I := I) (G d.t1)
        (nabla2Barrier d.t1 d.x1) (vec2 d.v d.v) =
      laplacian (I := I) cov (G d.t1)
        (fun p : M => B p (fun q : Fin 2 => V q p)) d.x1)
    (hX : X d.t1 d.x1 = Xsec d.x1)
    (hnabla : nablaBarrier d.t1 d.x1 = nablaB d.x1)
    (hV : ∀ q : Fin 2, V q d.x1 = d.v)
    (hB :
      ∀ p : M,
        B p (fun q : Fin 2 => V q p) =
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
            d.t1 p (V 0 p) (V 0 p))
    (hcovV :
      ∀ q : Fin 2, ((cov (fun p : M => V q p) d.x1) (Xsec d.x1)) = 0)
    (hmdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => B p (fun q : Fin 2 => V q p)) d.x1)
    (hmdiff_near :
      ∀ᶠ y in nhds d.x1,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => B p (fun q : Fin 2 => V q p)) y)
    (hgrad :
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G d.t1)
          (fun p : M => B p (fun q : Fin 2 => V q p)) y) d.x1) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  let phi : M -> Real := fun p => B p (fun q : Fin 2 => V q p)
  have hmin : IsLocalMin phi d.x1 :=
    firstNullLocalMin (I := I) (M := M) d V hV hB
  have hphi :
      extDerivFun (I := I) phi d.x1 (Xsec d.x1) = 0 := by
    have hmf :
        mfderiv I 𝓘(Real, Real) phi d.x1 = 0 :=
      mfderiv_eq_zero_at_spatial_min (I := I) hmin hmdiff
    rw [RicciFlower.extDerivFun_real_eq_mfderiv, hmf]
    rfl
  have hlap_nonneg :
      0 ≤ laplacian (I := I) cov (G d.t1) phi d.x1 :=
    hlapMin hmin hmdiff hmdiff_near hgrad
  exact scalarSigns_of_local (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    (cov := cov) (B := B) (nablaB := nablaB)
    hstrict hnull d (laplacian (I := I) cov (G d.t1) phi d.x1)
    hlap_nonneg hlap hreal Xsec V hX hnabla hV hphi hcovV

/-- Single-section version of `scalarSigns_of_local_min`.

This is the shape needed by the geometric first-null proof: one local test
section is evaluated in both tensor slots. -/
theorem scalarSigns_oneSec
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (Xsec Vsec :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hlapMin : LaplacianNonnegativeAtSpatialMin (I := I) cov (G d.t1))
    (hessPhi :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 d.x1)
    (hlap :
      ScalarLaplacianRealizesTraceAt (I := I) cov (G d.t1)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) hessPhi)
    (hslots :
      ∀ U W : TangentSpace I d.x1,
        (nabla2Barrier d.t1 d.x1)
          (metricTraceInput (I := I) U W (vec2 (I := I) d.v d.v)) =
        hessPhi (vec2 (I := I) U W))
    (hX : X d.t1 d.x1 = Xsec d.x1)
    (hnabla : nablaBarrier d.t1 d.x1 = nablaB d.x1)
    (hV : Vsec d.x1 = d.v)
    (hB :
      ∀ p : M,
        B p (vec2 (I := I) (Vsec p) (Vsec p)) =
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
            d.t1 p (Vsec p) (Vsec p))
    (hcovV : ((cov (fun p : M => Vsec p) d.x1) (Xsec d.x1)) = 0)
    (hmdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) d.x1)
    (hmdiff_near :
      ∀ᶠ y in nhds d.x1,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) y)
    (hgrad :
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G d.t1)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) y) d.x1) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  let V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun _ => Vsec
  have hV' : ∀ q : Fin 2, V q d.x1 = d.v := by
    intro q
    exact hV
  have hB' :
      ∀ p : M,
        B p (fun q : Fin 2 => V q p) =
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
            d.t1 p (V 0 p) (V 0 p) := by
    intro p
    simpa [V, vec2_self_eq_const] using hB p
  have hcovV' :
      ∀ q : Fin 2, ((cov (fun p : M => V q p) d.x1) (Xsec d.x1)) = 0 := by
    intro q
    simpa [V] using hcovV
  have hlap' :
      metricTraceFirstTwo0SAt (I := I) (G d.t1)
        (nabla2Barrier d.t1 d.x1) (vec2 d.v d.v) =
      laplacian (I := I) cov (G d.t1)
        (fun p : M => B p (fun q : Fin 2 => V q p)) d.x1 := by
    have hraw :
        metricTraceFirstTwo0SAt (I := I) (G d.t1)
          (nabla2Barrier d.t1 d.x1) (vec2 d.v d.v) =
        laplacian (I := I) cov (G d.t1)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) d.x1 := by
      exact lapTrace_of_slots (I := I) cov (G d.t1)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p)))
        (nabla2Barrier d.t1 d.x1) (vec2 (I := I) d.v d.v)
        hessPhi hlap hslots
    simpa [V, vec2_self_eq_const] using hraw
  have hmdiff' :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => B p (fun q : Fin 2 => V q p)) d.x1 := by
    simpa [V, vec2_self_eq_const] using hmdiff
  have hmdiff_near' :
      ∀ᶠ y in nhds d.x1,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => B p (fun q : Fin 2 => V q p)) y := by
    simpa [V, vec2_self_eq_const] using hmdiff_near
  have hgrad' :
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G d.t1)
          (fun p : M => B p (fun q : Fin 2 => V q p)) y) d.x1 := by
    simpa [V, vec2_self_eq_const] using hgrad
  exact scalarSigns_of_local_min (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    (cov := cov) (B := B) (nablaB := nablaB)
    hstrict hnull d hreal Xsec V hlapMin hlap' hX hnabla hV' hB' hcovV'
    hmdiff' hmdiff_near' hgrad'

/-- One-section scalar signs using a realized scalar Hessian for
`phi = B(V,V)`.

This is the real bridge that discharges the raw `hslots` input of
`scalarSigns_oneSec` from the checked second-derivative product rule. -/
theorem scalarSigns_hess
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    {du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1}
    {Hess : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (hreal1 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (hreal2 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (Xsec Vsec :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hlapMin : LaplacianNonnegativeAtSpatialMin (I := I) cov (G d.t1))
    (hnabla2 : nabla2Barrier d.t1 d.x1 = nabla2B d.x1)
    (hkerL : ∀ w : TangentSpace I d.x1, B d.x1 (vec2 (I := I) d.v w) = 0)
    (hkerR : ∀ w : TangentSpace I d.x1, B d.x1 (vec2 (I := I) w d.v) = 0)
    (hdu :
      DuFieldRealizes (I := I)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) du)
    (hHess :
      HessianRealizesNablaDuAt (I := I) cov du Hess d.x1)
    (hlap :
      ScalarLaplacianRealizesTraceAt (I := I) cov (G d.t1)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) (Hess d.x1))
    (hAreg :
      ∀ Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _),
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, ((cov (fun q : M => Vsec q) p) (Y p))⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) d.x1)
    (hX : X d.t1 d.x1 = Xsec d.x1)
    (hnabla : nablaBarrier d.t1 d.x1 = nablaB d.x1)
    (hV : Vsec d.x1 = d.v)
    (hB :
      ∀ p : M,
        B p (vec2 (I := I) (Vsec p) (Vsec p)) =
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
            d.t1 p (Vsec p) (Vsec p))
    (hcovV :
      ∀ W : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _),
        ((cov (fun p : M => Vsec p) d.x1) (W d.x1)) = 0)
    (hmdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) d.x1)
    (hmdiff_near :
      ∀ᶠ y in nhds d.x1,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) y)
    (hgrad :
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G d.t1)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) y) d.x1) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  have hslots :
      ∀ U W : TangentSpace I d.x1,
        (nabla2Barrier d.t1 d.x1)
          (metricTraceInput (I := I) U W (vec2 (I := I) d.v d.v)) =
        (Hess d.x1) (vec2 (I := I) U W) := by
    intro U W
    rw [hnabla2]
    exact nabla2Eval_hess_slots (I := I) (M := M)
      hreal1 hreal2 Vsec hV hcovV hkerL hkerR hdu hHess hAreg U W
  exact scalarSigns_oneSec (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    (cov := cov) (B := B) (nablaB := nablaB)
    hstrict hnull d hreal1 Xsec Vsec hlapMin (Hess d.x1) hlap hslots
    hX hnabla hV hB (hcovV Xsec) hmdiff hmdiff_near hgrad

/-- One-jet scalar signs with canonical scalar `du`, Hessian, and Laplacian
trace producers.

This section-backed producer removes the explicit `du`/Hessian/Laplacian
realization inputs from `scalarSigns_hess`.  The correction field
`p ↦ (cov V p) (Y p)` is produced as a local `C1` slot from connection
regularity; scalar gradient regularity is derived from smoothness of
`phi = B(V,V)`. -/
theorem scalarSigns_covHess
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    {nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (hcovInf : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G (twoTensorSecToFamily (I := I) (M := M) S) X N
      nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S)
        (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov (G d.t1))
    (hreal1 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (hreal2 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 cov nablaB nabla2B)
    (Xsec :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hlapMin : LaplacianNonnegativeAtSpatialMin (I := I) cov (G d.t1))
    (hnabla2 : nabla2Barrier d.t1 d.x1 = nabla2B d.x1)
    (hkerB_left :
      ∀ w : TangentSpace I d.x1,
        B d.x1 (vec2 (I := I) d.v w) =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 d.v w)
    (hkerB_right :
      ∀ w : TangentSpace I d.x1,
        B d.x1 (vec2 (I := I) w d.v) =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 w d.v)
    (hX : X d.t1 d.x1 = Xsec d.x1)
    (hnabla : nablaBarrier d.t1 d.x1 = nablaB d.x1)
    (hB :
      ∀ Vsec :
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        Vsec d.x1 = d.v ->
        ∀ p : M,
          B p (vec2 (I := I) (Vsec p) (Vsec p)) =
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 d.t1 p (Vsec p) (Vsec p)) :
    TensorFirstNullScalarSigns (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N epsilon delta t0 d := by
  obtain ⟨Vsec, hV, hcovVall⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov1 d.x1 d.v
  let phi : M -> Real := fun p => B p (vec2 (I := I) (Vsec p) (Vsec p))
  have hphi :
      ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) phi := by
    let Slots : Fin 2 ->
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      fun _ => Vsec
    have hraw :=
      TensorMultilinear.contMDiff_tensor0SField_apply (I := I) (M := M) B Slots
    simpa [phi, Slots, vec2_self_eq_const] using hraw
  let du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
    duSec (I := I) phi hphi
  let Hess : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y :=
    fun y => hessianSec (I := I) cov hcovInf phi hphi y
  have hdu : DuFieldRealizes (I := I) phi du := by
    simpa [du] using duSec_realizes (I := I) phi hphi
  have hHess : HessianRealizesNablaDuAt (I := I) cov du Hess d.x1 := by
    simpa [du, Hess] using
      hessianSec_realizesAt (I := I) cov hcovInf phi hphi d.x1
  have hlap :
      ScalarLaplacianRealizesTraceAt (I := I) cov (G d.t1) phi (Hess d.x1) := by
    simpa [Hess] using
      scalarLap_smooth (I := I) cov hcovInf (G d.t1) hmc phi hphi
  have hkerL : ∀ w : TangentSpace I d.x1,
      B d.x1 (vec2 (I := I) d.v w) = 0 :=
    firstNullFieldKerL (I := I) (M := M) hsym d hkerB_left
  have hkerR : ∀ w : TangentSpace I d.x1,
      B d.x1 (vec2 (I := I) w d.v) = 0 :=
    firstNullFieldKerR (I := I) (M := M) hsym d hkerB_right
  have hmdiff :
      MDifferentiableAt I 𝓘(Real, Real) phi d.x1 :=
    hphi.contMDiffAt.mdifferentiableAt (by simp)
  have hmdiff_near :
      ∀ᶠ y in nhds d.x1, MDifferentiableAt I 𝓘(Real, Real) phi y := by
    refine Filter.Eventually.of_forall ?_
    intro y
    exact hphi.contMDiffAt.mdifferentiableAt (by simp)
  have hgrad :
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G d.t1) phi y) d.x1 :=
    gradientFun_mdiffAt (I := I) (G d.t1) hphi d.x1
  have hAreg :
      ∀ Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _),
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, ((cov (fun q : M => Vsec q) p) (Y p))⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) d.x1 := by
    intro Y
    simpa using
      CovariantDerivative.smoothSections_cov_contMDiffAt_one
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        cov hcov1 Y Vsec d.x1
  exact scalarSigns_hess (I := I) (M := M)
    (G := G) (S := twoTensorSecToFamily (I := I) (M := M) S)
    (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    (cov := cov) (B := B) (nablaB := nablaB) (nabla2B := nabla2B)
    (du := du) (Hess := Hess)
    hstrict hnull d hreal1 hreal2 Xsec Vsec hlapMin hnabla2
    hkerL hkerR hdu hHess hlap hAreg
    hX hnabla hV (hB Vsec hV) hcovVall hmdiff hmdiff_near
    (by simpa [phi] using hgrad)

/-- Section-backed version of `scalarSigns_covHess`.

This instantiates the frozen barrier tensor and its first two spatial
covariant derivatives from `barrierDerivs`; no separate `B`, `∇B`, or `∇²B`
producer is exposed. -/
theorem scalarSigns_secHess
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nablaS : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2S : TensorNabla2SecFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    {cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G (twoTensorSecToFamily (I := I) (M := M) S) X N
      (fun t x => nabla2S t x) (fun t x => nablaS t x)
      epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S)
        (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0)
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (cov d.t1) (1 : WithTop ℕ∞))
    (hcovInf : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (cov d.t1) (∞ : WithTop ℕ∞))
    (hmc : ∀ t : Real,
      RicciFlower.Connection.IsMetricCompatible (I := I) (cov t) (G t))
    (hS : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S)
    (Xsec :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hlapMin : LaplacianNonnegativeAtSpatialMin (I := I) (cov d.t1) (G d.t1))
    (hX : X d.t1 d.x1 = Xsec d.x1) :
    TensorFirstNullScalarSigns (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N epsilon delta t0 d := by
  let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0) d.t1
  have hbarDerivs :
      TensorSpatialDerivs (I := I) (M := M) cov
        (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0)
        nablaS nabla2S :=
    barrierDerivs (I := I) (M := M) cov G S nablaS nabla2S
      epsilon delta t0 hmc hS
  have hkerB_left :
      ∀ w : TangentSpace I d.x1,
        B d.x1 (vec2 (I := I) d.v w) =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 d.v w := by
    intro w
    simpa [B] using
      tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
        d.t1 d.x1 d.v w
  have hkerB_right :
      ∀ w : TangentSpace I d.x1,
        B d.x1 (vec2 (I := I) w d.v) =
          tensorBarrierFamily (I := I) (M := M) G
            (twoTensorSecToFamily (I := I) (M := M) S)
            epsilon delta t0 d.t1 d.x1 w d.v := by
    intro w
    simpa [B] using
      tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
        d.t1 d.x1 w d.v
  have hB :
      ∀ Vsec :
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        Vsec d.x1 = d.v ->
        ∀ p : M,
          B p (vec2 (I := I) (Vsec p) (Vsec p)) =
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 d.t1 p (Vsec p) (Vsec p) := by
    intro Vsec _hV p
    simpa [B] using
      tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0
        d.t1 p (Vsec p) (Vsec p)
  exact scalarSigns_covHess (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := fun t x => nabla2S t x)
    (nablaBarrier := fun t x => nablaS t x)
    (cov := cov d.t1) (B := B) (nablaB := nablaS d.t1)
    (nabla2B := nabla2S d.t1)
    hcov1 hcovInf hstrict hnull hsym d (hmc d.t1)
    (hbarDerivs.first d.t1) (hbarDerivs.second d.t1) Xsec hlapMin
    rfl hkerB_left hkerB_right hX rfl hB

/--
First-null scalar signs with the local zero-covariant-derivative test section
constructed internally.

This is the `OneJet` consumer: callers no longer supply the local test section
or the proof `∇V = 0` at the first-null point.  The remaining hypotheses are
the genuine scalar-test-function producers for the section selected by the
one-jet theorem: the Laplacian bridge, the equality with the barrier scalar
test, and the differentiability/gradient inputs used by
`LaplacianNonnegativeAtSpatialMin`.
-/
theorem scalarSigns_covZero
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2}
    {nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
      G N (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (hreal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B nablaB)
    (Xsec :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hlapMin : LaplacianNonnegativeAtSpatialMin (I := I) cov (G d.t1))
    (hX : X d.t1 d.x1 = Xsec d.x1)
    (hnabla : nablaBarrier d.t1 d.x1 = nablaB d.x1)
    (hessPhi :
      ∀ Vsec :
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        Vsec d.x1 = d.v ->
        Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 d.x1)
    (hlap :
      ∀ (Vsec :
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
        (hV : Vsec d.x1 = d.v),
        ScalarLaplacianRealizesTraceAt (I := I) cov (G d.t1)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p)))
          (hessPhi Vsec hV))
    (hslots :
      ∀ Vsec :
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        ∀ hV : Vsec d.x1 = d.v,
          ∀ U W : TangentSpace I d.x1,
            (nabla2Barrier d.t1 d.x1)
              (metricTraceInput (I := I) U W (vec2 (I := I) d.v d.v)) =
            (hessPhi Vsec hV) (vec2 (I := I) U W))
    (hB :
      ∀ Vsec :
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        Vsec d.x1 = d.v ->
        ∀ p : M,
          B p (vec2 (I := I) (Vsec p) (Vsec p)) =
            tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
              d.t1 p (Vsec p) (Vsec p))
    (hmdiff :
      ∀ Vsec :
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        Vsec d.x1 = d.v ->
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) d.x1)
    (hmdiff_near :
      ∀ Vsec :
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        Vsec d.x1 = d.v ->
        ∀ᶠ y in nhds d.x1,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) y)
    (hgrad :
      ∀ Vsec :
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        Vsec d.x1 = d.v ->
        MDiffAt (T% fun y : M =>
          gradientFun (I := I) (G d.t1)
            (fun p : M => B p (vec2 (I := I) (Vsec p) (Vsec p))) y) d.x1) :
    TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d := by
  obtain ⟨Vsec, hV, hcovVall⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov d.x1 d.v
  exact scalarSigns_oneSec (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    (cov := cov) (B := B) (nablaB := nablaB)
    hstrict hnull d hreal Xsec Vsec hlapMin (hessPhi Vsec hV)
    (hlap Vsec hV) (hslots Vsec hV) hX hnabla hV (hB Vsec hV) (hcovVall Xsec)
    (hmdiff Vsec hV) (hmdiff_near Vsec hV) (hgrad Vsec hV)

/--
Uniform barrier nonnegativity on a fixed short slab for small barriers.

The time slab is fixed before `epsilon` varies over `0 < epsilon ≤ 1`; this is
the form needed for the local `epsilon -> 0` argument.
-/
def TensorBarrierUniformOnSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (delta t0 : Real) : Prop :=
  ∀ epsilon : Real, SmallBarrierEps epsilon ->
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0)
      (Set.Icc t0 (t0 + delta))

/--
On a fixed short slab, uniform nonnegativity of all small positive barriers
implies nonnegativity of the unperturbed tensor.
-/
theorem tensorBarrier_limit_on_fixed_slab
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {delta t0 : Real}
    (hdelta : 0 < delta)
    (hbarrier : TensorBarrierUniformOnSlab (I := I) (M := M) G S delta t0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) S
      (Set.Icc t0 (t0 + delta)) := by
  intro t ht x v
  let q : Real := S t x v v
  let c : Real := (delta + t - t0) * (G t).inner x v v
  have htime_nonneg : 0 ≤ delta + t - t0 := by
    have ht_sub : 0 ≤ t - t0 := sub_nonneg.mpr ht.1
    have hsum : 0 ≤ delta + (t - t0) :=
      add_nonneg (le_of_lt hdelta) ht_sub
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsum
  have hmetric_nonneg : 0 ≤ (G t).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact le_of_lt ((G t).pos x v hv)
  have hc_nonneg : 0 ≤ c := by
    simpa [c] using mul_nonneg htime_nonneg hmetric_nonneg
  have hforall : ∀ e : Real, 0 < e -> 0 ≤ q + e := by
    intro e he
    let eta : Real := min 1 (e / (c + 1))
    have hden_pos : 0 < c + 1 :=
      add_pos_of_nonneg_of_pos hc_nonneg zero_lt_one
    have hdiv_pos : 0 < e / (c + 1) :=
      div_pos he hden_pos
    have heta_pos : 0 < eta := by
      dsimp [eta]
      exact lt_min zero_lt_one hdiv_pos
    have heta_le_one : eta ≤ 1 := by
      dsimp [eta]
      exact min_le_left 1 (e / (c + 1))
    have heta_le_div : eta ≤ e / (c + 1) := by
      dsimp [eta]
      exact min_le_right 1 (e / (c + 1))
    have heta_small : SmallBarrierEps eta := ⟨heta_pos, heta_le_one⟩
    have hbar_eta :
        0 ≤
          tensorBarrierFamily (I := I) (M := M) G S eta delta t0 t x v v :=
      hbarrier eta heta_small t ht x v
    have hbar_q : 0 ≤ q + eta * c := by
      simpa [tensorBarrierFamily, q, c, mul_assoc] using hbar_eta
    have heta_nonneg : 0 ≤ eta := le_of_lt heta_pos
    have hcoeff_le : c ≤ c + 1 := le_add_of_nonneg_right zero_le_one
    have hprod_le : eta * c ≤ eta * (c + 1) :=
      mul_le_mul_of_nonneg_left hcoeff_le heta_nonneg
    have hden_ne : c + 1 ≠ 0 := ne_of_gt hden_pos
    have heta_mul_den_le : eta * (c + 1) ≤ e := by
      have hmul_le : eta * (c + 1) ≤ (e / (c + 1)) * (c + 1) :=
        mul_le_mul_of_nonneg_right heta_le_div (le_of_lt hden_pos)
      have hdiv_mul : (e / (c + 1)) * (c + 1) = e := by
        field_simp [hden_ne]
      simpa [hdiv_mul] using hmul_le
    have heta_c_le : eta * c ≤ e := by
      exact le_trans hprod_le heta_mul_den_le
    exact le_trans hbar_q (by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left heta_c_le q)
  have hq_nonneg : 0 ≤ q := le_of_forall_pos_le_add hforall
  simpa [q] using hq_nonneg

/--
Global finite-subinterval continuation for the tensor barrier.

The local input is already uniform in small `epsilon`; the fixed-slab epsilon
limit is therefore separated from the global reachability/closedness argument.
-/
def TensorBarrierLimitClosureOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (T : Real) : Prop :=
  TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S 0 ->
  (∀ t0 : Real, t0 ∈ Set.Icc 0 T -> t0 < T ->
    TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t0 ->
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      TensorBarrierUniformOnSlab (I := I) (M := M) G S delta t0) ->
  TwoTensorFamilyNonnegativeOn (I := I) (M := M) S (Set.Icc 0 T)

/-- The set of times where a tensor family is pointwise nonnegative is closed
on a compact time interval, provided every quadratic evaluation is continuous
there. -/
private theorem nonnegativeTime_isClosed
    {S : TwoTensorFamily (I := I) (M := M)}
    {T : Real}
    (hcont : ∀ x, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : Real => S t x v w) (Set.Icc 0 T)) :
    IsClosed ({t : Real | TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      S t} ∩ Set.Icc 0 T) := by
  rw [show
      {t : Real | TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t} ∩
          Set.Icc 0 T =
        Set.Icc 0 T ∩ ⋂ x : M, ⋂ v : TangentSpace I x,
          (Set.Icc 0 T ∩ (fun t : Real => S t x v v) ⁻¹' Set.Ici 0) by
    ext t
    constructor
    · intro ht
      refine ⟨ht.2, ?_⟩
      rw [Set.mem_iInter]
      intro x
      rw [Set.mem_iInter]
      intro v
      exact ⟨ht.2, ht.1 x v⟩
    · intro ht
      refine ⟨?_, ht.1⟩
      intro x v
      exact ((Set.mem_iInter.mp (Set.mem_iInter.mp ht.2 x) v)).2]
  exact isClosed_Icc.inter
    (isClosed_iInter fun x =>
      isClosed_iInter fun v =>
        (hcont x v v).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)

/-- Closed-interval continuation closes the global barrier-limit step once the
unperturbed tensor evaluations are continuous in time. -/
private theorem barrierLimitClosure_of_continuous
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {T : Real}
    (hT : 0 ≤ T)
    (hcont : ∀ x, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : Real => S t x v w) (Set.Icc 0 T)) :
    TensorBarrierLimitClosureOn (I := I) (M := M) G S T := by
  intro hinit hstep
  let P : Set Real := {t : Real | TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t}
  have hclosed : IsClosed (P ∩ Set.Icc 0 T) := by
    simpa [P] using nonnegativeTime_isClosed (I := I) (M := M) (S := S) hcont
  have hP : Set.Icc 0 T ⊆ P := by
    refine hclosed.Icc_subset_of_forall_exists_gt (a := 0) (b := T) ?_ ?_
    · simpa [P] using hinit
    · intro t ht y hy
      have htIcc : t ∈ Set.Icc 0 T := ⟨ht.2.1, le_of_lt ht.2.2⟩
      obtain ⟨delta, hdelta, _hdeltaT, hbarrier⟩ :=
        hstep t htIcc ht.2.2 ht.1
      have hslab : TwoTensorFamilyNonnegativeOn (I := I) (M := M) S
          (Set.Icc t (t + delta)) :=
        tensorBarrier_limit_on_fixed_slab (I := I) (M := M)
          (G := G) (S := S) hdelta hbarrier
      let z : Real := min y (t + delta)
      have htz : t < z := by
        dsimp [z]
        exact lt_min hy (by linarith)
      have hz_le_delta : z ≤ t + delta := by
        dsimp [z]
        exact min_le_right y (t + delta)
      have hz_le_y : z ≤ y := by
        dsimp [z]
        exact min_le_left y (t + delta)
      have hzP : P z :=
        hslab z ⟨le_of_lt htz, hz_le_delta⟩
      exact ⟨z, hzP, htz, hz_le_y⟩
  intro t ht
  exact hP ht

/-- Regularity package for the tensor WMP, without any strict-barrier witness. -/
structure TensorWMPCore
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  symmetric : TwoTensorFamilySymmetricOn (I := I) (M := M) S (Set.Icc 0 T)
  barrierRegularity :
    TensorBarrierRegularityOn (I := I) (M := M) G S X N T
  firstNullCompactness :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      TensorFirstNullCompactnessOn (I := I) (M := M) G S epsilon delta t0

/--
Compatibility regularity package needed by the original raw WMP theorem.

New producer routes should prefer `TensorWMPCore` plus a `TensorStrictCert`;
this package remains as the old interface whose scalar signs must work for an
arbitrary strict-barrier witness.
-/
structure TensorWMPRegularityOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  symmetric : TwoTensorFamilySymmetricOn (I := I) (M := M) S (Set.Icc 0 T)
  barrierRegularity :
    TensorBarrierRegularityOn (I := I) (M := M) G S X N T
  firstNullCompactness :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      TensorFirstNullCompactnessOn (I := I) (M := M) G S epsilon delta t0
  firstNullScalarSigns :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
        (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
      (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
        G S X N nabla2Barrier nablaBarrier epsilon delta t0) ->
      (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
        G N (Set.Icc t0 (t0 + delta))) ->
      (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0) ->
      TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d

namespace TensorWMPRegularityOn

/-- Forget the compatibility scalar-sign producer, retaining only regularity. -/
def toCore
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (h : TensorWMPRegularityOn (I := I) (M := M) G S X N T) :
    TensorWMPCore (I := I) (M := M) G S X N T where
  symmetric := h.symmetric
  barrierRegularity := h.barrierRegularity
  firstNullCompactness := h.firstNullCompactness

end TensorWMPRegularityOn

/--
Section-backed regularity package for Hamilton's tensor WMP, without scalar
signs.  The signs are produced later by strict-barrier certificates whose
derivative witnesses match the section covariant derivatives.
-/
structure TensorWMPSectionCore
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  symmetric :
    TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T)
  barrierRegularity :
    TensorBarrierRegularityOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N T
  unitSlabCompact :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
            (Set.Icc t0 (t0 + delta))))
  metricQuadCont :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      Continuous
        (metricBundleQuad (I := I) (M := M) G
          (Set.Icc t0 (t0 + delta)))
  tensorQuadCont :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      Continuous
        (tensorSecBundleQuad (I := I) (M := M) S
          (Set.Icc t0 (t0 + delta)))
  barrierFixedContinuous :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ x (v : TangentSpace I x),
        ContinuousOn
          (fun t : Real =>
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 t x v v)
          (Set.Icc t0 (t0 + delta))

/--
Compatibility section-backed regularity package for Hamilton's tensor WMP.

This is the public geometric entry point for smooth two-tensor sections.  It
replaces the raw `firstNullCompactness` field with the transparent inputs used
by `TensorFirstNullCompactnessOn.of_section`: compactness of the metric
unit-tangent geometric time slab, continuity of the metric and tensor
quadratic evaluations on the ambient time/tangent-bundle product, and
fixed-vector time continuity.  New producers should prefer
`TensorWMPSectionCore` plus `TensorStrictCert`.
-/
structure TensorWMPSectionReg
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  symmetric :
    TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T)
  barrierRegularity :
    TensorBarrierRegularityOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N T
  unitSlabCompact :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
            (Set.Icc t0 (t0 + delta))))
  metricQuadCont :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      Continuous
        (metricBundleQuad (I := I) (M := M) G
          (Set.Icc t0 (t0 + delta)))
  tensorQuadCont :
    ∀ delta t0 : Real,
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      Continuous
        (tensorSecBundleQuad (I := I) (M := M) S
          (Set.Icc t0 (t0 + delta)))
  barrierFixedContinuous :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ x (v : TangentSpace I x),
        ContinuousOn
          (fun t : Real =>
            tensorBarrierFamily (I := I) (M := M) G
              (twoTensorSecToFamily (I := I) (M := M) S)
              epsilon delta t0 t x v v)
          (Set.Icc t0 (t0 + delta))
  firstNullScalarSigns :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
        (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
      (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
        G (twoTensorSecToFamily (I := I) (M := M) S) X N
        nabla2Barrier nablaBarrier epsilon delta t0) ->
      (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
        G N (Set.Icc t0 (t0 + delta))) ->
      (d : TensorFirstNullData (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) ->
      TensorFirstNullScalarSigns (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N epsilon delta t0 d

namespace TensorWMPSectionCore

/-- Build the section-backed core regularity package from compact slab data. -/
theorem ofCompact
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hMetric :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (metricBundleQuad (I := I) (M := M) G
            (Set.Icc t0 (t0 + delta))))
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (tensorSecBundleQuad (I := I) (M := M) S
            (Set.Icc t0 (t0 + delta))))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) G
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta))) :
    TensorWMPSectionCore (I := I) (M := M) G S X N T where
  symmetric := hsym
  barrierRegularity := hbar
  unitSlabCompact := by
    intro delta t0 hdelta hsub
    exact metricUnitTimeSlab_icc_compact_of_bundle (I := I) (M := M)
      G t0 (t0 + delta) (G t0)
      (by
        simpa [metricBundleQuad] using hMetric delta t0 hdelta hsub)
  metricQuadCont := hMetric
  tensorQuadCont := hTensor
  barrierFixedContinuous := hFixed

/-- Build section-backed core regularity from total-space continuity. -/
theorem ofTotal
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hMetric :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (metricTensorField (I := I) (G q.1.1) q.2.proj)))
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (S q.1.1 q.2.proj)))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) G
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta))) :
    TensorWMPSectionCore (I := I) (M := M) G S X N T :=
  ofCompact (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N) (T := T)
    hsym hbar
    (fun delta t0 hdelta hsub =>
      RicciFlower.Realized.metricFamQuadCont (I := I) (M := M)
        G (Set.Icc t0 (t0 + delta))
        (hMetric delta t0 hdelta hsub))
    (fun delta t0 hdelta hsub =>
      RicciFlower.Realized.tensorQuadCont (I := I) (M := M)
        S (Set.Icc t0 (t0 + delta))
        (hTensor delta t0 hdelta hsub))
    hFixed

/-- Build the section-backed core package from a smooth realized metric family. -/
theorem ofSmoothMetric
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) (fun t => G.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (S q.1.1 q.2.proj)))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) (fun t => G.metric t)
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta))) :
    TensorWMPSectionCore (I := I) (M := M) (fun t => G.metric t) S X N T :=
  ofTotal (I := I) (M := M)
    (G := fun t => G.metric t) (S := S) (X := X) (N := N) (T := T)
    hsym hbar
    (fun delta t0 hdelta hsub =>
      metricTensor_tangentBundle_cont_of_metricFamilySmoothOn
        (I := I) (M := M) G hG
        (fun t ht => hTsub (hsub ht)))
    hTensor hFixed

/-- Convert section-backed core regularity to raw core regularity. -/
theorem toRaw
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (h : TensorWMPSectionCore (I := I) (M := M) G S X N T) :
    TensorWMPCore (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N T where
  symmetric := h.symmetric
  barrierRegularity := h.barrierRegularity
  firstNullCompactness := by
    intro epsilon delta t0 hepsilon hdelta hsub
    exact TensorFirstNullCompactnessOn.of_section_timeSlab (I := I) (M := M)
      G S epsilon delta t0
      (h.unitSlabCompact delta t0 hdelta hsub)
      (barrierTimeCont (I := I) (M := M) G S epsilon delta t0
        (Set.Icc t0 (t0 + delta))
        (h.tensorQuadCont delta t0 hdelta hsub)
        (h.metricQuadCont delta t0 hdelta hsub))
      (h.barrierFixedContinuous epsilon delta t0 hepsilon hdelta hsub)

end TensorWMPSectionCore

namespace TensorWMPSectionReg

/-- Forget the compatibility scalar-sign producer, retaining only core data. -/
def toCore
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (h : TensorWMPSectionReg (I := I) (M := M) G S X N T) :
    TensorWMPSectionCore (I := I) (M := M) G S X N T where
  symmetric := h.symmetric
  barrierRegularity := h.barrierRegularity
  unitSlabCompact := h.unitSlabCompact
  metricQuadCont := h.metricQuadCont
  tensorQuadCont := h.tensorQuadCont
  barrierFixedContinuous := h.barrierFixedContinuous

/-- Build the section-backed WMP regularity package using the geometric
closed-slab compactness theorem for the unit tangent time slab.  Callers supply
the transparent scalar quadratic continuities; compactness is no longer a
separate first-null input. -/
theorem ofCompact
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hMetric :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (metricBundleQuad (I := I) (M := M) G
            (Set.Icc t0 (t0 + delta))))
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (tensorSecBundleQuad (I := I) (M := M) S
            (Set.Icc t0 (t0 + delta))))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) G
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta)))
    (hSigns :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
          (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
        (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
          G (twoTensorSecToFamily (I := I) (M := M) S) X N
          nabla2Barrier nablaBarrier epsilon delta t0) ->
        (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
          G N (Set.Icc t0 (t0 + delta))) ->
        (d : TensorFirstNullData (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) ->
        TensorFirstNullScalarSigns (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S) X N epsilon delta t0 d) :
    TensorWMPSectionReg (I := I) (M := M) G S X N T where
  symmetric := hsym
  barrierRegularity := hbar
  unitSlabCompact := by
    intro delta t0 hdelta hsub
    exact metricUnitTimeSlab_icc_compact_of_bundle (I := I) (M := M)
      G t0 (t0 + delta) (G t0)
      (by
        simpa [metricBundleQuad] using hMetric delta t0 hdelta hsub)
  metricQuadCont := hMetric
  tensorQuadCont := hTensor
  barrierFixedContinuous := hFixed
  firstNullScalarSigns := hSigns

/-- Build the section-backed regularity package from total-space continuity of
the time-dependent metric and two-tensor sections over each compact test slab. -/
theorem ofTotal
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hMetric :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (metricTensorField (I := I) (G q.1.1) q.2.proj)))
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (S q.1.1 q.2.proj)))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) G
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta)))
    (hSigns :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
          (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
        (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
          G (twoTensorSecToFamily (I := I) (M := M) S) X N
          nabla2Barrier nablaBarrier epsilon delta t0) ->
        (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
          G N (Set.Icc t0 (t0 + delta))) ->
        (d : TensorFirstNullData (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) ->
        TensorFirstNullScalarSigns (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S) X N epsilon delta t0 d) :
    TensorWMPSectionReg (I := I) (M := M) G S X N T :=
  ofCompact (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N) (T := T)
    hsym hbar
    (fun delta t0 hdelta hsub =>
      RicciFlower.Realized.metricFamQuadCont (I := I) (M := M)
        G (Set.Icc t0 (t0 + delta))
        (hMetric delta t0 hdelta hsub))
    (fun delta t0 hdelta hsub =>
      RicciFlower.Realized.tensorQuadCont (I := I) (M := M)
        S (Set.Icc t0 (t0 + delta))
        (hTensor delta t0 hdelta hsub))
    hFixed hSigns

/-- Build the section-backed WMP regularity package from a smooth realized
metric family.  The strengthened `MetricFamilySmoothOn` supplies the metric
total-space continuity; callers still supply the tensor-family continuity. -/
theorem ofSmoothMetric
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T))
    (hbar :
      TensorBarrierRegularityOn (I := I) (M := M) (fun t => G.metric t)
        (twoTensorSecToFamily (I := I) (M := M) S) X N T)
    (hTensor :
      ∀ delta t0 : Real,
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        Continuous
          (fun q : {t : Real // t ∈ Set.Icc t0 (t0 + delta)} × TangentBundle I M =>
            TotalSpace.mk' (Tensor0SModel 2 Real E)
              (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
              (S q.1.1 q.2.proj)))
    (hFixed :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ x (v : TangentSpace I x),
          ContinuousOn
            (fun t : Real =>
              tensorBarrierFamily (I := I) (M := M) (fun t => G.metric t)
                (twoTensorSecToFamily (I := I) (M := M) S)
                epsilon delta t0 t x v v)
            (Set.Icc t0 (t0 + delta)))
    (hSigns :
      ∀ epsilon delta t0 : Real,
        0 < epsilon ->
        0 < delta ->
        Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
        ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
          (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
        (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
          (fun t => G.metric t) (twoTensorSecToFamily (I := I) (M := M) S) X N
          nabla2Barrier nablaBarrier epsilon delta t0) ->
        (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
          (fun t => G.metric t) N (Set.Icc t0 (t0 + delta))) ->
        (d : TensorFirstNullData (I := I) (M := M) (fun t => G.metric t)
          (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0) ->
        TensorFirstNullScalarSigns (I := I) (M := M) (fun t => G.metric t)
          (twoTensorSecToFamily (I := I) (M := M) S) X N epsilon delta t0 d) :
    TensorWMPSectionReg (I := I) (M := M) (fun t => G.metric t) S X N T :=
  ofTotal (I := I) (M := M)
    (G := fun t => G.metric t) (S := S) (X := X) (N := N) (T := T)
    hsym hbar
    (fun delta t0 hdelta hsub =>
      metricTensor_tangentBundle_cont_of_metricFamilySmoothOn
        (I := I) (M := M) G hG
        (fun t ht => hTsub (hsub ht)))
    hTensor hFixed hSigns

/-- Convert the section-backed WMP regularity package to the raw kernel
package, producing first-null compactness via `TensorFirstNullCompactnessOn.of_section`. -/
theorem toRaw
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (h : TensorWMPSectionReg (I := I) (M := M) G S X N T) :
    TensorWMPRegularityOn (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) X N T where
  symmetric := h.symmetric
  barrierRegularity := h.barrierRegularity
  firstNullCompactness := by
    intro epsilon delta t0 hepsilon hdelta hsub
    exact TensorFirstNullCompactnessOn.of_section_timeSlab (I := I) (M := M)
      G S epsilon delta t0
      (h.unitSlabCompact delta t0 hdelta hsub)
      (barrierTimeCont (I := I) (M := M) G S epsilon delta t0
        (Set.Icc t0 (t0 + delta))
        (h.tensorQuadCont delta t0 hdelta hsub)
        (h.metricQuadCont delta t0 hdelta hsub))
      (h.barrierFixedContinuous epsilon delta t0 hepsilon hdelta hsub)
  firstNullScalarSigns := h.firstNullScalarSigns

end TensorWMPSectionReg

/-- Convert an absolute-value reaction estimate into the one-sided upper bound
needed in the strict-barrier local estimate. -/
private theorem reaction_bound_of_abs {a b R : Real}
    (h : |a - b| ≤ R) : b ≤ a + R := by
  have hnegR : -R ≤ -|a - b| := neg_le_neg h
  have hnegabs : -|a - b| ≤ a - b := neg_abs_le (a - b)
  have hle : -R ≤ a - b := le_trans hnegR hnegabs
  linarith

/-- The smallness condition `4 K delta < 1` makes the Lipschitz reaction error
smaller than the half-metric gain on nonzero tangent vectors. -/
private theorem reactionErr_lt_gain
    {K epsilon delta c g : Real}
    (hK : 0 ≤ K)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta)
    (hc_nonneg : 0 ≤ c)
    (hc_le : c ≤ 2 * delta)
    (hsmall : 4 * K * delta < 1)
    (hg : 0 < g) :
    K * |epsilon * c * g| < (epsilon / 2) * g := by
  have harg_nonneg : 0 ≤ epsilon * c * g := by
    exact mul_nonneg (mul_nonneg (le_of_lt hepsilon) hc_nonneg) (le_of_lt hg)
  rw [abs_of_nonneg harg_nonneg]
  have hkc_le : K * c ≤ K * (2 * delta) :=
    mul_le_mul_of_nonneg_left hc_le hK
  have htwo : K * (2 * delta) < 1 / 2 := by
    nlinarith
  have hkc_lt : K * c < 1 / 2 := lt_of_le_of_lt hkc_le htwo
  have hepsg_pos : 0 < epsilon * g := mul_pos hepsilon hg
  have hmul := mul_lt_mul_of_pos_right hkc_lt hepsg_pos
  nlinarith

/-- Produce the strict-barrier constants and pointwise estimates from the
metric time-gain control and the uniform small-barrier reaction Lipschitz
bound. -/
theorem strictBarrierBounds
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T t0 : Real}
    (hreg : TensorWMPCore (I := I) (M := M) G S X N T)
    (ht0 : t0 ∈ Set.Icc 0 T)
    (ht0T : t0 < T)
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    (_hbase : TensorParabolicInequalityWithDriftOn (I := I) (M := M)
      G S X N nabla2S nablaS T) :
    ∃ delta0 K : Real,
      0 < delta0 ∧ 0 ≤ K ∧ t0 + delta0 ≤ T ∧
        ∀ delta : Real,
          0 < delta ->
          delta ≤ delta0 ->
          4 * K * delta < 1 ->
          ∀ epsilon : Real,
            SmallBarrierEps epsilon ->
            ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
            ∃ reactionErr : TensorQuadraticFormFamily (I := I) (M := M),
            ∃ metricGain : TensorQuadraticFormFamily (I := I) (M := M),
              (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  HasDerivWithinAt (fun s : Real => (G s).inner x v v)
                    (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
              (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  metricGain t x v ≤
                    epsilon * ((G t).inner x v v +
                      (delta + t - t0) * metricDeriv t x v)) ∧
              (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  N t (G t)
                      (tensorBarrierFamily (I := I) (M := M)
                        G S epsilon delta t0 t) x v v ≤
                    N t (G t) (S t) x v v + reactionErr t x v) ∧
              (∀ t, t ∈ Set.Ioc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  v ≠ 0 -> reactionErr t x v < metricGain t x v) := by
  obtain ⟨delta0, hdelta0, hdelta0T, hmetric⟩ :=
    hreg.barrierRegularity.metricGainControl t0 ht0 ht0T
  have hsub0 : Set.Icc t0 (t0 + delta0) ⊆ Set.Icc 0 T := by
    intro t ht
    exact ⟨le_trans ht0.1 ht.1, le_trans ht.2 hdelta0T⟩
  obtain ⟨K, hK, hLip⟩ :=
    hreg.barrierRegularity.smallBarrierLip delta0 t0 hdelta0 hsub0
  refine ⟨delta0, K, hdelta0, hK, hdelta0T, ?_⟩
  intro delta hdelta hdelta_le hsmall epsilon hepsilon
  obtain ⟨metricDeriv, hmetric_deriv, hmetric_gain⟩ :=
    hmetric delta hdelta hdelta_le epsilon hepsilon
  let reactionErr : TensorQuadraticFormFamily (I := I) (M := M) :=
    fun t x v =>
      K * |epsilon * (delta + t - t0) * (G t).inner x v v|
  let metricGain : TensorQuadraticFormFamily (I := I) (M := M) :=
    fun t x v => (epsilon / 2) * (G t).inner x v v
  refine ⟨metricDeriv, reactionErr, metricGain, hmetric_deriv, ?_, ?_, ?_⟩
  · intro t ht x v
    exact hmetric_gain t ht x v
  · intro t ht x v
    have ht_closed : t ∈ Set.Icc t0 (t0 + delta) := ⟨le_of_lt ht.1, ht.2⟩
    have hLip_t := hLip epsilon delta hepsilon hdelta hdelta_le t ht_closed x v
    dsimp [reactionErr]
    exact reaction_bound_of_abs (a := N t (G t) (S t) x v v)
      (b := N t (G t)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t) x v v)
      hLip_t
  · intro t ht x v hv
    dsimp [reactionErr, metricGain]
    have htime_nonneg : 0 ≤ delta + t - t0 := by
      have ht_sub : 0 ≤ t - t0 := sub_nonneg.mpr (le_of_lt ht.1)
      have hsum : 0 ≤ delta + (t - t0) :=
        add_nonneg (le_of_lt hdelta) ht_sub
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsum
    have htime_le : delta + t - t0 ≤ 2 * delta := by
      have ht_le : t - t0 ≤ delta := by linarith [ht.2]
      linarith
    exact reactionErr_lt_gain (K := K) (epsilon := epsilon) (delta := delta)
      (c := delta + t - t0) (g := (G t).inner x v v)
      hK hepsilon.1 hdelta htime_nonneg htime_le hsmall ((G t).pos x v hv)

/--
Parabolic supersolution package for the drifted tensor inequality

`(partial_t - Delta) S >= X^k nabla_k S + N(S,g,t)`.

The evaluated inequality is kept as an analytic predicate in this first
interface pass, but its spatial part is the direct tensor heat-with-drift
operator evaluated on supplied first and second covariant derivative tensors.
-/
structure TensorParabolicSupersolutionWithDriftOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (nabla2S : TensorNabla2Family (I := I) (M := M))
    (nablaS : TensorNabla1Family (I := I) (M := M))
    (T : Real) : Prop where
  evaluatedInequality :
    TensorParabolicInequalityWithDriftOn (I := I) (M := M) G S X N
      nabla2S nablaS T

/-! ## Barrier proof blocks -/

/--
Step 1: the barrier is initially positive definite.

This is the `S_epsilon(t0) = S(t0) + epsilon * delta * g(t0)` step.
-/
theorem tensorBarrier_initial_positive
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t0) :
    ∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t0) x := by
  intro x v hv
  have hS : 0 ≤ S t0 x v v := hinit x v
  have hmetric : 0 < (G t0).inner x v v := (G t0).pos x v hv
  have hcoeff : 0 < epsilon * (delta + t0 - t0) := by
    have htime : delta + t0 - t0 = delta := by ring
    rw [htime]
    exact mul_pos hepsilon hdelta
  have hbarrier : 0 < epsilon * (delta + t0 - t0) * (G t0).inner x v v :=
    mul_pos hcoeff hmetric
  exact add_pos_of_nonneg_of_pos hS hbarrier

/-- Choose a short time step satisfying both slab containment and `4 K delta < 1`. -/
private theorem exists_small_delta
    {t0 T delta0 K : Real}
    (hroom : t0 < T)
    (hdelta0 : 0 < delta0)
    (hK : 0 ≤ K) :
    ∃ delta : Real,
      0 < delta ∧ delta ≤ delta0 ∧ t0 + delta ≤ T ∧ 4 * K * delta < 1 := by
  let delta : Real :=
    min (min (delta0 / 2) ((T - t0) / 2)) (1 / (4 * K + 1))
  have hdelta0_half_pos : 0 < delta0 / 2 := by positivity
  have hroom_half_pos : 0 < (T - t0) / 2 := by linarith
  have hden_pos : 0 < 4 * K + 1 := by nlinarith
  have hrecip_pos : 0 < 1 / (4 * K + 1) := by positivity
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact lt_min (lt_min hdelta0_half_pos hroom_half_pos) hrecip_pos
  have hdelta_le_half0 : delta ≤ delta0 / 2 := by
    dsimp [delta]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hdelta_le_room_half : delta ≤ (T - t0) / 2 := by
    dsimp [delta]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hdelta_le_recip : delta ≤ 1 / (4 * K + 1) := by
    dsimp [delta]
    exact min_le_right _ _
  have hdelta_le_delta0 : delta ≤ delta0 := by linarith
  have hdelta_le_room : delta ≤ T - t0 := by linarith
  have htime : t0 + delta ≤ T := by linarith
  have hcoef_nonneg : 0 ≤ 4 * K := by nlinarith
  have hmul_le :
      4 * K * delta ≤ 4 * K * (1 / (4 * K + 1)) := by
    exact mul_le_mul_of_nonneg_left hdelta_le_recip hcoef_nonneg
  have hfrac_lt : 4 * K * (1 / (4 * K + 1)) < 1 := by
    field_simp [hden_pos.ne']
    nlinarith
  have hstrict : 4 * K * delta < 1 := lt_of_le_of_lt hmul_le hfrac_lt
  exact Exists.intro delta
    (And.intro hdelta_pos
      (And.intro hdelta_le_delta0 (And.intro htime hstrict)))

/--
Step 2: the metric-variation and Lipschitz estimates make the barrier a strict
supersolution on a sufficiently short slab.
-/
theorem tensorBarrier_strict_supersolution
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {t0 T : Real}
    (ht0 : t0 ∈ Set.Icc 0 T)
    (ht0T : t0 < T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N nabla2S nablaS T) :
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      TensorBarrierUniformStrictOnSlab (I := I) (M := M) G S X N
        delta t0 := by
  obtain ⟨delta0, K, hdelta0, hK, _hdelta0T, hstrict_bounds⟩ :=
    strictBarrierBounds (I := I) (M := M)
      hreg.toCore ht0 ht0T hparabolic.evaluatedInequality
  obtain ⟨delta, hdelta, hdelta_le_delta0, hdeltaT, hsmall⟩ :=
    exists_small_delta (t0 := t0) (T := T) (delta0 := delta0) (K := K)
      ht0T hdelta0 hK
  refine ⟨delta, hdelta, hdeltaT, ?_⟩
  intro epsilon hepsilon
  obtain ⟨metricDeriv, reactionErr, metricGain,
      hmetric_deriv, hgain, hreaction, hmargin⟩ :=
    hstrict_bounds delta hdelta hdelta_le_delta0 hsmall epsilon hepsilon
  refine ⟨nabla2S, nablaS, ?_⟩
  have hsubInterior : Set.Ioc t0 (t0 + delta) ⊆ Set.Ioc 0 T := by
    intro t ht
    exact ⟨lt_of_le_of_lt ht0.1 ht.1, le_trans ht.2 hdeltaT⟩
  exact strictBarrier_of_derivEst (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2S := nabla2S) (nablaS := nablaS)
    (epsilon := epsilon) (delta := delta) (t0 := t0) (T := T)
    hsubInterior hparabolic.evaluatedInequality
    metricDeriv reactionErr metricGain hmetric_deriv hgain hreaction hmargin

/--
Compatibility adapter from the old regularity package to the certificate
route.

The old package asks scalar signs for every strict-barrier derivative witness.
This theorem is the only place in the old raw WMP route where that stronger
field is used: it turns the strict-barrier witnesses into `TensorStrictCert`s.
-/
theorem certSlab_of_reg
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {t0 T : Real}
    (ht0 : t0 ∈ Set.Icc 0 T)
    (ht0T : t0 < T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N nabla2S nablaS T) :
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      TensorStrictCertSlab (I := I) (M := M) G S X N delta t0 := by
  obtain ⟨delta, hdelta, hdeltaT, hstrict_uniform⟩ :=
    tensorBarrier_strict_supersolution (I := I) (M := M)
      (G := G) (S := S) (X := X) (N := N)
      ht0 ht0T hreg hparabolic
  refine ⟨delta, hdelta, hdeltaT, ?_⟩
  intro epsilon hepsilon
  obtain ⟨nabla2Barrier, nablaBarrier, hstrict⟩ :=
    hstrict_uniform epsilon hepsilon
  refine ⟨?_⟩
  refine
    { nabla2Barrier := nabla2Barrier
      nablaBarrier := nablaBarrier
      strict := hstrict
      signs := ?_ }
  intro hnull d
  have hsub : Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T := by
    intro t ht
    exact ⟨le_trans ht0.1 ht.1, le_trans ht.2 hdeltaT⟩
  exact
    hreg.firstNullScalarSigns epsilon delta t0 hepsilon.1 hdelta hsub
      nabla2Barrier nablaBarrier hstrict hnull d

/-- Section-backed strict-barrier certificates with scalar signs tied to the
section covariant derivative witnesses. -/
theorem strictCert_sec
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nablaS : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2S : TensorNabla2SecFamily (I := I) (M := M)}
    {cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {t0 T : Real}
    (ht0 : t0 ∈ Set.Icc 0 T)
    (ht0T : t0 < T)
    (hreg : TensorWMPSectionCore (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G (twoTensorSecToFamily (I := I) (M := M) S) X N
      (fun t x => nabla2S t x) (fun t x => nablaS t x) T)
    (hcov1 : ∀ t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (cov t) (1 : WithTop ℕ∞))
    (hcovInf : ∀ t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (cov t) (∞ : WithTop ℕ∞))
    (hmc : ∀ t : Real,
      RicciFlower.Connection.IsMetricCompatible (I := I) (cov t) (G t))
    (hS : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S) :
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      TensorStrictCertSlab (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N delta t0 := by
  obtain ⟨delta0, K, hdelta0, hK, _hdelta0T, hstrict_bounds⟩ :=
    strictBarrierBounds (I := I) (M := M)
      hreg.toRaw ht0 ht0T hparabolic.evaluatedInequality
  obtain ⟨delta, hdelta, hdelta_le_delta0, hdeltaT, hsmall⟩ :=
    exists_small_delta (t0 := t0) (T := T) (delta0 := delta0) (K := K)
      ht0T hdelta0 hK
  refine ⟨delta, hdelta, hdeltaT, ?_⟩
  intro epsilon hepsilon
  obtain ⟨metricDeriv, reactionErr, metricGain,
      hmetric_deriv, hgain, hreaction, hmargin⟩ :=
    hstrict_bounds delta hdelta hdelta_le_delta0 hsmall epsilon hepsilon
  have hsubInterior : Set.Ioc t0 (t0 + delta) ⊆ Set.Ioc 0 T := by
    intro t ht
    exact ⟨lt_of_le_of_lt ht0.1 ht.1, le_trans ht.2 hdeltaT⟩
  have hsubClosed : Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T := by
    intro t ht
    exact ⟨le_trans ht0.1 ht.1, le_trans ht.2 hdeltaT⟩
  have hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G (twoTensorSecToFamily (I := I) (M := M) S) X N
      (fun t x => nabla2S t x) (fun t x => nablaS t x)
      epsilon delta t0 :=
    strictBarrier_of_derivEst (I := I) (M := M)
      (G := G) (S := twoTensorSecToFamily (I := I) (M := M) S)
      (X := X) (N := N)
      (nabla2S := fun t x => nabla2S t x)
      (nablaS := fun t x => nablaS t x)
      (epsilon := epsilon) (delta := delta) (t0 := t0) (T := T)
      hsubInterior hparabolic.evaluatedInequality
      metricDeriv reactionErr metricGain hmetric_deriv hgain hreaction hmargin
  refine ⟨⟨fun t x => nabla2S t x, fun t x => nablaS t x, hstrict, ?_⟩⟩
  intro hnull d
  obtain ⟨Xsec, hXsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      d.x1 (X d.t1 d.x1)
  have hsym :
      TwoTensorFamilySymmetricOn (I := I) (M := M)
        (twoTensorSecToFamily (I := I) (M := M) S)
        (Set.Icc t0 (t0 + delta)) := by
    intro t ht x
    exact hreg.symmetric t (hsubClosed ht) x
  exact scalarSigns_secHess (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nablaS := nablaS) (nabla2S := nabla2S) (cov := cov)
    hstrict hnull hsym d (hcov1 d.t1) (hcovInf d.t1) hmc hS Xsec
    (laplacianNonnegativeAtSpatialMin_of_metricCompatible
      (I := I) (cov d.t1) (G d.t1) (hmc d.t1))
    hXsec.symm

/-- Compatibility adapter from the old section regularity package to the
certificate route.  New section producers should use `strictCert_sec` instead,
where the derivative witnesses are fixed by `TensorSpatialDerivs`. -/
theorem certSlab_of_sectionReg
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {t0 T : Real}
    (ht0 : t0 ∈ Set.Icc 0 T)
    (ht0T : t0 < T)
    (hreg : TensorWMPSectionReg (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G (twoTensorSecToFamily (I := I) (M := M) S) X N
      nabla2S nablaS T) :
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      TensorStrictCertSlab (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) X N delta t0 :=
  certSlab_of_reg (I := I) (M := M)
    (G := G) (S := twoTensorSecToFamily (I := I) (M := M) S)
    (X := X) (N := N) ht0 ht0T hreg.toRaw hparabolic

/--
Step 3: if the barrier fails to stay positive, compactness gives first-null
data.
-/
theorem tensorBarrier_first_null_of_failure
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hcompact : TensorFirstNullCompactnessOn (I := I) (M := M)
      G S epsilon delta t0)
    (hinit_pos : ∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t0) x)
    (hfail : ¬ TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0)
      (Set.Icc t0 (t0 + delta))) :
    Nonempty (TensorFirstNullData (I := I) (M := M) G S epsilon delta t0) := by
  exact hcompact.firstNull_of_failure hinit_pos hfail

/--
Pure scalar order contradiction used at a first null vector.

Here `timeDeriv` is `partial_t phi`, `laplacian` is `Delta phi`, `drift`
is `X · nabla phi`, and `reaction` is the evaluated reaction term.
-/
private theorem firstNullOrder
    {timeDeriv laplacian drift reaction : Real}
    (htime : timeDeriv ≤ 0)
    (hlap : 0 ≤ laplacian)
    (hdrift : drift = 0)
    (hreaction : 0 ≤ reaction)
    (hstrict : drift + reaction < timeDeriv - laplacian) :
    False := by
  have hsource_nonneg : 0 ≤ drift + reaction := by
    simpa [hdrift] using hreaction
  have htarget_pos : 0 < timeDeriv - laplacian :=
    lt_of_le_of_lt hsource_nonneg hstrict
  have htarget_nonpos : timeDeriv - laplacian ≤ 0 := by
    simpa [sub_eq_add_neg] using add_nonpos htime (neg_nonpos.mpr hlap)
  exact (not_lt_of_ge htarget_nonpos) htarget_pos

/--
Step 4: evaluating the strict inequality at the first null vector contradicts
the scalar maximum-principle signs and the null-eigenvector condition.
-/
theorem tensor_first_null_contradiction
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (_hnull : TensorNullEigenvectorCondition (I := I) (M := M) G
      N (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (hsigns : TensorFirstNullScalarSigns (I := I) (M := M)
      G S X N epsilon delta t0 d) :
    False := by
  rcases hstrict with ⟨timeDeriv, _hderiv, hstrict_eval⟩
  have ht1_mem_slab : d.t1 ∈ Set.Icc t0 (t0 + delta) :=
    ⟨le_of_lt d.t1_mem.1, d.t1_mem.2⟩
  have _hstrict_at_first_null :
      tensorHeatWithDrift2QuadMetricAt (I := I) (G d.t1) (X d.t1)
          (nabla2Barrier d.t1 d.x1) (nablaBarrier d.t1 d.x1) d.v +
        N d.t1 (G d.t1)
            (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
            d.x1 d.v d.v <
        timeDeriv d.t1 d.x1 d.v := by
    exact hstrict_eval d.t1 d.t1_mem d.x1 d.v d.v_ne_zero
  have ht1_mem_until : d.t1 ∈ Set.Icc t0 d.t1 :=
    ⟨le_of_lt d.t1_mem.1, le_rfl⟩
  have hbarrier_nonnegative :
      TwoTensorNonnegativeAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
        d.x1 :=
    d.nonnegative_until d.t1 ht1_mem_until d.x1
  have _hreaction_nonnegative :
      0 ≤
        N d.t1 (G d.t1)
          (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
          d.x1 d.v d.v := by
    exact _hnull d.t1 ht1_mem_slab
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
      d.x1 hbarrier_nonnegative d.v d.null
  rcases hsigns with
    ⟨timeDeriv, laplacian, drift, reaction,
      htime_nonpos, hlaplacian_nonneg, hdrift_zero, hreaction_nonneg, hstrict_ineq⟩
  exact firstNullOrder htime_nonpos hlaplacian_nonneg hdrift_zero
    hreaction_nonneg hstrict_ineq

/--
Step 5: the strict barrier remains nonnegative on the short slab.
-/
theorem shortSlab_cert
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {t0 T : Real}
    (ht0 : t0 ∈ Set.Icc 0 T)
    (_ht0T : t0 < T)
    (hreg : TensorWMPCore (I := I) (M := M) G S X N T)
    (hcert :
      ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
        TensorStrictCertSlab (I := I) (M := M) G S X N delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G
      N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t0) :
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      TensorBarrierUniformOnSlab (I := I) (M := M) G S delta t0 := by
  classical
  obtain ⟨delta, hdelta, hdeltaT, hstrict_uniform⟩ := hcert
  refine ⟨delta, hdelta, hdeltaT, ?_⟩
  intro epsilon hepsilon
  obtain ⟨cert⟩ := hstrict_uniform epsilon hepsilon
  by_contra hfail
  have hinit_pos : ∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t0) x :=
    tensorBarrier_initial_positive (I := I) (M := M)
      (G := G) (S := S) hepsilon.1 hdelta hinit
  have hsub : Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T := by
    intro t ht
    exact ⟨le_trans ht0.1 ht.1, le_trans ht.2 hdeltaT⟩
  have hcompact : TensorFirstNullCompactnessOn (I := I) (M := M)
      G S epsilon delta t0 :=
    hreg.firstNullCompactness epsilon delta t0 hepsilon.1 hdelta hsub
  obtain ⟨d⟩ :=
    tensorBarrier_first_null_of_failure (I := I) (M := M)
      (G := G) (S := S) (epsilon := epsilon) (delta := delta) (t0 := t0)
      hcompact hinit_pos hfail
  have hnull_slab : TensorNullEigenvectorCondition (I := I) (M := M) G
      N (Set.Icc t0 (t0 + delta)) := by
    intro t ht A x hA v hv
    exact hnull t (hsub ht) A x hA v hv
  exact tensor_first_null_contradiction (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := cert.nabla2Barrier) (nablaBarrier := cert.nablaBarrier)
    cert.strict hnull_slab d (cert.signs hnull_slab d)

theorem tensorBarrier_nonnegative_on_short_slab
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {t0 T : Real}
    (ht0 : t0 ∈ Set.Icc 0 T)
    (ht0T : t0 < T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N nabla2S nablaS T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G
      N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t0) :
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      TensorBarrierUniformOnSlab (I := I) (M := M) G S delta t0 := by
  exact shortSlab_cert (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    ht0 ht0T hreg.toCore
    (certSlab_of_reg (I := I) (M := M)
      (G := G) (S := S) (X := X) (N := N)
      ht0 ht0T hreg hparabolic)
    hnull hinit

/--
Step 6: iterate short slabs and let `epsilon -> 0`.
-/
theorem tensor_wmp_of_barrier_limit
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {T : Real}
    (_hT : 0 ≤ T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N nabla2S nablaS T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) S (Set.Icc 0 T) := by
  exact barrierLimitClosure_of_continuous (I := I) (M := M)
    (G := G) (S := S) _hT hreg.barrierRegularity.tensor_eval_continuous hinit
    (fun t0 ht0 ht0T hinit_t0 =>
      shortSlab_cert (I := I) (M := M)
        (G := G) (S := S) (X := X) (N := N)
        ht0 ht0T hreg.toCore
        (certSlab_of_reg (I := I) (M := M)
          (G := G) (S := S) (X := X) (N := N)
          ht0 ht0T hreg hparabolic)
        hnull hinit_t0)

/-- Tensor WMP from core regularity and strict-barrier certificates. -/
theorem wmp_of_cert
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (_hT : 0 ≤ T)
    (hreg : TensorWMPCore (I := I) (M := M) G S X N T)
    (hcert :
      ∀ t0 : Real, t0 ∈ Set.Icc 0 T -> t0 < T ->
        ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
          TensorStrictCertSlab (I := I) (M := M) G S X N delta t0)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) S (Set.Icc 0 T) := by
  exact barrierLimitClosure_of_continuous (I := I) (M := M)
    (G := G) (S := S) _hT hreg.barrierRegularity.tensor_eval_continuous hinit
    (fun t0 ht0 ht0T hinit_t0 =>
      shortSlab_cert (I := I) (M := M)
        (G := G) (S := S) (X := X) (N := N)
        ht0 ht0T hreg (hcert t0 ht0 ht0T) hnull hinit_t0)

/-- Theorem 7.5, section-backed producer form.

This is the generic tensor WMP endpoint for smooth two-tensor sections.  The
strict-barrier derivatives are selected from `TensorSpatialDerivs`, and the
first-null scalar signs are produced by `strictCert_sec` for those same
derivative witnesses. -/
theorem wmp_section_sec
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nablaS : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2S : TensorNabla2SecFamily (I := I) (M := M)}
    {cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {T : Real}
    (_hT : 0 ≤ T)
    (hreg : TensorWMPSectionCore (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G (twoTensorSecToFamily (I := I) (M := M) S) X N
      (fun t x => nabla2S t x) (fun t x => nablaS t x) T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) 0)
    (hcov1 : ∀ t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (cov t) (1 : WithTop ℕ∞))
    (hcovInf : ∀ t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (cov t) (∞ : WithTop ℕ∞))
    (hmc : ∀ t : Real,
      RicciFlower.Connection.IsMetricCompatible (I := I) (cov t) (G t))
    (hS : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T) := by
  exact wmp_of_cert (I := I) (M := M)
    (G := G) (S := twoTensorSecToFamily (I := I) (M := M) S)
    (X := X) (N := N) _hT hreg.toRaw
    (fun t0 ht0 ht0T =>
      strictCert_sec (I := I) (M := M)
        (G := G) (S := S) (X := X) (N := N)
        (nablaS := nablaS) (nabla2S := nabla2S) (cov := cov)
        ht0 ht0T hreg hparabolic hcov1 hcovInf hmc hS)
    hnull hinit

/-- Hypothesis package for theorem 7.5 in its generic section-backed form.

This is only a bundled presentation of the real inputs consumed by
`wmp_section_sec`; it does not add a new producer predicate or hide a
Ricci-flow-specific assumption. -/
structure TensorWMPInput
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (nablaS : TensorNabla1SecFamily (I := I) (M := M))
    (nabla2S : TensorNabla2SecFamily (I := I) (M := M))
    (T : Real) : Prop where
  hT : 0 ≤ T
  reg : TensorWMPSectionCore (I := I) (M := M) G S X N T
  parabolic :
    TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G (twoTensorSecToFamily (I := I) (M := M) S) X N
      (fun t x => nabla2S t x) (fun t x => nablaS t x) T
  null : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T)
  initial :
    TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) 0
  hcov1 : ∀ t : Real,
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (cov t) (1 : WithTop ℕ∞)
  hcovInf : ∀ t : Real,
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (cov t) (∞ : WithTop ℕ∞)
  hmc : ∀ t : Real,
    RicciFlower.Connection.IsMetricCompatible (I := I) (cov t) (G t)
  spatial : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S

/-- Theorem 7.5 in LaTeX-facing packaged form. -/
theorem tensor_wmp
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {nablaS : TensorNabla1SecFamily (I := I) (M := M)}
    {nabla2S : TensorNabla2SecFamily (I := I) (M := M)}
    {T : Real}
    (data : TensorWMPInput (I := I) (M := M) G S X N cov nablaS nabla2S T) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T) := by
  exact wmp_section_sec (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nablaS := nablaS) (nabla2S := nabla2S) (cov := cov)
    data.hT data.reg data.parabolic data.null data.initial
    data.hcov1 data.hcovInf data.hmc data.spatial

/--
Hamilton's weak maximum principle for symmetric two-tensors.

The proof is routed through the named barrier blocks above.
-/
theorem hamilton_tensor_wmp
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {T : Real}
    (_hT : 0 ≤ T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (_hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N nabla2S nablaS T)
    (_hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (_hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) S (Set.Icc 0 T) := by
  exact wmp_of_cert (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N) _hT hreg.toCore
    (fun t0 ht0 ht0T =>
      certSlab_of_reg (I := I) (M := M)
        (G := G) (S := S) (X := X) (N := N)
        ht0 ht0T hreg _hparabolic)
    _hnull _hinit

/-- Compatibility section-backed public wrapper for Hamilton's tensor WMP.

This preserves the older `TensorWMPSectionReg` interface, whose scalar-sign
field is stronger than the producer route now needs.  New theorem-7.5 producers
should use `wmp_section_sec`. -/
theorem hamilton_tensor_wmp_section
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorSecFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {T : Real}
    (_hT : 0 ≤ T)
    (hreg : TensorWMPSectionReg (I := I) (M := M) G S X N T)
    (_hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G (twoTensorSecToFamily (I := I) (M := M) S)
      X N nabla2S nablaS T)
    (_hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (_hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S) (Set.Icc 0 T) := by
  exact wmp_of_cert (I := I) (M := M)
    (G := G) (S := twoTensorSecToFamily (I := I) (M := M) S)
    (X := X) (N := N) _hT hreg.toCore.toRaw
    (fun t0 ht0 ht0T =>
      certSlab_of_sectionReg (I := I) (M := M)
        (G := G) (S := S) (X := X) (N := N)
        ht0 ht0T hreg _hparabolic)
    _hnull _hinit

end

end Realized
end RicciFlower
