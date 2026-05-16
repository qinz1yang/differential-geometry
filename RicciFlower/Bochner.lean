import RicciFlower.ScalarBochner
import RicciFlower.Realized.CurvatureTensor
import RicciFlower.Coordinates.Tensor
import RicciFlower.Tensor.RSTensor.Tensor0SRiemannian
import RicciFlower.Tensor.Multilinear.BundleSmoothEval
set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# RicciFlower Coordinate Bochner Formulae

This file contains the coordinate-facing Bochner consumers needed for the
Ricci-norm evolution calculation.

The geometric producer statements are kept explicit: this file does not prove
that a scalar Laplacian or a rough tensor Laplacian has a particular coordinate
expression.  Once those expressions are supplied, the Bochner identities below
are finite-sum algebra.
-/

namespace RicciFlower
namespace Realized

noncomputable section

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

/-! ## Pointwise metric tensor norms -/

section TensorInner

variable [FiniteDimensional Real E]

/-- Local time-dependent alias for `(0,2)` tensor sections.  Time-dependent
curvature does not belong in the static curvature files. -/
abbrev Tensor02Field (Time : Type*) :=
  Time -> Tensor02Section (I := I) (M := M)

/-- Local time-dependent inverse-metric component predicate used by the
Bochner coordinate bridges. -/
def InverseMetricComponentsInFrameTime
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t x i j,
    (∑ k : Idx, gInv t x i k * (G.metric t).inner x (frame k x) (frame j x)) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, (G.metric t).inner x (frame i x) (frame k x) * gInv t x k j) =
        (if i = j then 1 else 0)

private noncomputable instance tangentSpace_addCommMonoid (x : M) :
    AddCommMonoid (TangentSpace I x) :=
  inferInstanceAs (AddCommMonoid E)

private noncomputable instance tangentSpace_module (x : M) :
    Module Real (TangentSpace I x) :=
  inferInstanceAs (Module Real E)

/-- First-principles metric inner product on covariant two-tensors, delegated
to the tensor metric layer. -/
def inner02
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B : Tensor02At (I := I) x) : Real :=
  Tensor0SBundle.inner0S (I := I) (M := M) g x 2 A B

/-- Squared norm of a covariant two-tensor from the metric inner product. -/
def normSq02
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor02At (I := I) x) : Real :=
  inner02 (I := I) g x A A

@[simp] theorem normSq02_eq_inner02
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor02At (I := I) x) :
    normSq02 (I := I) g x A = inner02 (I := I) g x A A := by
  rfl

/-- Pointwise norm square of a time-dependent `(0,2)` tensor field. -/
def tensorNormSq02
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (A : Tensor02Field (I := I) (M := M) Time) :
    Time -> M -> Real :=
  fun t x => normSq02 (I := I) (G.metric t) x (A t x)

/-- Components of a `(0,2)` tensor in a frame. -/
def tensor02Comp
    {Idx : Type*}
    (A : Tensor02Field (I := I) (M := M) Time)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) (i j : Idx) : Real :=
  A t x (fun a => if a = 0 then frame i x else frame j x)

/-- Basis-coordinate contraction formula for the pointwise `(0,2)` tensor inner
product. This is the direct bridge from the intrinsic tensor metric to local
coordinates. -/
theorem inner02_eq_coord_direct
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : Tensor0SBundle.MetricInverseInBasis (I := I) (M := M) g x basis gInv)
    (A B : Tensor02At (I := I) x) :
    inner02 (I := I) g x A B =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (vec2 (basis i) (basis j)) *
            B (vec2 (basis k) (basis l)) := by
  simpa [inner02, vec2] using
    Tensor0SBundle.inner0S_two_eq_coord_direct (I := I) (M := M) g x
      basis gInv hinv A B

/-- A local frame turns the frame inverse-component predicate into the
basis-level inverse predicate needed by tensor coordinate formulas. -/
theorem metricInverseInBasis_of_frame
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {u : Set M}
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hinv : InverseMetricComponentsInFrameTime (I := I) G gInv frame)
    (t : Time) {x : M} (hx : x ∈ u) :
    Tensor0SBundle.MetricInverseInBasis (I := I) (M := M) (G.metric t) x
      (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) := by
  intro i j
  constructor
  · simpa [IsLocalFrameOn.toBasisAt_coe] using (hinv t x i j).1
  · simpa [IsLocalFrameOn.toBasisAt_coe] using (hinv t x i j).2

/-- Coordinate contraction formula for the pointwise `(0,2)` tensor inner
product. -/
theorem inner02_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {u : Set M}
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (A B : Tensor02Field (I := I) (M := M) Time)
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hinv : InverseMetricComponentsInFrameTime (I := I) G gInv frame)
    (t : Time) {x : M} (hx : x ∈ u) :
    inner02 (I := I) (G.metric t) x (A t x) (B t x) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv t x i k * gInv t x j l *
          tensor02Comp (I := I) A frame t x i j *
            tensor02Comp (I := I) B frame t x k l := by
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis (I := I) (M := M) (G.metric t) x
        (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) :=
    metricInverseInBasis_of_frame (I := I) G gInv frame hframe hinv t hx
  simpa [tensor02Comp, vec2, IsLocalFrameOn.toBasisAt_coe] using
    inner02_eq_coord_direct (I := I) (G.metric t) x
      (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) hinvAt
      (A t x) (B t x)

/-- Coordinate formula for the first-principles squared norm. -/
theorem normSq02_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {u : Set M}
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (A : Tensor02Field (I := I) (M := M) Time)
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hinv : InverseMetricComponentsInFrameTime (I := I) G gInv frame)
    (t : Time) {x : M} (hx : x ∈ u) :
    tensorNormSq02 (I := I) G A t x =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv t x i k * gInv t x j l *
          tensor02Comp (I := I) A frame t x i j *
            tensor02Comp (I := I) A frame t x k l := by
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis (I := I) (M := M) (G.metric t) x
        (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) :=
    metricInverseInBasis_of_frame (I := I) G gInv frame hframe hinv t hx
  simpa [tensorNormSq02, normSq02, inner02, tensor02Comp,
    IsLocalFrameOn.toBasisAt_coe] using
    Tensor0SBundle.normSq0S_two_eq_coord (I := I) (M := M) (G.metric t) x
      (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) hinvAt
      (A t x)

end TensorInner

/-! ## General coordinate Bochner data -/

section GeneralTensorNorm

variable {Comp Dir : Type*} [Fintype Comp] [Fintype Dir]

/-- A weighted coordinate squared norm for a tensor component list.

The finite component type `Comp` is deliberately abstract. For a concrete
covariant tensor, `weight` packages the appropriate inverse-metric contractions
for the chosen frame and slot convention.

This is only a finite-sum algebra helper for coordinate calculations. The
first-principles `(0,2)` metric norm is `normSq02`, with coordinate evaluation
given by `normSq02_eq_coord`. -/
def tensorNormSqInFrame
    (weight component : Time -> M -> Comp -> Real) :
    Time -> M -> Real :=
  fun t x => ∑ I : Comp, weight t x I * component t x I * component t x I

@[simp] theorem tensorNormSqInFrame_apply
    (weight component : Time -> M -> Comp -> Real)
    (t : Time) (x : M) :
    tensorNormSqInFrame (M := M) weight component t x =
      ∑ I : Comp, weight t x I * component t x I * component t x I := by
  rfl

/-- Coordinate inner product of a rough Laplacian component with the tensor. -/
def roughLapTensorInnerInFrame
    (weight roughLap component : Time -> M -> Comp -> Real) :
    Time -> M -> Real :=
  fun t x => ∑ I : Comp, weight t x I * roughLap t x I * component t x I

@[simp] theorem roughLapTensorInnerInFrame_apply
    (weight roughLap component : Time -> M -> Comp -> Real)
    (t : Time) (x : M) :
    roughLapTensorInnerInFrame (M := M) weight roughLap component t x =
      ∑ I : Comp, weight t x I * roughLap t x I * component t x I := by
  rfl

/-- Coordinate squared norm of the covariant derivative of a tensor.

The finite direction type `Dir` represents the traced derivative direction.
Any inverse-metric factors for that trace are included in `weight`. -/
def nablaTensorNormSqInFrame
    (weight : Time -> M -> Comp -> Real)
    (nablaComponent : Time -> M -> Dir -> Comp -> Real) :
    Time -> M -> Real :=
  fun t x =>
    ∑ a : Dir, ∑ I : Comp,
      weight t x I * nablaComponent t x a I * nablaComponent t x a I

@[simp] theorem nablaTensorNormSqInFrame_apply
    (weight : Time -> M -> Comp -> Real)
    (nablaComponent : Time -> M -> Dir -> Comp -> Real)
    (t : Time) (x : M) :
    nablaTensorNormSqInFrame (M := M) weight nablaComponent t x =
      ∑ a : Dir, ∑ I : Comp,
        weight t x I * nablaComponent t x a I * nablaComponent t x a I := by
  rfl

/-- The supplied scalar Laplacian of `|T|^2` realizes the coordinate Bochner
product expansion. This is the geometric bridge left explicit in this pass. -/
def ScalarLaplacianRealizesTensorNormBochnerInFrame
    (lapNormSq : Time -> M -> Real)
    (weight roughLap component : Time -> M -> Comp -> Real)
    (nablaComponent : Time -> M -> Dir -> Comp -> Real) : Prop :=
  forall (t : Time) (x : M),
    lapNormSq t x =
      (∑ I : Comp, 2 * (weight t x I * roughLap t x I * component t x I)) +
        (∑ a : Dir, ∑ I : Comp,
          2 * (weight t x I * nablaComponent t x a I * nablaComponent t x a I))

/-- Named Bochner product-rule conclusion for tensor norms. -/
def TensorNormBochnerComponentsInFrame
    (lapNormSq roughLapInner nablaNormSq : Time -> M -> Real) : Prop :=
  forall (t : Time) (x : M),
    lapNormSq t x = 2 * roughLapInner t x + 2 * nablaNormSq t x

/-- Finite-sum proof of the coordinate Bochner product rule. -/
theorem tensorNormBochnerComponentsInFrame_of_coordinate_expansion
    (lapNormSq : Time -> M -> Real)
    (weight roughLap component : Time -> M -> Comp -> Real)
    (nablaComponent : Time -> M -> Dir -> Comp -> Real)
    (h_lap : ScalarLaplacianRealizesTensorNormBochnerInFrame
      (M := M) lapNormSq weight roughLap component nablaComponent) :
    TensorNormBochnerComponentsInFrame
      lapNormSq
      (roughLapTensorInnerInFrame (M := M) weight roughLap component)
      (nablaTensorNormSqInFrame (M := M) weight nablaComponent) := by
  intro t x
  rw [h_lap t x]
  unfold roughLapTensorInnerInFrame nablaTensorNormSqInFrame
  let roughTerm : Comp -> Real :=
    fun I => weight t x I * roughLap t x I * component t x I
  let nablaTerm : Dir -> Comp -> Real :=
    fun a I => weight t x I * nablaComponent t x a I * nablaComponent t x a I
  change
      (∑ I : Comp, 2 * roughTerm I) +
          (∑ a : Dir, ∑ I : Comp, 2 * nablaTerm a I) =
        2 * (∑ I : Comp, roughTerm I) +
          2 * (∑ a : Dir, ∑ I : Comp, nablaTerm a I)
  have hrough :
      (∑ I : Comp, 2 * roughTerm I) = 2 * (∑ I : Comp, roughTerm I) := by
    rw [Finset.mul_sum]
  have hnabla :
      (∑ a : Dir, ∑ I : Comp, 2 * nablaTerm a I) =
        2 * (∑ a : Dir, ∑ I : Comp, nablaTerm a I) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  rw [hrough, hnabla]

/-- Consume the named Bochner product-rule conclusion. -/
theorem tensor_norm_laplacian_eq_of_bochner_components
    (lapNormSq roughLapInner nablaNormSq : Time -> M -> Real)
    (h : TensorNormBochnerComponentsInFrame lapNormSq roughLapInner nablaNormSq)
    (t : Time) (x : M) :
    lapNormSq t x = 2 * roughLapInner t x + 2 * nablaNormSq t x :=
  h t x

end GeneralTensorNorm

/-! ## Ricci-specific coordinate quantities -/

section RicciNorm

variable {Idx : Type*} [Fintype Idx]

/-- Components of Ricci with both indices raised:
`Ric^{ij} = g^{ia} g^{jb} Ric_ab`. -/
def raisedRicciComponentsInFrame
    (Ric : Time -> TwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Time -> M -> Idx -> Idx -> Real :=
  fun t x i j =>
    ∑ a : Idx, ∑ b : Idx,
      gInv t x i a * gInv t x j b * Ric t x (frame a x) (frame b x)

@[simp] theorem raisedRicciComponentsInFrame_apply
    (Ric : Time -> TwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) (i j : Idx) :
    raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j =
      ∑ a : Idx, ∑ b : Idx,
        gInv t x i a * gInv t x j b * Ric t x (frame a x) (frame b x) := by
  rfl

/-- Coordinate squared norm of Ricci:
`|Ric|^2 = Ric_ij Ric^{ij}`. -/
def ricciNormSqInFrame
    (Ric : Time -> TwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Time -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx,
      Ric t x (frame i x) (frame j x) *
        raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j

@[simp] theorem ricciNormSqInFrame_apply
    (Ric : Time -> TwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) :
    ricciNormSqInFrame (I := I) Ric gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        Ric t x (frame i x) (frame j x) *
          raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j := by
  rfl

/-- Coordinate inner product `<roughDelta Ric, Ric>`. -/
def roughLapRicciInnerInFrame
    (roughLapRic : Time -> M -> Idx -> Idx -> Real)
    (Ric : Time -> TwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Time -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx,
      roughLapRic t x i j *
        raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j

@[simp] theorem roughLapRicciInnerInFrame_apply
    (roughLapRic : Time -> M -> Idx -> Idx -> Real)
    (Ric : Time -> TwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) :
    roughLapRicciInnerInFrame (I := I) roughLapRic Ric gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        roughLapRic t x i j *
          raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j := by
  rfl

/-- Coordinate squared norm of `nabla Ric`:
`g^{ab} g^{ik} g^{jl} (nabla_a Ric_ij) (nabla_b Ric_kl)`. -/
def nablaRicciNormSqInFrame
    (nablaRic : Time -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : Time -> InverseMetricComponents M Idx) :
    Time -> M -> Real :=
  fun t x =>
    ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      gInv t x a b * gInv t x i k * gInv t x j l *
        nablaRic t x a i j * nablaRic t x b k l

@[simp] theorem nablaRicciNormSqInFrame_apply
    (nablaRic : Time -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : Time -> InverseMetricComponents M Idx)
    (t : Time) (x : M) :
    nablaRicciNormSqInFrame (M := M) nablaRic gInv t x =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv t x a b * gInv t x i k * gInv t x j l *
          nablaRic t x a i j * nablaRic t x b k l := by
  rfl

/-! ## `(0,2)` tensor norm product-rule layer -/

section Tensor02Product

variable [FiniteDimensional Real E]

private theorem tensor0S_curry_apply_cons_local
    {x : M} (s : ℕ)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (X : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A X) tail =
      A (Fin.cons X tail) := by
  change
    (((continuousMultilinearCurryLeftEquiv Real
        (fun _ : Fin (s + 1) => E) Real)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x) A)
        X)
        tail) =
      ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x) A)
        (Fin.cons X tail)
  rw [continuousMultilinearCurryLeftEquiv_apply]

private theorem fin_cons_vec2_eq_vec3
    {x : M} (X Y Z : TangentSpace I x) :
    Fin.cons X (vec2 (I := I) Y Z) =
      vec3 (I := I) X Y Z := by
  funext a
  fin_cases a <;> rfl

private theorem fin_cons_vec3_eq_vec4
    {x : M} (X Y Z W : TangentSpace I x) :
    Fin.cons X (vec3 (I := I) Y Z W) =
      vec4 (I := I) X Y Z W := by
  funext a
  fin_cases a <;> rfl

private theorem metricTraceInput_vec2_eq_vec4
    {x : M} (X Y Z W : TangentSpace I x) :
    metricTraceInput (I := I) X Y (vec2 (I := I) Z W) =
      vec4 (I := I) X Y Z W := by
  funext a
  fin_cases a <;> rfl

private theorem sum_six_rotate_two
    {Idx A : Type*} [Fintype Idx] [AddCommMonoid A]
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> A) :
    (∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        F a b i j k l) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, ∑ b : Idx,
        F a b i j k l := by
  calc
    (∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        F a b i j k l)
        =
      ∑ a : Idx, ∑ i : Idx, ∑ b : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        F a b i j k l := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ a : Idx, ∑ b : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        F a b i j k l := by
          rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ b : Idx, ∑ k : Idx, ∑ l : Idx,
        F a b i j k l := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx, ∑ k : Idx, ∑ l : Idx,
        F a b i j k l := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ k : Idx, ∑ b : Idx, ∑ l : Idx,
        F a b i j k l := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ a : Idx, ∑ b : Idx, ∑ l : Idx,
        F a b i j k l := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ a : Idx, ∑ l : Idx, ∑ b : Idx,
        F a b i j k l := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, ∑ b : Idx,
        F a b i j k l := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_comm]

private theorem sum_trace_tensor02_rough
    {Idx : Type*} [Fintype Idx]
    (G A : Idx -> Idx -> Real)
    (B : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a : Idx, ∑ b : Idx,
        G a b *
          (∑ i : Idx, ∑ j : Idx,
            B a b i j *
              (∑ k : Idx, ∑ l : Idx, G i k * G j l * A k l))) =
      ∑ i : Idx, ∑ j : Idx,
        (∑ a : Idx, ∑ b : Idx, G a b * B a b i j) *
          (∑ k : Idx, ∑ l : Idx, G i k * G j l * A k l) := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [sum_six_rotate_two]
  simp [mul_left_comm, mul_comm]

private theorem sum_trace_tensor02_nabla
    {Idx : Type*} [Fintype Idx]
    (G : Idx -> Idx -> Real)
    (B : Idx -> Idx -> Idx -> Real) :
    (∑ a : Idx, ∑ b : Idx,
        G a b *
          (∑ i : Idx, ∑ j : Idx,
            B a i j *
              (∑ k : Idx, ∑ l : Idx, G i k * G j l * B b k l))) =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        G a b * G i k * G j l * B a i j * B b k l := by
  simp_rw [Finset.mul_sum]
  simp [mul_left_comm, mul_comm]

/-- Coordinate expression for `<roughDelta A, A>` for a `(0,2)` tensor. -/
def tensor02RoughInnerCoord
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (A roughA : Tensor02At (I := I) x) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    roughA (vec2 (I := I) (basis i) (basis j)) *
      (∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (vec2 (I := I) (basis k) (basis l)))

/-- Coordinate expression for `|nabla A|^2` for a `(0,2)` tensor. -/
def tensor02NablaNormCoord
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Real :=
  ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
    gInv a b * gInv i k * gInv j l *
      nablaA (vec3 (I := I) (basis a) (basis i) (basis j)) *
        nablaA (vec3 (I := I) (basis b) (basis k) (basis l))

/-- Freeze the derivative slot of a `(0,3)` tensor, leaving a `(0,2)` tensor. -/
def tensor02FreezeNabla
    {x : M}
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (X : TangentSpace I x) : Tensor02At (I := I) x :=
  freezeLastTwo0S3 (I := I) nablaA X

@[simp] theorem tensor02FreezeNabla_apply
    {x : M}
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (X Y Z : TangentSpace I x) :
    tensor02FreezeNabla (I := I) nablaA X (vec2 (I := I) Y Z) =
      nablaA (vec3 (I := I) X Y Z) := by
  exact freezeLastTwo0S3_apply (I := I) nablaA X Y Z

private theorem tensor02FreezeNabla_eq_curry
    {x : M}
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (X : TangentSpace I x) :
    tensor02FreezeNabla (I := I) nablaA X =
      tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x nablaA X := by
  ext v
  have hv : v = vec2 (I := I) (v 0) (v 1) := by
    funext a
    fin_cases a <;> rfl
  rw [hv, tensor02FreezeNabla_apply, tensor0S_curry_apply_cons_local]
  congr 1
  exact (fin_cons_vec2_eq_vec3 (I := I) X (v 0) (v 1)).symm

/-- Metric compatibility lifted to the induced inner product on `(0,2)` tensor
fibers.

This is the invariant producer needed for the `(0,2)` Bochner product rule.
The currently exposed metric-compatibility API applies to tangent-vector slots;
this theorem records the missing bridge to the induced tensor metric. -/
theorem tensor02_inner_extDerivFun_eq_inner_nabla
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (nablaA nablaB :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 2 cov A nablaA)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 2 cov B nablaB)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    extDerivFun (I := I)
      (fun y : M => inner02 (I := I) g y (A y) (B y)) x (X x) =
      inner02 (I := I) g x
        (tensor02FreezeNabla (I := I) (nablaA x) (X x)) (B x) +
        inner02 (I := I) g x (A x)
          (tensor02FreezeNabla (I := I) (nablaB x) (X x)) := by
  have h :=
    Tensor0SBundle.inner0S_two_metricCompatible_extDerivFun (I := I)
      cov g hmc A B nablaA nablaB hA hB X x
  have hfreezeA :
      tensor02FreezeNabla (I := I) (nablaA x) (X x) =
        tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
          (nablaA x) (X x) :=
    tensor02FreezeNabla_eq_curry (I := I) (nablaA x) (X x)
  have hfreezeB :
      tensor02FreezeNabla (I := I) (nablaB x) (X x) =
        tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
          (nablaB x) (X x) :=
    tensor02FreezeNabla_eq_curry (I := I) (nablaB x) (X x)
  simpa [inner02, hfreezeA, hfreezeB] using h

/-- Freeze the two derivative slots of a `(0,4)` tensor, leaving a `(0,2)` tensor. -/
def tensor02FreezeNabla2
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (X Y : TangentSpace I x) : Tensor02At (I := I) x :=
  freezeLastTwo0S3 (I := I)
    (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 3 x nabla2A X) Y

@[simp] theorem tensor02FreezeNabla2_apply
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (X Y Z W : TangentSpace I x) :
    tensor02FreezeNabla2 (I := I) nabla2A X Y (vec2 (I := I) Z W) =
      nabla2A (vec4 (I := I) X Y Z W) := by
  unfold tensor02FreezeNabla2
  rw [freezeLastTwo0S3_apply]
  change Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 3 x nabla2A X)
      (vec3 (I := I) Y Z W) =
    Tensor0SSpace.toModel nabla2A (vec4 (I := I) X Y Z W)
  rw [TensorMultilinear.tensor0S_curry_apply_eval]
  congr 1
  exact fin_cons_vec3_eq_vec4 (I := I) X Y Z W

/-- Pointwise Hessian product rule for the norm square of a `(0,2)` tensor,
evaluated on a basis. -/
def Tensor02NormHessianProductInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (A : Tensor02At (I := I) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (normSecond : Tensor02At (I := I) x) : Prop :=
  ∀ i j : Idx,
    normSecond (vec2 (I := I) (basis i) (basis j)) =
      (2 : Real) *
        (tensor02RoughInnerCoord (I := I) basis gInv A
            (tensor02FreezeNabla2 (I := I) nabla2A (basis i) (basis j)) +
          tensor02RoughInnerCoord (I := I) basis gInv
            (tensor02FreezeNabla (I := I) nablaA (basis j))
            (tensor02FreezeNabla (I := I) nablaA (basis i)))

/-- The traced second-product rule for the norm of a `(0,2)` tensor.

This is the precise tensor Bochner product-rule frontier:
`tr_g Hess |A|^2 = 2 <roughDelta A, A> + 2 |nabla A|^2`. -/
def Tensor02NormSecondProductInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (A roughA : Tensor02At (I := I) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond : Tensor02At (I := I) x) : Prop :=
  metricTrace0S2InBasis (I := I) basis gInv normSecond Fin.elim0 =
    (2 : Real) *
      (tensor02RoughInnerCoord (I := I) basis gInv A roughA +
        tensor02NablaNormCoord (I := I) basis gInv nablaA)

set_option maxHeartbeats 800000 in
/-- Trace the pointwise `(0,2)` norm Hessian product rule. -/
theorem Tensor02NormSecondProductInBasis.of_hessian_product
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (A roughA : Tensor02At (I := I) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (normSecond : Tensor02At (I := I) x)
    (hprod : Tensor02NormHessianProductInBasis (I := I) basis gInv A nablaA
      nabla2A normSecond)
    (hrough : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv
      (s := 2) roughA nabla2A) :
    Tensor02NormSecondProductInBasis (I := I) basis gInv A roughA nablaA
      normSecond := by
  classical
  unfold Tensor02NormSecondProductInBasis metricTrace0S2InBasis
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          normSecond (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0))
        =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * normSecond (vec2 (I := I) (basis i) (basis j)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          have hinput :
              metricTraceInput (I := I) (basis i) (basis j) Fin.elim0 =
                vec2 (I := I) (basis i) (basis j) := by
            funext a
            fin_cases a
            · simp [metricTraceInput, vec2, RicciFlower.Curvature.vec2]
            · rfl
          rw [hinput]
    _ =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * ((2 : Real) *
          (tensor02RoughInnerCoord (I := I) basis gInv A
              (tensor02FreezeNabla2 (I := I) nabla2A (basis i) (basis j)) +
            tensor02RoughInnerCoord (I := I) basis gInv
              (tensor02FreezeNabla (I := I) nablaA (basis j))
              (tensor02FreezeNabla (I := I) nablaA (basis i)))) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [hprod i j]
    _ =
      (2 : Real) *
        (tensor02RoughInnerCoord (I := I) basis gInv A roughA +
          tensor02NablaNormCoord (I := I) basis gInv nablaA) := by
          have hrough_eval : ∀ p q : Idx,
              roughA (vec2 (I := I) (basis p) (basis q)) =
                ∑ i : Idx, ∑ j : Idx,
                  gInv i j *
                    tensor02FreezeNabla2 (I := I) nabla2A (basis i) (basis j)
                      (vec2 (I := I) (basis p) (basis q)) := by
            intro p q
            rw [hrough (vec2 (I := I) (basis p) (basis q))]
            unfold roughLap0SAt metricTrace0S2InBasis
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            congr 1
            rw [tensor02FreezeNabla2_apply]
            congr 1
            exact metricTraceInput_vec2_eq_vec4 (I := I)
              (basis i) (basis j) (basis p) (basis q)
          let R : Real :=
            ∑ i : Idx, ∑ j : Idx,
              gInv i j *
                tensor02RoughInnerCoord (I := I) basis gInv A
                  (tensor02FreezeNabla2 (I := I) nabla2A (basis i) (basis j))
          let N : Real :=
            ∑ i : Idx, ∑ j : Idx,
              gInv i j *
                tensor02RoughInnerCoord (I := I) basis gInv
                  (tensor02FreezeNabla (I := I) nablaA (basis j))
                  (tensor02FreezeNabla (I := I) nablaA (basis i))
          have hR :
              R = tensor02RoughInnerCoord (I := I) basis gInv A roughA := by
            unfold R tensor02RoughInnerCoord
            simpa [hrough_eval] using
              (sum_trace_tensor02_rough
                (G := gInv)
                (A := fun k l => A (vec2 (I := I) (basis k) (basis l)))
                (B := fun a b i j =>
                  tensor02FreezeNabla2 (I := I) nabla2A (basis a) (basis b)
                    (vec2 (I := I) (basis i) (basis j))))
          have hN :
              N = tensor02NablaNormCoord (I := I) basis gInv nablaA := by
            unfold N tensor02RoughInnerCoord tensor02NablaNormCoord
            simpa [tensor02FreezeNabla_apply] using
              (sum_trace_tensor02_nabla
                (G := gInv)
                (B := fun a i j =>
                  nablaA (vec3 (I := I) (basis a) (basis i) (basis j))))
          calc
            (∑ i : Idx, ∑ j : Idx,
                gInv i j *
                  (2 *
                    (tensor02RoughInnerCoord (I := I) basis gInv A
                        (tensor02FreezeNabla2 (I := I) nabla2A (basis i) (basis j)) +
                      tensor02RoughInnerCoord (I := I) basis gInv
                        (tensor02FreezeNabla (I := I) nablaA (basis j))
                        (tensor02FreezeNabla (I := I) nablaA (basis i)))))
                = (2 : Real) * (R + N) := by
                  unfold R N
                  simp_rw [mul_add, Finset.sum_add_distrib]
                  simp [Finset.mul_sum, mul_left_comm]
            _ = (2 : Real) *
                (tensor02RoughInnerCoord (I := I) basis gInv A roughA +
                  tensor02NablaNormCoord (I := I) basis gInv nablaA) := by
                  rw [hR, hN]

/-- Product-rule conclusion for the scalar Laplacian of a `(0,2)` tensor norm. -/
def Tensor02NormProductRuleInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (lapNormSq : Real)
    (A roughA : Tensor02At (I := I) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  lapNormSq =
    2 * tensor02RoughInnerCoord (I := I) basis gInv A roughA +
      2 * tensor02NablaNormCoord (I := I) basis gInv nablaA

/-- The scalar trace realization and the traced second-product rule imply the
coordinate product-rule conclusion for a `(0,2)` tensor norm. -/
theorem tensor02_norm_product_rule_of_second_product
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (f : M -> Real)
    (A roughA : Tensor02At (I := I) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond : Tensor02At (I := I) x)
    (hlap : ScalarLaplacianRealizesTraceAtInBasis (I := I) cov g basis gInv f normSecond)
    (hsecond : Tensor02NormSecondProductInBasis (I := I) basis gInv A roughA
      nablaA normSecond) :
    Tensor02NormProductRuleInBasis (I := I) basis gInv
      (laplacian (I := I) cov g f x) A roughA nablaA := by
  unfold Tensor02NormProductRuleInBasis Tensor02NormSecondProductInBasis
    ScalarLaplacianRealizesTraceAtInBasis at *
  rw [hlap, hsecond]
  ring

end Tensor02Product

/-- Exact coordinate expansion of the scalar Laplacian of `|Ric|^2`.

This is the geometric Bochner product-rule input for Lemma 6.7.  It is kept as
the single explicit frontier: proving it should come from metric compatibility
and the tensor norm product rule, not from Christoffel expansion. -/
def RicciNormScalarLaplacianExpansionInFrame
    (ricciNormLap : Time -> M -> Real)
    (roughLapRic : Time -> M -> Idx -> Idx -> Real)
    (Ric : Time -> TwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRic : Time -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Time) (x : M),
    ricciNormLap t x =
      2 * (∑ i : Idx, ∑ j : Idx,
        roughLapRic t x i j *
          raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j) +
        2 * (∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx,
          ∑ k : Idx, ∑ l : Idx,
            gInv t x a b * gInv t x i k * gInv t x j l *
              nablaRic t x a i j * nablaRic t x b k l)

section Tensor02ProductProducer

variable [FiniteDimensional Real E]

/-- Produce the Ricci-norm scalar-Laplacian expansion from a `(0,2)` tensor
norm product rule and component identifications.

The tensor field `A` is the bundled `(0,2)` realization of the Ricci tensor in
the chosen frame; `roughA` and `nablaA` realize the rough Laplacian and first
covariant derivative components used by the formula. -/
theorem ricciNormScalarLaplacianExpansionInFrame_of_tensor02_product_rule
    (ricciNormLap : Time -> M -> Real)
    (roughLapRic : Time -> M -> Idx -> Idx -> Real)
    (Ric : Time -> TwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRic : Time -> M -> Idx -> Idx -> Idx -> Real)
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (A roughA : Tensor02Field (I := I) (M := M) Time)
    (nablaA : Time -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond : Tensor02Field (I := I) (M := M) Time)
    (hframe : forall x i, basis x i = frame i x)
    (hlapTrace : forall t x,
      ricciNormLap t x =
        metricTrace0S2InBasis (I := I) (basis x) (gInv t x)
          (normSecond t x) Fin.elim0)
    (hsecond : forall t x,
      Tensor02NormSecondProductInBasis (I := I) (basis x) (gInv t x)
        (A t x) (roughA t x) (nablaA t x) (normSecond t x))
    (hAComp : forall t x i j,
      A t x (vec2 (I := I) (frame i x) (frame j x)) =
        Ric t x (frame i x) (frame j x))
    (hroughComp : forall t x i j,
      roughA t x (vec2 (I := I) (frame i x) (frame j x)) =
        roughLapRic t x i j)
    (hnablaComp : forall t x a i j,
      nablaA t x (vec3 (I := I) (frame a x) (frame i x) (frame j x)) =
        nablaRic t x a i j) :
    RicciNormScalarLaplacianExpansionInFrame
      (I := I) ricciNormLap roughLapRic Ric gInv frame nablaRic := by
  classical
  intro t x
  have hprod :
      ricciNormLap t x =
        2 * tensor02RoughInnerCoord (I := I) (basis x) (gInv t x)
            (A t x) (roughA t x) +
          2 * tensor02NablaNormCoord (I := I) (basis x) (gInv t x)
            (nablaA t x) := by
    rw [hlapTrace t x]
    rw [hsecond t x]
    ring
  have hrough :
      tensor02RoughInnerCoord (I := I) (basis x) (gInv t x)
          (A t x) (roughA t x) =
        ∑ i : Idx, ∑ j : Idx,
          roughLapRic t x i j *
            raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j := by
    unfold tensor02RoughInnerCoord raisedRicciComponentsInFrame
    simp_rw [hframe]
    simp_rw [hAComp]
    simp_rw [hroughComp]
  have hnabla :
      tensor02NablaNormCoord (I := I) (basis x) (gInv t x) (nablaA t x) =
        ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv t x a b * gInv t x i k * gInv t x j l *
            nablaRic t x a i j * nablaRic t x b k l := by
    unfold tensor02NablaNormCoord
    simp_rw [hframe]
    simp_rw [hnablaComp]
  rw [hprod, hrough, hnabla]

end Tensor02ProductProducer

/-- The cubic curvature-Ricci-Ricci reaction
`R_ikjl Ric^{ij} Ric^{kl}` in the frame convention fixed in
`Curvature.lean`. -/
def curvRicciRicciReactionInFrame
    (Riemann04 : Time -> FourTensorField (I := I) (M := M))
    (RicRaised : Time -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Time -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      Riemann04 t x (frame i x) (frame k x) (frame j x) (frame l x) *
        RicRaised t x i j * RicRaised t x k l

@[simp] theorem curvRicciRicciReactionInFrame_apply
    (Riemann04 : Time -> FourTensorField (I := I) (M := M))
    (RicRaised : Time -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) :
    curvRicciRicciReactionInFrame (I := I) Riemann04 RicRaised frame t x =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        Riemann04 t x (frame i x) (frame k x) (frame j x) (frame l x) *
          RicRaised t x i j * RicRaised t x k l := by
  rfl

/-- Time-derivative component identity for the Ricci norm.

This is the point at which the inverse-metric variation terms and the
`-2 Ric_i^k Ric_kj` part of Ricci evolution are assumed to have cancelled. -/
def RicciNormTimeDerivativeComponentsInFrame
    (ricciNormDt roughLapInner reaction : Time -> M -> Real) : Prop :=
  forall (t : Time) (x : M),
    ricciNormDt t x = 2 * roughLapInner t x + 4 * reaction t x

/-- Laplacian component identity for the Ricci norm, i.e. the Bochner product
rule specialized to Ricci. -/
def RicciNormLaplacianComponentsInFrame
    (ricciNormLap roughLapInner nablaRicNormSq : Time -> M -> Real) : Prop :=
  forall (t : Time) (x : M),
    ricciNormLap t x = 2 * roughLapInner t x + 2 * nablaRicNormSq t x

/-- Ricci-specific Bochner producer from the exact scalar-Laplacian expansion.

The conclusion is the reusable component form
`Δ |Ric|² = 2 <Δ Ric, Ric> + 2 |∇ Ric|²`. -/
theorem ricciNormLaplacianComponentsInFrame_of_normSq_laplacian_expansion
    (ricciNormLap : Time -> M -> Real)
    (roughLapRic : Time -> M -> Idx -> Idx -> Real)
    (Ric : Time -> TwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRic : Time -> M -> Idx -> Idx -> Idx -> Real)
    (h_lap : RicciNormScalarLaplacianExpansionInFrame
      (I := I) ricciNormLap roughLapRic Ric gInv frame nablaRic) :
    RicciNormLaplacianComponentsInFrame
      ricciNormLap
      (roughLapRicciInnerInFrame (I := I) roughLapRic Ric gInv frame)
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv) := by
  intro t x
  rw [h_lap t x]
  rfl

/-- Lemma 6.7 in coordinate-component form:
`(partial_t - Delta)|Ric|^2 = -2 |nabla Ric|^2 + 4 R_ikjl Ric^ij Ric^kl`. -/
theorem ricci_norm_heat_eq_of_bochner_components
    (ricciNormDt ricciNormLap roughLapInner nablaRicNormSq reaction : Time -> M -> Real)
    (h_dt : RicciNormTimeDerivativeComponentsInFrame
      ricciNormDt roughLapInner reaction)
    (h_lap : RicciNormLaplacianComponentsInFrame
      ricciNormLap roughLapInner nablaRicNormSq) :
    forall (t : Time) (x : M),
      ricciNormDt t x - ricciNormLap t x =
        -2 * nablaRicNormSq t x + 4 * reaction t x := by
  intro t x
  rw [h_dt t x, h_lap t x]
  ring

end RicciNorm

end

end Realized
end RicciFlower

