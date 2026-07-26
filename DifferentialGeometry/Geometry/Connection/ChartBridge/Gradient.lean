import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension

/-!
# Bridge between the chart-local gradient and the metric dual of the differential

This file provides the bridge between the concrete chart-local gradient `gradFun g f`
defined in `Geometry.Gradient` and the abstract metric dual of the differential
`mfderiv I 𝓘(ℝ, ℝ) f x` of a smooth scalar function `f : M → ℝ`.

The pointwise gradient `gradFun g f x : TangentSpace I x` is by construction the metric
sharp of the linear functional `(mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap`. Equivalently, it is
characterised by the duality identity
$$
  g_x(\mathrm{grad}_g f, v) = (\mathrm{d}f)_x(v) \qquad \text{for every } v \in T_x M.
$$

The role of this file is to record the bridge in several equivalent forms suitable for
downstream consumers:

* `gradFun_metricDual` — the pointwise duality identity in the form `g.inner x grad v =
  mfderiv f x v`, restated for callers who think in terms of the differential rather than
  the abstract sharp.
* `metricFlat_gradFun_apply` — the operator-level identity `metricFlat g (gradFun g f) x =
  mfderiv f x` (after the `NormedSpace.fromTangentSpace` identification), expressing that
  applying the metric flat to the gradient recovers the differential as a cotangent
  section.
* `gradFun_eq_metricSharp_mfderiv` — the definitional unfolding to the metric sharp.
* `gradFun_zero`, `gradFun_const`, `gradFun_add`, `gradFun_smul` — basic linearity and
  constants.
* `gradFun_contMDiff_total_section` — the smoothness lemma re-exported under the bridge
  namespace for downstream callers.

All identities are pointwise; no covariant derivative or curvature appears at this stage.
The Hessian bridge (where the Levi-Civita connection enters as `∇ (gradFun g f)`) is built
on top of this file.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- The connection-layer and chart-local gradient functions are the same
pointwise metric dual of the differential. -/
theorem gradient_eq_gradFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    gradientFun (I := I) g f x = gradFun (I := I) g f x := rfl

variable [InnerProductSpace ℝ E] [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]

/-- **Metric duality of the gradient with the differential.** For every smooth scalar
function `f : M → ℝ` and every tangent vector `v : T_x M`,
`g.inner x (gradFun g f x) v = mfderiv I 𝓘(ℝ, ℝ) f x v`.
This is the defining characterisation of the gradient as the metric sharp of the
differential `df`. -/
theorem gradFun_metricDual
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x (gradFun (I := I) g f x) v = mfderiv I 𝓘(ℝ, ℝ) f x v :=
  inner_gradFun (I := I) g f x v

/-- Symmetric form of `gradFun_metricDual`: the gradient appears in the second argument
of the inner product. -/
theorem gradFun_metricDual_right
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x v (gradFun (I := I) g f x) = mfderiv I 𝓘(ℝ, ℝ) f x v :=
  inner_gradFun_right (I := I) g f x v

/-- Operator form: the metric flat map sends the gradient to the differential. -/
theorem metricFlatMap_gradFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    metricFlatMap (I := I) g x (gradFun (I := I) g f x) =
      (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap := by
  ext v
  rw [metricFlatMap_apply]
  exact gradFun_metricDual (I := I) g f x v

/-- Definitional unfolding: the gradient is the metric sharp of the differential viewed as
a linear functional on the tangent space. -/
lemma gradFun_eq_metricSharp_mfderiv
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    gradFun (I := I) g f x =
      metricSharp (I := I) g x (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap := rfl

/-- Conversely, the gradient is the unique tangent vector whose metric inner product with
every test vector recovers the differential. -/
theorem gradFun_unique
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) {x : M}
    {w : TangentSpace I x}
    (hw : ∀ v : TangentSpace I x, g.inner x w v = mfderiv I 𝓘(ℝ, ℝ) f x v) :
    w = gradFun (I := I) g f x := by
  apply metricFlatLinear_injective (I := I) g x
  ext v
  rw [metricFlatLinear_apply, metricFlatLinear_apply]
  rw [hw v]
  exact (gradFun_metricDual (I := I) g f x v).symm

/-- Pointwise: `metricFlat g (gradFun g f)` agrees with the cotangent-section
representation of the differential of `f`. -/
theorem metricFlat_gradFun_apply
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    metricFlat g (fun y => gradFun (I := I) g f y) x v =
      mfderiv I 𝓘(ℝ, ℝ) f x v := by
  change g.inner x (gradFun (I := I) g f x) v = _
  exact gradFun_metricDual (I := I) g f x v

/-- Pointwise: `metricFlat g (gradFun g f) x` agrees with `extDerivFun f x` (Mathlib's
exterior derivative of a scalar function as a cotangent-bundle section). The two
continuous linear maps from `TangentSpace I x` to `ℝ` are equal as elements of the
cotangent fibre. -/
theorem metricFlat_gradFun_eq_extDerivFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    metricFlat g (fun y => gradFun (I := I) g f y) x = extDerivFun (I := I) f x := by
  ext v
  rw [metricFlat_gradFun_apply (I := I) g f x v]
  rfl

/-- The gradient of a constant function vanishes pointwise. -/
@[simp] lemma gradFun_const
    (g : SmoothRiemannianMetric I M) (c : ℝ) (x : M) :
    gradFun (I := I) g (fun _ : M => c) x = (0 : TangentSpace I x) := by
  apply gradFun_eq_zero_of_mfderiv_eq_zero (I := I) g (f := fun _ : M => c)
  exact mfderiv_const

/-- The gradient of the zero function vanishes pointwise. -/
@[simp] lemma gradFun_zero
    (g : SmoothRiemannianMetric I M) (x : M) :
    gradFun (I := I) g (fun _ : M => (0 : ℝ)) x = (0 : TangentSpace I x) :=
  gradFun_const (I := I) g 0 x

/-- Pointwise: the metric duality, restated through `extDerivFun` (which is genuinely
`ℝ`-valued and additive). -/
lemma gradFun_metricDual_extDerivFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x (gradFun (I := I) g f x) v = extDerivFun (I := I) f x v := by
  rw [gradFun_metricDual (I := I) g f x v]
  rfl

/-- The gradient of a sum of differentiable scalars at a point is the sum of gradients. -/
theorem gradFun_add
    (g : SmoothRiemannianMetric I M) {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x) :
    gradFun (I := I) g (fun y => f y + h y) x =
      gradFun (I := I) g f x + gradFun (I := I) g h x := by
  refine (gradFun_unique (I := I) g (fun y => f y + h y)
    (w := gradFun (I := I) g f x + gradFun (I := I) g h x) ?_).symm
  intro v
  have h_left : g.inner x (gradFun (I := I) g f x + gradFun (I := I) g h x) v =
      extDerivFun (I := I) f x v + extDerivFun (I := I) h x v := by
    rw [show g.inner x (gradFun (I := I) g f x + gradFun (I := I) g h x) v =
          g.inner x (gradFun (I := I) g f x) v + g.inner x (gradFun (I := I) g h x) v from
        by rw [map_add, ContinuousLinearMap.add_apply]]
    rw [gradFun_metricDual_extDerivFun (I := I) g f x v,
        gradFun_metricDual_extDerivFun (I := I) g h x v]
  have h_right :
      (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => f y + h y) x v : ℝ) =
        extDerivFun (I := I) f x v + extDerivFun (I := I) h x v := by
    have hsum : (fun y : M => f y + h y) = f + h := rfl
    change extDerivFun (I := I) (fun y : M => f y + h y) x v = _
    rw [hsum, extDerivFun_add hf hh, ContinuousLinearMap.add_apply]
  rw [h_left, ← h_right]

/-- The gradient of a finite sum of functions differentiable at a point is
the finite sum of their gradients at that point. -/
theorem gradFun_finset
    (g : SmoothRiemannianMetric I M) {ι : Type*} (s : Finset ι)
    (f : ι → M → ℝ) {x : M}
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x) :
    gradFun (I := I) g (s.sum f) x =
      s.sum (fun i => gradFun (I := I) g (f i) x) := by
  classical
  have hsum_diff : ∀ t : Finset ι,
      (∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x) →
      MDifferentiableAt I 𝓘(ℝ, ℝ) (t.sum f) x := by
    intro t ht
    induction t using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using
          (mdifferentiableAt_const :
            MDifferentiableAt I 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) x)
    | @insert i t hit ih =>
        have hi : MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x :=
          ht i (Finset.mem_insert_self i t)
        have htail : ∀ j ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f j) x :=
          fun j hj => ht j (Finset.mem_insert_of_mem hj)
        rw [Finset.sum_insert hit]
        exact hi.add (ih htail)
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using gradFun_zero (I := I) g x
  | @insert i s his ih =>
      have hi : MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x :=
        hf i (Finset.mem_insert_self i s)
      have hs : ∀ j ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (f j) x :=
        fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hsum : MDifferentiableAt I 𝓘(ℝ, ℝ) (s.sum f) x :=
        hsum_diff s hs
      rw [Finset.sum_insert his, Finset.sum_insert his]
      change gradFun (I := I) g (fun y => f i y + s.sum f y) x = _
      rw [gradFun_add (I := I) g hi hsum, ih hs]

/-- The gradient is `ℝ`-linear in `f`: a scalar multiple `c • f` of a differentiable
function `f : M → ℝ` has gradient `c • gradFun g f`.

Stated using `Pi.smul`-shape `c • f` (the canonical Mathlib form for `mfderiv` linearity).
For the pointwise-product form `(fun y => c * f y)`, the user can apply `funext` to rewrite
the function to the `c • f` form. -/
theorem gradFun_const_smul
    (g : SmoothRiemannianMetric I M) (c : ℝ) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    gradFun (I := I) g (c • f) x = c • gradFun (I := I) g f x := by
  refine (gradFun_unique (I := I) g (c • f)
    (w := c • gradFun (I := I) g f x) ?_).symm
  intro v
  have h_left : g.inner x (c • gradFun (I := I) g f x) v =
      c * extDerivFun (I := I) f x v := by
    rw [show g.inner x (c • gradFun (I := I) g f x) v =
          c * g.inner x (gradFun (I := I) g f x) v from
        by rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]]
    rw [gradFun_metricDual_extDerivFun (I := I) g f x v]
  have h_right : (mfderiv I 𝓘(ℝ, ℝ) (c • f) x v : ℝ) =
      c * extDerivFun (I := I) f x v := by
    have h := const_smul_mfderiv (I := I) (𝕜 := ℝ) (f := f) (z := x) hf c
    change extDerivFun (I := I) (c • f) x v = c * extDerivFun (I := I) f x v
    suffices hsmul : extDerivFun (I := I) (c • f) x = c • extDerivFun (I := I) f x by
      rw [hsmul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    change (NormedSpace.fromTangentSpace ((c • f) x)).toContinuousLinearMap ∘L
            (mfderiv I 𝓘(ℝ, ℝ) (c • f) x) =
          c • ((NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap ∘L
            mfderiv I 𝓘(ℝ, ℝ) f x)
    rw [h]
    rfl
  rw [h_left, ← h_right]

/-- The gradient of the negation of a differentiable scalar is the negation
of its gradient. -/
theorem gradFun_neg
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    gradFun (I := I) g (fun y => -f y) x =
      -gradFun (I := I) g f x := by
  have hneg : (fun y : M => -f y) = (-1 : ℝ) • f := by
    funext y
    simp only [Pi.smul_apply, neg_smul, one_smul]
  rw [hneg, gradFun_const_smul (I := I) g (-1 : ℝ) hf]
  simp only [neg_smul, one_smul]

/-- The gradient of a difference of differentiable scalars is the difference
of their gradients. -/
theorem gradFun_sub
    (g : SmoothRiemannianMetric I M) {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x) :
    gradFun (I := I) g (fun y => f y - h y) x =
      gradFun (I := I) g f x - gradFun (I := I) g h x := by
  change gradFun (I := I) g (fun y => f y + -h y) x = _
  calc
    gradFun (I := I) g (fun y => f y + -h y) x =
        gradFun (I := I) g f x +
          gradFun (I := I) g (fun y => -h y) x :=
      gradFun_add (I := I) g hf hh.neg
    _ = gradFun (I := I) g f x - gradFun (I := I) g h x := by
      rw [gradFun_neg (I := I) g hh]
      rw [sub_eq_add_neg]

/-- Under `[I.Boundaryless]`, the gradient of a smooth scalar function is smooth as a
total-space section of the tangent bundle. -/
theorem gradFun_contMDiff_total_section [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x)) :=
  gradFun_contMDiff_total (I := I) g hf

end Connection
end Integral
end DifferentialGeometry
