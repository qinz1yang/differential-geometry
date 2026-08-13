import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator

theorem gradient_eq_gradFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    gradientFun (I := I) g f x = gradFun (I := I) g f x := rfl

theorem gradFun_metricDual
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x (gradFun (I := I) g f x) v = mfderiv I 𝓘(ℝ, ℝ) f x v :=
  inner_gradFun (I := I) g f x v

theorem gradFun_metricDual_right
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x v (gradFun (I := I) g f x) = mfderiv I 𝓘(ℝ, ℝ) f x v :=
  inner_gradFun_right (I := I) g f x v

theorem metricFlatMap_gradFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    metricFlatMap (I := I) g x (gradFun (I := I) g f x) =
      (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap := by
  ext v
  rw [metricFlatMap_apply]
  exact gradFun_metricDual (I := I) g f x v

lemma gradFun_eq_metricSharp_mfderiv
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    gradFun (I := I) g f x =
      metricSharp (I := I) g x (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap := rfl

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

theorem metricFlat_gradFun_apply
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    metricFlat g (fun y => gradFun (I := I) g f y) x v =
      mfderiv I 𝓘(ℝ, ℝ) f x v := by
  change g.inner x (gradFun (I := I) g f x) v = _
  exact gradFun_metricDual (I := I) g f x v

theorem metricFlat_gradFun_eq_extDerivFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    metricFlat g (fun y => gradFun (I := I) g f y) x = extDerivFun (I := I) f x := by
  ext v
  rw [metricFlat_gradFun_apply (I := I) g f x v]
  rfl

@[simp] lemma gradFun_const
    (g : SmoothRiemannianMetric I M) (c : ℝ) (x : M) :
    gradFun (I := I) g (fun _ : M => c) x = (0 : TangentSpace I x) := by
  apply gradFun_eq_zero_of_mfderiv_eq_zero (I := I) g (f := fun _ : M => c)
  exact mfderiv_const

@[simp] lemma gradFun_zero
    (g : SmoothRiemannianMetric I M) (x : M) :
    gradFun (I := I) g (fun _ : M => (0 : ℝ)) x = (0 : TangentSpace I x) :=
  gradFun_const (I := I) g 0 x

lemma gradFun_metricDual_extDerivFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x (gradFun (I := I) g f x) v = extDerivFun (I := I) f x v := by
  rw [gradFun_metricDual (I := I) g f x v]
  rfl

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

theorem gradFun_contMDiff_total_section [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x)) :=
  gradFun_contMDiff_total (I := I) g hf

end Connection
end Geometry
end DifferentialGeometry
