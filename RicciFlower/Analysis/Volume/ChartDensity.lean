import RicciFlower.Metric.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Chart-local volume density from a Riemannian metric

Given a smooth `ContMDiffRiemannianMetric` `g` on the tangent bundle of a manifold `M`
and a base point `x₀ : M`, we construct a chart-local positive smooth density on the
domain of the base chart at `x₀`, and the associated chart-local Borel measure on `M`.

## Overview

Inside the open set `triv.baseSet = (chartAt H x₀).source`, we build a pointwise basis of
the tangent bundle by transporting a fixed algebraic basis of the model space `E` through
the tangent-bundle trivialization centred at `x₀`. The Gram matrix of this basis under
`g` is symmetric positive-definite, so its determinant is strictly positive and its
square root gives a positive smooth density on the chart domain.

The chart-local measure is obtained by weighting a chosen reference measure on the model
space `E` by the pullback of this density through the extended chart, and then pushing
forward to `M`.

## Main definitions

* `chartBasisVec g x₀ i` : the tangent-bundle section over `triv.baseSet` whose value
  at `x` is the image of the `i`-th model-space basis vector under the inverse of the
  tangent trivialization centred at `x₀`.
* `chartGramMatrix g x₀ x` : the Gram matrix at `x` of the family `chartBasisVec g x₀ •`
  under the inner product `g.inner x`.
* `chartDensity g x₀ x` : the positive density `√(det (chartGramMatrix g x₀ x))`.
* `chartLocalMeasure g x₀` : the chart-local measure on `M` obtained by pushing
  forward the weighted canonical additive Haar measure on the model space `E`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace RicciFlower
namespace Analysis
namespace Volume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Canonical measurable-space and Borel-space instances on `E` and `M`

These are file-local instances that equip any finite-dimensional real normed space `E`
with its Borel σ-algebra and any topological manifold `M` with the Borel σ-algebra
induced from its topology. They are declared `local` so they do not leak into calling
files as global instances; callers that need to interact with the measures defined below
should install matching instances in their own scope. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- RicciFlower analytic-smooth Riemannian metrics, used directly by the volume layer. -/
abbrev SmoothRiemannianMetric (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  RicciFlower.SmoothRiemannianMetric I M

/-! ## Tangent-bundle sections from a fixed model-space basis -/

/-- The `i`-th pointwise tangent vector of the chart-local frame attached to `x₀`. For `x`
in the trivialization base set this is the image of the `i`-th model-space basis vector
under `(trivializationAt E (TangentSpace I) x₀).symm x`; off that set it is a default
(junk) value in the fiber, still well-defined. -/
def chartBasisVecFiber (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    TangentSpace I x :=
  (trivializationAt E (TangentSpace I) x₀).symm x ((Module.finBasis ℝ E) i)

/-- The `i`-th pointwise tangent-bundle section of the chart-local frame attached to `x₀`.
Smooth on `triv.baseSet`. -/
def chartBasisVec (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    M → TotalSpace E (TangentSpace I : M → Type _) :=
  fun x => TotalSpace.mk' E x (chartBasisVecFiber (I := I) x₀ i x)

@[simp] lemma chartBasisVec_proj (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    (chartBasisVec (I := I) x₀ i x).proj = x := rfl

@[simp] lemma chartBasisVec_snd (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    (chartBasisVec (I := I) x₀ i x).2 = chartBasisVecFiber (I := I) x₀ i x := rfl

/-- On the base set of the trivialization at `x₀`, applying the trivialization to the
chart-basis vector recovers the constant model-basis vector. -/
lemma trivializationAt_chartBasisVec_snd
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (trivializationAt E (TangentSpace I) x₀
        ⟨x, chartBasisVecFiber (I := I) x₀ i x⟩).2
      = (Module.finBasis ℝ E) i := by
  have h := (trivializationAt E (TangentSpace I) x₀).apply_mk_symm hx
    ((Module.finBasis ℝ E) i)
  simpa [chartBasisVecFiber] using congrArg Prod.snd h

/-- The chart-basis tangent-bundle section is smooth on the base set of the
trivialization at `x₀`. -/
lemma chartBasisVec_contMDiffOn
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (chartBasisVec (I := I) x₀ i)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hiff :=
    ((trivializationAt E (TangentSpace I) x₀)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞) (s := fun x => chartBasisVecFiber (I := I) x₀ i x)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => (Module.finBasis ℝ E) i)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
    contMDiffOn_const
  refine hconst.congr ?_
  intro x hx
  exact (trivializationAt_chartBasisVec_snd (I := I) x₀ i hx)

/-! ## Fiberwise basis from the trivialization -/

/-- The chart-basis family at a point `x ∈ triv.baseSet` is a basis of `TangentSpace I x`,
obtained by transporting the fixed model-space basis through the continuous linear
equivalence given by the trivialization. -/
def chartBasisFamily (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
  (Module.finBasis ℝ E).map
    (ContinuousLinearEquiv.toLinearEquiv
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x hx).symm)

lemma chartBasisFamily_apply (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisFamily (I := I) x₀ hx i =
      chartBasisVecFiber (I := I) x₀ i x := by
  unfold chartBasisFamily chartBasisVecFiber
  rw [Module.Basis.map_apply]
  rfl

/-- The chart-basis family is linearly independent at each base-set point. -/
lemma chartBasisFamily_linearIndependent (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) x₀ i x) := by
  have h := (chartBasisFamily (I := I) x₀ hx).linearIndependent
  have hcongr : (chartBasisFamily (I := I) x₀ hx : Fin (Module.finrank ℝ E) → TangentSpace I x)
      = fun i => chartBasisVecFiber (I := I) x₀ i x := by
    funext i
    exact chartBasisFamily_apply (I := I) x₀ hx i
  rw [← hcongr]
  exact h

/-! ## The Gram matrix of the chart-basis family -/

/-- The Gram matrix of the chart-basis family at `x` under `g.inner x`. -/
def chartGramMatrix (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    g.inner x
      (chartBasisVecFiber (I := I) x₀ i x)
      (chartBasisVecFiber (I := I) x₀ j x)

@[simp] lemma chartGramMatrix_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix g x₀ x i j =
      g.inner x
        (chartBasisVecFiber (I := I) x₀ i x)
        (chartBasisVecFiber (I := I) x₀ j x) := rfl

/-- The Gram matrix is Hermitian (symmetric for real entries). -/
lemma chartGramMatrix_isHermitian
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M) :
    (chartGramMatrix g x₀ x).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  show star (chartGramMatrix g x₀ x j i) = chartGramMatrix g x₀ x i j
  rw [chartGramMatrix_apply, chartGramMatrix_apply, star_trivial]
  exact g.symm x
    (chartBasisVecFiber (I := I) x₀ j x)
    (chartBasisVecFiber (I := I) x₀ i x)

/-- Helper: the quadratic form of the Gram matrix equals the inner product of the linear
combinations. This is the tangent-space version of the standard identity used in
`Matrix.star_dotProduct_gram_mulVec`. -/
lemma chartGramMatrix_dotProduct_mulVec
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M)
    (c : Fin (Module.finrank ℝ E) → ℝ) :
    star c ⬝ᵥ (chartGramMatrix g x₀ x) *ᵥ c =
      g.inner x
        (∑ i, c i • chartBasisVecFiber (I := I) x₀ i x)
        (∑ j, c j • chartBasisVecFiber (I := I) x₀ j x) := by
  -- Direct bilinear expansion via `map_sum` and `map_smul`.
  have hexpand' :
      g.inner x
          (∑ i, c i • chartBasisVecFiber (I := I) x₀ i x)
          (∑ j, c j • chartBasisVecFiber (I := I) x₀ j x)
        = ∑ i, ∑ j, (c i * c j) *
            g.inner x
              (chartBasisVecFiber (I := I) x₀ i x)
              (chartBasisVecFiber (I := I) x₀ j x) := by
    -- Left linearity: pull the ∑ᵢ cᵢ • vᵢ out.
    have hL :
        g.inner x (∑ i, c i • chartBasisVecFiber (I := I) x₀ i x)
          = ∑ i, c i • g.inner x (chartBasisVecFiber (I := I) x₀ i x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
    -- Apply both sides at `∑ⱼ cⱼ • vⱼ`.
    rw [hL]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    -- Goal: `(c i • g.inner x vᵢ) (∑ⱼ cⱼ • vⱼ) = ∑ⱼ (c i * c j) * g.inner x vᵢ vⱼ`.
    rw [ContinuousLinearMap.smul_apply]
    -- Now goal: `c i • (g.inner x vᵢ) (∑ⱼ cⱼ • vⱼ) = ∑ⱼ (c i * c j) * g.inner x vᵢ vⱼ`.
    -- Right linearity on the right argument.
    have hR :
        g.inner x (chartBasisVecFiber (I := I) x₀ i x)
            (∑ j, c j • chartBasisVecFiber (I := I) x₀ j x)
          = ∑ j, c j *
              g.inner x
                (chartBasisVecFiber (I := I) x₀ i x)
                (chartBasisVecFiber (I := I) x₀ j x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [map_smul, smul_eq_mul]
    rw [hR, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hexpand']
  -- Now the left-hand side.
  simp only [dotProduct, Matrix.mulVec, chartGramMatrix_apply, Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  -- Goal: `c i * (A i j * c j) = (c i * c j) * A i j` where `A i j = g.inner x vᵢ vⱼ`.
  ring

/-- The Gram matrix of the chart-basis family is positive-definite on the base set. -/
lemma chartGramMatrix_posDef
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (chartGramMatrix g x₀ x).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (chartGramMatrix_isHermitian (I := I) g x₀ x) ?_
  intro c hc
  set w : TangentSpace I x :=
    ∑ i, c i • chartBasisVecFiber (I := I) x₀ i x with hw_def
  have heq := chartGramMatrix_dotProduct_mulVec (I := I) g x₀ x c
  rw [heq]
  have hwnz : w ≠ 0 := by
    intro hw0
    have hli := chartBasisFamily_linearIndependent (I := I) x₀ hx
    rw [Fintype.linearIndependent_iff] at hli
    have : c = 0 := funext (hli c hw0)
    exact hc this
  exact g.pos x w hwnz

/-- The determinant of the Gram matrix is positive on the base set. -/
lemma chartGramMatrix_det_pos
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    0 < (chartGramMatrix g x₀ x).det :=
  (chartGramMatrix_posDef (I := I) g x₀ hx).det_pos

/-! ## The chart-local density -/

/-- The chart-local density at `x` is `√(det (Gram matrix at x))`. -/
def chartDensity (g : SmoothRiemannianMetric I M) (x₀ : M) : M → ℝ :=
  fun x => Real.sqrt (chartGramMatrix g x₀ x).det

/-- The chart-local density is strictly positive on the trivialization base set. -/
lemma chartDensity_pos
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    0 < chartDensity g x₀ x :=
  Real.sqrt_pos.mpr (chartGramMatrix_det_pos (I := I) g x₀ hx)

/-! ## Smoothness of the Gram matrix entries and density -/

/-- Each Gram-matrix entry is smooth on the trivialization base set. Proof: the inner
product evaluated at two smooth sections is smooth, via `ContMDiffOn.clm_bundle_apply₂`
applied to `g.contMDiff` and two copies of `chartBasisVec`. -/
lemma chartGramMatrix_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => chartGramMatrix g x₀ x i j)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        b (g.inner b))
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
    (g.contMDiff.of_le le_top).contMDiffOn
  have hv := chartBasisVec_contMDiffOn (I := I) x₀ i
  have hw := chartBasisVec_contMDiffOn (I := I) x₀ j
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            g.inner m
              (chartBasisVecFiber (I := I) x₀ i m)
              (chartBasisVecFiber (I := I) x₀ j m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) x₀).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hg hv hw
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

/-- Each entry of the Gram matrix viewed as a function of `x`, but indexed by a pair
`(i, j)`, is smooth on the base set. -/
private lemma chartGramMatrix_pair_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => chartGramMatrix g x₀ x ij.1 ij.2)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
  chartGramMatrix_entry_contMDiffOn (I := I) g x₀ ij.1 ij.2

/-- The determinant of the Gram matrix is smooth on the trivialization base set. We expand
`Matrix.det` into a finite sum over permutations of finite products of entries, then use
the smooth-manifold finite-sum / finite-product lemmas for scalar-valued functions. -/
lemma chartGramMatrix_det_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => (chartGramMatrix g x₀ x).det)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  classical
  -- `det A = ∑_{σ} sign σ • ∏_i A (σ i) i`
  have hexp :
      (fun x : M => (chartGramMatrix g x₀ x).det)
        = (fun x : M =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ i, chartGramMatrix g x₀ x (σ i) i) := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul
    (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finset_prod (fun i _ => ?_)
  exact chartGramMatrix_entry_contMDiffOn (I := I) g x₀ (σ i) i

lemma chartDensity_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity g x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  intro x hx
  have hdet := chartGramMatrix_det_contMDiffOn (I := I) g x₀ x hx
  have hpos_ne : (chartGramMatrix (I := I) g x₀ x).det ≠ 0 :=
    ne_of_gt (chartGramMatrix_det_pos (I := I) g x₀ hx)
  have hsqrt : ContDiffAt ℝ ∞ Real.sqrt
      (chartGramMatrix (I := I) g x₀ x).det :=
    Real.contDiffAt_sqrt hpos_ne
  -- Apply `ContDiffAt.comp_contMDiffWithinAt` with the right target.
  have := hsqrt.comp_contMDiffWithinAt (f :=
      fun y : M => (chartGramMatrix (I := I) g x₀ y).det) hdet
  exact this

/-! ## The chart-local measure -/

/-- The canonical additive Haar measure on the model space `E`, obtained from the
canonical basis `Module.finBasis ℝ E`. Serves as the reference measure on the chart
target. -/
noncomputable def modelHaar : MeasureTheory.Measure E := (Module.finBasis ℝ E).addHaar

/-- The canonical Haar measure on `E` is an additive Haar measure. This
instance is derived from `Module.Basis.addHaar`. -/
instance modelHaar_isAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure (modelHaar (E := E)) := by
  unfold modelHaar
  infer_instance

/-- Chart-local measure on `M` built from the chart-local density and the extended
chart at `x₀`, using the canonical additive Haar measure on the model space `E`.

The measure is constructed in three steps: restrict the canonical Haar measure on `E` to
the target of the extended chart; weight it by the pullback of the chart-local density
through the extended chart's inverse; push forward the result to `M` along the extended
chart's inverse. -/
def chartLocalMeasure
    (g : SmoothRiemannianMetric I M) (x₀ : M) : MeasureTheory.Measure M :=
  MeasureTheory.Measure.map (extChartAt I x₀).symm
    (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
      (fun y : E =>
        ENNReal.ofReal
          (chartDensity g x₀ ((extChartAt I x₀).symm y))))

/-- The chart-local measure is (by definition) the pushforward along `(extChartAt I x₀).symm`
of the density-weighted restriction of the canonical Haar measure on `E` to the chart
target. -/
lemma chartLocalMeasure_def
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    chartLocalMeasure (I := I) g x₀ =
      MeasureTheory.Measure.map (extChartAt I x₀).symm
        (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
          (fun y : E =>
            ENNReal.ofReal
              (chartDensity g x₀ ((extChartAt I x₀).symm y)))) := rfl

end Volume
end Analysis
end RicciFlower
