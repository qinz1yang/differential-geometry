import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Defs
import DifferentialGeometry.Geometry.Gradient
import DifferentialGeometry.Integral.DivergenceTheorem.IntegrationByParts
import DifferentialGeometry.Integral.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Integral.DivergenceTheorem.POUReduction
import DifferentialGeometry.Integral.DivergenceTheorem.TangentAction
import DifferentialGeometry.Integral.L2.CompactSupport
import DifferentialGeometry.Integral.Measure.Properties
import DifferentialGeometry.Integral.Measure.Glue
import DifferentialGeometry.Integral.Measure.Invariance
import DifferentialGeometry.Tensor.RSTensor.TangentRiemannian
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Intrinsic Sobolev space `W^{1,p}_{int,Lp}(M)` with measurable `L^p` weak gradients

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` and an
exponent `1 ≤ p ≤ ∞` (with `p ≠ ∞`), this file extends the intrinsic Sobolev
space defined in `Intrinsic.lean` (where the weak gradient was required to be a
*smooth* tangent section) to the standard setting where the weak gradient is a
*measurable* tangent section in `L^p`.

A function `G : M → E` (interpreted as a tangent section via the canonical
definitional equality `TangentSpace I x = E` from the project's tangent-bundle
setup) is a **weak Riemannian gradient** of `u : M → ℝ` when:

1. The pairing `x ↦ g.inner x (G x) (Y x)` is `AEStronglyMeasurable` for every
   smooth tangent test field `Y` (this captures the measurability of `G`
   tested against the smooth-section "test space").
2. For every smooth, compactly-supported tangent test field `X`, the
   integration-by-parts identity
   $$\int_M g.inner x (G x) (X x)\,d\mu_g = -\int_M u(x) \cdot
     \operatorname{div}_g(X)(x)\,d\mu_g$$ holds.

The intrinsic Sobolev space `MemW1pIntrinsicLp g p u` then asks for `u ∈ L^p`
plus the existence of such a `G` whose pointwise `g`-norm
`x ↦ √(g.inner x (G x) (G x))` is in `L^p`.

## Representation choice

We represent measurable tangent sections as functions `M → E`, exploiting the
project-internal definitional equality `TangentSpace I x = E`. This avoids
dependent-function gymnastics. The `g.inner x` continuous bilinear form has
type `TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ`, agreeing with
`E →L[ℝ] E →L[ℝ] ℝ` by the same defeq.

The predicate phrases measurability of `G` purely through scalar pairings
`g.inner x (G x) (Y x)` against smooth test fields `Y`, sidestepping the
subtle question of whether the abuse-of-defeq map `(G x : E)` is itself a
Borel-measurable map `M → E` (which depends on the bundle topology).

## Main definitions

* `HasWeakRiemannianGradLp g u G` : `G : M → E` is a weak Riemannian gradient
  of `u` (encoded through the IBP identity and pairing measurability).
* `MemW1pIntrinsicLp g p u` : `u ∈ L^p(M, μ_g)` and admits an `L^p` weak
  Riemannian gradient.
* `w1pNormIntrinsicLp g p u` : the intrinsic Sobolev norm using the infimum
  over weak gradients of the `L^p` norm of `√(g(G,G))`.

## Main results

* `MemW1pIntrinsicLp.zero`, `MemW1pIntrinsicLp.const_smul`,
  `MemW1pIntrinsicLp.neg` : algebraic closure of the predicate under the
  standard `ℝ`-vector-space operations on scalar functions; closure under
  addition is recorded as `HasWeakRiemannianGradLp.add` at the IBP level.
* `MemW1pIntrinsicLp_of_MemW1pIntrinsic` : every `Intrinsic.MemW1pIntrinsic`
  function (smooth-section weak gradient form) is also in
  `MemW1pIntrinsicLp`.
* `MemW1pIntrinsicLp_of_contMDiff` : every smooth function on a closed
  Riemannian manifold lies in `MemW1pIntrinsicLp` for every exponent `p`.
* `HasWeakRiemannianGradLp.pairing_inner_eq` : two weak `L^p` gradients of
  the same function pair identically against every smooth compactly-supported
  tangent test field.
* `w1pNormIntrinsicLp_zero` : the norm of the zero function is zero.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Function
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace IntrinsicLp
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Intrinsic

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma g_inner_add_left
    (g : SmoothRiemannianMetric I M) (x : M) (v w y : TangentSpace I x) :
    g.inner x (v + w) y = g.inner x v y + g.inner x w y := by
  rw [map_add (g.inner x), ContinuousLinearMap.add_apply]

private lemma g_inner_add_right
    (g : SmoothRiemannianMetric I M) (x : M) (v y w : TangentSpace I x) :
    g.inner x v (y + w) = g.inner x v y + g.inner x v w :=
  ContinuousLinearMap.map_add (g.inner x v) y w

private lemma g_inner_smul_left
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ) (v y : TangentSpace I x) :
    g.inner x (c • v) y = c * g.inner x v y := by
  rw [map_smul (g.inner x), ContinuousLinearMap.smul_apply, smul_eq_mul]

private lemma g_inner_smul_right
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) (c : ℝ)
    (y : TangentSpace I x) :
    g.inner x v (c • y) = c * g.inner x v y := by
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

private lemma g_inner_zero_left
    (g : SmoothRiemannianMetric I M) (x : M) (y : TangentSpace I x) :
    g.inner x (0 : TangentSpace I x) y = 0 := by
  rw [map_zero, ContinuousLinearMap.zero_apply]

private lemma g_inner_zero_right
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    g.inner x v (0 : TangentSpace I x) = 0 := by
  rw [ContinuousLinearMap.map_zero]

private lemma g_inner_neg_left
    (g : SmoothRiemannianMetric I M) (x : M) (v y : TangentSpace I x) :
    g.inner x (-v) y = - g.inner x v y := by
  rw [map_neg, ContinuousLinearMap.neg_apply]

private lemma g_inner_neg_right
    (g : SmoothRiemannianMetric I M) (x : M) (v y : TangentSpace I x) :
    g.inner x v (-y) = - g.inner x v y := by
  rw [ContinuousLinearMap.map_neg]

/-- Bilinear expansion: `g.inner x (v + w) (v + w) = g(v,v) + 2 g(v,w) + g(w,w)`. -/
private lemma g_inner_add_diag
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    g.inner x (v + w) (v + w) =
      g.inner x v v + 2 * g.inner x v w + g.inner x w w := by
  rw [g_inner_add_left g x v w (v + w),
    g_inner_add_right g x v v w, g_inner_add_right g x w v w]
  have hsymm : g.inner x w v = g.inner x v w := g.symm x w v
  rw [hsymm]; ring

/-- Bilinear expansion in the Cauchy–Schwarz quadratic form:
`g(t • v + w, t • v + w) = t² g(v,v) + 2 t g(v,w) + g(w,w)`. -/
private lemma g_inner_smul_add_diag
    (g : SmoothRiemannianMetric I M) (x : M) (t : ℝ) (v w : TangentSpace I x) :
    g.inner x (t • v + w) (t • v + w) =
      t * t * g.inner x v v + 2 * t * g.inner x v w + g.inner x w w := by
  rw [g_inner_add_left g x (t • v) w (t • v + w),
    g_inner_add_right g x (t • v) (t • v) w,
    g_inner_add_right g x w (t • v) w]
  rw [g_inner_smul_left g x t v (t • v), g_inner_smul_right g x v t v,
    g_inner_smul_left g x t v w, g_inner_smul_right g x w t v]
  have hsymm : g.inner x w v = g.inner x v w := g.symm x w v
  rw [hsymm]; ring

/-- Cauchy–Schwarz for the metric inner product. -/
private lemma g_inner_cauchy_schwarz
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    |g.inner x v w| ≤ Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  set a := g.inner x v v
  set b := g.inner x w w
  set c := g.inner x v w
  have ha_nn : 0 ≤ a := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · simp [a, hv0]
    · exact (g.pos x v hv0).le
  have hb_nn : 0 ≤ b := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · simp [b, hw0]
    · exact (g.pos x w hw0).le
  have hquad : ∀ t : ℝ, 0 ≤ t * t * a + 2 * t * c + b := by
    intro t
    have hpos : 0 ≤ g.inner x (t • v + w) (t • v + w) := by
      rcases eq_or_ne (t • v + w) 0 with hz | hnz
      · rw [hz, g_inner_zero_left]
      · exact (g.pos x _ hnz).le
    have h_expand := g_inner_smul_add_diag g x t v w
    rw [h_expand] at hpos
    exact hpos
  have hCS_sq : c ^ 2 ≤ a * b := by
    rcases lt_or_eq_of_le ha_nn with ha_pos | ha_zero
    · have hroot := hquad (-c / a)
      have ha_ne : a ≠ 0 := ne_of_gt ha_pos
      have hsimp : -c / a * (-c / a) * a + 2 * (-c / a) * c + b =
          b - c^2 / a := by field_simp; ring
      rw [hsimp] at hroot
      have hcsa : c ^ 2 / a ≤ b := by linarith
      have h1 : c ^ 2 = a * (c ^ 2 / a) := by field_simp
      rw [h1]
      exact mul_le_mul_of_nonneg_left hcsa ha_nn
    · have ha_eq : a = 0 := ha_zero.symm
      have hv_zero : v = 0 := by
        by_contra hne
        have hpos : 0 < g.inner x v v := g.pos x v hne
        rw [show g.inner x v v = a from rfl, ha_eq] at hpos
        exact lt_irrefl 0 hpos
      have hc_eq : c = 0 := by
        change g.inner x v w = 0
        rw [hv_zero]
        exact g_inner_zero_left g x w
      rw [hc_eq, ha_eq]; simp
  have hC : |c| ≤ Real.sqrt (a * b) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hCS_sq
  have hsqrt_mul : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b :=
    Real.sqrt_mul ha_nn b
  rw [hsqrt_mul] at hC
  exact hC

/-- Triangle inequality for the metric `g`-norm. -/
private lemma g_norm_triangle
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    Real.sqrt (g.inner x (v + w) (v + w)) ≤
      Real.sqrt (g.inner x v v) + Real.sqrt (g.inner x w w) := by
  set a := g.inner x v v
  set b := g.inner x w w
  set c := g.inner x v w
  have ha_nn : 0 ≤ a := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · simp [a, hv0]
    · exact (g.pos x v hv0).le
  have hb_nn : 0 ≤ b := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · simp [b, hw0]
    · exact (g.pos x w hw0).le
  have h_expand := g_inner_add_diag g x v w
  rw [h_expand]
  have hCS : |c| ≤ Real.sqrt a * Real.sqrt b :=
    g_inner_cauchy_schwarz g x v w
  have hc_le : c ≤ Real.sqrt a * Real.sqrt b :=
    (le_abs_self c).trans hCS
  have h_le_sq : a + 2 * c + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have h_sq_expand : (Real.sqrt a + Real.sqrt b) ^ 2 =
        a + 2 * (Real.sqrt a * Real.sqrt b) + b := by
      have ha_sq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha_nn
      have hb_sq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb_nn
      nlinarith [ha_sq, hb_sq]
    rw [h_sq_expand]
    linarith
  have h_nn : 0 ≤ Real.sqrt a + Real.sqrt b :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_sqrt_le := Real.sqrt_le_sqrt h_le_sq
  rw [show Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) = Real.sqrt a + Real.sqrt b
      from Real.sqrt_sq h_nn] at h_sqrt_le
  exact h_sqrt_le

/-- Scalar homogeneity for the metric `g`-norm. -/
private lemma g_norm_const_smul
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ) (v : TangentSpace I x) :
    Real.sqrt (g.inner x (c • v) (c • v)) =
      |c| * Real.sqrt (g.inner x v v) := by
  rw [g_inner_smul_left g x c v (c • v), g_inner_smul_right g x v c v]
  rw [show c * (c * g.inner x v v) = c ^ 2 * g.inner x v v from by ring]
  rw [Real.sqrt_mul (sq_nonneg c)]
  rw [Real.sqrt_sq_eq_abs]

/-- Negation preserves the metric `g`-norm. -/
private lemma g_norm_neg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    Real.sqrt (g.inner x (-v) (-v)) = Real.sqrt (g.inner x v v) := by
  rw [g_inner_neg_left g x v (-v), g_inner_neg_right g x v v]
  simp

/-- Continuity of `b ↦ g.inner b (G b) (X b)` for two smooth tangent
sections `G, X`. Re-exports the project-level theorem. -/
private lemma continuous_g_inner_smooth_sections
    (g : SmoothRiemannianMetric I M)
    (G X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Continuous (fun b : M => g.inner b (G b) (X b)) :=
  TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g G X

/-- The pointwise `g`-norm of a smooth tangent section is continuous. -/
private lemma continuous_g_norm_smooth_section
    (g : SmoothRiemannianMetric I M)
    (G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Continuous (fun b : M => Real.sqrt (g.inner b (G b) (G b))) :=
  Real.continuous_sqrt.comp (continuous_g_inner_smooth_sections g G G)

/-- Continuous functions on a closed manifold are bounded. -/
private lemma exists_bound_continuous_compactSpace
    [CompactSpace M] {f : M → ℝ} (hf : Continuous f) :
    ∃ C : ℝ, ∀ x : M, |f x| ≤ C := by
  by_cases hM : Nonempty M
  · have hrange : IsCompact (Set.range f) := isCompact_range hf
    obtain ⟨C₁, hC₁⟩ := hrange.bddAbove
    have hrange_neg : IsCompact (Set.range (-f)) := isCompact_range hf.neg
    obtain ⟨C₂, hC₂⟩ := hrange_neg.bddAbove
    refine ⟨max C₁ C₂, ?_⟩
    intro x
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have : -f x ≤ C₂ := hC₂ ⟨x, rfl⟩
      linarith [le_max_right C₁ C₂]
    · have : f x ≤ C₁ := hC₁ ⟨x, rfl⟩
      linarith [le_max_left C₁ C₂]
  · refine ⟨0, ?_⟩
    intro x
    exact (hM ⟨x⟩).elim

/-- A continuous function on a closed manifold lies in `L^p`. -/
private lemma continuous_memLp_of_compactSpace
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (p : ℝ≥0∞)
    {f : M → ℝ} (hf : Continuous f) :
    MemLp f p (riemannianVolumeMeasure I M g) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hmeas : AEStronglyMeasurable f (riemannianVolumeMeasure I M g) :=
    hf.aestronglyMeasurable
  obtain ⟨C, hC⟩ := exists_bound_continuous_compactSpace hf
  exact MemLp.of_bound hmeas C (Filter.Eventually.of_forall (fun x => hC x))

/-- A continuous function on a closed manifold is integrable. -/
private lemma continuous_integrable_of_compactSpace
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : Continuous f) :
    Integrable f (riemannianVolumeMeasure I M g) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have h_one : MemLp f 1 (riemannianVolumeMeasure I M g) :=
    continuous_memLp_of_compactSpace g 1 hf
  exact memLp_one_iff_integrable.mp h_one

/-- For two smooth tangent sections, the metric inner product is integrable. -/
private lemma integrable_g_inner_smooth_sections
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (G X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Integrable (fun b : M => g.inner b (G b) (X b))
      (riemannianVolumeMeasure I M g) :=
  continuous_integrable_of_compactSpace g
    (continuous_g_inner_smooth_sections g G X)

/-- A function `G : M → E` (interpreted as a tangent section via the canonical
`TangentSpace I x = E` definitional equality) is a **weak Riemannian gradient**
of `u : M → ℝ` if:

* the pairing `x ↦ g.inner x (G x) (Y x)` is `AEStronglyMeasurable` for every
  smooth tangent test field `Y` (this is the measurability hypothesis on `G`,
  expressed entirely through inner-product pairings); and
* for every smooth compactly-supported tangent test field `X`, the
  integration-by-parts identity
  $$\int_M g.inner x (G x) (X x)\,d\mu_g
    = -\int_M u(x) \cdot \operatorname{div}_g(X)(x)\,d\mu_g$$
  holds. -/
def HasWeakRiemannianGradLp
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) (G : M → E) : Prop :=
  (∀ Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
    AEStronglyMeasurable (fun x : M => g.inner x (G x) (Y x))
      (riemannianVolumeMeasure I M g)) ∧
  ∀ X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
    HasCompactSupport (fun x : M => (X x : E)) →
      ∫ x, g.inner x (G x) (X x) ∂(riemannianVolumeMeasure I M g) =
        -∫ x, u x * divergence_g (I := I) g X x
          ∂(riemannianVolumeMeasure I M g)

namespace HasWeakRiemannianGradLp

variable {g : SmoothRiemannianMetric I M} {u : M → ℝ} {G : M → E}

/-- The integration-by-parts identity. -/
lemma pairing_eq
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (h : HasWeakRiemannianGradLp (I := I) (M := M) g u G)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport (fun x : M => (X x : E))) :
    ∫ x, g.inner x (G x) (X x) ∂(riemannianVolumeMeasure I M g) =
      -∫ x, u x * divergence_g (I := I) g X x
        ∂(riemannianVolumeMeasure I M g) := h.2 X hX

/-- The pairing is `AEStronglyMeasurable` against every smooth test section. -/
lemma pairing_aestronglyMeasurable
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (h : HasWeakRiemannianGradLp (I := I) (M := M) g u G)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    AEStronglyMeasurable (fun x : M => g.inner x (G x) (Y x))
      (riemannianVolumeMeasure I M g) := h.1 Y

end HasWeakRiemannianGradLp

/-- `MemW1pIntrinsicLp g p u` means:

* `u : M → ℝ` is in `L^p` against the Riemannian volume measure;
* there exists a function `G : M → E` which is a weak Riemannian gradient of
  `u` (in the `HasWeakRiemannianGradLp` sense), and whose pointwise `g`-norm
  `x ↦ √(g.inner x (G x) (G x))` is in `L^p` against the Riemannian volume
  measure. -/
def MemW1pIntrinsicLp
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) (u : M → ℝ) : Prop :=
  MemLp u p (riemannianVolumeMeasure I M g) ∧
  ∃ G : M → E, HasWeakRiemannianGradLp (I := I) (M := M) g u G ∧
      MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
        (riemannianVolumeMeasure I M g)

/-- The `L^p` membership component. -/
lemma MemW1pIntrinsicLp.memLp_self
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} {u : M → ℝ}
    (h : MemW1pIntrinsicLp (I := I) (M := M) g p u) :
    MemLp u p (riemannianVolumeMeasure I M g) := h.1

/-- A smooth-section weak Riemannian gradient yields an `L^p` weak Riemannian
gradient. -/
theorem hasWeakRiemannianGradLp_of_smooth
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {u : M → ℝ}
    {G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (h : Intrinsic.HasWeakRiemannianGrad (I := I) (M := M) g u G) :
    HasWeakRiemannianGradLp (I := I) (M := M) g u (fun x : M => (G x : E)) := by
  refine ⟨?_, ?_⟩
  · intro Y
    exact (continuous_g_inner_smooth_sections g G Y).aestronglyMeasurable
  · intro X hX
    exact h X hX

/-- **Bridge**: every smooth-section intrinsic Sobolev function is also in
the measurable-section intrinsic Sobolev space. -/
theorem MemW1pIntrinsicLp_of_MemW1pIntrinsic
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} {u : M → ℝ}
    (h : Intrinsic.MemW1pIntrinsic (I := I) (M := M) g p u) :
    MemW1pIntrinsicLp (I := I) (M := M) g p u := by
  obtain ⟨hu, G, hG_weak, hG_p⟩ := h
  refine ⟨hu, (fun x : M => (G x : E)), ?_, ?_⟩
  · exact hasWeakRiemannianGradLp_of_smooth (I := I) (M := M) hG_weak
  · convert hG_p using 1

/-- **Bridge to smooth functions**: every smooth function on a closed
Riemannian manifold lies in `MemW1pIntrinsicLp` for every exponent `p`. -/
theorem MemW1pIntrinsicLp_of_contMDiff
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    MemW1pIntrinsicLp (I := I) (M := M) g p u :=
  MemW1pIntrinsicLp_of_MemW1pIntrinsic (I := I) (M := M)
    (Intrinsic.MemW1pIntrinsic_of_contMDiff (I := I) (M := M) g p hu)

/-- The zero `M → E` map is a weak `L^p` Riemannian gradient of the zero
function. -/
theorem HasWeakRiemannianGradLp.zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    HasWeakRiemannianGradLp (I := I) (M := M) g (fun _ : M => (0 : ℝ))
      (fun _ : M => (0 : E)) := by
  refine ⟨?_, ?_⟩
  · intro Y
    have hcongr : (fun x : M =>
        g.inner x ((fun _ : M => (0 : E)) x) (Y x)) =
        (fun _ : M => (0 : ℝ)) := by
      funext x
      change g.inner x (0 : TangentSpace I x) (Y x) = 0
      exact g_inner_zero_left g x (Y x)
    rw [hcongr]
    exact aestronglyMeasurable_const
  · intro X _
    have h_LHS : (fun x : M =>
        g.inner x ((fun _ : M => (0 : E)) x) (X x)) =
        (fun _ : M => (0 : ℝ)) := by
      funext x
      change g.inner x (0 : TangentSpace I x) (X x) = 0
      exact g_inner_zero_left g x (X x)
    rw [h_LHS]
    rw [show (fun x : M => (0 : ℝ) * divergence_g (I := I) g X x) =
        (fun _ : M => (0 : ℝ)) from by funext x; simp]
    simp [integral_zero]

/-- The zero scalar function is in `MemW1pIntrinsicLp` for every exponent. -/
theorem MemW1pIntrinsicLp.zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) :
    MemW1pIntrinsicLp (I := I) (M := M) g p (fun _ : M => (0 : ℝ)) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  refine ⟨MemLp.zero, (fun _ : M => (0 : E)),
    HasWeakRiemannianGradLp.zero (I := I) (M := M) g, ?_⟩
  have hcongr : (fun x : M => Real.sqrt
      (g.inner x ((fun _ : M => (0 : E)) x) ((fun _ : M => (0 : E)) x))) =
      (fun _ : M => (0 : ℝ)) := by
    funext x
    change Real.sqrt (g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x)) = 0
    rw [g_inner_zero_left g x (0 : TangentSpace I x)]
    exact Real.sqrt_zero
  rw [hcongr]
  exact MemLp.zero

/-- Sum of two `L^p` weak Riemannian gradients. -/
theorem HasWeakRiemannianGradLp.add
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ} {G G' : M → E}
    (h₁ : HasWeakRiemannianGradLp (I := I) (M := M) g u G)
    (h₂ : HasWeakRiemannianGradLp (I := I) (M := M) g v G')
    (hu : MemLp u p (riemannianVolumeMeasure I M g))
    (hv : MemLp v p (riemannianVolumeMeasure I M g))
    (hGn : MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
      (riemannianVolumeMeasure I M g))
    (hG'n : MemLp (fun x : M => Real.sqrt (g.inner x (G' x) (G' x))) p
      (riemannianVolumeMeasure I M g)) :
    HasWeakRiemannianGradLp (I := I) (M := M) g
      (fun x => u x + v x) (fun x : M => G x + G' x) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  refine ⟨?_, ?_⟩
  · intro Y
    have hcongr : (fun x : M =>
        g.inner x ((fun y : M => G y + G' y) x) (Y x)) =
        (fun x : M => g.inner x (G x) (Y x) +
          g.inner x (G' x) (Y x)) := by
      funext x
      exact g_inner_add_left g x (G x) (G' x) (Y x)
    rw [hcongr]
    exact (h₁.1 Y).add (h₂.1 Y)
  · intro X hX
    have hpt : ∀ x : M,
        g.inner x ((fun y : M => G y + G' y) x) (X x) =
          g.inner x (G x) (X x) + g.inner x (G' x) (X x) := by
      intro x
      exact g_inner_add_left g x (G x) (G' x) (X x)
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hX_norm_cont : Continuous (fun x : M =>
        Real.sqrt (g.inner x (X x) (X x))) :=
      continuous_g_norm_smooth_section g X
    obtain ⟨C_X, hC_X⟩ := exists_bound_continuous_compactSpace hX_norm_cont
    have h_bound_aux : ∀ (W : M → E), ∀ x : M,
        |g.inner x (W x) (X x)| ≤
          C_X * Real.sqrt (g.inner x (W x) (W x)) := by
      intro W x
      have hCS := g_inner_cauchy_schwarz g x (W x) (X x)
      have hX_bd : Real.sqrt (g.inner x (X x) (X x)) ≤ C_X := by
        have h := hC_X x
        have hnn : 0 ≤ Real.sqrt (g.inner x (X x) (X x)) := Real.sqrt_nonneg _
        rw [abs_of_nonneg hnn] at h; exact h
      calc |g.inner x (W x) (X x)|
          ≤ Real.sqrt (g.inner x (W x) (W x)) * Real.sqrt (g.inner x (X x) (X x)) := hCS
        _ ≤ Real.sqrt (g.inner x (W x) (W x)) * C_X :=
              mul_le_mul_of_nonneg_left hX_bd (Real.sqrt_nonneg _)
        _ = C_X * Real.sqrt (g.inner x (W x) (W x)) := by ring
    have h_int_G : Integrable (fun x : M => g.inner x (G x) (X x))
        (riemannianVolumeMeasure I M g) := by
      have hG_one : MemLp (fun x : M =>
          Real.sqrt (g.inner x (G x) (G x))) 1
          (riemannianVolumeMeasure I M g) :=
        hGn.mono_exponent hp
      have hG_int : Integrable (fun x : M =>
          Real.sqrt (g.inner x (G x) (G x)))
          (riemannianVolumeMeasure I M g) :=
        memLp_one_iff_integrable.mp hG_one
      refine Integrable.mono' (g := fun x : M =>
          C_X * Real.sqrt (g.inner x (G x) (G x))) ?_ (h₁.1 X) ?_
      · exact hG_int.const_mul C_X
      · refine Filter.Eventually.of_forall (fun x => ?_)
        rw [Real.norm_eq_abs]
        exact h_bound_aux G x
    have h_int_G' : Integrable (fun x : M => g.inner x (G' x) (X x))
        (riemannianVolumeMeasure I M g) := by
      have hG'_one : MemLp (fun x : M =>
          Real.sqrt (g.inner x (G' x) (G' x))) 1
          (riemannianVolumeMeasure I M g) :=
        hG'n.mono_exponent hp
      have hG'_int : Integrable (fun x : M =>
          Real.sqrt (g.inner x (G' x) (G' x)))
          (riemannianVolumeMeasure I M g) :=
        memLp_one_iff_integrable.mp hG'_one
      refine Integrable.mono' (g := fun x : M =>
          C_X * Real.sqrt (g.inner x (G' x) (G' x))) ?_ (h₂.1 X) ?_
      · exact hG'_int.const_mul C_X
      · refine Filter.Eventually.of_forall (fun x => ?_)
        rw [Real.norm_eq_abs]
        exact h_bound_aux G' x
    rw [integral_add h_int_G h_int_G']
    rw [h₁.pairing_eq X hX, h₂.pairing_eq X hX]
    have h_div_cont : Continuous (divergence_g (I := I) g X) :=
      (divergence_g_contMDiff (I := I) g X).continuous
    have h_int_uX : Integrable (fun x : M => u x * divergence_g (I := I) g X x)
        (riemannianVolumeMeasure I M g) := by
      have hu_one : MemLp u 1 (riemannianVolumeMeasure I M g) :=
        hu.mono_exponent hp
      have hu_int : Integrable u (riemannianVolumeMeasure I M g) :=
        memLp_one_iff_integrable.mp hu_one
      obtain ⟨C, hC⟩ := exists_bound_continuous_compactSpace h_div_cont
      refine hu_int.mul_bdd (c := C) ?_ ?_
      · exact h_div_cont.aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs]
        exact hC x
    have h_int_vX : Integrable (fun x : M => v x * divergence_g (I := I) g X x)
        (riemannianVolumeMeasure I M g) := by
      have hv_one : MemLp v 1 (riemannianVolumeMeasure I M g) :=
        hv.mono_exponent hp
      have hv_int : Integrable v (riemannianVolumeMeasure I M g) :=
        memLp_one_iff_integrable.mp hv_one
      obtain ⟨C, hC⟩ := exists_bound_continuous_compactSpace h_div_cont
      refine hv_int.mul_bdd (c := C) ?_ ?_
      · exact h_div_cont.aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs]
        exact hC x
    rw [show (-∫ x, u x * divergence_g (I := I) g X x
              ∂(riemannianVolumeMeasure I M g)) +
          (-∫ x, v x * divergence_g (I := I) g X x
              ∂(riemannianVolumeMeasure I M g)) =
        -((∫ x, u x * divergence_g (I := I) g X x
              ∂(riemannianVolumeMeasure I M g)) +
          (∫ x, v x * divergence_g (I := I) g X x
              ∂(riemannianVolumeMeasure I M g))) from by ring]
    rw [← integral_add h_int_uX h_int_vX]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    ring

/-- `MemW1pIntrinsicLp` is closed under addition, provided the pointwise
`g`-norm-squared of the sum is `AEStronglyMeasurable`. The latter hypothesis
is automatic for smooth weak gradients (where the norm is continuous), and
in general can be supplied by ad-hoc means. -/
theorem MemW1pIntrinsicLp.add_of_aestronglyMeasurable_norm
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemW1pIntrinsicLp (I := I) (M := M) g p u)
    (hv : MemW1pIntrinsicLp (I := I) (M := M) g p v)
    (hSum_aem :
      ∀ G G' : M → E,
        HasWeakRiemannianGradLp (I := I) (M := M) g u G →
        HasWeakRiemannianGradLp (I := I) (M := M) g v G' →
        AEStronglyMeasurable
          (fun x : M => Real.sqrt
            (g.inner x ((fun y : M => G y + G' y) x)
              ((fun y : M => G y + G' y) x)))
          (riemannianVolumeMeasure I M g)) :
    MemW1pIntrinsicLp (I := I) (M := M) g p (fun x => u x + v x) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  obtain ⟨hu_p, G, hG_weak, hG_p⟩ := hu
  obtain ⟨hv_p, G', hG'_weak, hG'_p⟩ := hv
  refine ⟨hu_p.add hv_p, (fun x : M => G x + G' x), ?_, ?_⟩
  · exact HasWeakRiemannianGradLp.add (I := I) (M := M) hp hG_weak hG'_weak
      hu_p hv_p hG_p hG'_p
  · refine MemLp.of_le (g := fun x : M =>
        Real.sqrt (g.inner x (G x) (G x)) +
          Real.sqrt (g.inner x (G' x) (G' x)))
      (hG_p.add hG'_p) ?_ ?_
    · exact hSum_aem G G' hG_weak hG'_weak
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have htri := g_norm_triangle g x (G x) (G' x)
      have hLHS_nn : 0 ≤ Real.sqrt (g.inner x (G x + G' x) (G x + G' x)) :=
        Real.sqrt_nonneg _
      have hRHS_nn : 0 ≤ Real.sqrt (g.inner x (G x) (G x)) +
          Real.sqrt (g.inner x (G' x) (G' x)) :=
        add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      rw [Real.norm_eq_abs (Real.sqrt _),
        Real.norm_eq_abs (Real.sqrt _ + Real.sqrt _),
        abs_of_nonneg hLHS_nn, abs_of_nonneg hRHS_nn]
      exact htri

/-- A constant scalar multiple of a weak Riemannian gradient. -/
theorem HasWeakRiemannianGradLp.const_smul
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ} {G : M → E}
    (h : HasWeakRiemannianGradLp (I := I) (M := M) g u G)
    (hu : MemLp u p (riemannianVolumeMeasure I M g)) :
    HasWeakRiemannianGradLp (I := I) (M := M) g (fun x => c * u x)
      (fun x : M => c • G x) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  refine ⟨?_, ?_⟩
  · intro Y
    have hcongr : (fun x : M =>
        g.inner x ((fun y : M => c • G y) x) (Y x)) =
        (fun x : M => c * g.inner x (G x) (Y x)) := by
      funext x
      exact g_inner_smul_left g x c (G x) (Y x)
    rw [hcongr]
    exact (h.1 Y).const_mul c
  · intro X hX
    have hpt : ∀ x : M,
        g.inner x ((fun y : M => c • G y) x) (X x) =
          c * g.inner x (G x) (X x) := by
      intro x
      exact g_inner_smul_left g x c (G x) (X x)
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_const_mul c]
    rw [h.pairing_eq X hX]
    have h_div_cont : Continuous (divergence_g (I := I) g X) :=
      (divergence_g_contMDiff (I := I) g X).continuous
    have h_int_uX : Integrable (fun x : M => u x * divergence_g (I := I) g X x)
        (riemannianVolumeMeasure I M g) := by
      have hu_one : MemLp u 1 (riemannianVolumeMeasure I M g) :=
        hu.mono_exponent hp
      have hu_int : Integrable u (riemannianVolumeMeasure I M g) :=
        memLp_one_iff_integrable.mp hu_one
      obtain ⟨C, hC⟩ := exists_bound_continuous_compactSpace h_div_cont
      refine hu_int.mul_bdd (c := C) ?_ ?_
      · exact h_div_cont.aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs]
        exact hC x
    have hcong : (fun x : M => (c * u x) * divergence_g (I := I) g X x) =
        (fun x : M => c * (u x * divergence_g (I := I) g X x)) := by
      funext x; ring
    rw [hcong, integral_const_mul]
    ring

/-- Closure of `MemW1pIntrinsicLp` under scalar multiplication. -/
theorem MemW1pIntrinsicLp.const_smul
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ}
    (hu : MemW1pIntrinsicLp (I := I) (M := M) g p u) :
    MemW1pIntrinsicLp (I := I) (M := M) g p (fun x => c * u x) := by
  obtain ⟨hu_p, G, hG_weak, hG_p⟩ := hu
  refine ⟨hu_p.const_mul c, (fun x : M => c • G x), ?_, ?_⟩
  · exact HasWeakRiemannianGradLp.const_smul (I := I) (M := M) hp c hG_weak hu_p
  · have hcongr : (fun x : M => Real.sqrt
        (g.inner x ((fun y : M => c • G y) x)
          ((fun y : M => c • G y) x))) =
        (fun x : M => |c| * Real.sqrt (g.inner x (G x) (G x))) := by
      funext x
      exact g_norm_const_smul g x c (G x)
    rw [hcongr]
    exact hG_p.const_mul (|c|)

/-- The negation of a weak Riemannian gradient is a weak gradient of the
negated function. -/
theorem HasWeakRiemannianGradLp.neg
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ} {G : M → E}
    (h : HasWeakRiemannianGradLp (I := I) (M := M) g u G)
    (hu : MemLp u p (riemannianVolumeMeasure I M g)) :
    HasWeakRiemannianGradLp (I := I) (M := M) g (fun x => -u x)
      (fun x : M => -G x) := by
  have h1 : HasWeakRiemannianGradLp (I := I) (M := M) g (fun x => (-1 : ℝ) * u x)
      (fun x : M => (-1 : ℝ) • G x) :=
    HasWeakRiemannianGradLp.const_smul (I := I) (M := M) hp (-1) h hu
  have h_u : (fun x : M => (-1 : ℝ) * u x) = (fun x => -u x) := by
    funext x; ring
  have h_G : (fun x : M => (-1 : ℝ) • G x) = (fun x : M => -G x) := by
    funext x; rw [neg_one_smul]
  rw [h_u] at h1
  rw [h_G] at h1
  exact h1

/-- Closure of `MemW1pIntrinsicLp` under negation. -/
theorem MemW1pIntrinsicLp.neg
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ}
    (hu : MemW1pIntrinsicLp (I := I) (M := M) g p u) :
    MemW1pIntrinsicLp (I := I) (M := M) g p (fun x => -u x) := by
  have h := MemW1pIntrinsicLp.const_smul (I := I) (M := M) hp (-1) hu
  have h_eq : (fun x : M => (-1 : ℝ) * u x) = (fun x => -u x) := by
    funext x; ring
  rw [h_eq] at h
  exact h

/-- Closure of `MemW1pIntrinsicLp` under subtraction, given a measurability
hypothesis on the difference's `g`-norm. -/
theorem MemW1pIntrinsicLp.sub_of_aestronglyMeasurable_norm
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemW1pIntrinsicLp (I := I) (M := M) g p u)
    (hv : MemW1pIntrinsicLp (I := I) (M := M) g p v)
    (hSub_aem :
      ∀ G G' : M → E,
        HasWeakRiemannianGradLp (I := I) (M := M) g u G →
        HasWeakRiemannianGradLp (I := I) (M := M) g (fun x => -v x)
          (fun x : M => -G' x) →
        AEStronglyMeasurable
          (fun x : M => Real.sqrt
            (g.inner x ((fun y : M => G y + -G' y) x)
              ((fun y : M => G y + -G' y) x)))
          (riemannianVolumeMeasure I M g)) :
    MemW1pIntrinsicLp (I := I) (M := M) g p (fun x => u x - v x) := by
  obtain ⟨hu_p, G, hG_weak, hG_p⟩ := hu
  obtain ⟨hv_p, G', hG'_weak, hG'_p⟩ := hv
  have h_neg_v : MemW1pIntrinsicLp (I := I) (M := M) g p (fun x => -v x) := by
    refine ⟨hv_p.neg, (fun x : M => -G' x), ?_, ?_⟩
    · exact HasWeakRiemannianGradLp.neg (I := I) (M := M) hp hG'_weak hv_p
    · have hcongr : (fun x : M =>
          Real.sqrt (g.inner x ((fun y : M => -G' y) x)
            ((fun y : M => -G' y) x))) =
          (fun x : M => Real.sqrt (g.inner x (G' x) (G' x))) := by
        funext x
        exact g_norm_neg g x (G' x)
      rw [hcongr]
      exact hG'_p
  have h_neg_v_unfold : ∃ G'' : M → E,
      HasWeakRiemannianGradLp (I := I) (M := M) g (fun x => -v x) G'' ∧
      MemLp (fun x : M => Real.sqrt (g.inner x (G'' x) (G'' x))) p
        (riemannianVolumeMeasure I M g) := h_neg_v.2
  obtain ⟨G_neg, hG_neg_weak, hG_neg_p⟩ := h_neg_v_unfold
  refine ⟨?_, (fun x : M => G x + -G' x), ?_, ?_⟩
  · have : (fun x : M => u x - v x) = (fun x => u x + -v x) := by
      funext x; ring
    rw [this]
    exact hu_p.add hv_p.neg
  · have h_neg_G' : HasWeakRiemannianGradLp (I := I) (M := M) g (fun x => -v x)
        (fun x : M => -G' x) :=
      HasWeakRiemannianGradLp.neg (I := I) (M := M) hp hG'_weak hv_p
    have h_add : HasWeakRiemannianGradLp (I := I) (M := M) g
        (fun x => u x + -v x) (fun x : M => G x + -G' x) := by
      have h_neg_v_p : MemLp (fun x => -v x) p
          (riemannianVolumeMeasure I M g) := hv_p.neg
      have h_neg_G'_p : MemLp (fun x : M =>
          Real.sqrt (g.inner x (-G' x) (-G' x))) p
          (riemannianVolumeMeasure I M g) := by
        have hcongr : (fun x : M =>
            Real.sqrt (g.inner x (-G' x) (-G' x))) =
            (fun x : M => Real.sqrt (g.inner x (G' x) (G' x))) := by
          funext x
          exact g_norm_neg g x (G' x)
        rw [hcongr]
        exact hG'_p
      exact HasWeakRiemannianGradLp.add (I := I) (M := M) hp hG_weak h_neg_G'
        hu_p h_neg_v_p hG_p h_neg_G'_p
    have h_eq : (fun x : M => u x - v x) = (fun x => u x + -v x) := by
      funext x; ring
    rw [h_eq]
    exact h_add
  · have h_neg_G' : HasWeakRiemannianGradLp (I := I) (M := M) g (fun x => -v x)
        (fun x : M => -G' x) :=
      HasWeakRiemannianGradLp.neg (I := I) (M := M) hp hG'_weak hv_p
    have h_aem := hSub_aem G G' hG_weak h_neg_G'
    refine MemLp.of_le (g := fun x : M =>
        Real.sqrt (g.inner x (G x) (G x)) +
          Real.sqrt (g.inner x (G' x) (G' x)))
      (hG_p.add hG'_p) ?_ ?_
    · exact h_aem
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have htri := g_norm_triangle g x (G x) (-G' x)
      have h_neg_norm : Real.sqrt (g.inner x (-G' x) (-G' x)) =
          Real.sqrt (g.inner x (G' x) (G' x)) := g_norm_neg g x (G' x)
      rw [h_neg_norm] at htri
      have hLHS_nn : 0 ≤ Real.sqrt (g.inner x (G x + -G' x) (G x + -G' x)) :=
        Real.sqrt_nonneg _
      have hRHS_nn : 0 ≤ Real.sqrt (g.inner x (G x) (G x)) +
          Real.sqrt (g.inner x (G' x) (G' x)) :=
        add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      rw [Real.norm_eq_abs (Real.sqrt _),
        Real.norm_eq_abs (Real.sqrt _ + Real.sqrt _),
        abs_of_nonneg hLHS_nn, abs_of_nonneg hRHS_nn]
      exact htri

/-- The `W^{1,p}_{int,Lp}` norm of `u`. -/
def w1pNormIntrinsicLp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) (u : M → ℝ) : ℝ≥0∞ :=
  eLpNorm u p (riemannianVolumeMeasure I M g) +
    ⨅ (G : M → E) (_ : HasWeakRiemannianGradLp (I := I) (M := M) g u G),
      eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
        (riemannianVolumeMeasure I M g)

private def gradInfimumLp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) (u : M → ℝ) : ℝ≥0∞ :=
  ⨅ (G : M → E) (_ : HasWeakRiemannianGradLp (I := I) (M := M) g u G),
    eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
      (riemannianVolumeMeasure I M g)

private lemma w1pNormIntrinsicLp_def
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) (u : M → ℝ) :
    w1pNormIntrinsicLp (I := I) (M := M) g p u =
      eLpNorm u p (riemannianVolumeMeasure I M g) +
        gradInfimumLp (I := I) (M := M) g p u := rfl

/-- The norm of the zero function is zero. -/
theorem w1pNormIntrinsicLp_zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) :
    w1pNormIntrinsicLp (I := I) (M := M) g p (fun _ : M => (0 : ℝ)) = 0 := by
  rw [w1pNormIntrinsicLp_def]
  rw [show eLpNorm (fun _ : M => (0 : ℝ)) p
        (riemannianVolumeMeasure I M g) = 0 from
      eLpNorm_zero]
  rw [zero_add]
  apply le_antisymm
  · have hzero_grad : HasWeakRiemannianGradLp (I := I) (M := M) g
        (fun _ : M => (0 : ℝ)) (fun _ : M => (0 : E)) :=
      HasWeakRiemannianGradLp.zero (I := I) (M := M) g
    have h_zero_norm :
        eLpNorm (fun x : M => Real.sqrt
          (g.inner x ((fun _ : M => (0 : E)) x)
            ((fun _ : M => (0 : E)) x))) p
          (riemannianVolumeMeasure I M g) = 0 := by
      have hcongr : (fun x : M => Real.sqrt
          (g.inner x ((fun _ : M => (0 : E)) x)
            ((fun _ : M => (0 : E)) x))) =
          (fun _ : M => (0 : ℝ)) := by
        funext x
        change Real.sqrt (g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x)) = 0
        rw [g_inner_zero_left g x (0 : TangentSpace I x)]
        exact Real.sqrt_zero
      rw [hcongr]
      exact eLpNorm_zero
    refine le_trans ?_ (le_of_eq h_zero_norm)
    unfold gradInfimumLp
    exact iInf_le_of_le (fun _ : M => (0 : E)) (iInf_le _ hzero_grad)
  · exact zero_le _

/-- Two weak `L^p` Riemannian gradients of the same function pair identically
against every smooth compactly-supported tangent test field. -/
theorem HasWeakRiemannianGradLp.pairing_inner_eq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {u : M → ℝ}
    {G G' : M → E}
    (h₁ : HasWeakRiemannianGradLp (I := I) (M := M) g u G)
    (h₂ : HasWeakRiemannianGradLp (I := I) (M := M) g u G')
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport (fun x : M => (X x : E))) :
    ∫ x, g.inner x (G x) (X x) ∂(riemannianVolumeMeasure I M g) =
      ∫ x, g.inner x (G' x) (X x) ∂(riemannianVolumeMeasure I M g) := by
  rw [h₁.pairing_eq X hX, h₂.pairing_eq X hX]

/-- The pairing of the difference of two weak `L^p` Riemannian gradients with
any smooth compactly-supported tangent test field is zero. -/
theorem HasWeakRiemannianGradLp.pairing_inner_diff_eq_zero
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {u : M → ℝ}
    {G G' : M → E}
    (h₁ : HasWeakRiemannianGradLp (I := I) (M := M) g u G)
    (h₂ : HasWeakRiemannianGradLp (I := I) (M := M) g u G')
    (hG_p : MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) 1
      (riemannianVolumeMeasure I M g))
    (hG'_p : MemLp (fun x : M => Real.sqrt (g.inner x (G' x) (G' x))) 1
      (riemannianVolumeMeasure I M g))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport (fun x : M => (X x : E))) :
    ∫ x, (g.inner x (G x) (X x) - g.inner x (G' x) (X x))
        ∂(riemannianVolumeMeasure I M g) = 0 := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hX_norm_cont : Continuous (fun x : M =>
      Real.sqrt (g.inner x (X x) (X x))) :=
    continuous_g_norm_smooth_section g X
  obtain ⟨C_X, hC_X⟩ := exists_bound_continuous_compactSpace hX_norm_cont
  have h_bound_G : ∀ x : M, |g.inner x (G x) (X x)| ≤
      C_X * Real.sqrt (g.inner x (G x) (G x)) := by
    intro x
    have hCS := g_inner_cauchy_schwarz g x (G x) (X x)
    have hX_bd : Real.sqrt (g.inner x (X x) (X x)) ≤ C_X := by
      have h := hC_X x
      have hnn : 0 ≤ Real.sqrt (g.inner x (X x) (X x)) := Real.sqrt_nonneg _
      rw [abs_of_nonneg hnn] at h; exact h
    calc |g.inner x (G x) (X x)|
        ≤ Real.sqrt (g.inner x (G x) (G x)) * Real.sqrt (g.inner x (X x) (X x)) := hCS
      _ ≤ Real.sqrt (g.inner x (G x) (G x)) * C_X :=
            mul_le_mul_of_nonneg_left hX_bd (Real.sqrt_nonneg _)
      _ = C_X * Real.sqrt (g.inner x (G x) (G x)) := by ring
  have h_int_G : Integrable (fun x : M => g.inner x (G x) (X x))
      (riemannianVolumeMeasure I M g) := by
    have hG_int : Integrable (fun x : M => Real.sqrt (g.inner x (G x) (G x)))
        (riemannianVolumeMeasure I M g) := memLp_one_iff_integrable.mp hG_p
    refine Integrable.mono' (g := fun x : M =>
        C_X * Real.sqrt (g.inner x (G x) (G x))) ?_ (h₁.1 X) ?_
    · exact hG_int.const_mul C_X
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs]
      exact h_bound_G x
  have h_bound_G' : ∀ x : M, |g.inner x (G' x) (X x)| ≤
      C_X * Real.sqrt (g.inner x (G' x) (G' x)) := by
    intro x
    have hCS := g_inner_cauchy_schwarz g x (G' x) (X x)
    have hX_bd : Real.sqrt (g.inner x (X x) (X x)) ≤ C_X := by
      have h := hC_X x
      have hnn : 0 ≤ Real.sqrt (g.inner x (X x) (X x)) := Real.sqrt_nonneg _
      rw [abs_of_nonneg hnn] at h; exact h
    calc |g.inner x (G' x) (X x)|
        ≤ Real.sqrt (g.inner x (G' x) (G' x)) * Real.sqrt (g.inner x (X x) (X x)) := hCS
      _ ≤ Real.sqrt (g.inner x (G' x) (G' x)) * C_X :=
            mul_le_mul_of_nonneg_left hX_bd (Real.sqrt_nonneg _)
      _ = C_X * Real.sqrt (g.inner x (G' x) (G' x)) := by ring
  have h_int_G' : Integrable (fun x : M => g.inner x (G' x) (X x))
      (riemannianVolumeMeasure I M g) := by
    have hG'_int : Integrable (fun x : M => Real.sqrt (g.inner x (G' x) (G' x)))
        (riemannianVolumeMeasure I M g) := memLp_one_iff_integrable.mp hG'_p
    refine Integrable.mono' (g := fun x : M =>
        C_X * Real.sqrt (g.inner x (G' x) (G' x))) ?_ (h₂.1 X) ?_
    · exact hG'_int.const_mul C_X
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs]
      exact h_bound_G' x
  rw [integral_sub h_int_G h_int_G']
  rw [HasWeakRiemannianGradLp.pairing_inner_eq h₁ h₂ X hX, sub_self]

/-- The scalar function `x ↦ g.inner x (G x) (σ x) - g.inner x (G' x) (σ x)`
vanishes almost everywhere when `G, G'` are two weak `L^p` Riemannian
gradients of the same function and `σ` is any smooth tangent section. -/
theorem HasWeakRiemannianGradLp.pairing_diff_smooth_aeEq_zero
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {u : M → ℝ}
    {G G' : M → E}
    (h₁ : HasWeakRiemannianGradLp (I := I) (M := M) g u G)
    (h₂ : HasWeakRiemannianGradLp (I := I) (M := M) g u G')
    (hG_p : MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) 1
      (riemannianVolumeMeasure I M g))
    (hG'_p : MemLp (fun x : M => Real.sqrt (g.inner x (G' x) (G' x))) 1
      (riemannianVolumeMeasure I M g))
    (σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (fun x : M => g.inner x (G x) (σ x) - g.inner x (G' x) (σ x))
      =ᵐ[riemannianVolumeMeasure I M g] (fun _ => 0) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hf_aem : AEStronglyMeasurable
      (fun x : M => g.inner x (G x) (σ x) - g.inner x (G' x) (σ x))
      (riemannianVolumeMeasure I M g) :=
    (h₁.1 σ).sub (h₂.1 σ)
  have hσ_norm_cont : Continuous (fun x : M =>
      Real.sqrt (g.inner x (σ x) (σ x))) :=
    continuous_g_norm_smooth_section g σ
  obtain ⟨C_σ, hC_σ⟩ := exists_bound_continuous_compactSpace hσ_norm_cont
  have h_bound_aux : ∀ (W : M → E), ∀ x : M,
      |g.inner x (W x) (σ x)| ≤
        C_σ * Real.sqrt (g.inner x (W x) (W x)) := by
    intro W x
    have hCS := g_inner_cauchy_schwarz g x (W x) (σ x)
    have hσ_bd : Real.sqrt (g.inner x (σ x) (σ x)) ≤ C_σ := by
      have h := hC_σ x
      have hnn : 0 ≤ Real.sqrt (g.inner x (σ x) (σ x)) := Real.sqrt_nonneg _
      rw [abs_of_nonneg hnn] at h; exact h
    calc |g.inner x (W x) (σ x)|
        ≤ Real.sqrt (g.inner x (W x) (W x)) * Real.sqrt (g.inner x (σ x) (σ x)) := hCS
      _ ≤ Real.sqrt (g.inner x (W x) (W x)) * C_σ :=
            mul_le_mul_of_nonneg_left hσ_bd (Real.sqrt_nonneg _)
      _ = C_σ * Real.sqrt (g.inner x (W x) (W x)) := by ring
  have h_int_G : Integrable (fun x : M => g.inner x (G x) (σ x))
      (riemannianVolumeMeasure I M g) := by
    have hG_int : Integrable (fun x : M => Real.sqrt (g.inner x (G x) (G x)))
        (riemannianVolumeMeasure I M g) := memLp_one_iff_integrable.mp hG_p
    refine Integrable.mono' (g := fun x : M =>
        C_σ * Real.sqrt (g.inner x (G x) (G x))) ?_ (h₁.1 σ) ?_
    · exact hG_int.const_mul C_σ
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs]
      exact h_bound_aux G x
  have h_int_G' : Integrable (fun x : M => g.inner x (G' x) (σ x))
      (riemannianVolumeMeasure I M g) := by
    have hG'_int : Integrable (fun x : M => Real.sqrt (g.inner x (G' x) (G' x)))
        (riemannianVolumeMeasure I M g) := memLp_one_iff_integrable.mp hG'_p
    refine Integrable.mono' (g := fun x : M =>
        C_σ * Real.sqrt (g.inner x (G' x) (G' x))) ?_ (h₂.1 σ) ?_
    · exact hG'_int.const_mul C_σ
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs]
      exact h_bound_aux G' x
  have hf_int : Integrable
      (fun x : M => g.inner x (G x) (σ x) - g.inner x (G' x) (σ x))
      (riemannianVolumeMeasure I M g) :=
    h_int_G.sub h_int_G'
  refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero (I := I)
    hf_int.locallyIntegrable ?_
  intro φ hφ_smooth hφ_supp
  set φσ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothSmul (I := I) φ hφ_smooth σ with hφσ_def
  have hφσ_supp : HasCompactSupport (fun x : M => (φσ x : E)) := by
    have hsupp_sub : Function.support (fun x : M => (φσ x : E)) ⊆
        Function.support φ := by
      intro x hx
      change φ x • σ x ≠ 0 at hx
      by_contra hne
      have h0 : φ x = 0 := Function.notMem_support.mp hne
      apply hx
      rw [h0]; exact zero_smul _ _
    refine HasCompactSupport.of_support_subset_isCompact (K := tsupport φ)
      hφ_supp ?_
    exact hsupp_sub.trans (subset_tsupport _)
  have h_pair_G : ∫ x, g.inner x (G x) (φσ x)
        ∂(riemannianVolumeMeasure I M g) =
      -∫ x, u x * divergence_g (I := I) g φσ x
        ∂(riemannianVolumeMeasure I M g) := h₁.pairing_eq φσ hφσ_supp
  have h_pair_G' : ∫ x, g.inner x (G' x) (φσ x)
        ∂(riemannianVolumeMeasure I M g) =
      -∫ x, u x * divergence_g (I := I) g φσ x
        ∂(riemannianVolumeMeasure I M g) := h₂.pairing_eq φσ hφσ_supp
  have h_diff_eq : ∫ x, (g.inner x (G x) (φσ x) - g.inner x (G' x) (φσ x))
        ∂(riemannianVolumeMeasure I M g) = 0 := by
    have h_int_G_φσ : Integrable (fun x : M => g.inner x (G x) (φσ x))
        (riemannianVolumeMeasure I M g) := by
      have hφσ_norm_cont : Continuous (fun x : M =>
          Real.sqrt (g.inner x (φσ x) (φσ x))) :=
        continuous_g_norm_smooth_section g φσ
      obtain ⟨C_φσ, hC_φσ⟩ := exists_bound_continuous_compactSpace hφσ_norm_cont
      have hG_int : Integrable (fun x : M => Real.sqrt (g.inner x (G x) (G x)))
          (riemannianVolumeMeasure I M g) := memLp_one_iff_integrable.mp hG_p
      refine Integrable.mono' (g := fun x : M =>
          C_φσ * Real.sqrt (g.inner x (G x) (G x))) ?_ (h₁.1 φσ) ?_
      · exact hG_int.const_mul C_φσ
      · refine Filter.Eventually.of_forall (fun x => ?_)
        rw [Real.norm_eq_abs]
        have hCS := g_inner_cauchy_schwarz g x (G x) (φσ x)
        have hφσ_bd : Real.sqrt (g.inner x (φσ x) (φσ x)) ≤ C_φσ := by
          have h := hC_φσ x
          have hnn : 0 ≤ Real.sqrt (g.inner x (φσ x) (φσ x)) :=
            Real.sqrt_nonneg _
          rw [abs_of_nonneg hnn] at h; exact h
        calc |g.inner x (G x) (φσ x)|
            ≤ Real.sqrt (g.inner x (G x) (G x)) * Real.sqrt (g.inner x (φσ x) (φσ x)) := hCS
          _ ≤ Real.sqrt (g.inner x (G x) (G x)) * C_φσ :=
                mul_le_mul_of_nonneg_left hφσ_bd (Real.sqrt_nonneg _)
          _ = C_φσ * Real.sqrt (g.inner x (G x) (G x)) := by ring
    have h_int_G'_φσ : Integrable (fun x : M => g.inner x (G' x) (φσ x))
        (riemannianVolumeMeasure I M g) := by
      have hφσ_norm_cont : Continuous (fun x : M =>
          Real.sqrt (g.inner x (φσ x) (φσ x))) :=
        continuous_g_norm_smooth_section g φσ
      obtain ⟨C_φσ, hC_φσ⟩ := exists_bound_continuous_compactSpace hφσ_norm_cont
      have hG'_int : Integrable (fun x : M =>
          Real.sqrt (g.inner x (G' x) (G' x)))
          (riemannianVolumeMeasure I M g) := memLp_one_iff_integrable.mp hG'_p
      refine Integrable.mono' (g := fun x : M =>
          C_φσ * Real.sqrt (g.inner x (G' x) (G' x))) ?_ (h₂.1 φσ) ?_
      · exact hG'_int.const_mul C_φσ
      · refine Filter.Eventually.of_forall (fun x => ?_)
        rw [Real.norm_eq_abs]
        have hCS := g_inner_cauchy_schwarz g x (G' x) (φσ x)
        have hφσ_bd : Real.sqrt (g.inner x (φσ x) (φσ x)) ≤ C_φσ := by
          have h := hC_φσ x
          have hnn : 0 ≤ Real.sqrt (g.inner x (φσ x) (φσ x)) :=
            Real.sqrt_nonneg _
          rw [abs_of_nonneg hnn] at h; exact h
        calc |g.inner x (G' x) (φσ x)|
            ≤ Real.sqrt (g.inner x (G' x) (G' x)) * Real.sqrt (g.inner x (φσ x) (φσ x)) := hCS
          _ ≤ Real.sqrt (g.inner x (G' x) (G' x)) * C_φσ :=
                mul_le_mul_of_nonneg_left hφσ_bd (Real.sqrt_nonneg _)
          _ = C_φσ * Real.sqrt (g.inner x (G' x) (G' x)) := by ring
    rw [integral_sub h_int_G_φσ h_int_G'_φσ]
    rw [h_pair_G, h_pair_G', sub_self]
  have hpt_eq : ∀ x : M,
      g.inner x (G x) (φσ x) - g.inner x (G' x) (φσ x) =
        φ x • (g.inner x (G x) (σ x) - g.inner x (G' x) (σ x)) := by
    intro x
    change g.inner x (G x) (φ x • σ x) - g.inner x (G' x) (φ x • σ x) =
        φ x * (g.inner x (G x) (σ x) - g.inner x (G' x) (σ x))
    rw [g_inner_smul_right g x (G x) (φ x) (σ x),
      g_inner_smul_right g x (G' x) (φ x) (σ x)]
    ring
  rw [show (fun x : M => φ x •
      (g.inner x (G x) (σ x) - g.inner x (G' x) (σ x))) =
      (fun x : M => g.inner x (G x) (φσ x) - g.inner x (G' x) (φσ x)) from by
    funext x; exact (hpt_eq x).symm]
  exact h_diff_eq

end IntrinsicLp
end Sobolev
end Analysis
end DifferentialGeometry

end
