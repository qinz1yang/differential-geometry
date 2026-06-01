import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lp
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Gradient
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.IntegrationByParts
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Global
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InteriorCompactSupport
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.POUReduction
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.PartialDerivWithin
import DifferentialGeometry.Integral.DivergenceTheorem.POUReduction
import DifferentialGeometry.Integral.DivergenceTheorem.TangentAction
import DifferentialGeometry.Integral.Measure.Properties
import DifferentialGeometry.Tensor.RSTensor.TangentRiemannian
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Intrinsic Sobolev space `W^{1,p}_{int,Lp}(M)` on manifolds with boundary

For a closed (compact) smooth Riemannian manifold `(M, g)` whose model `I` may
carry a smooth boundary, and an exponent `1 ≤ p ≤ ∞` (with `p ≠ ∞`), this file
extends the boundaryless intrinsic Sobolev space
`Analysis/Sobolev/IntrinsicLp.lean` to the with-boundary setting.

Compared with the boundaryless case, the integration-by-parts identity carries
a boundary correction term in general:
`∫_M g.inner G X = -∫_M u · div_g^∂ X + ∫_∂M u · g.inner X ν dS`.

The cleanest way to define the Sobolev space without referring to a boundary
trace is to test only against tangent fields **supported in the manifold
interior** `I.interior M`. The boundary correction term then vanishes
identically (because both `X` and `div_g^∂ X` vanish on the boundary), so the
IBP identity reduces to the boundaryless form
`∫_M g.inner G X = -∫_M u · div_g^∂ X` against interior-supported test fields.
This corresponds to the **Dirichlet-style** weak gradient.

A function `G : M → E` (interpreted as a tangent section via the canonical
definitional equality `TangentSpace I x = E`) is a **weak Riemannian gradient
with boundary** of `u : M → ℝ` when:

1. The pairing `x ↦ g.inner x (G x) (Y x)` is `AEStronglyMeasurable` for every
   smooth tangent test field `Y`.
2. For every smooth tangent test field `X` with **compact support contained
   in the manifold interior** `I.interior M`, the IBP identity
   `∫_M g.inner G X dμ_g = -∫_M u · div_g^∂ X dμ_g` holds.

The Sobolev space `MemW1pIntrinsicLp_withBoundary g p u` then asks for
`u ∈ L^p` plus the existence of such a `G` whose pointwise `g`-norm
`x ↦ √(g.inner x (G x) (G x))` is in `L^p`.

## Main definitions

* `HasWeakRiemannianGradLp_withBoundary g u G` — `G : M → E` is a weak
  Riemannian gradient of `u` (against interior-supported test fields).
* `MemW1pIntrinsicLp_withBoundary g p u` — `u ∈ L^p` and admits an `L^p` weak
  Riemannian gradient with boundary.
* `w1pNormIntrinsicLp_withBoundary g p u` — the intrinsic Sobolev norm.

## Main results

* `MemW1pIntrinsicLp_withBoundary.zero` and
  `MemW1pIntrinsicLp_withBoundary.const_smul` — algebraic closure under zero
  and scalar multiplication.
* `HasWeakRiemannianGradLp_withBoundary.add` — additivity at the IBP-identity
  level.
* `MemW1pIntrinsicLp_withBoundary_const` — every constant function on a
  closed Riemannian manifold with smooth boundary lies in
  `MemW1pIntrinsicLp_withBoundary` for every exponent `p`.
* `w1pNormIntrinsicLp_withBoundary_zero` — the norm of the zero function is
  zero.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Function
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary
namespace IntrinsicLp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

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

private lemma g_inner_neg_left
    (g : SmoothRiemannianMetric I M) (x : M) (v y : TangentSpace I x) :
    g.inner x (-v) y = - g.inner x v y := by
  rw [map_neg, ContinuousLinearMap.neg_apply]

private lemma g_inner_neg_right
    (g : SmoothRiemannianMetric I M) (x : M) (v y : TangentSpace I x) :
    g.inner x v (-y) = - g.inner x v y := by
  rw [ContinuousLinearMap.map_neg]

private lemma g_inner_add_diag
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    g.inner x (v + w) (v + w) =
      g.inner x v v + 2 * g.inner x v w + g.inner x w w := by
  rw [g_inner_add_left g x v w (v + w),
    g_inner_add_right g x v v w, g_inner_add_right g x w v w]
  have hsymm : g.inner x w v = g.inner x v w := g.symm x w v
  rw [hsymm]; ring

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

private lemma g_norm_const_smul
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ) (v : TangentSpace I x) :
    Real.sqrt (g.inner x (c • v) (c • v)) =
      |c| * Real.sqrt (g.inner x v v) := by
  rw [g_inner_smul_left g x c v (c • v), g_inner_smul_right g x v c v]
  rw [show c * (c * g.inner x v v) = c ^ 2 * g.inner x v v from by ring]
  rw [Real.sqrt_mul (sq_nonneg c)]
  rw [Real.sqrt_sq_eq_abs]

private lemma g_norm_neg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    Real.sqrt (g.inner x (-v) (-v)) = Real.sqrt (g.inner x v v) := by
  rw [g_inner_neg_left g x v (-v), g_inner_neg_right g x v v]
  simp

private lemma continuous_g_inner_smooth_sections
    (g : SmoothRiemannianMetric I M)
    (G X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Continuous (fun b : M => g.inner b (G b) (X b)) :=
  TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g G X

private lemma continuous_g_norm_smooth_section
    (g : SmoothRiemannianMetric I M)
    (G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Continuous (fun b : M => Real.sqrt (g.inner b (G b) (G b))) :=
  Real.continuous_sqrt.comp (continuous_g_inner_smooth_sections g G G)

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

/-- A function `G : M → E` (interpreted as a tangent section via the canonical
`TangentSpace I x = E` definitional equality) is a **weak Riemannian
gradient with boundary** of `u : M → ℝ` if:

* the pairing `x ↦ g.inner x (G x) (Y x)` is `AEStronglyMeasurable` for every
  smooth tangent test field `Y`; and
* for every smooth tangent test field `X` with compact support contained in
  the manifold interior `I.interior M`, the integration-by-parts identity
  $$\int_M g.inner x (G x) (X x)\,d\mu_g
    = -\int_M u(x) \cdot \operatorname{div}_g^{(\partial)}(X)(x)\,d\mu_g$$
  holds.

The interior-supported test-field requirement makes the boundary correction
term in the with-boundary divergence theorem vanish identically, so the
identity above takes the same shape as in the boundaryless case. -/
def HasWeakRiemannianGradLp_withBoundary
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) (G : M → E) : Prop :=
  (∀ Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
    AEStronglyMeasurable (fun x : M => g.inner x (G x) (Y x))
      (riemannianVolumeMeasure I M g)) ∧
  ∀ X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
    HasCompactSupport (fun x : M => (X x : E)) →
    tsupport (fun x : M => (X x : E)) ⊆ I.interior M →
      ∫ x, g.inner x (G x) (X x) ∂(riemannianVolumeMeasure I M g) =
        -∫ x, u x * divergence_g_with_boundary (I := I) g X x
          ∂(riemannianVolumeMeasure I M g)

namespace HasWeakRiemannianGradLp_withBoundary

variable {g : SmoothRiemannianMetric I M} {u : M → ℝ} {G : M → E}

/-- The integration-by-parts identity. -/
lemma pairing_eq
    [T2Space M] [SigmaCompactSpace M]
    (h : HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g u G)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport (fun x : M => (X x : E)))
    (hX_int : tsupport (fun x : M => (X x : E)) ⊆ I.interior M) :
    ∫ x, g.inner x (G x) (X x) ∂(riemannianVolumeMeasure I M g) =
      -∫ x, u x * divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure I M g) := h.2 X hX hX_int

/-- The pairing is `AEStronglyMeasurable` against every smooth test section. -/
lemma pairing_aestronglyMeasurable
    [T2Space M] [SigmaCompactSpace M]
    (h : HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g u G)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    AEStronglyMeasurable (fun x : M => g.inner x (G x) (Y x))
      (riemannianVolumeMeasure I M g) := h.1 Y

end HasWeakRiemannianGradLp_withBoundary

/-- `MemW1pIntrinsicLp_withBoundary g p u` means:

* `u : M → ℝ` is in `L^p` against the Riemannian volume measure;
* there exists a function `G : M → E` which is a weak Riemannian gradient
  of `u` with boundary (in the `HasWeakRiemannianGradLp_withBoundary` sense),
  and whose pointwise `g`-norm `x ↦ √(g.inner x (G x) (G x))` is in `L^p`. -/
def MemW1pIntrinsicLp_withBoundary
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) (u : M → ℝ) : Prop :=
  MemLp u p (riemannianVolumeMeasure I M g) ∧
  ∃ G : M → E,
    HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g u G ∧
      MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
        (riemannianVolumeMeasure I M g)

/-- The `L^p` membership component. -/
lemma MemW1pIntrinsicLp_withBoundary.memLp_self
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} {u : M → ℝ}
    (h : MemW1pIntrinsicLp_withBoundary (I := I) (M := M) g p u) :
    MemLp u p (riemannianVolumeMeasure I M g) := h.1

/-- The zero `M → E` map is a weak `L^p` Riemannian gradient with boundary
of the zero function. -/
theorem HasWeakRiemannianGradLp_withBoundary.zero
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g
      (fun _ : M => (0 : ℝ)) (fun _ : M => (0 : E)) := by
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
  · intro X _ _
    have h_LHS : (fun x : M =>
        g.inner x ((fun _ : M => (0 : E)) x) (X x)) =
        (fun _ : M => (0 : ℝ)) := by
      funext x
      change g.inner x (0 : TangentSpace I x) (X x) = 0
      exact g_inner_zero_left g x (X x)
    rw [h_LHS]
    rw [show (fun x : M => (0 : ℝ) * divergence_g_with_boundary (I := I) g X x) =
        (fun _ : M => (0 : ℝ)) from by funext x; simp]
    simp [integral_zero]

/-- The zero scalar function is in `MemW1pIntrinsicLp_withBoundary` for every
exponent. -/
theorem MemW1pIntrinsicLp_withBoundary.zero
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) :
    MemW1pIntrinsicLp_withBoundary (I := I) (M := M) g p
      (fun _ : M => (0 : ℝ)) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  refine ⟨MemLp.zero, (fun _ : M => (0 : E)),
    HasWeakRiemannianGradLp_withBoundary.zero (I := I) (M := M) g, ?_⟩
  have hcongr : (fun x : M => Real.sqrt
      (g.inner x ((fun _ : M => (0 : E)) x) ((fun _ : M => (0 : E)) x))) =
      (fun _ : M => (0 : ℝ)) := by
    funext x
    change Real.sqrt (g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x)) = 0
    rw [g_inner_zero_left g x (0 : TangentSpace I x)]
    exact Real.sqrt_zero
  rw [hcongr]
  exact MemLp.zero

/-- The zero `M → E` map is a weak `L^p` Riemannian gradient with boundary
for any constant function. The IBP identity reduces to `0 = -c · ∫ div`,
which holds because the integral of the with-boundary divergence of an
interior-supported, compactly-supported smooth tangent section is zero. -/
theorem HasWeakRiemannianGradLp_withBoundary.const
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (c : ℝ) :
    HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g
      (fun _ : M => c) (fun _ : M => (0 : E)) := by
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
  · intro X hX hX_int
    have h_LHS : (fun x : M =>
        g.inner x ((fun _ : M => (0 : E)) x) (X x)) =
        (fun _ : M => (0 : ℝ)) := by
      funext x
      change g.inner x (0 : TangentSpace I x) (X x) = 0
      exact g_inner_zero_left g x (X x)
    rw [h_LHS]
    rw [integral_zero]
    have hX' : HasCompactSupport (X : ∀ x, TangentSpace I x) := hX
    have hdiv_zero :
        ∫ x, divergence_g_with_boundary (I := I) g X x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
      integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support
        (I := I) g X hX' hX_int
    have : (fun x : M => c * divergence_g_with_boundary (I := I) g X x) =
        (fun x : M => c * divergence_g_with_boundary (I := I) g X x) := rfl
    rw [show (fun x : M => c * divergence_g_with_boundary (I := I) g X x) =
        (fun x : M => c * divergence_g_with_boundary (I := I) g X x) from rfl]
    rw [integral_const_mul]
    rw [hdiv_zero]
    ring

/-- Every constant function on a closed Riemannian manifold with smooth
boundary lies in `MemW1pIntrinsicLp_withBoundary` for every exponent `p`.
The witness is the zero gradient. -/
theorem MemW1pIntrinsicLp_withBoundary_const
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) (c : ℝ) :
    MemW1pIntrinsicLp_withBoundary (I := I) (M := M) g p
      (fun _ : M => c) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  refine ⟨?_, (fun _ : M => (0 : E)),
    HasWeakRiemannianGradLp_withBoundary.const (I := I) (M := M) g c, ?_⟩
  · exact continuous_memLp_of_compactSpace g p continuous_const
  · have hcongr : (fun x : M => Real.sqrt
        (g.inner x ((fun _ : M => (0 : E)) x) ((fun _ : M => (0 : E)) x))) =
        (fun _ : M => (0 : ℝ)) := by
      funext x
      change Real.sqrt (g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x)) = 0
      rw [g_inner_zero_left g x (0 : TangentSpace I x)]
      exact Real.sqrt_zero
    rw [hcongr]
    exact MemLp.zero

/-- Sum of two `L^p` weak Riemannian gradients with boundary. -/
theorem HasWeakRiemannianGradLp_withBoundary.add
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ} {G G' : M → E}
    (h₁ : HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g u G)
    (h₂ : HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g v G')
    (hu : MemLp u p (riemannianVolumeMeasure I M g))
    (hv : MemLp v p (riemannianVolumeMeasure I M g))
    (hGn : MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
      (riemannianVolumeMeasure I M g))
    (hG'n : MemLp (fun x : M => Real.sqrt (g.inner x (G' x) (G' x))) p
      (riemannianVolumeMeasure I M g)) :
    HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g
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
  · intro X hX hX_int
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
    rw [h₁.pairing_eq X hX hX_int, h₂.pairing_eq X hX hX_int]
    have hX' : HasCompactSupport (X : ∀ x, TangentSpace I x) := hX
    have h_div_supp : tsupport (divergence_g_with_boundary (I := I) g X) ⊆
        tsupport (X : ∀ x, TangentSpace I x) :=
      tsupport_divergence_g_with_boundary_subset_of_interior_support
        (I := I) g X hX_int
    have h_div_supp_int :
        tsupport (divergence_g_with_boundary (I := I) g X) ⊆ I.interior M :=
      h_div_supp.trans hX_int
    have h_div_cont : Continuous (divergence_g_with_boundary (I := I) g X) := by
      rw [continuous_iff_continuousAt]
      intro x
      by_cases hx_supp : x ∈ tsupport (divergence_g_with_boundary (I := I) g X)
      · have hopen_int : IsOpen (I.interior M) :=
          I.isOpen_interior (M := M) (n := ∞)
            (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0))
        have hx_int : x ∈ I.interior M := h_div_supp_int hx_supp
        have hcont_int :
            ContinuousOn (divergence_g_with_boundary (I := I) g X) (I.interior M) :=
          divergence_g_with_boundary_continuousOn_interior (I := I) g X
        exact (hcont_int x hx_int).continuousAt (hopen_int.mem_nhds hx_int)
      · have h_open : IsOpen (tsupport (divergence_g_with_boundary (I := I) g X))ᶜ :=
          (isClosed_tsupport _).isOpen_compl
        have hev_zero : (divergence_g_with_boundary (I := I) g X) =ᶠ[𝓝 x]
            (fun _ => (0 : ℝ)) := by
          filter_upwards [h_open.mem_nhds hx_supp] with y hy
          by_contra hne
          exact hy (subset_tsupport _ hne)
        exact (continuous_const.continuousAt.congr hev_zero.symm)
    have h_int_uX : Integrable (fun x : M => u x * divergence_g_with_boundary (I := I) g X x)
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
    have h_int_vX : Integrable (fun x : M => v x * divergence_g_with_boundary (I := I) g X x)
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
    rw [show (-∫ x, u x * divergence_g_with_boundary (I := I) g X x
              ∂(riemannianVolumeMeasure I M g)) +
          (-∫ x, v x * divergence_g_with_boundary (I := I) g X x
              ∂(riemannianVolumeMeasure I M g)) =
        -((∫ x, u x * divergence_g_with_boundary (I := I) g X x
              ∂(riemannianVolumeMeasure I M g)) +
          (∫ x, v x * divergence_g_with_boundary (I := I) g X x
              ∂(riemannianVolumeMeasure I M g))) from by ring]
    rw [← integral_add h_int_uX h_int_vX]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    ring

/-- A constant scalar multiple of a weak Riemannian gradient with boundary. -/
theorem HasWeakRiemannianGradLp_withBoundary.const_smul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ} {G : M → E}
    (h : HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g u G)
    (hu : MemLp u p (riemannianVolumeMeasure I M g)) :
    HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g
      (fun x => c * u x) (fun x : M => c • G x) := by
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
  · intro X hX hX_int
    have hpt : ∀ x : M,
        g.inner x ((fun y : M => c • G y) x) (X x) =
          c * g.inner x (G x) (X x) := by
      intro x
      exact g_inner_smul_left g x c (G x) (X x)
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_const_mul c]
    rw [h.pairing_eq X hX hX_int]
    have h_div_supp : tsupport (divergence_g_with_boundary (I := I) g X) ⊆
        tsupport (X : ∀ x, TangentSpace I x) :=
      tsupport_divergence_g_with_boundary_subset_of_interior_support
        (I := I) g X hX_int
    have h_div_supp_int :
        tsupport (divergence_g_with_boundary (I := I) g X) ⊆ I.interior M :=
      h_div_supp.trans hX_int
    have h_div_cont : Continuous (divergence_g_with_boundary (I := I) g X) := by
      rw [continuous_iff_continuousAt]
      intro x
      by_cases hx_supp : x ∈ tsupport (divergence_g_with_boundary (I := I) g X)
      · have hopen_int : IsOpen (I.interior M) :=
          I.isOpen_interior (M := M) (n := ∞)
            (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0))
        have hx_int : x ∈ I.interior M := h_div_supp_int hx_supp
        have hcont_int :
            ContinuousOn (divergence_g_with_boundary (I := I) g X) (I.interior M) :=
          divergence_g_with_boundary_continuousOn_interior (I := I) g X
        exact (hcont_int x hx_int).continuousAt (hopen_int.mem_nhds hx_int)
      · have h_open : IsOpen (tsupport (divergence_g_with_boundary (I := I) g X))ᶜ :=
          (isClosed_tsupport _).isOpen_compl
        have hev_zero : (divergence_g_with_boundary (I := I) g X) =ᶠ[𝓝 x]
            (fun _ => (0 : ℝ)) := by
          filter_upwards [h_open.mem_nhds hx_supp] with y hy
          by_contra hne
          exact hy (subset_tsupport _ hne)
        exact (continuous_const.continuousAt.congr hev_zero.symm)
    have h_int_uX : Integrable (fun x : M => u x * divergence_g_with_boundary (I := I) g X x)
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
    have hcong : (fun x : M => (c * u x) * divergence_g_with_boundary (I := I) g X x) =
        (fun x : M => c * (u x * divergence_g_with_boundary (I := I) g X x)) := by
      funext x; ring
    rw [hcong, integral_const_mul]
    ring

/-- Closure of `MemW1pIntrinsicLp_withBoundary` under scalar multiplication. -/
theorem MemW1pIntrinsicLp_withBoundary.const_smul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ}
    (hu : MemW1pIntrinsicLp_withBoundary (I := I) (M := M) g p u) :
    MemW1pIntrinsicLp_withBoundary (I := I) (M := M) g p
      (fun x => c * u x) := by
  obtain ⟨hu_p, G, hG_weak, hG_p⟩ := hu
  refine ⟨hu_p.const_mul c, (fun x : M => c • G x), ?_, ?_⟩
  · exact HasWeakRiemannianGradLp_withBoundary.const_smul
      (I := I) (M := M) hp c hG_weak hu_p
  · have hcongr : (fun x : M => Real.sqrt
        (g.inner x ((fun y : M => c • G y) x)
          ((fun y : M => c • G y) x))) =
        (fun x : M => |c| * Real.sqrt (g.inner x (G x) (G x))) := by
      funext x
      exact g_norm_const_smul g x c (G x)
    rw [hcongr]
    exact hG_p.const_mul (|c|)

/-- The negation of a weak Riemannian gradient with boundary is a weak
gradient of the negated function. -/
theorem HasWeakRiemannianGradLp_withBoundary.neg
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ} {G : M → E}
    (h : HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g u G)
    (hu : MemLp u p (riemannianVolumeMeasure I M g)) :
    HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g
      (fun x => -u x) (fun x : M => -G x) := by
  have h1 : HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g
      (fun x => (-1 : ℝ) * u x) (fun x : M => (-1 : ℝ) • G x) :=
    HasWeakRiemannianGradLp_withBoundary.const_smul (I := I) (M := M) hp (-1) h hu
  have h_u : (fun x : M => (-1 : ℝ) * u x) = (fun x => -u x) := by
    funext x; ring
  have h_G : (fun x : M => (-1 : ℝ) • G x) = (fun x : M => -G x) := by
    funext x; rw [neg_one_smul]
  rw [h_u] at h1
  rw [h_G] at h1
  exact h1

/-- Closure of `MemW1pIntrinsicLp_withBoundary` under negation. -/
theorem MemW1pIntrinsicLp_withBoundary.neg
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ}
    (hu : MemW1pIntrinsicLp_withBoundary (I := I) (M := M) g p u) :
    MemW1pIntrinsicLp_withBoundary (I := I) (M := M) g p
      (fun x => -u x) := by
  have h := MemW1pIntrinsicLp_withBoundary.const_smul (I := I) (M := M) hp (-1) hu
  have h_eq : (fun x : M => (-1 : ℝ) * u x) = (fun x => -u x) := by
    funext x; ring
  rw [h_eq] at h
  exact h

/-- The `W^{1,p}_{int,Lp}` norm of `u` on a manifold with boundary. -/
def w1pNormIntrinsicLp_withBoundary
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) (u : M → ℝ) : ℝ≥0∞ :=
  eLpNorm u p (riemannianVolumeMeasure I M g) +
    ⨅ (G : M → E)
      (_ : HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g u G),
      eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
        (riemannianVolumeMeasure I M g)

private def gradInfimumLp_withBoundary
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) (u : M → ℝ) : ℝ≥0∞ :=
  ⨅ (G : M → E)
    (_ : HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g u G),
    eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
      (riemannianVolumeMeasure I M g)

private lemma w1pNormIntrinsicLp_withBoundary_def
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) (u : M → ℝ) :
    w1pNormIntrinsicLp_withBoundary (I := I) (M := M) g p u =
      eLpNorm u p (riemannianVolumeMeasure I M g) +
        gradInfimumLp_withBoundary (I := I) (M := M) g p u := rfl

/-- The norm of the zero function is zero. -/
theorem w1pNormIntrinsicLp_withBoundary_zero
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) :
    w1pNormIntrinsicLp_withBoundary (I := I) (M := M) g p
      (fun _ : M => (0 : ℝ)) = 0 := by
  rw [w1pNormIntrinsicLp_withBoundary_def]
  rw [show eLpNorm (fun _ : M => (0 : ℝ)) p
        (riemannianVolumeMeasure I M g) = 0 from
      eLpNorm_zero]
  rw [zero_add]
  apply le_antisymm
  · have hzero_grad : HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g
        (fun _ : M => (0 : ℝ)) (fun _ : M => (0 : E)) :=
      HasWeakRiemannianGradLp_withBoundary.zero (I := I) (M := M) g
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
    unfold gradInfimumLp_withBoundary
    exact iInf_le_of_le (fun _ : M => (0 : E)) (iInf_le _ hzero_grad)
  · exact zero_le _

end IntrinsicLp
end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry

end
