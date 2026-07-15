import DifferentialGeometry.Geometry.Metric.SmoothMetricFromCoeff
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field

/-!
# Smooth convex combination of two Riemannian metrics

Given two smooth Riemannian metrics `g₁ g₂` and a smooth weight `χ : M → ℝ` valued in `[0,1]`,
the fiberwise convex combination

`(g₁.convexComb g₂ χ).inner x = χ x • g₁.inner x + (1 - χ x) • g₂.inner x`

is again a smooth Riemannian metric.  Symmetry and positive-definiteness are pointwise convex-
combination facts; smoothness is the local-frame component route of
`smoothMetric_of_localCoeff`, with each frame component
`χ · (gₐ.inner · frameᵢ frameⱼ)` smooth via `metric_inner_contMDiffAt` and the smoothness of `χ`.

## Main results

* `SmoothRiemannianMetric.convexComb` : the bundled convex-combination metric.
* `convexComb_inner` : its inner product is the convex combination of the two inner products.
* `convexComb_eq_left_on` : on a set where `χ = 1`, it agrees with `g₁` (the locality lemma).
-/

noncomputable section

open Bundle Manifold Set ContinuousLinearMap Bornology
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace Geometry

/-- The fiberwise convex-combination bilinear form `χ x • g₁.inner x + (1-χ x) • g₂.inner x`,
as a continuous linear map. -/
private def convexCombForm (g₁ g₂ : SmoothRiemannianMetric I M) (χ : M → ℝ) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  χ x • g₁.inner x + (1 - χ x) • g₂.inner x

omit [FiniteDimensional ℝ E] in
private lemma convexCombForm_apply (g₁ g₂ : SmoothRiemannianMetric I M) (χ : M → ℝ)
    (x : M) (v w : TangentSpace I x) :
    convexCombForm (I := I) g₁ g₂ χ x v w =
      χ x • g₁.inner x v w + (1 - χ x) • g₂.inner x v w := by
  simp [convexCombForm, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]

omit [FiniteDimensional ℝ E] in
/-- The convex-combination form is symmetric, from symmetry of `g₁` and `g₂`. -/
private lemma convexCombForm_symm (g₁ g₂ : SmoothRiemannianMetric I M) (χ : M → ℝ)
    (x : M) (v w : TangentSpace I x) :
    convexCombForm (I := I) g₁ g₂ χ x v w = convexCombForm (I := I) g₁ g₂ χ x w v := by
  rw [convexCombForm_apply, convexCombForm_apply, g₁.symm x v w, g₂.symm x v w]

omit [FiniteDimensional ℝ E] in
/-- The convex-combination form is positive-definite when `χ x ∈ [0,1]`, by the convexity
argument of `convex_posDefForms`. -/
private lemma convexCombForm_pos (g₁ g₂ : SmoothRiemannianMetric I M) (χ : M → ℝ)
    (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < convexCombForm (I := I) g₁ g₂ χ x v v := by
  rw [convexCombForm_apply]
  simp only [smul_eq_mul]
  have h1 := g₁.pos x v hv
  have h2 := g₂.pos x v hv
  have ha : 0 ≤ χ x := (hχ01 x).1
  have hb : 0 ≤ 1 - χ x := by linarith [(hχ01 x).2]
  rcases lt_or_eq_of_le ha with ha' | ha'
  · have hb1 : 0 < χ x * g₁.inner x v v := mul_pos ha' h1
    have hb2 : 0 ≤ (1 - χ x) * g₂.inner x v v := mul_nonneg hb h2.le
    positivity
  · rw [← ha']
    have hb1 : (1 : ℝ) - 0 = 1 := by ring
    rw [hb1]
    simpa using h2

/-- The trivialization-induced local frame `frameVec x₀ i` is a smooth section at every point of
the trivialization's base set: there it equals Mathlib's `localFrame`, which is smooth on the
base set. -/
private lemma frameVec_contMDiffAt (x₀ : M) (i : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (frameVec (I := I) x₀ i y)) x := by
  set e := trivializationAt E (TangentSpace I) x₀ with he
  set b := Module.finBasis ℝ E with hb
  have hfr : frameVec (I := I) x₀ i =ᶠ[𝓝 x] e.localFrame b i := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    rw [e.localFrame_apply_of_mem_baseSet b hy]
    change (e.symmL ℝ y) (b i) = e.basisAt b hy i
    rw [Bundle.Trivialization.basisAt, Module.Basis.map_apply,
      Bundle.Trivialization.symmL_apply, Bundle.Trivialization.linearEquivAt_symm_apply]
  refine (contMDiffAt_localFrame_of_mem (I := I) (n := (∞ : WithTop ℕ∞)) (e := e) (b := b)
    (i := i) hx).congr_of_eventuallyEq ?_
  exact hfr.mono (fun y hy => congrArg (TotalSpace.mk' E y) hy)

/-- The convex-combination frame component
`χ · (χ x • g₁.inner · frameᵢ frameⱼ + (1-χ) • g₂.inner · frameᵢ frameⱼ)` is smooth on the base set
of the trivialization at `x₀`. -/
private lemma convexCombForm_coeff_contMDiffOn (g₁ g₂ : SmoothRiemannianMetric I M) (χ : M → ℝ)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => convexCombForm (I := I) g₁ g₂ χ x
        (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hrw : (fun x => convexCombForm (I := I) g₁ g₂ χ x
        (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x))
      = (fun x => χ x * g₁.inner x (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x)
          + (1 - χ x) * g₂.inner x (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x)) := by
    funext x
    rw [convexCombForm_apply]
    simp [smul_eq_mul]
  rw [hrw]
  intro x hx
  have hfri := frameVec_contMDiffAt (I := I) x₀ i hx
  have hfrj := frameVec_contMDiffAt (I := I) x₀ j hx
  have hg1 :
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y : M => g₁.inner y (frameVec (I := I) x₀ i y) (frameVec (I := I) x₀ j y)) x :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.metric_inner_contMDiffAt
      (I := I) g₁ hfri hfrj le_rfl
  have hg2 :
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y : M => g₂.inner y (frameVec (I := I) x₀ i y) (frameVec (I := I) x₀ j y)) x :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.metric_inner_contMDiffAt
      (I := I) g₂ hfri hfrj le_rfl
  have hχx : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ χ x := hχ x
  have hχ1x : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y : M => 1 - χ y) x :=
    contMDiffAt_const.sub hχx
  exact ((hχx.mul hg1).add (hχ1x.mul hg2)).contMDiffWithinAt

end Geometry

open Geometry

/-- **Smooth convex combination of two Riemannian metrics.** For a smooth weight `χ` valued in
`[0,1]`, the fiberwise convex combination `χ x • g₁.inner x + (1 - χ x) • g₂.inner x` is again a
smooth Riemannian metric. -/
noncomputable def SmoothRiemannianMetric.convexComb
    (g₁ g₂ : SmoothRiemannianMetric I M) (χ : M → ℝ)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) :
    SmoothRiemannianMetric I M :=
  (smoothMetric_of_localCoeff (I := I) (convexCombForm (I := I) g₁ g₂ χ)
    (fun x v w => convexCombForm_symm (I := I) g₁ g₂ χ x v w)
    (fun x v hv => convexCombForm_pos (I := I) g₁ g₂ χ hχ01 x v hv)
    (fun x₀ i j => convexCombForm_coeff_contMDiffOn (I := I) g₁ g₂ χ hχ x₀ i j)).choose

@[simp] theorem convexComb_inner
    (g₁ g₂ : SmoothRiemannianMetric I M) (χ : M → ℝ)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (x : M) (v w : TangentSpace I x) :
    (g₁.convexComb g₂ χ hχ hχ01).inner x v w =
      χ x • g₁.inner x v w + (1 - χ x) • g₂.inner x v w := by
  rw [show (g₁.convexComb g₂ χ hχ hχ01).inner x v w
        = convexCombForm (I := I) g₁ g₂ χ x v w from
      (smoothMetric_of_localCoeff (I := I) (convexCombForm (I := I) g₁ g₂ χ)
        (fun x v w => convexCombForm_symm (I := I) g₁ g₂ χ x v w)
        (fun x v hv => convexCombForm_pos (I := I) g₁ g₂ χ hχ01 x v hv)
        (fun x₀ i j => convexCombForm_coeff_contMDiffOn
          (I := I) g₁ g₂ χ hχ x₀ i j)).choose_spec x v w]
  exact convexCombForm_apply (I := I) g₁ g₂ χ x v w

/-- **Locality.** On a set `V` where `χ = 1`, the convex-combination metric agrees with `g₁`. -/
theorem convexComb_eq_left_on
    (g₁ g₂ : SmoothRiemannianMetric I M) (χ : M → ℝ)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (V : Set M) (hV : ∀ x ∈ V, χ x = 1) (x : M) (hx : x ∈ V) (v w : TangentSpace I x) :
    (g₁.convexComb g₂ χ hχ hχ01).inner x v w = g₁.inner x v w := by
  rw [convexComb_inner, hV x hx]
  simp

end DifferentialGeometry
