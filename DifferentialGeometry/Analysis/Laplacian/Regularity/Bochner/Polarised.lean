import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.LaplacianFinal

/-!
# Polarised Bochner-Weitzenböck identity for smooth `(φ, v)`

For a closed smooth Riemannian manifold `(M, g)` and two smooth real-valued
functions `φ, v : C^∞⟮I, M; ℝ⟯`, this module derives the polarised
Bochner-Weitzenböck identity

```
Δ_g(g(∇φ, ∇v))(x) =
    g(∇(Δφ), ∇v)(x) + g(∇φ, ∇(Δv))(x)
  + 2 · hessPairingChart g φ v x
  + 2 · ricciTensor g x (∇φ x) (∇v x)
```

from the unpolarised `bochner_pointwise_concrete_metric_unconditional` applied
to `(φ + v)` and `(φ - v)`, divided by `4`.

Rearranged into `(1 - Δ_g)` form:

```
(1 - Δ_g)(g(∇φ, ∇v))(x) =
    g(∇φ, ∇v)(x)
  - g(∇(Δφ), ∇v)(x) - g(∇φ, ∇(Δv))(x)
  - 2 · hessPairingChart g φ v x
  - 2 · ricciTensor g x (∇φ x) (∇v x).
```

This is the **smooth-case pointwise content** of the unconditional Bochner
candidate identification:

```
gradInnerLaplacianCandidateUnconditional g φ (smoothToH1Compl_mem_laplacianDomainPow_two g v)
  =ᵐ smoothToLp((1-Δ_classical)(g(∇φ, ∇v))).
```

## Key technical insight

The pointwise polarisation requires `Δ_g(-f) = -Δ_g(f)` and `gradFun(-f) = -gradFun(f)`,
which themselves rely on `Δ_g` being independent of the specific smoothness witness
(since `Δ_g g hf := divergence_g g (grad_g g hf)`, and `grad_g g hf` is a
`ContMDiffSection` whose underlying function is `gradFun g f` — which depends only
on `f`, not on `hf`). We expose this fact as `Δ_g_smoothness_irrelevant` and use
it to build linearity lemmas for `Δ_g`.

## Main results

* `grad_g_congr` — two `grad_g` calls with the same underlying function produce
  equal `ContMDiffSection`s.

* `Δ_g_congr_func` — `Δ_g` only depends on the underlying function `f`, not on
  the smoothness witness.

* `gradFun_neg` — pointwise gradient of a negation.

* `gradFun_sub` — pointwise gradient of a difference.

* `Δ_g_neg` — Laplacian of a negation.

* `Δ_g_sub` — Laplacian of a difference.

* `g_inner_grad_lap_polar` — the polarisation of `g(∇f, ∇Δf)` for smooth `(φ, v)`.

* `normGradSqFun_polar` — the polarisation of `|∇·|²_g` for smooth `(φ, v)`.

* `bochner_polarised_pointwise` — the headline polarised Bochner identity.

* `bochner_polarised_pointwise_oneSubLap` — the same identity in `(1 - Δ_g)`-form.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace BochnerPolarised

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalLimitGeneral

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## `Δ_g` is independent of the smoothness witness

The Laplacian `Δ_g g hf` is defined as `divergence_g g (grad_g g hf)`, where
`grad_g g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯` is the smooth gradient
section. The underlying function of `grad_g g hf` is `fun x => gradFun g f x`,
which depends only on `f` (not on `hf`). Since `ContMDiffSection` is
extensionally determined by its `toFun`, two `grad_g g hf` calls with the same
`f` produce equal sections. Hence `Δ_g g hf` is independent of `hf`. -/

/-- `grad_g g hf` depends only on the underlying function `f`, not on the
smoothness witness `hf`. -/
lemma grad_g_congr
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf₁ hf₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    (grad_g (I := I) g hf₁ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
      (grad_g (I := I) g hf₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
  -- Both sections have the same toFun (= gradFun g f), hence are equal via ext.
  refine ContMDiffSection.ext (fun _ => rfl)

/-- `Δ_g g hf` depends only on the underlying function `f`, not on the smoothness
witness `hf`. -/
lemma Δ_g_congr_func
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf₁ hf₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    Δ_g (I := I) g hf₁ x = Δ_g (I := I) g hf₂ x := by
  -- grad_g g hf₁ = grad_g g hf₂ as ContMDiffSections via grad_g_congr.
  -- Δ_g is divergence_g (grad_g · ·) x, so the equality propagates.
  have h := grad_g_congr (I := I) g hf₁ hf₂
  change divergence_g (I := I) g (grad_g (I := I) g hf₁) x =
    divergence_g (I := I) g (grad_g (I := I) g hf₂) x
  rw [h]

/-- `grad_g` for two (syntactically distinct but pointwise-equal) functions
agrees as a section. -/
lemma grad_g_congr_funext
    (g : SmoothRiemannianMetric I M) {f₁ f₂ : M → ℝ}
    (hf₁ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₁) (hf₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₂)
    (h_eq : f₁ = f₂) :
    (grad_g (I := I) g hf₁ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
      (grad_g (I := I) g hf₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
  refine ContMDiffSection.ext (fun x => ?_)
  -- Both reduce to gradFun, which depends only on the function via mfderiv.
  change gradFun (I := I) g f₁ x = gradFun (I := I) g f₂ x
  rw [h_eq]

/-- `Δ_g g hf` for two (syntactically distinct but pointwise-equal) functions
agrees pointwise. -/
lemma Δ_g_congr_funext
    (g : SmoothRiemannianMetric I M) {f₁ f₂ : M → ℝ}
    (hf₁ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₁) (hf₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₂)
    (h_eq : f₁ = f₂) (x : M) :
    Δ_g (I := I) g hf₁ x = Δ_g (I := I) g hf₂ x := by
  have h := grad_g_congr_funext (I := I) g hf₁ hf₂ h_eq
  change divergence_g (I := I) g (grad_g (I := I) g hf₁) x =
    divergence_g (I := I) g (grad_g (I := I) g hf₂) x
  rw [h]

/-! ## Gradient and Laplacian of negation / subtraction -/

/-- The pointwise gradient of a negation: `∇(-f)(x) = -∇f(x)`. -/
lemma gradFun_neg
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    gradFun (I := I) g (fun y : M => -f y) x =
      -gradFun (I := I) g f x := by
  -- -f = (-1 : ℝ) • f via Pi.smul. Apply gradFun_const_smul with c = -1.
  have h_neg : (fun y : M => -f y) = (-1 : ℝ) • f := by
    funext y; simp [Pi.smul_apply]
  rw [h_neg]
  rw [gradFun_const_smul (I := I) g (-1 : ℝ) hf]
  rw [neg_smul, one_smul]

/-- The pointwise gradient of a difference of differentiable functions. -/
lemma gradFun_sub
    (g : SmoothRiemannianMetric I M) {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x) :
    gradFun (I := I) g (fun y : M => f y - h y) x =
      gradFun (I := I) g f x - gradFun (I := I) g h x := by
  -- f - h = f + (-h).
  have h_sub : (fun y : M => f y - h y) = (fun y : M => f y + -h y) := by
    funext y; ring
  rw [h_sub]
  have h_neg_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => -h y) x := by
    have : (fun y : M => -h y) = (-1 : ℝ) • h := by funext y; simp [Pi.smul_apply]
    rw [this]
    exact hh.const_smul (-1 : ℝ)
  rw [DifferentialGeometry.Integral.Connection.gradFun_add (I := I) g hf h_neg_diff]
  rw [gradFun_neg (I := I) g hh]
  abel

/-- Laplacian of a negation: `Δ_g(-f)(x) = -Δ_g(f)(x)`. -/
lemma Δ_g_neg
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ∀ (hneg : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => -f y)) (x : M),
    Δ_g (I := I) g hneg x = -Δ_g (I := I) g hf x := by
  intro hneg x
  -- Use Δ_g_add applied to f and -f: Δ_g(f + (-f)) = Δ_g f + Δ_g (-f).
  -- And f + (-f) = 0 pointwise, so by witness-independence Δ_g of sum is 0.
  have h_add := Δ_g_add (I := I) g hf hneg x
  -- The function (fun y => f y + -f y) equals (fun _ => 0).
  have h_sum_eq_zero : (fun y : M => f y + -f y) = (fun _ : M => (0 : ℝ)) := by
    funext y; ring
  -- Δ_g of (f + -f) using `Δ_g_congr_funext` bridges to Δ_g of (fun _ => 0).
  -- And Δ_g of (fun _ => 0) is 0 by `Δ_g_const` for c = 0.
  have h_zero_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ)) :=
    contMDiff_const
  have hΔ_sum_eq_zero :
      Δ_g (I := I) g (hf.add hneg) x = 0 := by
    -- Bridge from Δ_g(hf.add hneg) to Δ_g(h_zero_smooth) via function equality.
    rw [Δ_g_congr_funext (I := I) g (hf.add hneg) h_zero_smooth h_sum_eq_zero x]
    exact Δ_g_const (I := I) g (0 : ℝ) x
  linarith [h_add, hΔ_sum_eq_zero]

/-- Laplacian of a difference. -/
lemma Δ_g_sub
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
    ∀ (hsub : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => f y - h y)) (x : M),
    Δ_g (I := I) g hsub x = Δ_g (I := I) g hf x - Δ_g (I := I) g hh x := by
  intro hsub x
  -- f - h = f + (-h). Use Δ_g_add applied to f and -h.
  have hneg : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => -h y) := by
    have h_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (-1 : ℝ)) := contMDiff_const
    have h_smul := h_const.mul hh
    refine h_smul.congr ?_
    intro y
    simp [neg_one_mul]
  -- (f + (-h)) and (f - h) are the same function.
  have h_sub_eq_add_neg : (fun y : M => f y - h y) = (fun y : M => f y + -h y) := by
    funext y; ring
  -- Bridge hsub to hf.add hneg via Δ_g_congr_funext.
  rw [Δ_g_congr_funext (I := I) g hsub (hf.add hneg) h_sub_eq_add_neg x]
  rw [Δ_g_add (I := I) g hf hneg x]
  rw [Δ_g_neg (I := I) g hh hneg x]
  ring

/-! ## Pointwise polarisation identity for `|∇·|²_g` -/

/-- Polarisation of `g(∇f, ∇f)` for smooth `(φ, v)` at the pointwise level:
`g(∇(φ+v), ∇(φ+v))(x) - g(∇(φ-v), ∇(φ-v))(x) = 4 g(∇φ, ∇v)(x)`. -/
lemma normGradSqFun_polar
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (x : M) :
    normGradSqFun (I := I) g (fun y : M => φ y + v y) x -
        normGradSqFun (I := I) g (fun y : M => φ y - v y) x =
      4 * g.inner x
        (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g (v : M → ℝ) x) := by
  -- normGradSqFun g f x = g(∇f, ∇f)(x).
  unfold normGradSqFun
  -- ∇(φ+v)(x) = ∇φ(x) + ∇v(x), ∇(φ-v)(x) = ∇φ(x) - ∇v(x).
  have hφ_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (φ : M → ℝ) x :=
    φ.contMDiff.mdifferentiable (by simp) x
  have hv_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (v : M → ℝ) x :=
    v.contMDiff.mdifferentiable (by simp) x
  rw [DifferentialGeometry.Integral.Connection.gradFun_add (I := I) g hφ_diff hv_diff]
  rw [gradFun_sub (I := I) g hφ_diff hv_diff]
  -- Now LHS = g.inner x (∇φ + ∇v) (∇φ + ∇v) - g.inner x (∇φ - ∇v) (∇φ - ∇v).
  -- Use g_inner_polar with u := ∇φ, w := ∇v.
  exact g_inner_polar (I := I) (M := M) g x
    (gradFun (I := I) g (φ : M → ℝ) x)
    (gradFun (I := I) g (v : M → ℝ) x)

/-! ## Pointwise polarisation identity for `ricciTensor(∇f, ∇f)` -/

/-- Polarisation of `ricciTensor(∇f, ∇f)` for smooth `(φ, v)` at the pointwise level. -/
lemma ricciTensor_grad_polar
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (x : M) :
    ricciTensor (I := I) g x
        (gradFun (I := I) g (fun y : M => φ y + v y) x)
        (gradFun (I := I) g (fun y : M => φ y + v y) x) -
      ricciTensor (I := I) g x
        (gradFun (I := I) g (fun y : M => φ y - v y) x)
        (gradFun (I := I) g (fun y : M => φ y - v y) x) =
      4 * ricciTensor (I := I) g x
        (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g (v : M → ℝ) x) := by
  have hφ_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (φ : M → ℝ) x :=
    φ.contMDiff.mdifferentiable (by simp) x
  have hv_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (v : M → ℝ) x :=
    v.contMDiff.mdifferentiable (by simp) x
  rw [DifferentialGeometry.Integral.Connection.gradFun_add (I := I) g hφ_diff hv_diff]
  rw [gradFun_sub (I := I) g hφ_diff hv_diff]
  exact ricciTensor_polar (I := I) (M := M) g x
    (gradFun (I := I) g (φ : M → ℝ) x)
    (gradFun (I := I) g (v : M → ℝ) x)

/-! ## Pointwise polarisation identity for `g(∇f, ∇Δf)`

For smooth `(φ, v)`, by bilinearity of `g.inner` and linearity of `∇` and `Δ_g`:
`g(∇(φ+v), ∇Δ(φ+v)) - g(∇(φ-v), ∇Δ(φ-v)) = 2(g(∇φ, ∇Δv) + g(∇v, ∇Δφ))`. -/

/-- Polarisation of `g(∇f, ∇Δf)` for smooth `(φ, v)` at the pointwise level. -/
lemma g_inner_grad_lap_polar
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (x : M)
    (hφv_add : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y))
    (hφv_sub : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y)) :
    g.inner x
        (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y) x)
        (gradFun (I := I) g (Δ_g (I := I) g hφv_add) x) -
      g.inner x
        (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y) x)
        (gradFun (I := I) g (Δ_g (I := I) g hφv_sub) x) =
      2 * (g.inner x
            (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g (Δ_g (I := I) g v.contMDiff) x) +
          g.inner x
            (gradFun (I := I) g (v : M → ℝ) x)
            (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) x)) := by
  classical
  -- Step 1: Identify ∇(φ + v)(x) = ∇φ(x) + ∇v(x), and similarly for difference.
  have hφ_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (φ : M → ℝ) x :=
    φ.contMDiff.mdifferentiable (by simp) x
  have hv_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (v : M → ℝ) x :=
    v.contMDiff.mdifferentiable (by simp) x
  rw [DifferentialGeometry.Integral.Connection.gradFun_add (I := I) g hφ_diff hv_diff]
  rw [gradFun_sub (I := I) g hφ_diff hv_diff]
  -- Step 2: Identify Δ_g(φ + v) and Δ_g(φ - v) as functions, via Δ_g_add / Δ_g_sub.
  -- We need ∇(Δ_g(φ + v))(x) and ∇(Δ_g(φ - v))(x).
  -- By Δ_g_add: Δ_g(φ + v)(y) = Δ_g φ y + Δ_g v y for all y.
  -- Hence the function `Δ_g(φ + v)` agrees pointwise with `Δ_g φ + Δ_g v`.
  -- Then ∇(Δ_g(φ + v))(x) = ∇(Δ_g φ + Δ_g v)(x) (by funext + gradFun depending on function only)
  --                       = ∇(Δ_g φ)(x) + ∇(Δ_g v)(x).
  -- Same for difference.
  -- The technical issue: ∇ takes a witness of smoothness; we need to handle the change.
  set Δφ : M → ℝ := Δ_g (I := I) g φ.contMDiff with hΔφ_def
  set Δv : M → ℝ := Δ_g (I := I) g v.contMDiff with hΔv_def
  have hΔφ_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ Δφ :=
    Δ_g_contMDiff (I := I) g φ.contMDiff
  have hΔv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ Δv :=
    Δ_g_contMDiff (I := I) g v.contMDiff
  -- Function-level identification: Δ_g(φ + v) y = Δφ y + Δv y.
  have h_Δ_add_func :
      (fun y : M => Δ_g (I := I) g hφv_add y) = (fun y : M => Δφ y + Δv y) := by
    funext y; exact Δ_g_add (I := I) g φ.contMDiff v.contMDiff y
  have h_Δ_sub_func :
      (fun y : M => Δ_g (I := I) g hφv_sub y) = (fun y : M => Δφ y - Δv y) := by
    funext y; exact Δ_g_sub (I := I) g φ.contMDiff v.contMDiff hφv_sub y
  -- Now gradFun is determined by the function alone (via mfderiv).
  -- gradFun g (Δ_g(φ + v)) x = gradFun g (fun y => Δφ y + Δv y) x.
  -- gradFun g (Δ_g(φ - v)) x = gradFun g (fun y => Δφ y - Δv y) x.
  have h_grad_Δ_add :
      gradFun (I := I) g (Δ_g (I := I) g hφv_add) x =
      gradFun (I := I) g (fun y : M => Δφ y + Δv y) x := by
    rw [show (Δ_g (I := I) g hφv_add : M → ℝ) = (fun y : M => Δφ y + Δv y) from
      h_Δ_add_func]
  have h_grad_Δ_sub :
      gradFun (I := I) g (Δ_g (I := I) g hφv_sub) x =
      gradFun (I := I) g (fun y : M => Δφ y - Δv y) x := by
    rw [show (Δ_g (I := I) g hφv_sub : M → ℝ) = (fun y : M => Δφ y - Δv y) from
      h_Δ_sub_func]
  rw [h_grad_Δ_add, h_grad_Δ_sub]
  -- Now expand ∇(Δφ + Δv)(x) = ∇Δφ x + ∇Δv x, ∇(Δφ - Δv)(x) = ∇Δφ x - ∇Δv x.
  have hΔφ_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) Δφ x :=
    hΔφ_smooth.mdifferentiable (by simp) x
  have hΔv_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) Δv x :=
    hΔv_smooth.mdifferentiable (by simp) x
  rw [DifferentialGeometry.Integral.Connection.gradFun_add (I := I) g hΔφ_diff hΔv_diff]
  rw [gradFun_sub (I := I) g hΔφ_diff hΔv_diff]
  -- Now LHS:
  --   g.inner x (∇φ + ∇v) (∇Δφ + ∇Δv) - g.inner x (∇φ - ∇v) (∇Δφ - ∇Δv).
  -- By bilinearity:
  --   g.inner x (a+b) (c+d) - g.inner x (a-b) (c-d) = 2 g(a, d) + 2 g(b, c).
  -- For us: a = ∇φ, b = ∇v, c = ∇Δφ, d = ∇Δv.
  -- Result: 2 g(∇φ, ∇Δv) + 2 g(∇v, ∇Δφ).
  set u : TangentSpace I x := gradFun (I := I) g (φ : M → ℝ) x with hu_def
  set w : TangentSpace I x := gradFun (I := I) g (v : M → ℝ) x with hw_def
  set p : TangentSpace I x := gradFun (I := I) g Δφ x with hp_def
  set q : TangentSpace I x := gradFun (I := I) g Δv x with hq_def
  -- g.inner x (u + w) (p + q) - g.inner x (u - w) (p - q) = ?
  have hp1 : g.inner x (u + w) (p + q) =
      g.inner x u p + g.inner x u q + g.inner x w p + g.inner x w q := by
    rw [ContinuousLinearMap.map_add (g.inner x) u w]
    rw [ContinuousLinearMap.add_apply]
    rw [(g.inner x u).map_add, (g.inner x w).map_add]
    ring
  have hp2 : g.inner x (u - w) (p - q) =
      g.inner x u p - g.inner x u q - g.inner x w p + g.inner x w q := by
    rw [ContinuousLinearMap.map_sub (g.inner x) u w]
    rw [ContinuousLinearMap.sub_apply]
    rw [(g.inner x u).map_sub, (g.inner x w).map_sub]
    ring
  rw [hp1, hp2]
  ring

/-! ## The polarised Bochner-Weitzenböck identity (pointwise smooth) -/

/-- **The polarised Bochner-Weitzenböck identity** for smooth `(φ, v)` at the
pointwise level. For all `x : M`:

```
Δ_g(g(∇φ, ∇v))(x) =
    g(∇φ, ∇Δv)(x) + g(∇v, ∇Δφ)(x)
  + 2 · hessPairingChart g φ v x
  + 2 · ricciTensor g x (∇φ x) (∇v x).
```

Note: the statement is parametrised by smoothness witnesses for `φ + v`,
`φ - v`, and `g(∇φ, ∇v)`. -/
theorem bochner_polarised_pointwise
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯)
    (hφv_add : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y))
    (hφv_sub : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y))
    (h_gphi_gv_smooth :
      ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun y : M => g.inner y (gradFun (I := I) g (φ : M → ℝ) y)
          (gradFun (I := I) g (v : M → ℝ) y)))
    (x : M) :
    Δ_g (I := I) g h_gphi_gv_smooth x =
      g.inner x
          (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (Δ_g (I := I) g v.contMDiff) x) +
        g.inner x
          (gradFun (I := I) g (v : M → ℝ) x)
          (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) x) +
        2 * hessPairingChart (I := I) g φ v x +
        2 * ricciTensor (I := I) g x
              (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (v : M → ℝ) x) := by
  classical
  -- Apply bochner_pointwise_concrete_metric_unconditional to f := φ + v and f := φ - v.
  have hΔ_add := bochner_pointwise_concrete_metric_unconditional
    (I := I) g hφv_add x
  have hΔ_sub := bochner_pointwise_concrete_metric_unconditional
    (I := I) g hφv_sub x
  -- hΔ_add: Δ_g(|∇(φ+v)|²)(x) = 2 chartHessFrobSq(φ+v, x) + 2 ricci(...) + 2 g(∇(φ+v), ∇Δ(φ+v))(x).
  -- hΔ_sub: similar for φ - v.
  -- Subtract: Δ_g(|∇(φ+v)|² - |∇(φ-v)|²)(x) = 2[chartHessFrobSq(φ+v) - chartHessFrobSq(φ-v)] +
  --                                          2[ricci(∇(φ+v),...) - ricci(∇(φ-v),...)] +
  --                                          2[g(∇(φ+v),∇Δ(φ+v)) - g(∇(φ-v),∇Δ(φ-v))].
  -- LHS = 4 Δ_g(g(∇φ, ∇v))(x).
  -- Use normGradSqFun_polar and Δ_g_sub on the LHS.
  -- Identify each term on the RHS using the polarisation lemmas.

  -- Identify normGradSqFun_contMDiff:
  -- normGradSqFun g (φ+v) = g.inner (∇(φ+v)) (∇(φ+v)) is smooth (by composing smooth pieces).
  -- We need: (normGradSqFun g (φ+v) - normGradSqFun g (φ-v)) = 4 * g.inner (∇φ) (∇v) (pointwise).
  have hpolar_norm := normGradSqFun_polar (I := I) (M := M) g φ v x

  -- Define `psi := 4 * g.inner (∇φ) (∇v)`, which is the LHS of bochner divided by 4.
  -- We want Δ_g(g.inner (∇φ) (∇v)) x.

  -- Strategy: 4 * Δ_g(g.inner (∇φ) (∇v))(x) = Δ_g(normGradSqFun g (φ+v))(x) - Δ_g(normGradSqFun g (φ-v))(x).
  -- Because Δ_g is linear: Δ_g(a - b) = Δ_g a - Δ_g b on smooth pieces (when same function).

  -- The function (normGradSqFun g (φ+v) - normGradSqFun g (φ-v)) at y equals 4 * g.inner(∇φ, ∇v) at y.
  -- So Δ_g of it equals 4 * Δ_g(g.inner(∇φ, ∇v)).
  -- The Laplacian witness for `4 · g.inner` can be obtained from `h_gphi_gv_smooth` via `const_smul`.

  -- We use Δ_g_sub on the smooth witnesses for normGradSqFun_contMDiff(φ+v) and normGradSqFun(φ-v).
  set N1 : M → ℝ := normGradSqFun (I := I) g (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y)
    with hN1_def
  set N2 : M → ℝ := normGradSqFun (I := I) g (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y)
    with hN2_def

  have hN1_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ N1 :=
    normGradSqFun_contMDiff (I := I) g hφv_add
  have hN2_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ N2 :=
    normGradSqFun_contMDiff (I := I) g hφv_sub

  -- The smooth function (N1 - N2) y = 4 * g.inner y (∇φ y) (∇v y) (pointwise by hpolar_norm).
  have hN_sub_eq : ∀ y : M,
      (N1 y - N2 y) = 4 * g.inner y
        (gradFun (I := I) g (φ : M → ℝ) y)
        (gradFun (I := I) g (v : M → ℝ) y) :=
    fun y => normGradSqFun_polar (I := I) (M := M) g φ v y

  -- Smoothness witness for (N1 - N2):
  have hN_sub_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => N1 y - N2 y) :=
    hN1_smooth.sub hN2_smooth

  -- Smoothness witness for `4 * g.inner(∇φ, ∇v)`:
  have h_4gphi_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => 4 * g.inner y
        (gradFun (I := I) g (φ : M → ℝ) y)
        (gradFun (I := I) g (v : M → ℝ) y)) := by
    -- 4 * (g.inner ∇φ ∇v) = const(4) · (g.inner ∇φ ∇v); smooth-const times smooth.
    have h_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (4 : ℝ)) := contMDiff_const
    exact h_const.mul h_gphi_gv_smooth

  -- Δ_g(N1 - N2)(x) = Δ_g N1(x) - Δ_g N2(x).
  have h_Δ_N_sub := Δ_g_sub (I := I) g hN1_smooth hN2_smooth hN_sub_smooth x

  -- (N1 - N2) y = 4 * (g.inner(∇φ, ∇v))(y) (function-level equality)
  have hN_eq_4ginner :
      (fun y : M => N1 y - N2 y) =
      (fun y : M => 4 * g.inner y
        (gradFun (I := I) g (φ : M → ℝ) y)
        (gradFun (I := I) g (v : M → ℝ) y)) := by
    funext y; exact hN_sub_eq y

  -- Δ_g of the same function with two witnesses agrees:
  have h_Δ_N_sub_eq_Δ_4ginner :
      Δ_g (I := I) g hN_sub_smooth x =
      Δ_g (I := I) g h_4gphi_smooth x := by
    -- Δ_g depends only on the underlying function; use the grad_g coe_inj trick.
    rw [Δ_g_def, Δ_g_def]
    have h_grad_eq :
        (grad_g (I := I) g hN_sub_smooth :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
        (grad_g (I := I) g h_4gphi_smooth :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
      apply ContMDiffSection.coe_inj
      funext y
      rw [grad_g_apply, grad_g_apply]
      change gradFun (I := I) g (fun z : M => N1 z - N2 z) y =
        gradFun (I := I) g (fun z : M => 4 * g.inner z
          (gradFun (I := I) g (φ : M → ℝ) z)
          (gradFun (I := I) g (v : M → ℝ) z)) y
      rw [hN_eq_4ginner]
    rw [h_grad_eq]

  -- Δ_g(4 * g.inner(∇φ, ∇v))(x) = 4 * Δ_g(g.inner(∇φ, ∇v))(x).
  -- Use Δ_g_smul_eq with φ_factor := const 4 and v_factor := g.inner ∇φ ∇v.
  -- Δ_g(const 4 · h) = (const 4) · Δ_g h + 2 g(∇const 4, ∇h) + h · Δ_g(const 4) = 4 · Δ_g h.
  have h_const_smul_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (4 : ℝ)) := contMDiff_const

  have h_Δ_4ginner_eq :
      Δ_g (I := I) g h_4gphi_smooth x = 4 * Δ_g (I := I) g h_gphi_gv_smooth x := by
    -- Use Δ_g_smul_eq with φ := (fun _ => 4), v := g.inner (∇φ) (∇v).
    -- Note: h_4gphi_smooth is for (fun y => 4 * (g.inner y...)). We need to match the form
    -- of Δ_g_smul_eq, which takes hφ.mul hv with φ.mul v.
    -- The function `fun y => 4 * (...y) = (fun _ => 4) y * (... y) = (const 4 · (...)) y`.
    -- So h_4gphi_smooth is precisely h_const_smul_smooth.mul h_gphi_gv_smooth up to witness.
    have h_witness_eq :
        Δ_g (I := I) g h_4gphi_smooth x =
        Δ_g (I := I) g
          (h_const_smul_smooth.mul h_gphi_gv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
            (fun y : M => 4 * g.inner y
              (gradFun (I := I) g (φ : M → ℝ) y)
              (gradFun (I := I) g (v : M → ℝ) y))) x :=
      Δ_g_congr_func (I := I) g h_4gphi_smooth _ x
    rw [h_witness_eq]
    rw [Δ_g_smul_eq (I := I) (M := M) g h_const_smul_smooth h_gphi_gv_smooth x]
    -- The result: Δ_g(const 4 · h) x = (4 : ℝ) * Δ_g h x + 2 g(∇const 4, ∇h) + h(x) * Δ_g(const 4) x.
    -- gradFun(const 4) = 0, Δ_g(const 4) = 0.
    -- Replace each summand.
    have h_grad_const_zero :
        gradFun (I := I) g (fun _ : M => (4 : ℝ)) x = (0 : TangentSpace I x) :=
      DifferentialGeometry.Integral.DivergenceTheorem.gradFun_const
        (I := I) g (4 : ℝ) x
    rw [h_grad_const_zero]
    -- The remaining term: const 4 · Δ_g h + 2 * g.inner x 0 (...) + (...) * Δ_g(const 4).
    -- g.inner x 0 (...) = 0 (linearity).
    -- Δ_g(const 4) = 0 (Δ_g_const).
    rw [show g.inner x (0 : TangentSpace I x) = (0 : TangentSpace I x →L[ℝ] ℝ) from
      map_zero _]
    -- Now Δ_g(const_smooth_4) x = 0 (Δ_g_const for c = 4).
    have hΔ_const_4 :
        Δ_g (I := I) g h_const_smul_smooth x = 0 := by
      -- h_const_smul_smooth is the constant `fun _ => (4 : ℝ)`. By Δ_g_const_4 with c = 4,
      -- Δ_g (contMDiff_const : ContMDiff (fun _ => 4)) x = 0.
      -- Need to use congruence to swap witness.
      have h_witness :
          Δ_g (I := I) g h_const_smul_smooth x =
          Δ_g (I := I) g (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (4 : ℝ))) x :=
        Δ_g_congr_func (I := I) g h_const_smul_smooth _ x
      rw [h_witness]
      exact Δ_g_const (I := I) g (4 : ℝ) x
    rw [hΔ_const_4]
    -- LHS: (fun _ => 4) x * Δ_g h x + 2 * (0 (∇v)) + (g.inner (∇φ) (∇v)) x * 0 = 4 * Δ_g h x.
    -- The `(0 : CLM)` applied to vectors yields 0; simp resolves this.
    simp only [ContinuousLinearMap.zero_apply, mul_zero, add_zero]

  -- Combine: 4 * Δ_g(g.inner(∇φ, ∇v))(x) = Δ_g N1 x - Δ_g N2 x.
  have h_Δ_4ginner_eq_sub :
      4 * Δ_g (I := I) g h_gphi_gv_smooth x =
      Δ_g (I := I) g hN1_smooth x - Δ_g (I := I) g hN2_smooth x := by
    rw [← h_Δ_4ginner_eq]
    rw [← h_Δ_N_sub_eq_Δ_4ginner]
    exact h_Δ_N_sub

  -- Now use bochner_pointwise_concrete_metric_unconditional applied to (φ+v) and (φ-v):
  -- hΔ_add: Δ_g N1 x = 2 chartHessFrobSq(φ+v) x + 2 ricci(...) + 2 g(∇(φ+v), ∇Δ(φ+v))(x).
  -- hΔ_sub: Δ_g N2 x = 2 chartHessFrobSq(φ-v) x + 2 ricci(...) + 2 g(∇(φ-v), ∇Δ(φ-v))(x).
  -- Subtract:
  --   Δ_g N1 - Δ_g N2 = 2 (chartHessFrobSq(φ+v) - chartHessFrobSq(φ-v)) +
  --                     2 (ricci(∇(φ+v),...) - ricci(∇(φ-v),...)) +
  --                     2 (g(∇(φ+v), ∇Δ(φ+v)) - g(∇(φ-v), ∇Δ(φ-v))).
  --                   = 2 * 4 * hessPairingChart + 2 * 4 * ricci(∇φ, ∇v) + 2 * 2 * (g(∇φ, ∇Δv) + g(∇v, ∇Δφ))
  --                   = 8 hessPair + 8 ricci(∇φ, ∇v) + 4 g(∇φ, ∇Δv) + 4 g(∇v, ∇Δφ).
  --
  -- Equating to 4 * Δ_g(g.inner(∇φ, ∇v))(x) and dividing by 4:
  --   Δ_g(g.inner(∇φ, ∇v))(x) = 2 hessPair + 2 ricci(∇φ, ∇v) + g(∇φ, ∇Δv) + g(∇v, ∇Δφ).

  -- Identify normGradSqFun in hΔ_add and hΔ_sub. The smoothness witness in
  -- `bochner_pointwise_concrete_metric_unconditional` is `normGradSqFun_contMDiff g hf`, and
  -- the LHS is `Δ_g g (normGradSqFun_contMDiff g hf)`. We need to relate this to
  -- `Δ_g g hN1_smooth`.
  -- normGradSqFun_contMDiff g hφv_add : ContMDiff I 𝓘(ℝ) ∞ (normGradSqFun g (φ + v)).
  -- hN1_smooth = normGradSqFun_contMDiff g hφv_add (since N1 = normGradSqFun g (φ + v)).
  -- Actually these are the same lemma's output -- but the model spaces might differ.
  -- bochner_pointwise_concrete_metric_unconditional uses `Δ_g g (normGradSqFun_contMDiff g hf)`.
  -- Δ_g takes a witness of type ContMDiff I 𝓘(ℝ, ℝ) ∞. normGradSqFun_contMDiff is `ContMDiff I 𝓘(ℝ) ∞`.
  -- These are equivalent: `𝓘(ℝ) = 𝓘(ℝ, ℝ)` (the model is `ℝ` itself).
  -- Let me check the types more carefully.

  -- Apply Δ_g_congr_func to bridge from normGradSqFun_contMDiff witness to hN1_smooth.
  -- Actually they should be the same witness (definitionally) since N1 = normGradSqFun g (φ + v).
  have hN1_witness_eq : hN1_smooth = normGradSqFun_contMDiff (I := I) g hφv_add := rfl
  have hN2_witness_eq : hN2_smooth = normGradSqFun_contMDiff (I := I) g hφv_sub := rfl

  -- Now rewrite hΔ_add and hΔ_sub to use hN1_smooth and hN2_smooth.
  have hΔN1 :
      Δ_g (I := I) g hN1_smooth x =
        2 * chartHessFrobeniusSq (I := I) g
              (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y) x +
          2 * ricciTensor (I := I) g x
                (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y) x)
                (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y) x) +
          2 * g.inner x
              (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y) x)
              (gradFun (I := I) g (Δ_g (I := I) g hφv_add) x) := by
    rw [hN1_witness_eq]
    exact hΔ_add

  have hΔN2 :
      Δ_g (I := I) g hN2_smooth x =
        2 * chartHessFrobeniusSq (I := I) g
              (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y) x +
          2 * ricciTensor (I := I) g x
                (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y) x)
                (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y) x) +
          2 * g.inner x
              (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y) x)
              (gradFun (I := I) g (Δ_g (I := I) g hφv_sub) x) := by
    rw [hN2_witness_eq]
    exact hΔ_sub

  -- Apply the polarisations.
  have h_hessPolar :
      chartHessFrobeniusSq (I := I) g
          (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y) x -
        chartHessFrobeniusSq (I := I) g
          (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y) x =
      4 * hessPairingChart (I := I) g φ v x :=
    chartHessFrobeniusSq_polar_eq_hessPairing (I := I) (M := M) g φ v x

  have h_ricciPolar :=
    ricciTensor_grad_polar (I := I) (M := M) g φ v x

  have h_gradLapPolar :=
    g_inner_grad_lap_polar (I := I) (M := M) g φ v x hφv_add hφv_sub

  -- Combine:
  -- Δ_g N1 - Δ_g N2 = 2 * (4 * hessPair) + 2 * (4 * ricci(∇φ, ∇v)) + 2 * (2 * (g(∇φ, ∇Δv) + g(∇v, ∇Δφ)))
  --                 = 8 hessPair + 8 ricci(∇φ, ∇v) + 4 (g(∇φ, ∇Δv) + g(∇v, ∇Δφ)).
  --
  -- 4 * Δ_g(g.inner) = Δ_g N1 - Δ_g N2 = above.
  --
  -- Δ_g(g.inner) = 2 hessPair + 2 ricci(∇φ, ∇v) + g(∇φ, ∇Δv) + g(∇v, ∇Δφ).

  -- We need:
  -- Δ_g h_gphi_gv_smooth x = g(∇φ, ∇Δv) + g(∇v, ∇Δφ) + 2 hessPair + 2 ricci(∇φ, ∇v).

  -- Let's prove this via h_Δ_4ginner_eq_sub.

  have key :
      4 * Δ_g (I := I) g h_gphi_gv_smooth x =
        8 * hessPairingChart (I := I) g φ v x +
          8 * ricciTensor (I := I) g x
                (gradFun (I := I) g (φ : M → ℝ) x)
                (gradFun (I := I) g (v : M → ℝ) x) +
          4 * (g.inner x
                (gradFun (I := I) g (φ : M → ℝ) x)
                (gradFun (I := I) g (Δ_g (I := I) g v.contMDiff) x) +
              g.inner x
                (gradFun (I := I) g (v : M → ℝ) x)
                (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) x)) := by
    rw [h_Δ_4ginner_eq_sub]
    rw [hΔN1, hΔN2]
    -- Goal: (RHS of hΔN1) - (RHS of hΔN2) = 8 hess + 8 ricci + 4 (g + g).
    -- Use h_hessPolar, h_ricciPolar, h_gradLapPolar to identify the polarised differences.
    linarith [h_hessPolar, h_ricciPolar, h_gradLapPolar]

  -- Divide key by 4.
  linarith [key]

/-! ## (1 - Δ_g) form of the polarised Bochner identity -/

/-- **The polarised Bochner-Weitzenböck identity, `(1 - Δ_g)` form**. For all `x`:

```
(1 - Δ_g)(g(∇φ, ∇v))(x) =
    g(∇φ, ∇v)(x)
  - g(∇Δφ, ∇v)(x) - g(∇φ, ∇Δv)(x)
  - 2 · hessPairingChart g φ v x
  - 2 · ricciTensor g x (∇φ x) (∇v x).
```

This is the target Lp-class-level identity for the unconditional Bochner
candidate identification. -/
theorem bochner_polarised_pointwise_oneSubLap
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯)
    (hφv_add : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y))
    (hφv_sub : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y))
    (h_gphi_gv_smooth :
      ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun y : M => g.inner y (gradFun (I := I) g (φ : M → ℝ) y)
          (gradFun (I := I) g (v : M → ℝ) y)))
    (x : M) :
    g.inner x
        (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g (v : M → ℝ) x) -
      Δ_g (I := I) g h_gphi_gv_smooth x =
      g.inner x
          (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (v : M → ℝ) x)
        - g.inner x
            (gradFun (I := I) g (v : M → ℝ) x)
            (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) x)
        - g.inner x
            (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g (Δ_g (I := I) g v.contMDiff) x)
        - 2 * hessPairingChart (I := I) g φ v x
        - 2 * ricciTensor (I := I) g x
              (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (v : M → ℝ) x) := by
  rw [bochner_polarised_pointwise (I := I) (M := M) g φ v hφv_add hφv_sub
    h_gphi_gv_smooth x]
  ring

end BochnerPolarised
end Laplacian
end Analysis
end DifferentialGeometry

end
