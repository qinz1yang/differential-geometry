import RicciFlower.Analysis.DivergenceTheorem.LocalFormula
import RicciFlower.Analysis.DivergenceTheorem.TangentAction
import RicciFlower.Analysis.DivergenceTheorem.POUReduction
import RicciFlower.Analysis.DivergenceTheorem.Proper
import RicciFlower.Analysis.Volume.Properties
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Support

/-!
# Smooth-section integration by parts on a boundaryless Riemannian manifold

For a smooth Riemannian metric `g` on a σ-compact Hausdorff smooth manifold `M`
without boundary, smooth scalar functions `f, h : M → ℝ` (without compact
support assumptions on the scalars), and a smooth tangent section `X` with
**compact support**, we establish the two integration-by-parts identities:

* `integral_tangentSectionAction_eq_neg_integral_smul_divergence`:
  $$\int_M X(f)\,d\mu_g = -\int_M f \cdot \operatorname{div}_g(X)\,d\mu_g.$$

* `integral_tangentSectionAction_mul_add_eq_neg`:
  $$\int_M \bigl(X(f)\,h + f\,X(h)\bigr)\,d\mu_g
       = -\int_M f\,h \cdot \operatorname{div}_g(X)\,d\mu_g.$$

The proof of (a) writes `divergence_g g (smoothSmul f hf X)` via the Leibniz
rule (`divergence_g_smoothSmul`) and integrates against the volume measure;
since `smoothSmul f hf X` has compact support inherited from `X`, the integral
of its divergence vanishes by `integral_divergence_eq_zero_of_hasCompactSupport`.

Identity (b) follows from (a) applied to the smooth product `f · h`, combined
with the Leibniz rule for the tangent action `tangentSectionAction_mul`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace RicciFlower
namespace Analysis
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open RicciFlower.Analysis.Volume

/-! ## File-local Borel-space instances

We match the convention in the surrounding files: `E` and `M` carry their
canonical Borel σ-algebras. Declared `local` to avoid leaking into callers. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Integrability of continuous compactly-supported functions

A continuous function with compact support is integrable against the Riemannian
volume measure, since the latter is finite on compacts. -/

/-- A continuous function with compact support is integrable against the
canonical Riemannian volume measure on a σ-compact Hausdorff manifold. -/
lemma Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact hf.integrable_of_hasCompactSupport hcs

/-! ## Leibniz rule for the tangent action on a product

For smooth scalars `f, h : M → ℝ` and a smooth tangent section `X`,
`X(f · h) = X(f) · h + f · X(h)`. This is the directional-derivative Leibniz
rule, derived from `HasMFDerivAt.mul` for the model space `ℝ`. -/

/-- Leibniz rule for `tangentSectionAction` on a product of smooth scalars.
For `f, h : M → ℝ` smooth and `X` a smooth tangent section,
`X(f · h)(x) = X(f)(x) · h(x) + f(x) · X(h)(x)`.

The proof uses `HasMFDerivAt.mul` for the model space `ℝ` (a normed
commutative ring) at `x`, evaluated at the vector `X x`. We work via the
identification `TangentSpace 𝓘(ℝ, ℝ) (·) = ℝ` (which holds definitionally),
exposing both differentials as continuous linear maps with codomain `ℝ`. -/
theorem tangentSectionAction_mul
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ) ∞ h) (x : M) :
    tangentSectionAction (I := I) X (f * h) x =
      tangentSectionAction (I := I) X f x * h x +
        f x * tangentSectionAction (I := I) X h x := by
  -- Both `f` and `h` are `MDifferentiableAt` at `x` (smoothness).
  have hf_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
    hf.mdifferentiableAt (by simp)
  have hh_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) h x :=
    hh.mdifferentiableAt (by simp)
  -- Re-cast `mfderiv I 𝓘(ℝ, ℝ) f x : TangentSpace I x →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) (f x)`
  -- as a CLM into `ℝ` (these are definitionally equal). Same for `h` and `f * h`.
  set f' : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f x
  set h' : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) h x
  set fh' : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) (f * h) x
  -- Get `HasMFDerivAt` statements with the recast CLMs.
  have hf_hasMF : HasMFDerivAt I 𝓘(ℝ, ℝ) f x f' := hf_mdiff.hasMFDerivAt
  have hh_hasMF : HasMFDerivAt I 𝓘(ℝ, ℝ) h x h' := hh_mdiff.hasMFDerivAt
  -- Apply `HasMFDerivAt.mul` (commutative-ring version): the mfderiv of `f * h`
  -- at `x` is `f x • h' + h x • f'`.
  have hmul : HasMFDerivAt I 𝓘(ℝ, ℝ) (f * h) x (f x • h' + h x • f') :=
    hf_hasMF.mul hh_hasMF
  -- Extract the mfderiv equality with the recast CLMs.
  have hmfderiv_eq : fh' = f x • h' + h x • f' := hmul.mfderiv
  -- Reduce the goal to a CLM application equality on `X x`.
  change fh' (X x) = f' (X x) * h x + f x * h' (X x)
  rw [hmfderiv_eq]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply]
  -- Goal: `f x • h' (X x) + h x • f' (X x)
  --        = f' (X x) * h x + f x * h' (X x)`.
  rw [smul_eq_mul, smul_eq_mul]
  ring

/-! ## Identity (a): basic integration by parts -/

/-- **Integration by parts (basic).** For a smooth scalar `f : M → ℝ`
(no compact support assumption) and a smooth tangent section `X` with compact
support on a σ-compact Hausdorff smooth Riemannian manifold `(M, g)` without
boundary,
$$\int_M X(f)\,d\mu_g = -\int_M f \cdot \operatorname{div}_g(X)\,d\mu_g.$$
The proof applies the divergence-Leibniz rule
`divergence_g_smoothSmul` to the section `smoothSmul f hf X` (which has
compact support inherited from `X`), so the integral of its divergence
vanishes by `integral_divergence_eq_zero_of_hasCompactSupport`. -/
theorem integral_tangentSectionAction_eq_neg_integral_smul_divergence
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) :
    ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * divergence_g (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- The section `Y := smoothSmul f hf X = f · X`.
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := smoothSmul (I := I) f hf X with hY_def
  -- `Y` has the same support as `X` (multiplying by a scalar function does not
  -- enlarge the support: `(f x • X x = 0)` whenever `X x = 0`).
  have hY_support : Function.support (Y : ∀ x, TangentSpace I x) ⊆
      Function.support (X : ∀ x, TangentSpace I x) := by
    intro x hx
    -- `Y x = f x • X x ≠ 0` ⇒ `X x ≠ 0`.
    by_contra hneX
    rw [Function.notMem_support] at hneX
    have hYx : (Y : ∀ x, TangentSpace I x) x = (0 : TangentSpace I x) := by
      change f x • X x = (0 : TangentSpace I x)
      rw [hneX]
      exact smul_zero _
    exact hx hYx
  have hY_cs : HasCompactSupport Y := by
    refine HasCompactSupport.of_support_subset_isCompact (hX : IsCompact (tsupport X)) ?_
    exact hY_support.trans (subset_tsupport _)
  -- The divergence of `Y`. By Leibniz, `divergence_g g Y = f · divergence_g g X + X(f)`.
  have hY_div : ∀ x : M,
      divergence_g (I := I) g Y x =
        f x * divergence_g (I := I) g X x + tangentSectionAction (I := I) X f x :=
    divergence_g_smoothSmul (I := I) g f hf X
  -- Both summands are continuous with compact support inside `tsupport X`, hence
  -- integrable; their pointwise sum equals `divergence_g g Y` whose integral vanishes.
  have hf_cont : Continuous f := hf.continuous
  have hX_div_cont : Continuous (divergence_g (I := I) g X) :=
    (divergence_g_contMDiff (I := I) g X).continuous
  have hAct_cont : Continuous (tangentSectionAction (I := I) X f) :=
    (tangentSectionAction_contMDiff (I := I) X hf).continuous
  have hX_div_cs : HasCompactSupport (divergence_g (I := I) g X) :=
    hasCompactSupport_divergence_g (I := I) g hX
  have hAct_cs : HasCompactSupport (tangentSectionAction (I := I) X f) :=
    hasCompactSupport_tangentSectionAction (I := I) hX f
  -- The product `f · divergence_g g X` is supported in `tsupport (divergence_g g X)`,
  -- hence has compact support.
  have hMul_cont : Continuous (fun x : M => f x * divergence_g (I := I) g X x) :=
    hf_cont.mul hX_div_cont
  have hMul_cs : HasCompactSupport (fun x : M => f x * divergence_g (I := I) g X x) :=
    hX_div_cs.mul_left
  -- Step 3: apply the divergence theorem to `Y`.
  have h_div_Y_zero :
      ∫ x, divergence_g (I := I) g Y x ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
    integral_divergence_eq_zero_of_hasCompactSupport (I := I) g Y hY_cs
  -- Step 4: rewrite using the Leibniz identity.
  have h_eq_pointwise : ∀ x : M, divergence_g (I := I) g Y x =
      f x * divergence_g (I := I) g X x + tangentSectionAction (I := I) X f x :=
    hY_div
  have h_div_Y_split :
      ∫ x, divergence_g (I := I) g Y x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, (f x * divergence_g (I := I) g X x +
                tangentSectionAction (I := I) X f x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact h_eq_pointwise x
  -- Integrability: split via `Integrable.add`.
  have h_int_mul : Integrable (fun x : M => f x * divergence_g (I := I) g X x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hMul_cont hMul_cs
  have h_int_act : Integrable (tangentSectionAction (I := I) X f)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hAct_cont hAct_cs
  have h_int_split :
      ∫ x, (f x * divergence_g (I := I) g X x +
              tangentSectionAction (I := I) X f x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, f x * divergence_g (I := I) g X x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
          ∫ x, tangentSectionAction (I := I) X f x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_add h_int_mul h_int_act
  -- Combine: `0 = ∫ f · div(X) + ∫ X(f)`, giving `∫ X(f) = -∫ f · div(X)`.
  have h_sum_zero :
      ∫ x, f x * divergence_g (I := I) g X x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
        ∫ x, tangentSectionAction (I := I) X f x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
    rw [← h_int_split, ← h_div_Y_split]; exact h_div_Y_zero
  linarith [h_sum_zero]

/-! ## Identity (b): symmetric integration by parts -/

/-- **Integration by parts (symmetric form).** For smooth scalars `f, h : M → ℝ`
(no compact support assumption) and a smooth tangent section `X` with compact
support on a σ-compact Hausdorff smooth Riemannian manifold `(M, g)` without
boundary,
$$\int_M \bigl(X(f)\,h + f\,X(h)\bigr)\,d\mu_g
       = -\int_M f\,h \cdot \operatorname{div}_g(X)\,d\mu_g.$$
The proof applies identity (a) to the smooth product `f · h` and uses the
tangent-action Leibniz rule `tangentSectionAction_mul`. -/
theorem integral_tangentSectionAction_mul_add_eq_neg
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) :
    ∫ x, (tangentSectionAction (I := I) X f x * h x +
            f x * tangentSectionAction (I := I) X h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * h x * divergence_g (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- The smooth product `f * h`.
  have hfh : ContMDiff I 𝓘(ℝ) ∞ (f * h) := hf.mul hh
  -- Apply identity (a) to `f * h`.
  have h_a := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) g hfh X hX
  -- Pointwise Leibniz rule for `tangentSectionAction X (f * h)`:
  -- `X(f · h)(x) = X(f)(x) · h(x) + f(x) · X(h)(x)`.
  have h_leibniz : ∀ x : M,
      tangentSectionAction (I := I) X (f * h) x =
        tangentSectionAction (I := I) X f x * h x +
          f x * tangentSectionAction (I := I) X h x := fun x =>
    tangentSectionAction_mul (I := I) X hf hh x
  have h_lhs_eq :
      ∫ x, tangentSectionAction (I := I) X (f * h) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, (tangentSectionAction (I := I) X f x * h x +
                f x * tangentSectionAction (I := I) X h x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact h_leibniz x
  -- Combine: `(f * h) x = f x * h x` is definitionally true.
  rw [← h_lhs_eq, h_a]
  -- The remaining goal `-∫ (f * h) x * div g X x = -∫ f x * h x * div g X x` is rfl.
  rfl

end DivergenceTheorem
end Analysis
end RicciFlower
