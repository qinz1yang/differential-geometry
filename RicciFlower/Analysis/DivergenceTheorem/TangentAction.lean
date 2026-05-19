import RicciFlower.Analysis.DivergenceTheorem.LocalFormula
import RicciFlower.Analysis.DivergenceTheorem.Invariance
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Action of a smooth tangent section on a smooth scalar function

For a smooth tangent section `X` and a smooth scalar function `f : M → ℝ`,
the *tangent action* `tangentSectionAction X f x := mfderiv I 𝓘(ℝ) f x (X x)` is
the directional derivative of `f` along `X` at `x`. This is an intrinsic
operation — no chart appears in the definition.

This file develops two facts about `tangentSectionAction`:

1. **Smoothness**: if `X` is a smooth tangent section and `f` is smooth, then
   `tangentSectionAction X f` is a smooth real-valued function on `M`.
2. **Chart-local representation**: in any chart `α : M`, on the chart base set,
   `tangentSectionAction X f x = ∑ i, chartCoeff α X i x · partialDeriv i (f ∘ symm) (φ x)`,
   where `partialDeriv` is the model-space partial derivative in the direction
   of the `i`-th model basis vector.

These are the standard coordinate identities. Together they provide the
intrinsic right-hand side of the chart-local integration-by-parts identity used
later for chart-invariance of the chart-local Voss–Weyl divergence.
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

/-! ## Definition and basic properties of `tangentSectionAction` -/

/-- The action of a smooth tangent section `X` on a smooth scalar function
`f : M → ℝ` at a point `x : M`. By definition, this is the directional
derivative `mfderiv I 𝓘(ℝ) f x (X x)`. -/
def tangentSectionAction
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) : M → ℝ :=
  fun x => mfderiv I 𝓘(ℝ) f x (X x)

@[simp] lemma tangentSectionAction_def
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) (x : M) :
    tangentSectionAction (I := I) X f x = mfderiv I 𝓘(ℝ) f x (X x) := rfl

/-! ## Chart-local representation of `tangentSectionAction`

In the chart at `α`, `tangentSectionAction X f x` can be written as
`∑ᵢ chartCoeff α X i x * partialDeriv i (f ∘ symm) (φ_α x)`. We prove this
identity below; it follows from the linearity of `mfderiv` and the chain rule
for the composition `f = (f ∘ symm) ∘ φ` on the chart source. -/

/-- The pullback of `f : M → ℝ` through the chart inverse, viewed as a function
on the chart target `(extChartAt I α).target ⊆ E`. -/
def scalarOnE (α : M) (f : M → ℝ) : E → ℝ :=
  fun y => f ((extChartAt I α).symm y)

@[simp] lemma scalarOnE_def (α : M) (f : M → ℝ) (y : E) :
    scalarOnE (I := I) α f y = f ((extChartAt I α).symm y) := rfl

/-- The map `f : M → ℝ` on the chart source equals the composition of its
chart-pullback `scalarOnE α f` with the extended chart. -/
lemma scalarOnE_extChartAt (α : M) (f : M → ℝ) {x : M}
    (hx : x ∈ (extChartAt I α).source) :
    scalarOnE (I := I) α f (extChartAt I α x) = f x := by
  change f ((extChartAt I α).symm (extChartAt I α x)) = f x
  rw [(extChartAt I α).left_inv hx]

/-- Smoothness of the pullback `scalarOnE α f` of a smooth function `f`. -/
lemma scalarOnE_contDiffOn (α : M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (scalarOnE (I := I) α f) (extChartAt I α).target := by
  -- `scalarOnE α f = f ∘ (extChartAt I α).symm`.
  -- Pull back `f` (smooth on `M`) through `(extChartAt I α).symm` (smooth on
  -- the chart target into the source).
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hf_on : ContMDiffOn I 𝓘(ℝ) ∞ f univ := hf.contMDiffOn
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f ∘ (extChartAt I α).symm)
      (extChartAt I α).target :=
    hf_on.comp hsymm (fun _ _ => mem_univ _)
  exact hcomp.contDiffOn

/-- Smoothness of the chart-pulled-back function `scalarOnE α f`, restricted
to a continuous-differentiability statement on `E`. -/
lemma scalarOnE_contDiffWithinAt
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞ (scalarOnE (I := I) α f) (extChartAt I α).target y :=
  scalarOnE_contDiffOn (I := I) α hf y hy

/-- Decomposition: applying `mfderiv` of `f` at `x` to the chart-basis frame
vector at index `i`, using the chart at `α`. The model space is `E`, so this is
just `partialDeriv i (scalarOnE α f) (φ_α x)`. To prove this we use the chain
rule `f = scalarOnE α f ∘ extChartAt I α` near `x`, plus the fact that
`mfderiv (extChartAt I α) x` sends the chart-basis frame at `α` to the model
basis (as a continuous linear map). -/
lemma mfderiv_chartBasisVecFiber (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ) f x
        (chartBasisVecFiber (I := I) α i x)
      = partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  -- Set up: writtenInExtChartAt at α (rather than at x).
  set φ := extChartAt I α
  have hxsrc : x ∈ φ.source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  -- Step 1: `f` is `MDifferentiableAt` at `x`, hence we have an `mfderiv`.
  have hf_mdiff_at : MDifferentiableAt I 𝓘(ℝ) f x := hf.mdifferentiableAt (by simp)
  -- Step 2: the chart-pulled-back function `scalarOnE α f` is `ContDiffOn ℝ ∞`
  -- on the chart target, so it's `DifferentiableAt` at `φ x` (which is in the
  -- interior of the chart target).
  have hscalar_smooth :=
    scalarOnE_contDiffOn (I := I) α hf
  have hint_open : IsOpen (interior φ.target) := isOpen_interior
  have hsubset : interior φ.target ⊆ φ.target := interior_subset
  have hscalar_at : ContDiffAt ℝ ∞ (scalarOnE (I := I) α f) (φ x) := by
    have h_within : ContDiffWithinAt ℝ ∞
        (scalarOnE (I := I) α f) φ.target (φ x) := hscalar_smooth (φ x) (hsubset hx_int)
    exact h_within.contDiffAt (mem_nhds_iff.mpr ⟨interior φ.target, hsubset, hint_open, hx_int⟩)
  have hscalar_diff : DifferentiableAt ℝ (scalarOnE (I := I) α f) (φ x) :=
    hscalar_at.differentiableAt (by simp)
  -- Step 3: The chart map `extChartAt I α` is smooth on its source. We use the
  -- key fact: `f = scalarOnE α f ∘ φ` on `φ.source` (a neighborhood of `x`).
  have hcomp_eq : ∀ᶠ y in 𝓝 x, f y = (scalarOnE (I := I) α f) (φ y) := by
    have hsrc_nhd : φ.source ∈ 𝓝 x :=
      (isOpen_extChartAt_source (I := I) α).mem_nhds hxsrc
    filter_upwards [hsrc_nhd] with y hy
    rw [scalarOnE_def, φ.left_inv hy]
  -- Step 4: from the chain rule formulation: `mfderiv f x = (fderiv (scalarOnE α f) (φ x)) ∘L (mfderiv φ x)`.
  -- Use `mfderiv_eq` for `extChartAt I α` near `x` (in chart source), and
  -- `mfderiv_eq_fderiv` for the scalar `scalarOnE α f` (which is in `E → ℝ`).
  -- A more direct route: convert to a `HasMFDerivAt` equation for `f`.
  -- Let `L := fderiv ℝ (scalarOnE α f) (φ x)` viewed as a CLM `E →L[ℝ] ℝ`.
  set L : E →L[ℝ] ℝ := fderiv ℝ (scalarOnE (I := I) α f) (φ x)
  -- The chart map `(extChartAt I α)` has `mfderiv` at `x` equal to a
  -- specific CLM; in fact, applied to `chartBasisVecFiber α i x`, the
  -- value is `(Module.finBasis ℝ E) i`. This is `trivializationAt_chartBasisVec_snd`.
  -- We derive `HasMFDerivAt` for `f` by stitching the chain.
  -- Direct path: use `MDifferentiableAt.mfderiv` formula.
  have hf_mfderiv := hf_mdiff_at.mfderiv
  -- `mfderiv I 𝓘(ℝ) f x = fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) x f) (range I) (φ_x x)`.
  -- This is too cumbersome to invoke directly. Use a different route:
  -- composition chain rule via `MDifferentiableAt.comp` to express `mfderiv f x`
  -- in terms of the constituent maps.
  -- Approach: use `Filter.EventuallyEq.mfderiv_eq` to replace `f` by
  -- `scalarOnE α f ∘ (extChartAt I α)` near `x`.
  have hcong : f =ᶠ[𝓝 x] (scalarOnE (I := I) α f) ∘ (extChartAt I α) := hcomp_eq
  have hmfderiv_cong : mfderiv I 𝓘(ℝ) f x =
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x :=
    Filter.EventuallyEq.mfderiv_eq hcong
  rw [hmfderiv_cong]
  -- Compose mfderiv: chain rule.
  -- `mfderiv (g ∘ φ) x = mfderiv g (φ x) ∘L mfderiv φ x` (when both are differentiable).
  -- For `g : E → ℝ` smooth, `mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g (φ x) = fderiv ℝ g (φ x)`.
  have hphi_diff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hx
  have hg_diff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x) :=
    hscalar_diff.mdifferentiableAt
  have hchain :
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x)).comp
          (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) :=
    mfderiv_comp x hg_diff hphi_diff
  rw [hchain]
  -- For the scalar function on `E`, `mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g (φ x) = fderiv ℝ g (φ x)`.
  rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x)
      = fderiv ℝ (scalarOnE (I := I) α f) (φ x) from
        mfderiv_eq_fderiv (𝕜 := ℝ) (f := scalarOnE (I := I) α f)]
  -- Now we need to identify
  --   `(fderiv (scalarOnE α f) (φ x)) (mfderiv φ x v)`
  -- with `partialDeriv i (scalarOnE α f) (φ x)`, when `v = chartBasisVecFiber α i x`.
  -- We claim: `mfderiv (extChartAt I α) x (chartBasisVecFiber α i x) = (Module.finBasis ℝ E) i`.
  -- This is the key chart-basis identity.
  have hmfderiv_chartBasis :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x
          (chartBasisVecFiber (I := I) α i x)
        = (Module.finBasis ℝ E) i := by
    -- `mfderiv (extChartAt I α) x = (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x`
    -- by `TangentBundle.continuousLinearMapAt_trivializationAt`. The latter applied to
    -- `chartBasisVecFiber α i x = (triv α).symm x ((finBasis ℝ E) i)` gives
    -- `(triv α).continuousLinearMapAt _ x ((triv α).symm x ((finBasis ℝ E) i)) = (finBasis ℝ E) i`,
    -- which holds whenever `x ∈ (triv α).baseSet`.
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx]
    -- Goal: `(triv α).continuousLinearMapAt ℝ x (chartBasisVecFiber α i x) = (finBasis ℝ E) i`.
    set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
      trivializationAt E (TangentSpace I) α
    -- `chartBasisVecFiber α i x = T.symm x ((finBasis ℝ E) i)` (definition).
    -- Then `T.continuousLinearMapAt ℝ x (T.symm x v) = v` for any `v`, on the base set.
    have heq : chartBasisVecFiber (I := I) α i x = T.symm x ((Module.finBasis ℝ E) i) :=
      rfl
    rw [heq]
    -- Use `Trivialization.continuousLinearMapAt_symmL` (or analogous lemma):
    -- `T.continuousLinearMapAt ℝ x ∘ T.symmL ℝ x = id` on the base set.
    have h_apply :
        T.continuousLinearMapAt ℝ x (T.symm x ((Module.finBasis ℝ E) i))
          = (Module.finBasis ℝ E) i := by
      -- Convert `T.symm x` to `T.symmL ℝ x` (these agree at base-set points).
      have : T.symm x ((Module.finBasis ℝ E) i)
            = T.symmL ℝ x ((Module.finBasis ℝ E) i) := by
        rw [Trivialization.symmL_apply]
      rw [this, Trivialization.continuousLinearMapAt_symmL T (b := x) hbase]
    exact h_apply
  -- Goal: `((fderiv ℝ (scalarOnE α f) (φ x)).comp (mfderiv (extChartAt I α) x)) (chartBasisVecFiber α i x) = partialDeriv i (scalarOnE α f) (φ x)`.
  change fderiv ℝ (scalarOnE (I := I) α f) (φ x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x (chartBasisVecFiber (I := I) α i x))
      = partialDeriv (E := E) i (scalarOnE (I := I) α f) (φ x)
  rw [hmfderiv_chartBasis]
  -- Now goal: `fderiv (scalarOnE α f) (φ x) ((Module.finBasis ℝ E) i) = partialDeriv i ...`.
  -- This is rfl from the definition of partialDeriv.
  rfl

/-- **Chart-local representation of `tangentSectionAction`.**
For `f : M → ℝ` smooth, `X` a smooth tangent section, `α : M`, and `x` in
the chart base set at `α` whose chart image lies in the interior of the chart
target,
`tangentSectionAction X f x = ∑ᵢ chartCoeff α X i x * partialDeriv i (scalarOnE α f) (φ_α x)`.
Both sides are equal as values in `ℝ`. The right-hand side depends on `α`
even though the left-hand side does not — this is the standard component-vs-action
duality. -/
theorem tangentSectionAction_chartLocal
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) :
    tangentSectionAction (I := I) X f x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i x *
          partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  -- Decompose `X x` in the chart-basis frame at `α`.
  have hXrecomp : X x = ∑ i, chartCoeff (I := I) α X i x •
        chartBasisVecFiber (I := I) α i x :=
    chartCoeff_recompose (I := I) α X hbase
  -- Linearly expand `mfderiv I 𝓘(ℝ) f x` applied to this decomposition.
  rw [tangentSectionAction_def, hXrecomp]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul]
  -- `mfderiv f x (c • v) = c • mfderiv f x v = c * mfderiv f x v` (since the codomain is `ℝ`).
  -- We have `mfderiv f x (chartBasisVecFiber α i x) = partialDeriv i (scalarOnE α f) (φ x)`
  -- by `mfderiv_chartBasisVecFiber`.
  rw [mfderiv_chartBasisVecFiber (I := I) α hf hx hx_int i]
  exact smul_eq_mul ..

/-! ### Boundaryless variant of the chart-local representation

Under `[I.Boundaryless]`, the chart target `(extChartAt I α).target` is open in `E`
(`isOpen_extChartAt_target`), so its interior coincides with itself. The
chart-local representation then holds whenever `x ∈ (chartAt H α).source`. -/

/-- Under `[I.Boundaryless]`, the chart target is open and equals its interior. -/
lemma extChartAt_target_subset_interior_of_boundaryless [I.Boundaryless] (α : M) :
    (extChartAt I α).target ⊆ interior (extChartAt I α).target := by
  intro y hy
  exact (isOpen_extChartAt_target (I := I) α).interior_eq.symm ▸ hy

/-- Under `[I.Boundaryless]`, the chart-local representation holds for any
point in the chart base set. -/
theorem tangentSectionAction_chartLocal_of_boundaryless [I.Boundaryless]
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    tangentSectionAction (I := I) X f x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i x *
          partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hx_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_target
  exact tangentSectionAction_chartLocal (I := I) α X hf hx hx_int

/-! ## Smoothness of `tangentSectionAction X f`

In any chart at `α`, the chart-local representation expresses
`tangentSectionAction X f` on the chart base set as a sum of products of smooth
functions: each `chartCoeff α X i` is `C^∞` on the base set (by
`chartCoeff_contMDiffOn`); each `partialDeriv i (scalarOnE α f) ∘ φ_α` is
`C^∞` on the smoothness domain (by composition of smoothness of the partial
derivative on the interior of the chart target with smoothness of the chart
map). Hence the action is `C^∞` on the chart base set.

A simpler statement is available under `[I.Boundaryless]`, where the chart
target is open and the smoothness domain reduces to the chart source. -/

/-- The pulled-back partial derivative is smooth on the interior of the chart
target. -/
private lemma partialDeriv_scalarOnE_contDiffOn_interior
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDeriv (E := E) i (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) := by
  -- `scalarOnE α f` is `C^∞` on the chart target, so `partialDeriv` is `C^∞`
  -- on the interior of the chart target by `partialDeriv_contDiffOn_interior`.
  have hbase : ContDiffOn ℝ ∞
      (scalarOnE (I := I) α f) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hbase_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (interior (extChartAt I α).target) := hbase.mono interior_subset
  -- Apply the same machinery as `partialDeriv_contDiffOn_interior` from `LocalFormula`.
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) :=
    hbase_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hconst : ContDiffOn ℝ ∞ (fun _ : E => (Module.finBasis ℝ E) i)
      (interior (extChartAt I α).target) := contDiffOn_const
  exact hfderiv.clm_apply hconst

/-- The pulled-back partial derivative composed with the chart map is smooth
on the smoothness domain. -/
private lemma partialDeriv_scalarOnE_comp_extChartAt_contMDiffOn
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  classical
  have hpartial : ContDiffOn ℝ ∞
      (partialDeriv (E := E) i (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) :=
    partialDeriv_scalarOnE_contDiffOn_interior (I := I) α hf i
  -- Lift to manifold smoothness on the same set.
  have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (partialDeriv (E := E) i (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) := hpartial.contMDiffOn
  -- `extChartAt I α` is smooth on its source.
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  have hchart' : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
    refine hchart.mono ?_
    intro x hx
    have h1 : x ∈ (extChartAt I α).source := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
    exact h1
  -- Composition lands in the interior of the target.
  have hsubset : (extChartAt I α).source ∩
      (extChartAt I α) ⁻¹' interior (extChartAt I α).target ⊆
        (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target :=
    fun _ hx => hx.2
  exact hpartialM.comp hchart' hsubset

/-- `tangentSectionAction X f` is `C^∞` on the chart base set at `α` whose chart
image lies in the interior of the chart target. -/
theorem tangentSectionAction_contMDiffOn
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  -- Use the chart-local representation: rewrite the function on the smoothness domain.
  set U : Set M := (extChartAt I α).source ∩
      (extChartAt I α) ⁻¹' interior (extChartAt I α).target with hU_def
  have hcongr : ∀ x ∈ U,
      tangentSectionAction (I := I) X f x =
        ∑ i : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) α X i x *
            partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
    intro x hx
    have hx_chart : x ∈ (chartAt H α).source := by
      have := hx.1
      rw [extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this
    exact tangentSectionAction_chartLocal (I := I) α X hf hx_chart hx.2
  -- Now show the right-hand side is smooth on `U`.
  refine ContMDiffOn.congr ?_ hcongr
  refine contMDiffOn_finset_sum (fun i _ => ?_)
  refine ContMDiffOn.mul ?_ ?_
  · -- `chartCoeff α X i` is smooth on the chart base set, hence on `U`.
    have h1 : ContMDiffOn I 𝓘(ℝ) ∞ (chartCoeff (I := I) α X i)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartCoeff_contMDiffOn (I := I) α X i
    refine h1.mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at this
    exact this
  · exact partialDeriv_scalarOnE_comp_extChartAt_contMDiffOn (I := I) α hf i

/-- Under `[I.Boundaryless]`, `tangentSectionAction X f` is `C^∞` on the entire
chart base set at `α`. -/
theorem tangentSectionAction_contMDiffOn_baseSet [I.Boundaryless]
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)
      (chartAt H α).source := by
  refine (tangentSectionAction_contMDiffOn (I := I) α X hf).mono ?_
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  · -- Under `Boundaryless`, the target is open, so its interior is itself.
    rw [show (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target =
          (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target from ?_]
    · exact (extChartAt I α).map_source
        (by rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx)
    · congr 1
      exact (isOpen_extChartAt_target (I := I) α).interior_eq

/-- `tangentSectionAction X f` is `C^∞` on `M` (under `[I.Boundaryless]`),
since smoothness can be established locally in any chart. -/
theorem tangentSectionAction_contMDiff [I.Boundaryless]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f) := by
  intro x
  -- Use the chart at `x`. The chart base set at `x` is a neighborhood of `x`.
  have hx_src : x ∈ (chartAt H x).source := mem_chart_source H x
  have hsrc_open : IsOpen ((chartAt H x).source) := (chartAt H x).open_source
  have hsmooth : ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)
      (chartAt H x).source :=
    tangentSectionAction_contMDiffOn_baseSet (I := I) x X hf
  exact (hsmooth x hx_src).contMDiffAt (hsrc_open.mem_nhds hx_src)

end DivergenceTheorem
end Analysis
end RicciFlower
