import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Local chart-coordinate continuity of `mfderiv` along a smooth curve

For a `C^∞` curve `γ : ℝ → M` into a smooth manifold modelled on
`(E, H, I)` and a chart basepoint `α : M`, the chart-`α`-coordinate of
the velocity vector,
$$
  t \;\longmapsto\; \bigl(\mathrm{d}\gamma_t(1)\bigr)_\alpha
   \;=\; \mathrm{d}(\mathrm{extChartAt}\,I\,\alpha)_{\gamma(t)}
        \bigl(\mathrm{mfderiv}\,\gamma\,t\,1\bigr)
   \;=\; \mathrm{fderiv}\,(\mathrm{extChartAt}\,I\,\alpha \circ \gamma)\,t\,1,
$$
is continuous on the open set
`U(α) := γ ⁻¹ ((chartAt H α).source)`.

This is the *chart-fixed* form of velocity-continuity. Together with the
chain-rule identity
`(trivializationAt α).continuousLinearMapAt ℝ (γ t) (mfderiv γ t 1)
 = fderiv (extChartAt I α ∘ γ) t 1`,
it is the analytic backbone for downstream integrability and
Lebesgue-number-style chart-patching arguments (e.g. in the
second-variation length-bound development).

## Main results

* `chartCoord_mfderiv_along_curve_eq_fderiv` —
  the chain-rule identity expressing the chart-`α`-coordinate of
  `mfderiv γ t 1` as a model-space `fderiv`.

* `continuousOn_chartCoord_mfderiv_along_curve` —
  continuity of the chart-`α`-coordinate of `mfderiv γ t 1`,
  on the open set `γ ⁻¹ ((chartAt H α).source)`. Stated equivalently
  as continuity of `t ↦ fderiv (extChartAt I α ∘ γ) t 1`.

* `chartCoord_mfderiv_along_curve_continuousOn` —
  the same continuity, packaged for a compact base set `s` contained in
  the chart-`α` preimage.

* `raw_mfderiv_eq_symmL_apply_fderiv` —
  the **raw-form rewrite identity**: for `γ t ∈ (chartAt H α).source`,
  `mfderiv γ t 1 = (trivializationAt α).symmL ℝ (γ t) (fderiv (extChartAt I α ∘ γ) t 1)`,
  obtained by applying the inverse trivialization at `γ t` to the
  chart-`α`-coordinate identity and using `Trivialization.symmL_continuousLinearMapAt`.
  This is the substantive bridge between the raw `mfderiv γ t 1 : E` (using the
  defeq `TangentSpace I (γ t) = E`) and the chart-pulled-back model-space
  `fderiv`.

The continuity of the *raw* `mfderiv γ t 1 : E` follows from the
rewrite identity above combined with the CLM-valued continuity of the family
`t ↦ (trivializationAt α).symmL ℝ (γ t)` on `γ ⁻¹ ((chartAt H α).source)`.
The latter is a vector-bundle infrastructure fact about the tangent bundle's
`symmL` family — it lives below this file (in the bundle / `tangentMap`
machinery) and is not duplicated here; downstream developments that need
it can route through the rewrite identity delivered above.
-/

noncomputable section

open Set Function Filter Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace MFDerivAlongCurve

/-- **Chart-`α`-coordinate of `mfderiv γ t 1` equals `fderiv (extChartAt I α ∘ γ) t 1`.**

For a `C^∞` curve `γ : ℝ → M` and a chart basepoint `α : M`, at any
`t : ℝ` with `γ t ∈ (chartAt H α).source`, the trivialization-`α`-coordinate
of the velocity vector,
  `(trivializationAt α).continuousLinearMapAt ℝ (γ t) (mfderiv γ t 1)`,
equals the ordinary `fderiv` of the chart-pulled-back curve,
  `fderiv (extChartAt I α ∘ γ) t 1`.

This is a direct consequence of the chain rule and the identification
`TangentBundle.continuousLinearMapAt_trivializationAt`. -/
theorem chartCoord_mfderiv_along_curve_eq_fderiv
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (α : M) {t : ℝ} (ht : γ t ∈ (chartAt H α).source) :
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) =
      (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I)
        (x₀ := α) (x := γ t) ht]
  have hγ_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    (hγ.contMDiffAt).mdifferentiableAt (by simp)
  have hφ_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) (γ t) :=
    mdifferentiableAt_extChartAt (I := I) (x := α) ht
  have hchain :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I α) ∘ γ) t =
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)).comp
          (mfderiv 𝓘(ℝ, ℝ) I γ t) :=
    mfderiv_comp t hφ_mdiff hγ_mdiff
  have hmf_eq_f :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I α) ∘ γ) t =
        fderiv ℝ ((extChartAt I α) ∘ γ) t :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (f := (extChartAt I α) ∘ γ) (x := t)
  have hRHS :
      (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) =
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)).comp
            (mfderiv 𝓘(ℝ, ℝ) I γ t)) (1 : ℝ) := by
    rw [← hmf_eq_f, hchain]; rfl
  rw [hRHS]; rfl

/-- **`MDifferentiableAt`-level chart-`α`-coordinate chain rule.**

The same chain-rule identity as `chartCoord_mfderiv_along_curve_eq_fderiv`, but
requiring only `MDifferentiableAt 𝓘(ℝ, ℝ) I γ t` (in place of global `C^∞`
smoothness of `γ`). The original proof uses the `C^∞` hypothesis solely to
extract `MDifferentiableAt 𝓘(ℝ, ℝ) I γ t`; everything downstream
(`mfderiv_comp`, `mfderiv_eq_fderiv`, `mdifferentiableAt_extChartAt`,
`TangentBundle.continuousLinearMapAt_trivializationAt`) is `MDifferentiableAt`-
level. This `C²`/`MDifferentiableAt`-relaxed form is the velocity bridge consumed
by second-order variational arguments where the curve is only twice continuously
differentiable (e.g. the radial geodesic variation behind Gauss's lemma). -/
theorem chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
    {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (α : M) (ht : γ t ∈ (chartAt H α).source) :
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) =
      (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I)
        (x₀ := α) (x := γ t) ht]
  have hφ_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) (γ t) :=
    mdifferentiableAt_extChartAt (I := I) (x := α) ht
  have hchain :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I α) ∘ γ) t =
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)).comp
          (mfderiv 𝓘(ℝ, ℝ) I γ t) :=
    mfderiv_comp t hφ_mdiff hγ
  have hmf_eq_f :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I α) ∘ γ) t =
        fderiv ℝ ((extChartAt I α) ∘ γ) t :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (f := (extChartAt I α) ∘ γ) (x := t)
  have hRHS :
      (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) =
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)).comp
            (mfderiv 𝓘(ℝ, ℝ) I γ t)) (1 : ℝ) := by
    rw [← hmf_eq_f, hchain]; rfl
  rw [hRHS]; rfl

/-- The chart-`α`-pullback `t ↦ (fderiv ℝ (extChartAt I α ∘ γ) t : ℝ → E) 1`
is continuous on the open set `U := γ ⁻¹ ((chartAt H α).source)`. -/
theorem continuousOn_fderiv_extChartAt_comp_curve
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (α : M) :
    ContinuousOn
      (fun t : ℝ => (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ → E) (1 : ℝ))
      (γ ⁻¹' (chartAt H α).source) := by
  classical
  set U : Set ℝ := γ ⁻¹' (chartAt H α).source with hU_def
  have hU_open : IsOpen U := by
    have : IsOpen (chartAt H α).source := by
      rw [← extChartAt_source (I := I)]
      exact isOpen_extChartAt_source (I := I) α
    exact hγ.continuous.isOpen_preimage _ this
  have h_comp_mdiff :
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((extChartAt I α) ∘ γ) U := by
    have hφ : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α)
        (chartAt H α).source :=
      contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
    have hγU : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ U := hγ.contMDiffOn
    have hmaps : MapsTo γ U (chartAt H α).source := fun _ ht => ht
    exact hφ.comp hγU hmaps
  have h_comp_diff :
      ContDiffOn ℝ ∞ ((extChartAt I α) ∘ γ) U :=
    contMDiffOn_iff_contDiffOn.mp h_comp_mdiff
  have h1le : (1 : ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)
  have h_fdW :
      ContinuousOn (fderivWithin ℝ ((extChartAt I α) ∘ γ) U) U :=
    h_comp_diff.continuousOn_fderivWithin hU_open.uniqueDiffOn h1le
  have h_fderiv_cont :
      ContinuousOn (fun t : ℝ => fderiv ℝ ((extChartAt I α) ∘ γ) t) U := by
    refine h_fdW.congr ?_
    intro t ht
    exact (fderivWithin_of_isOpen hU_open ht).symm
  exact h_fderiv_cont.clm_apply continuousOn_const

/-- **Continuity of the chart-`α`-coordinate of the velocity along a smooth curve.**

For a `C^∞` curve `γ : ℝ → M` and a chart basepoint `α : M`, the function
  `t ↦ (trivializationAt α).continuousLinearMapAt ℝ (γ t) (mfderiv γ t 1) : ℝ → E`
is continuous on the open set `γ ⁻¹ ((chartAt H α).source)`. -/
theorem continuousOn_chartCoord_mfderiv_along_curve
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (α : M) :
    ContinuousOn
      (fun t : ℝ =>
        (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
          ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) : E))
      (γ ⁻¹' (chartAt H α).source) := by
  refine ContinuousOn.congr
    (continuousOn_fderiv_extChartAt_comp_curve (I := I) (M := M) (γ := γ) hγ α) ?_
  intro t ht
  exact (chartCoord_mfderiv_along_curve_eq_fderiv (I := I) (M := M) (γ := γ) hγ
    α (t := t) ht)

/-- **Compact-domain version of the chart-`α`-coordinate continuity.**

For a `C^∞` curve `γ : ℝ → M`, a chart basepoint `α : M`, and a compact
subset `s ⊆ γ ⁻¹ ((chartAt H α).source)` contained in the chart-`α`
preimage, the chart-`α`-coordinate of `mfderiv γ t 1` is continuous on
`s`. -/
theorem chartCoord_mfderiv_along_curve_continuousOn
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (α : M)
    {s : Set ℝ} (_hs : IsCompact s)
    (hs_sub : s ⊆ γ ⁻¹' (chartAt H α).source) :
    ContinuousOn
      (fun t : ℝ =>
        (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
          ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) : E)) s := by
  exact (continuousOn_chartCoord_mfderiv_along_curve (I := I) (M := M)
    (γ := γ) hγ α).mono hs_sub

/-- **Raw form equals `symmL` of chart-pulled-back `fderiv`.**

For `t : ℝ` with `γ t ∈ (chartAt H α).source`, the raw mfderiv-velocity along
the curve `γ` at `t`, evaluated at `1 : ℝ`, equals
  `(trivializationAt α).symmL ℝ (γ t) (fderiv (extChartAt I α ∘ γ) t 1)`.

This is the inverse-trivialization companion of `chartCoord_mfderiv_along_curve_eq_fderiv`,
obtained by applying `(trivializationAt α).symmL ℝ (γ t)` to both sides of the
chart-coordinate identity and using `Trivialization.symmL_continuousLinearMapAt`. -/
theorem raw_mfderiv_eq_symmL_apply_fderiv
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (α : M) {t : ℝ} (ht : γ t ∈ (chartAt H α).source) :
    ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ) : E) =
      ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
        ((fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ)) := by
  have hCC : ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
      ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) =
        (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) :=
    chartCoord_mfderiv_along_curve_eq_fderiv (I := I) (M := M) (γ := γ) hγ α ht
  have hbaseSet : γ t ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact ht
  have hround :
      ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
          (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
            ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ))) =
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) :=
    (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
      (R := ℝ) hbaseSet _
  calc ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ) : E)
      = ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
          (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
            ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ))) := hround.symm
    _ = ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
          ((fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ)) := by rw [hCC]

/-- **`MDifferentiableAt`-level raw form equals `symmL` of chart-pulled-back
`fderiv`.**

The same identity as `raw_mfderiv_eq_symmL_apply_fderiv`, but requiring only
`MDifferentiableAt 𝓘(ℝ, ℝ) I γ t` (in place of global `C^∞` smoothness of `γ`).
The original proof uses the smoothness hypothesis solely through
`chartCoord_mfderiv_along_curve_eq_fderiv`, which itself has an
`MDifferentiableAt`-only variant
(`chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt`); everything else
(`symmL_continuousLinearMapAt`, the base-set membership) is regularity-free. This
is the velocity bridge consumed by variational arguments where the curve is only
finite-order differentiable. -/
theorem raw_mfderiv_eq_symmL_apply_fderiv_of_mdifferentiableAt
    {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (α : M) (ht : γ t ∈ (chartAt H α).source) :
    ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ) : E) =
      ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
        ((fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ)) := by
  have hCC : ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
      ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) =
        (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) :=
    chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := γ) hγ α ht
  have hbaseSet : γ t ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact ht
  have hround :
      ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
          (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
            ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ))) =
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) :=
    (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
      (R := ℝ) hbaseSet _
  calc ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ) : E)
      = ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
          (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
            ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ))) := hround.symm
    _ = ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
          ((fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ)) := by rw [hCC]

/-- **Tangent-bundle-valued unit-tangent map along a smooth curve is continuous.**

For a `C^n` curve `γ : ℝ → M` with `1 ≤ n`, the function
  `t ↦ tangentMap 𝓘(ℝ, ℝ) I γ ⟨t, 1⟩ : ℝ → TangentBundle I M`
is continuous on `ℝ`. By definition of `tangentMap`, this equals
`t ↦ ⟨γ t, mfderiv 𝓘(ℝ, ℝ) I γ t 1⟩ : ℝ → TangentBundle I M`,
packaging the raw mfderiv-velocity together with its basepoint as a continuous
bundle-valued function.

This is the canonical *bundle-level* continuity statement underlying the raw
`E`-valued mfderiv-velocity continuity along the curve (via fibre extraction
through the local trivialisation at any chart basepoint). -/
theorem continuous_tangentMap_unitLift
    {γ : ℝ → M} {n : WithTop ℕ∞} (hn : 1 ≤ n) (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ) :
    Continuous (fun t : ℝ =>
      tangentMap 𝓘(ℝ, ℝ) I γ (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
  have h_tan_cont : Continuous (tangentMap 𝓘(ℝ, ℝ) I γ) :=
    hγ.continuous_tangentMap hn
  have h_input_cont :
      Continuous (fun t : ℝ =>
        (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have h_homeo :
        Continuous ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm :
          ModelProd ℝ ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous
    have h_pair : Continuous (fun t : ℝ => (t, (1 : ℝ))) :=
      continuous_id.prodMk continuous_const
    exact h_homeo.comp h_pair
  exact h_tan_cont.comp h_input_cont

/-- The open chart-pullback cover `{U(α) : α ∈ M}` covers `ℝ` (via `γ`)
in the following sense: every `t : ℝ` lies in `γ ⁻¹ ((chartAt H (γ t)).source)`. -/
theorem mem_chartPullback_self {γ : ℝ → M} (t : ℝ) :
    t ∈ γ ⁻¹' (chartAt H (γ t)).source := by
  exact mem_chart_source H (γ t)

/-- For any subset `s ⊆ ℝ` and `C^∞` curve `γ : ℝ → M`, the family
`{γ ⁻¹ ((chartAt H (γ t₀)).source) : t₀ ∈ s}` covers `s`. (No
smoothness or compactness needed for the set-theoretic cover itself.) -/
theorem chartPullback_cover_compact
    {γ : ℝ → M} (_hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {s : Set ℝ} (_hs : IsCompact s) :
    s ⊆ ⋃ t₀ ∈ s, γ ⁻¹' (chartAt H (γ t₀)).source := by
  intro t ht
  refine mem_iUnion_of_mem t ?_
  refine mem_iUnion_of_mem ht ?_
  exact mem_chart_source H (γ t)

/-- A compact set `s ⊆ ℝ` admits a finite chart-pullback subcover
adapted to a `C^∞` curve `γ : ℝ → M`: there is a finite subset
`T ⊆ s` such that `s ⊆ ⋃_{t₀ ∈ T} γ ⁻¹ ((chartAt H (γ t₀)).source)`.
This is the standard Heine–Borel reduction underlying chart-by-chart
continuity patching. -/
theorem exists_finite_chartPullback_subcover
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    {s : Set ℝ} (hs : IsCompact s) :
    ∃ T : Set ℝ, T ⊆ s ∧ Set.Finite T ∧
      s ⊆ ⋃ t₀ ∈ T, γ ⁻¹' (chartAt H (γ t₀)).source := by
  classical
  have hopen : ∀ t₀ : ℝ, t₀ ∈ s → IsOpen (γ ⁻¹' (chartAt H (γ t₀)).source) := by
    intro t₀ _
    have : IsOpen (chartAt H (γ t₀)).source := by
      rw [← extChartAt_source (I := I)]
      exact isOpen_extChartAt_source (I := I) (γ t₀)
    exact hγ.continuous.isOpen_preimage _ this
  have hcover : s ⊆ ⋃ t₀ ∈ s, γ ⁻¹' (chartAt H (γ t₀)).source :=
    chartPullback_cover_compact (I := I) (M := M) (γ := γ) hγ hs
  exact hs.elim_finite_subcover_image hopen hcover

end MFDerivAlongCurve

end Riemannian
end Geometry
end DifferentialGeometry
