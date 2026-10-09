import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The Hessian of a function that is affine along chart geodesics (LFR11, kernels K2–K3)

For blueprint LFR11 (A:25566–25672): the Euclidean coordinate `t_a` of an exact metric splitting is
affine along every geodesic, hence its covariant Hessian vanishes. In a chart, with the chart
geodesic equation `c'' = -Γ(c)(c', c')`, this reads `D²f(z)(v, v) = Df(z)(Γ(z)(v, v))` (K3,
`fderiv_fderiv_apply_self_eq_of_comp_affine`), and by polarization
`D²f(z)(v, w) = Df(z)(½(Γ(z)(v, w) + Γ(z)(w, v)))` (K2, `fderiv_fderiv_eq_of_apply_self`).
No symmetry of `Γ` and no intrinsic connection is used.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The symmetrization `(v, w) ↦ ½ (Γ v w + Γ w v)` of a bilinear map. -/
def symmBilin (Γ : E →L[ℝ] E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] E :=
  (1 / 2 : ℝ) • (Γ + Γ.flip)

@[simp] theorem symmBilin_apply (Γ : E →L[ℝ] E →L[ℝ] E) (v w : E) :
    symmBilin Γ v w = (1 / 2 : ℝ) • (Γ v w + Γ w v) := by
  simp [symmBilin]

theorem contDiffOn_symmBilin {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {s : Set X} {Γ : X → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiffOn ℝ n Γ s) :
    ContDiffOn ℝ n (fun z => symmBilin (Γ z)) s := by
  unfold symmBilin
  exact (hΓ.add ((ContinuousLinearMap.flipₗᵢ ℝ E E E).contDiff.comp_contDiffOn hΓ)).const_smul _

/-- **Kernel K2 (polarization).** If the second derivative of a `C²` function agrees with
`Df ∘ Γ` on the diagonal, it agrees with `Df ∘ symmBilin Γ` everywhere. -/
theorem fderiv_fderiv_eq_of_apply_self {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (h : ∀ v : E, fderiv ℝ (fderiv ℝ f) z v v = fderiv ℝ f z (Γ v v)) (v w : E) :
    fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ f z (symmBilin Γ v w) := by
  have hsymm : fderiv ℝ (fderiv ℝ f) z w v = fderiv ℝ (fderiv ℝ f) z v w :=
    (hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])) w v
  have h1 := h (v + w)
  simp only [map_add, add_apply] at h1
  rw [h v, h w, hsymm] at h1
  rw [symmBilin_apply, map_smul, map_add, smul_eq_mul]
  linarith

/-- **Kernel K3 (affine along a chart geodesic).** Let `c` have velocity `v` near `t₀` and
`v' (t₀) = -Γ (v t₀) (v t₀)`. If `f ∘ c` is affine near `t₀` and `f` is `C²` at `c t₀`, then
`D²f(c t₀)(v t₀, v t₀) = Df(c t₀)(Γ (v t₀) (v t₀))`. -/
theorem fderiv_fderiv_apply_self_eq_of_comp_affine {f : E → ℝ} {Γ : E →L[ℝ] E →L[ℝ] E}
    {c v : ℝ → E} {t₀ a b : ℝ} (hf : ContDiffAt ℝ 2 f (c t₀))
    (hc : ∀ᶠ t in 𝓝 t₀, HasDerivAt c (v t) t) (hv : HasDerivAt v (-Γ (v t₀) (v t₀)) t₀)
    (haff : ∀ᶠ t in 𝓝 t₀, f (c t) = a + b * t) :
    fderiv ℝ (fderiv ℝ f) (c t₀) (v t₀) (v t₀) = fderiv ℝ f (c t₀) (Γ (v t₀) (v t₀)) := by
  have hc0 : HasDerivAt c (v t₀) t₀ := hc.self_of_nhds
  -- `f` is differentiable near `c t₀`, hence along `c` near `t₀`
  have hfd : ∀ᶠ y in 𝓝 (c t₀), DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hfdc : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ f (c t) :=
    hc0.continuousAt.preimage_mem_nhds hfd
  -- the derivative of `f ∘ c` is `b` near `t₀`
  have hk : ∀ᶠ t in 𝓝 t₀, fderiv ℝ f (c t) (v t) = b := by
    filter_upwards [hc, hfdc, haff.eventually_nhds] with t hct hft haft
    have h1 : HasDerivAt (fun s => f (c s)) (fderiv ℝ f (c t) (v t)) t :=
      hft.hasFDerivAt.comp_hasDerivAt t hct
    have h2 : HasDerivAt (fun s => f (c s)) b t := by
      have h3 : HasDerivAt (fun s : ℝ => a + b * s) b t := by
        simpa using ((hasDerivAt_id t).const_mul b).const_add a
      exact h3.congr_of_eventuallyEq haft
    exact h1.unique h2
  -- the derivative of `t ↦ Df(c t)(v t)` at `t₀`
  have hDf : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (c t₀)) (c t₀) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
  have hK : HasDerivAt (fun t => fderiv ℝ f (c t) (v t))
      (fderiv ℝ (fderiv ℝ f) (c t₀) (v t₀) (v t₀) +
        fderiv ℝ f (c t₀) (-Γ (v t₀) (v t₀))) t₀ :=
    (hDf.comp_hasDerivAt t₀ hc0).clm_apply hv
  have hK0 : HasDerivAt (fun t => fderiv ℝ f (c t) (v t)) 0 t₀ :=
    (hasDerivAt_const t₀ b).congr_of_eventuallyEq hk
  have he := hK.unique hK0
  rw [map_neg] at he
  linarith

end DifferentialGeometry.Analysis
