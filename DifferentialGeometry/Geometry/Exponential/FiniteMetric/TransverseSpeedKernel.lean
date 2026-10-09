import DifferentialGeometry.Geometry.Exponential.FiniteMetric.GaussKernel

/-!
# Chart kernel: the transverse speed of a normal variation of a geodesic is stationary

Let `Y(t, h)` be a `C²` two-parameter map into a chart, such that `t ↦ Y(t, 0)` is a solution of the
metric spray of `B` (a geodesic read in the chart) and the variation field `∂ₕY(t, 0)` is
`B`-orthogonal to the velocity `∂ₜY(t, 0)` for all `t` near `t₀`. Then the transverse speed
`G(h) = B(Y(t₀, h))(∂ₜY, ∂ₜY)` has `G'(0) = 0` (`hasDerivAt_transverse_speed_chart`).

Proof (in every dimension, no parallel transport): differentiate the orthogonality in `t`, use the
Koszul identity `MetricKoszul.metricSpray_snd_apply` for the acceleration and the symmetry of the
mixed second derivatives of `Y`; this gives `B(∂ₜY, ∂ₜ∂ₕY) = -½ ∂_{∂ₕY} B (∂ₜY, ∂ₜY)`, which is exactly
the cancellation in `G'(0) = ∂_{∂ₕY} B (∂ₜY, ∂ₜY) + 2 B(∂ₕ∂ₜY, ∂ₜY)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.MetricKoszul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ContinuousDualEquiv E]

local instance transverseBilinNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance transverseBilinNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- **Transverse speed kernel.** -/
theorem hasDerivAt_transverse_speed_chart {B : E → E →L[ℝ] E →L[ℝ] ℝ} {Y : ℝ × ℝ → E}
    {t₀ : ℝ} (hY : ContDiffAt ℝ 2 Y (t₀, 0))
    (hgeo : HasDerivAt (fun t => (Y (t, 0), fderiv ℝ Y (t, 0) ((1 : ℝ), (0 : ℝ))))
      (metricSpray B (Y (t₀, 0), fderiv ℝ Y (t₀, 0) ((1 : ℝ), (0 : ℝ)))) t₀)
    (hperp : ∀ᶠ t in 𝓝 t₀, B (Y (t, 0)) (fderiv ℝ Y (t, 0) ((1 : ℝ), (0 : ℝ)))
      (fderiv ℝ Y (t, 0) ((0 : ℝ), (1 : ℝ))) = 0)
    (hB : DifferentiableAt ℝ B (Y (t₀, 0))) (hco : IsCoercive (B (Y (t₀, 0))))
    (hsym : ∀ v w, B (Y (t₀, 0)) v w = B (Y (t₀, 0)) w v) :
    HasDerivAt (fun h => B (Y (t₀, h)) (fderiv ℝ Y (t₀, h) ((1 : ℝ), (0 : ℝ)))
      (fderiv ℝ Y (t₀, h) ((1 : ℝ), (0 : ℝ)))) 0 0 := by
  set D1 := fderiv ℝ Y with hD1def
  set D2 := fderiv ℝ D1 (t₀, 0) with hD2def
  set e₁ : ℝ × ℝ := ((1 : ℝ), (0 : ℝ)) with he₁
  set e₂ : ℝ × ℝ := ((0 : ℝ), (1 : ℝ)) with he₂
  set y₀ := Y (t₀, 0) with hy₀
  set U₀ := D1 (t₀, 0) e₁ with hU₀
  set X₀ := D1 (t₀, 0) e₂ with hX₀
  set A := (metricSpray B (y₀, U₀)).2 with hA
  -- regularity
  have hYd : DifferentiableAt ℝ Y (t₀, 0) := hY.differentiableAt (by simp)
  have hD1d : DifferentiableAt ℝ D1 (t₀, 0) :=
    (hY.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hsymm : ∀ a b, D2 a b = D2 b a :=
    hY.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  -- slices
  have hsl_t : HasDerivAt (fun t : ℝ => (t, (0 : ℝ))) e₁ t₀ :=
    (hasDerivAt_id t₀).prodMk (hasDerivAt_const t₀ (0 : ℝ))
  have hsl_h : HasDerivAt (fun h : ℝ => (t₀, h)) e₂ 0 :=
    (hasDerivAt_const (0 : ℝ) t₀).prodMk (hasDerivAt_id (0 : ℝ))
  -- `t`-derivatives along `h = 0`
  have hYt : HasDerivAt (fun t : ℝ => Y (t, 0)) U₀ t₀ :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t₀ hgeo
  have hVt : HasDerivAt (fun t : ℝ => D1 (t, 0) e₁) A t₀ :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t₀ hgeo
  have hD1t : HasDerivAt (fun t : ℝ => D1 (t, 0)) (D2 e₁) t₀ :=
    hD1d.hasFDerivAt.comp_hasDerivAt t₀ hsl_t
  have hXt : HasDerivAt (fun t : ℝ => D1 (t, 0) e₂) (D2 e₁ e₂) t₀ := by
    have h := hD1t.clm_apply (hasDerivAt_const t₀ e₂)
    simpa using h
  -- `h`-derivatives at `t = t₀`
  have hYh : HasDerivAt (fun h : ℝ => Y (t₀, h)) X₀ 0 :=
    hYd.hasFDerivAt.comp_hasDerivAt 0 hsl_h
  have hD1h : HasDerivAt (fun h : ℝ => D1 (t₀, h)) (D2 e₂) 0 :=
    hD1d.hasFDerivAt.comp_hasDerivAt 0 hsl_h
  have hVh : HasDerivAt (fun h : ℝ => D1 (t₀, h) e₁) (D2 e₂ e₁) 0 := by
    have h := hD1h.clm_apply (hasDerivAt_const (0 : ℝ) e₁)
    simpa using h
  -- the orthogonality, differentiated in `t`
  have hBt : HasDerivAt (fun t : ℝ => B (Y (t, 0))) (fderiv ℝ B y₀ U₀) t₀ :=
    hB.hasFDerivAt.comp_hasDerivAt t₀ hYt
  have hP := (hBt.clm_apply hVt).clm_apply hXt
  have hP0 : HasDerivAt (fun t : ℝ => B (Y (t, 0)) (D1 (t, 0) e₁) (D1 (t, 0) e₂)) 0 t₀ :=
    (hasDerivAt_const t₀ (0 : ℝ)).congr_of_eventuallyEq (hperp.mono fun t ht => ht)
  have hPeq := hP.unique hP0
  simp only [add_apply] at hPeq
  -- the transverse speed, differentiated in `h`
  have hBh : HasDerivAt (fun h : ℝ => B (Y (t₀, h))) (fderiv ℝ B y₀ X₀) 0 :=
    hB.hasFDerivAt.comp_hasDerivAt 0 hYh
  have hG := (hBh.clm_apply hVh).clm_apply hVh
  simp only [add_apply] at hG
  -- algebra: Koszul identity and symmetries
  have hk := metricSpray_snd_apply B y₀ U₀ X₀ hco
  rw [← hA] at hk
  have hW : B y₀ U₀ (D2 e₁ e₂) = B y₀ (D2 e₁ e₂) U₀ := hsym _ _
  rw [hsymm e₂ e₁] at hG
  simp only [← hy₀, ← hU₀, ← hX₀] at hPeq hG
  convert hG using 1
  linear_combination (-2 : ℝ) * hPeq + 2 * hk + hW

end DifferentialGeometry.MetricKoszul
