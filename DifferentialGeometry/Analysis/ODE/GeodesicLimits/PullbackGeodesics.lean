import DifferentialGeometry.Analysis.ODE.GeodesicLimits.MetricChristoffel
import DifferentialGeometry.Geometry.Geodesic.Naturality.MetricSpray

/-!
# LC50 binding kernel: chart geodesics of actual pullback metrics converge in `C¹`

Blueprint LC50 (A:22511), chart step: the lifts `j_i⁻¹ ∘ σ_i` of source geodesics `σ_i` are geodesics of
the ACTUAL pullbacks `h_i = j_i^* g_i`; in a chart of `N` their coefficient fields `b i` converge in `C¹`
to those of `g`, so the lifts converge in `C¹` to the `g`-geodesic with the limit initial data.

Chart data, for each `i`: a chart of `M_i` with coefficient field `c i` of `g_i` on `V i`, and the
transition `ψ i : V i → U` (`= chart_N ∘ j_i⁻¹ ∘ chart_{M_i}⁻¹`). The ACTUAL-pullback relation is
`c i = (ψ i)^* (b i)` (`hpull`), which is the chain rule for `mfderiv` applied to
`j_i ∘ chart_N⁻¹ ∘ ψ i = chart_{M_i}⁻¹`; no inverse function theorem is needed.

* `hasDerivWithinAt_pushforward_geodesic`: the image under `ψ` of a `c`-geodesic (in phase form) is a
  `b`-geodesic, where `c = ψ^* b` (from the tree's `isIntegralCurveOn_tangent_lift_geodesic` and
  `fderiv_fderiv_eq_raisedKoszulOp_of_pullback`).
* `tendstoUniformlyOn_of_pullback_geodesics`: CM4.c for these pushed-forward source geodesics.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology Metric
open DifferentialGeometry.MetricKoszul DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ContinuousDualEquiv F]

/-- The `ψ`-image of a geodesic of `c = ψ^* b` is a geodesic of `b` (phase form, within `s`). -/
theorem hasDerivWithinAt_pushforward_geodesic {U V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {b c : F → F →L[ℝ] F →L[ℝ] ℝ} {ψ : F → F}
    (hb : ContDiffOn ℝ 1 b U) (hbsymm : ∀ y ∈ U, ∀ u v : F, b y u v = b y v u)
    (hbco : ∀ y ∈ U, IsCoercive (b y)) (hψ : ContDiffOn ℝ 2 ψ V) (hψVU : MapsTo ψ V U)
    (hψinv : ∀ x ∈ V, (fderiv ℝ ψ x).IsInvertible)
    (hpull : ∀ x ∈ V, ∀ u v : F, c x u v = b (ψ x) (fderiv ℝ ψ x u) (fderiv ℝ ψ x v))
    {x x' : ℝ → F} {s : Set ℝ} (hxV : ∀ t ∈ s, x t ∈ V)
    (hx : ∀ t ∈ s, HasDerivWithinAt x (x' t) s t)
    (hx' : ∀ t ∈ s, HasDerivWithinAt x'
      (-(raisedKoszulOp (c (x t)) (fderiv ℝ c (x t)) (x' t) (x' t))) s t) :
    ∀ t ∈ s, HasDerivWithinAt (fun t => ψ (x t)) (fderiv ℝ ψ (x t) (x' t)) s t ∧
      HasDerivWithinAt (fun t => fderiv ℝ ψ (x t) (x' t))
        (-(raisedKoszulOp (b (ψ (x t))) (fderiv ℝ b (ψ (x t)))
          (fderiv ℝ ψ (x t) (x' t)) (fderiv ℝ ψ (x t) (x' t)))) s t := by
  have hcurve : IsIntegralCurveOn (fun t => (x t, x' t))
      (fun _ z => (z.2, -raisedKoszulOp (c z.1) (fderiv ℝ c z.1) z.2 z.2)) s :=
    fun t ht => HasDerivWithinAt.prodMk (hx t ht) (hx' t ht)
  have hpush := DifferentialGeometry.Geometry.Connection.isIntegralCurveOn_tangent_lift_geodesic
    (A := fun y => raisedKoszulOp (c y) (fderiv ℝ c y))
    (C := fun y => raisedKoszulOp (b y) (fderiv ℝ b y)) hcurve
    (fun t ht => hψ.contDiffAt (hV.mem_nhds (hxV t ht)))
    (fun t ht v => by
      rw [fderiv_fderiv_eq_raisedKoszulOp_of_pullback hV hU hb hbsymm hbco hψ hψVU hψinv hpull
        (hxV t ht) v v]
      exact sub_add_cancel _ _)
  intro t ht
  have h := hpush t ht
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ)
    (p := (ψ (x t), fderiv ℝ ψ (x t) (x' t)))).comp_hasDerivWithinAt t h
  have h2 := (hasFDerivAt_snd (𝕜 := ℝ)
    (p := (ψ (x t), fderiv ℝ ψ (x t) (x' t)))).comp_hasDerivWithinAt t h
  exact ⟨h1, h2⟩

/-- **LC50 binding kernel (chart form).** Let `b i` (the chart coefficients of the actual pullbacks
`j_i^* g_i`) be `C¹`, symmetric and coercive on an open `U`, converging in `C¹` on compact subsets of
`U` to a `C²` coercive field `bInf` (the chart coefficients of `g`). For each `i` let `c i = (ψ i)^* (b i)`
on `V i` (the chart coefficients of `g_i`) and let `(x i, x' i)` be a `c i`-geodesic on `[t₀, t₁]`
(a source geodesic in a chart of `M_i`). If the pushed-forward initial data converge to those of a
`bInf`-geodesic `(cInf, cInf')` in `U`, then the pushed-forward curves and their velocities converge
uniformly on `[t₀, t₁]` to `cInf` and `cInf'` (the whole sequence). -/
theorem tendstoUniformlyOn_of_pullback_geodesics {U : Set F} (hU : IsOpen U)
    (b : ℕ → F → F →L[ℝ] F →L[ℝ] ℝ) (bInf : F → F →L[ℝ] F →L[ℝ] ℝ)
    (hb : ∀ i, ContDiffOn ℝ 1 (b i) U) (hbsymm : ∀ i, ∀ y ∈ U, ∀ u v : F, b i y u v = b i y v u)
    (hbco : ∀ i, ∀ y ∈ U, IsCoercive (b i y)) (hbInf : ContDiffOn ℝ 2 bInf U)
    (hco : ∀ y ∈ U, IsCoercive (bInf y))
    (hconv : ∀ C : Set F, IsCompact C → C ⊆ U → MapCPConvergenceOn C 1 b bInf)
    (V : ℕ → Set F) (hV : ∀ i, IsOpen (V i)) (c : ℕ → F → F →L[ℝ] F →L[ℝ] ℝ) (ψ : ℕ → F → F)
    (hψ : ∀ i, ContDiffOn ℝ 2 (ψ i) (V i)) (hψVU : ∀ i, MapsTo (ψ i) (V i) U)
    (hψinv : ∀ i, ∀ x ∈ V i, (fderiv ℝ (ψ i) x).IsInvertible)
    (hpull : ∀ i, ∀ x ∈ V i, ∀ u v : F,
      c i x u v = b i (ψ i x) (fderiv ℝ (ψ i) x u) (fderiv ℝ (ψ i) x v))
    {t₀ t₁ : ℝ} (x x' : ℕ → ℝ → F) (hxV : ∀ i, ∀ t ∈ Icc t₀ t₁, x i t ∈ V i)
    (hx : ∀ i, ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt (x i) (x' i t) (Icc t₀ t₁) t)
    (hx' : ∀ i, ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt (x' i)
      (-(raisedKoszulOp (c i (x i t)) (fderiv ℝ (c i) (x i t)) (x' i t) (x' i t))) (Icc t₀ t₁) t)
    (cInf cInf' : ℝ → F) (hcU : ∀ t ∈ Icc t₀ t₁, cInf t ∈ U)
    (hc : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt cInf (cInf' t) (Icc t₀ t₁) t)
    (hc' : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt cInf'
      (-(raisedKoszulOp (bInf (cInf t)) (fderiv ℝ bInf (cInf t)) (cInf' t) (cInf' t))) (Icc t₀ t₁) t)
    (h0 : Tendsto (fun i => ψ i (x i t₀)) atTop (𝓝 (cInf t₀)))
    (h0' : Tendsto (fun i => fderiv ℝ (ψ i) (x i t₀) (x' i t₀)) atTop (𝓝 (cInf' t₀))) :
    TendstoUniformlyOn (fun i t => ψ i (x i t)) cInf atTop (Icc t₀ t₁) ∧
      TendstoUniformlyOn (fun i t => fderiv ℝ (ψ i) (x i t) (x' i t)) cInf' atTop (Icc t₀ t₁) := by
  have hpush := fun i => hasDerivWithinAt_pushforward_geodesic hU (hV i) (hb i) (hbsymm i)
    (hbco i) (hψ i) (hψVU i) (hψinv i) (hpull i) (hxV i) (hx i) (hx' i)
  exact tendstoUniformlyOn_of_metric_tendsto hU b bInf hb hbInf hco hconv cInf cInf' hcU hc hc'
    (fun i t => ψ i (x i t)) (fun i t => fderiv ℝ (ψ i) (x i t) (x' i t))
    (fun i t ht => (hpush i t ht).1) (fun i t ht => (hpush i t ht).2) h0 h0'

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
