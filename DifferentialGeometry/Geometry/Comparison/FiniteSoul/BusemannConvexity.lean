import DifferentialGeometry.Geometry.Comparison.Soul.BusemannLevels

/-!
# Busemann convexity from squared-distance convexity (S-BUS metric kernel)

Pure metric statements, no manifold:

* `convexOn_busemann_comp_of_convexOn_mul_sq_sub_sq`: if `t ↦ a t² - d(c s, σ t)²` is convex on
  `D` for every point `c s` of a ray `c`, then the Busemann function of `c` is convex along `σ`
  on `D`. Route: `F_s(t) = (a t² - d(c s, σ t)² + s²) / (2 s)` is convex and tends to
  `busemann c (σ t)` as `s → ∞` (the smooth template is `convexOn_busemann_intrinsicGeodesic_unit`).
* `convexOn_busemann_comp_of_convexOn_sq_sub_sq`: the frozen interface form (`a = 1`, `D = ℝ`).
* `convexOn_rayExhaustion_comp`: if every Busemann function of a ray from `o` is convex along `σ`,
  so is the ray exhaustion `rayExhaustion o`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology NNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry.Topology

variable {X : Type*} [MetricSpace X]

/-- **S-BUS kernel, general speed.** If `t ↦ a t² - d(c s, σ t)²` is convex on `D` for every
`s`, the Busemann function of the ray `c` is convex along `σ` on `D`. -/
theorem convexOn_busemann_comp_of_convexOn_mul_sq_sub_sq {c : ℝ≥0 → X} (hc : Isometry c)
    {σ : ℝ → X} {a : ℝ} {D : Set ℝ}
    (hσ : ∀ s : ℝ≥0, ConvexOn ℝ D (fun t => a * t ^ 2 - dist (c s) (σ t) ^ 2)) :
    ConvexOn ℝ D (fun t => busemann c (σ t)) := by
  let F : ℝ≥0 → ℝ → ℝ := fun s t =>
    (1 / 2 * (s : ℝ)⁻¹) * (a * t ^ 2 - dist (c s) (σ t) ^ 2 + (s : ℝ) ^ 2)
  have hF (s : ℝ≥0) : ConvexOn ℝ D (F s) :=
    ((hσ s).add_const ((s : ℝ) ^ 2)).smul (by positivity)
  have hlim (t : ℝ) : Tendsto (fun s => F s t) atTop (𝓝 (busemann c (σ t))) := by
    have hB := tendsto_busemannApprox hc (σ t)
    have hinv : Tendsto (fun s : ℝ≥0 => (s : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
    have hcorr := ((tendsto_const_nhds :
      Tendsto (fun _ : ℝ≥0 => a * t ^ 2) atTop (𝓝 (a * t ^ 2))).sub (hB.pow 2)).mul
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2))).mul hinv)
    have h := hB.add hcorr
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with s hs
    have hs' : (s : ℝ) ≠ 0 := ne_of_gt hs
    dsimp only [F, busemannApprox]
    rw [dist_comm (c s) (σ t)]
    field_simp
    ring
  refine ⟨(hσ 0).1, ?_⟩
  intro x hx y hy p q hp hq hpq
  exact le_of_tendsto_of_tendsto (hlim (p • x + q • y))
    (((hlim x).const_mul p).add ((hlim y).const_mul q))
    (Eventually.of_forall fun s => (hF s).2 hx hy hp hq hpq)

/-- **S-BUS kernel (frozen interface form).** If `t² - d(y, σ t)²` is convex for every point `y`
of the ray, the Busemann function of the ray is convex along `σ`. Supplier of the hypothesis for
a finite metric: CM-CHAIN's `convexOn_sq_sub_sq_dist_geodesicFlow_finite`. -/
theorem convexOn_busemann_comp_of_convexOn_sq_sub_sq
    {c : ℝ≥0 → X} (hc : Isometry c) {σ : ℝ → X}
    (hσ : ∀ s : ℝ≥0, ConvexOn ℝ univ (fun t => t ^ 2 - dist (c s) (σ t) ^ 2)) :
    ConvexOn ℝ univ (fun t => busemann c (σ t)) :=
  convexOn_busemann_comp_of_convexOn_mul_sq_sub_sq hc (a := 1)
    (fun s => (hσ s).congr fun t _ => by rw [one_mul])

/-- The ray exhaustion `rayExhaustion o` is convex along `σ` on `D` as soon as the Busemann
function of every ray from `o` is. -/
theorem convexOn_rayExhaustion_comp (o : X) {σ : ℝ → X} {D : Set ℝ} (hD : Convex ℝ D)
    (h : ∀ c : ℝ≥0 → X, Isometry c → c 0 = o → ConvexOn ℝ D (fun t => busemann c (σ t))) :
    ConvexOn ℝ D (fun t => rayExhaustion o (σ t)) := by
  refine ⟨hD, fun x hx y hy a b ha hb hab => ?_⟩
  have hR : 0 ≤ a • rayExhaustion o (σ x) + b • rayExhaustion o (σ y) :=
    add_nonneg (smul_nonneg ha (rayExhaustion_nonneg o _))
      (smul_nonneg hb (rayExhaustion_nonneg o _))
  refine (rayExhaustion_le_iff hR).2 fun c hc hc0 => ?_
  exact ((h c hc hc0).2 hx hy ha hb hab).trans
    (add_le_add (smul_le_smul_of_nonneg_left (busemann_le_rayExhaustion hc hc0 _) ha)
      (smul_le_smul_of_nonneg_left (busemann_le_rayExhaustion hc hc0 _) hb))

end DifferentialGeometry.Geometry.FiniteSoul
