import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.AffineHeightDifferential
import DifferentialGeometry.Geometry.Fibration.RiemannianDerivativeTools
import DifferentialGeometry.Geometry.Metric.Scaling

/-!
# BCG02's differential clause: the dual layer on the `g`-inner-product tangent space (lane BCG-7, G1)

Blueprint 207B, BCG02 (`B:8822–8958`): "`‖DU_b − A_bDη_a‖ < θ`. Differential norms use `R_a⁻²g`."
The covectors `DU_b` and `A_bDη_a` at a point `x` are continuous linear forms on the tangent space
`T_xM`, normed by the inner product `g_x` (for BCG02, `g = R_a⁻²g`). This module realizes that dual
on `T_xM` with the inner-product-space structure of the core of `g_x` (the topology of `T_xM` is kept,
so `mvfderiv` is a covector of it) and states everything back in the metric-free form
`|f u| ≤ C √(g_x(u, u))`, so no instance of the construction escapes.

* `exists_lt_abs_sub_le_of_slopes_BCG7`: BCG-4's saturation kernel `norm_sub_lt_of_slopes_BCG4`
  (FC15 with the budget `θ²/10⁵`) on `(T_xM, g_x)`: two covectors with `|f u|, |h u| ≤ (1 + δ₀)|u|_g`,
  within `δ₁`, `δ₂` of slopes `≥ 1 − δ₃` at one `g`-unit vector, `δ₀ + δ₁ + δ₂ + δ₃ ≤ θ²/10⁵`,
  `0 < θ < 1` ⟹ `∃ θ' < θ, ∀ u, |f u − h u| ≤ θ' |u|_g` (the operator norm in `g_x` is `< θ`);
* `sqrt_scaleMetric_inner_BCG7`: `|u|_{R⁻²g} = R⁻¹|u|_g`;
* `mvfderiv_affineHeight_BCG7`, `abs_mvfderiv_affineHeight_le_BCG7`: `U = (η − a)/R` has
  `DU = R⁻¹Dη`, and a bound `|Dη(u)| ≤ C|u|_g` becomes `|DU(u)| ≤ C|u|_{R⁻²g}`;
* `abs_row_apply_le_BCG7`, `abs_row_sub_div_le_BCG7`: a row `A : ℝᵐ → ℝ¹` of norm `≤ 1` turns the
  vector one-vector test `‖Dη(w) − ℓ⁻¹(ψ(z) − ψ(x))‖ < γ` (the circle `test` field) into the real
  test of the covector `A_bDη_a`, and bounds `|A_bDη_a(u)| ≤ ‖Dη(u)‖`;
* `abs_sign_sub_div_le_BCG7`: the same for a sign `a = ±1` and a real coordinate (edge, slim);
* `norm_mvfderiv_le_of_lipschitz_rescale_BCG7`: a map `R⁻¹d`-Lipschitz with constant `L` on an open
  set has `‖Df(u)‖ ≤ L|u|_{R⁻²g}` (the reference norms from the adapted Lipschitz fields);
* consumer `bcg02_covector_comparison_BCG7`: the comparison of `DU` (`U = (η − a)/R` with a norm bound
  `|Dη(u)| ≤ (1 + δ₀)|u|_g`) with a real covector in the `R⁻²g` normalization.
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Dual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **BCG02's saturation kernel on the `g`-inner-product tangent space.** Two covectors `f, h` of
`T_xM` with `|f u|, |h u| ≤ (1 + δ₀)|u|_g`, within `δ₁`, `δ₂` of slopes `s₁, s₂ ≥ 1 − δ₃` at one
`g`-unit vector `v`, with `δ₀ + δ₁ + δ₂ + δ₃ ≤ θ²/10⁵` and `0 < θ < 1`, differ by less than `θ` in the
dual norm of `g_x`: `|f u − h u| ≤ θ' |u|_g` for some `θ' < θ`. -/
theorem exists_lt_abs_sub_le_of_slopes_BCG7 (g : SmoothRiemannianMetric I M) (x : M)
    (f h : TangentSpace I x →L[ℝ] ℝ) {θ δ₀ δ₁ δ₂ δ₃ s₁ s₂ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁) (h2 : 0 ≤ δ₂) (h3 : 0 ≤ δ₃)
    (hbud : δ₀ + δ₁ + δ₂ + δ₃ ≤ θ ^ 2 / 100000)
    (hf : ∀ u : TangentSpace I x, |f u| ≤ (1 + δ₀) * Real.sqrt (g.inner x u u))
    (hh : ∀ u : TangentSpace I x, |h u| ≤ (1 + δ₀) * Real.sqrt (g.inner x u u))
    (v : TangentSpace I x) (hv : g.inner x v v = 1) (hfs : |f v - s₁| ≤ δ₁)
    (hhs : |h v - s₂| ≤ δ₂) (hs₁ : 1 - δ₃ ≤ s₁) (hs₂ : 1 - δ₃ ≤ s₂) :
    ∃ θ' < θ, ∀ u : TangentSpace I x, |f u - h u| ≤ θ' * Real.sqrt (g.inner x u u) := by
  let K : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hKcont : ContinuousAt (fun v : TangentSpace I x => K.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hKbounded : Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | RCLike.re (K.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  let _ : NormedAddCommGroup (TangentSpace I x) :=
    K.toNormedAddCommGroupOfTopology hKcont hKbounded
  let _ : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology K hKcont hKbounded
  have _ : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have _ : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  have hinner (v w : TangentSpace I x) : inner ℝ v w = g.inner x v w := rfl
  have hnorm (v : TangentSpace I x) : ‖v‖ = Real.sqrt (g.inner x v v) := by
    rw [norm_eq_sqrt_real_inner, hinner]
  have hfn : ‖f‖ ≤ 1 + δ₀ := ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun u => by
    rw [Real.norm_eq_abs, hnorm]
    exact hf u
  have hhn : ‖h‖ ≤ 1 + δ₀ := ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun u => by
    rw [Real.norm_eq_abs, hnorm]
    exact hh u
  have hv1 : ‖v‖ = 1 := by rw [hnorm, hv, Real.sqrt_one]
  have hlt := norm_sub_lt_of_slopes_BCG4 f h hθ hθ1 h0 h1 h2 h3 hbud hfn hhn v hv1 hfs hhs hs₁ hs₂
  refine ⟨‖f - h‖, hlt, fun u => ?_⟩
  have hle := (f - h).le_opNorm u
  rw [Real.norm_eq_abs, hnorm, sub_apply] at hle
  exact hle

omit [FiniteDimensional ℝ E] in
/-- **The `R⁻²g` normalization**: `|u|_{R⁻²g} = R⁻¹|u|_g`. -/
theorem sqrt_scaleMetric_inner_BCG7 (g : SmoothRiemannianMetric I M) {R : ℝ} (hR : 0 < R)
    (x : M) (u : TangentSpace I x) :
    Real.sqrt ((scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g).inner x u u) =
      R⁻¹ * Real.sqrt (g.inner x u u) := by
  rw [scaleMetric_inner, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.mpr hR).le]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- **The differential of an affine height** `U = (η − a)/R`: `DU = R⁻¹Dη`. -/
theorem mvfderiv_affineHeight_BCG7 {η : M → ℝ} {x : M}
    (hη : MDifferentiableAt I 𝓘(ℝ, ℝ) η x) (a R : ℝ) (u : TangentSpace I x) :
    mvfderiv I (fun y => (η y - a) / R) x u = R⁻¹ * mvfderiv I η x u := by
  have hφ : HasDerivAt (fun t : ℝ => (t - a) / R) (1 / R) (η x) :=
    ((hasDerivAt_id (η x)).sub_const a).div_const R
  rw [mvfderiv_comp_hasDerivAt hη hφ u, one_div]

omit [FiniteDimensional ℝ E] in
/-- **Norm bounds in the `R⁻²g` normalization**: `|Dη(u)| ≤ C|u|_g` for all `u` gives
`|DU(u)| ≤ C|u|_{R⁻²g}` for `U = (η − a)/R`. -/
theorem abs_mvfderiv_affineHeight_le_BCG7 (g : SmoothRiemannianMetric I M) {η : M → ℝ} {x : M}
    (hη : MDifferentiableAt I 𝓘(ℝ, ℝ) η x) (a : ℝ) {R C : ℝ} (hR : 0 < R)
    (hC : ∀ u : TangentSpace I x, |mvfderiv I η x u| ≤ C * Real.sqrt (g.inner x u u))
    (u : TangentSpace I x) :
    |mvfderiv I (fun y => (η y - a) / R) x u| ≤
      C * Real.sqrt ((scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g).inner x u u) := by
  rw [mvfderiv_affineHeight_BCG7 hη a R u, sqrt_scaleMetric_inner_BCG7 g hR x u, abs_mul,
    abs_of_pos (inv_pos.mpr hR)]
  have hRi : 0 < R⁻¹ := inv_pos.mpr hR
  calc R⁻¹ * |mvfderiv I η x u| ≤ R⁻¹ * (C * Real.sqrt (g.inner x u u)) :=
        mul_le_mul_of_nonneg_left (hC u) hRi.le
    _ = C * (R⁻¹ * Real.sqrt (g.inner x u u)) := by ring

end Dual

section Row

/-- A row `A : ℝᵐ → ℝ¹` of norm `≤ 1`: `|(A v)₀| ≤ ‖v‖`. -/
theorem abs_row_apply_le_BCG7 {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 1)) (hA : ‖A‖ ≤ 1)
    (v : EuclideanSpace ℝ (Fin m)) : |A v 0| ≤ ‖v‖ := by
  have h0 : ‖A v 0‖ ≤ ‖A v‖ := PiLp.norm_apply_le (A v) 0
  rw [Real.norm_eq_abs] at h0
  calc |A v 0| ≤ ‖A v‖ := h0
    _ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg v)
    _ = ‖v‖ := one_mul _

/-- **The row form of the one-vector test**: for a row `A` of norm `≤ 1`,
`|(A d)₀ − ((A q)₀ − (A p)₀)/ℓ| ≤ ‖d − ℓ⁻¹(q − p)‖`. With `d = Dη_a(w)` and `p, q` the reference
splitting values at the endpoints this is the test of the covector `A_bDη_a`. -/
theorem abs_row_sub_div_le_BCG7 {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 1)) (hA : ‖A‖ ≤ 1)
    (d p q : EuclideanSpace ℝ (Fin m)) (ℓ : ℝ) :
    |A d 0 - (A q 0 - A p 0) / ℓ| ≤ ‖d - ℓ⁻¹ • (q - p)‖ := by
  have he : A d 0 - (A q 0 - A p 0) / ℓ = A (d - ℓ⁻¹ • (q - p)) 0 := by
    simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact abs_row_apply_le_BCG7 A hA _

/-- **The sign form of the one-vector test** (edge and slim references): for `a = ±1`,
`|a d − (a q − a p)/ℓ| = |d − (q − p)/ℓ|`. -/
theorem abs_sign_sub_div_le_BCG7 {a : ℝ} (ha : a = 1 ∨ a = -1) (d p q ℓ : ℝ) :
    |a * d - (a * q - a * p) / ℓ| = |d - (q - p) / ℓ| := by
  have he : a * d - (a * q - a * p) / ℓ = a * (d - (q - p) / ℓ) := by ring
  rw [he, abs_mul]
  rcases ha with rfl | rfl <;> simp

end Row

section Lipschitz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompleteSpace M]
  [SigmaCompactSpace M]

/-- **Reference norms in the `R⁻²g` normalization from a rescaled Lipschitz bound.** If
`‖f y − f z‖ ≤ L R⁻¹ d(y, z)` on an open set `U ∋ x` (i.e. `f` is `L`-Lipschitz for `R⁻¹d`) and `f`
is differentiable at `x`, then `‖Df(u)‖ ≤ L|u|_{R⁻²g}`. -/
theorem norm_mvfderiv_le_of_lipschitz_rescale_BCG7 {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {f : M → F}
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) (hf : MDifferentiableAt I 𝓘(ℝ, F) f x)
    {L R : ℝ} (hL : 0 ≤ L) (hR : 0 < R)
    (hlip : ∀ y ∈ U, ∀ z ∈ U, ‖f y - f z‖ ≤ L * (R⁻¹ * dist y z)) (u : TangentSpace I x) :
    ‖mvfderiv I f x u‖ ≤
      L * Real.sqrt ((scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g).inner x u u) := by
  have hRi : 0 < R⁻¹ := inv_pos.mpr hR
  have h := norm_mvfderiv_le_of_lipschitzOn_riem g hmetric hU hx hf (L := L * R⁻¹)
    (mul_nonneg hL hRi.le) (fun y hy z hz => by
      calc ‖f y - f z‖ ≤ L * (R⁻¹ * dist y z) := hlip y hy z hz
        _ = L * R⁻¹ * dist y z := by ring) u
  rw [sqrt_scaleMetric_inner_BCG7 g hR x u]
  calc ‖mvfderiv I f x u‖ ≤ L * R⁻¹ * Real.sqrt (g.inner x u u) := h
    _ = L * (R⁻¹ * Real.sqrt (g.inner x u u)) := by ring

end Lipschitz

section Consumer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Consumer: BCG02's differential comparison in the `R⁻²g` normalization.** For an affine height
`U = (η − a)/R` with `|Dη(u)| ≤ (1 + δ₀)|u|_g` and a real covector `h` with
`|h u| ≤ (1 + δ₀)|u|_{R⁻²g}`, if `DU` and `h` are within `δ₁`, `δ₂` of slopes `≥ 1 − δ₃` at one
`R⁻²g`-unit vector `v` and `δ₀ + δ₁ + δ₂ + δ₃ ≤ θ²/10⁵`, then `‖DU − h‖_{R⁻²g} < θ`. -/
theorem bcg02_covector_comparison_BCG7 (g : SmoothRiemannianMetric I M) {η : M → ℝ} {x : M}
    (hη : MDifferentiableAt I 𝓘(ℝ, ℝ) η x) (a : ℝ) {R : ℝ} (hR : 0 < R)
    (h : TangentSpace I x →L[ℝ] ℝ) {θ δ₀ δ₁ δ₂ δ₃ s₁ s₂ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁) (h2 : 0 ≤ δ₂) (h3 : 0 ≤ δ₃)
    (hbud : δ₀ + δ₁ + δ₂ + δ₃ ≤ θ ^ 2 / 100000)
    (hηn : ∀ u : TangentSpace I x, |mvfderiv I η x u| ≤ (1 + δ₀) * Real.sqrt (g.inner x u u))
    (hhn : ∀ u : TangentSpace I x, |h u| ≤
      (1 + δ₀) * Real.sqrt ((scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g).inner x u u))
    (v : TangentSpace I x)
    (hv : (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g).inner x v v = 1)
    (hfs : |mvfderiv I (fun y => (η y - a) / R) x v - s₁| ≤ δ₁) (hhs : |h v - s₂| ≤ δ₂)
    (hs₁ : 1 - δ₃ ≤ s₁) (hs₂ : 1 - δ₃ ≤ s₂) :
    ∃ θ' < θ, ∀ u : TangentSpace I x, |mvfderiv I (fun y => (η y - a) / R) x u - h u| ≤
      θ' * Real.sqrt ((scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g).inner x u u) :=
  exists_lt_abs_sub_le_of_slopes_BCG7 (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g) x
    (mvfderiv I (fun y => (η y - a) / R) x) h hθ hθ1 h0 h1 h2 h3 hbud
    (abs_mvfderiv_affineHeight_le_BCG7 g hη a hR hηn) hhn v hv hfs hhs hs₁ hs₂

end Consumer

end DifferentialGeometry.Geometry.Collapse
