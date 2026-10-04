import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound
import DifferentialGeometry.Geometry.Metric.Distance.Ball

/-!
# The curvature scale of the finite zero packet (first step of LFR49)

Frozen blueprint master207A, theorem `thm:collapse-finite-joint-zero-packet` (LFR49, lines
29096–29218), first paragraph of the proof: the supplied bounds `sec_{g_i} ≥ -ε_i` on the
`L_i`-balls are put in LC57's form by `H_i = min {L_i, ε_i^{-1/2}}` (the second entry read as
infinity when `ε_i = 0`). Then `H_i → ∞` and `sec_{g_i} ≥ -H_i⁻²` on the `H_i`-ball. This uses the
separate supplied curvature bounds only.

* `exists_curvature_scale_of_tendsto`: the scalar kernel;
* `exists_curvature_scale_of_ball_lower_bounds`: the binding to actual smooth Riemannian
  manifolds (`SectionalBoundedBelowAt` on `riemannianBallOf`).
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

/-- The scale `H = L` if `ε = 0`, and `H = min {L, ε^{-1/2}}` otherwise. -/
def curvatureScale (L ε : ℝ) : ℝ :=
  if ε = 0 then L else min L (Real.sqrt ε)⁻¹

theorem curvatureScale_le (L ε : ℝ) : curvatureScale L ε ≤ L := by
  unfold curvatureScale
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- On a positive scale the supplied lower bound `-ε` dominates `-H⁻²`. -/
theorem le_inv_sq_curvatureScale {L ε : ℝ} (hε : 0 ≤ ε) (hH : 0 < curvatureScale L ε) :
    ε ≤ (curvatureScale L ε ^ 2)⁻¹ := by
  unfold curvatureScale at hH ⊢
  split_ifs with h0
  · rw [h0]
    positivity
  · simp only [h0, ↓reduceIte] at hH
    have hεpos : 0 < ε := lt_of_le_of_ne hε (Ne.symm h0)
    have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hεpos
    have hle : min L (Real.sqrt ε)⁻¹ ≤ (Real.sqrt ε)⁻¹ := min_le_right _ _
    have hsq : min L (Real.sqrt ε)⁻¹ ^ 2 ≤ ((Real.sqrt ε)⁻¹) ^ 2 :=
      pow_le_pow_left₀ hH.le hle 2
    have hinv : ((Real.sqrt ε)⁻¹) ^ 2 = ε⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hε]
    rw [hinv] at hsq
    calc ε = (ε⁻¹)⁻¹ := (inv_inv ε).symm
      _ ≤ (min L (Real.sqrt ε)⁻¹ ^ 2)⁻¹ := inv_anti₀ (pow_pos hH 2) hsq

/-- **LFR49, scalar kernel.** `L → ∞` and `0 ≤ ε → 0` give `H = curvatureScale L ε → ∞`, with
`H ≤ L` and `ε ≤ H⁻²` wherever `H > 0`. -/
theorem exists_curvature_scale_of_tendsto {L ε : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hε0 : ∀ i, 0 ≤ ε i) (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ Hs : ℕ → ℝ, Tendsto Hs atTop atTop ∧ (∀ i, Hs i ≤ L i) ∧
      ∀ i, 0 < Hs i → ε i ≤ (Hs i ^ 2)⁻¹ := by
  refine ⟨fun i => curvatureScale (L i) (ε i), ?_, fun i => curvatureScale_le _ _,
    fun i hi => le_inv_sq_curvatureScale (hε0 i) hi⟩
  rw [tendsto_atTop]
  intro b
  set K : ℝ := max b 1 with hK
  have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_right b 1)
  have hsmall : ∀ᶠ i in atTop, ε i < (K ^ 2)⁻¹ :=
    hε (gt_mem_nhds (inv_pos.mpr (pow_pos hKpos 2)))
  filter_upwards [tendsto_atTop.mp hL K, hsmall] with i hLi hεi
  refine le_trans (le_max_left b 1) ?_
  change K ≤ curvatureScale (L i) (ε i)
  unfold curvatureScale
  split_ifs with h0
  · exact hLi
  · refine le_min hLi ?_
    have hεpos : 0 < ε i := lt_of_le_of_ne (hε0 i) (Ne.symm h0)
    have hs : 0 < Real.sqrt (ε i) := Real.sqrt_pos.mpr hεpos
    have hsK : Real.sqrt (ε i) < K⁻¹ := by
      rw [show K⁻¹ = Real.sqrt ((K ^ 2)⁻¹) by
        rw [Real.sqrt_inv, Real.sqrt_sq hKpos.le]]
      exact Real.sqrt_lt_sqrt (hε0 i) hεi
    rw [le_inv_comm₀ hKpos hs]
    exact hsK.le

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)]

/-- **LFR49, curvature scale (binding).** Supplied bounds `sec_{g_i} ≥ -ε_i` on the balls
`B(p_i, L_i)`, with `L_i → ∞` and `0 ≤ ε_i → 0`, give scales `H_i → ∞`, `H_i ≤ L_i`, with
`sec_{g_i} ≥ -H_i⁻²` on `B(p_i, H_i)` (LC57's form). -/
theorem exists_curvature_scale_of_ball_lower_bounds (g : ∀ i, SmoothRiemannianMetric I (X i))
    (p : ∀ i, X i) {L ε : ℕ → ℝ} (hL : Tendsto L atTop atTop) (hε0 : ∀ i, 0 ≤ ε i)
    (hε : Tendsto ε atTop (𝓝 0))
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      Riemannian.SectionalBoundedBelowAt (g i) y (-ε i)) :
    ∃ Hs : ℕ → ℝ, Tendsto Hs atTop atTop ∧ (∀ i, Hs i ≤ L i) ∧
      ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (Hs i),
        Riemannian.SectionalBoundedBelowAt (g i) y (-(Hs i ^ 2)⁻¹) := by
  obtain ⟨Hs, hHs, hHL, hHε⟩ := exists_curvature_scale_of_tendsto hL hε0 hε
  refine ⟨Hs, hHs, hHL, fun i y hy => ?_⟩
  by_cases hpos : 0 < Hs i
  · exact (hsec i y (riemannianBallOf_mono (g i) (p i) (hHL i) hy)).mono
      (neg_le_neg (hHε i hpos))
  · exfalso
    have hy' : riemannianEDistOf (I := I) (g i) (p i) y < ENNReal.ofReal (Hs i) := hy
    rw [ENNReal.ofReal_of_nonpos (not_lt.mp hpos)] at hy'
    exact ENNReal.not_lt_zero hy'

end DifferentialGeometry.Geometry.Collapse
