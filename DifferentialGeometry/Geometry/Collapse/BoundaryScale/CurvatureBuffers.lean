import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusBounds
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls

/-!
# Curvature-scale buffers from sectional bounds (BSA01 and BCP05.a kernels)

Blueprint 207B, BSA01 (`B:7591`) and BCP05 (`B:8617`). In the nearly cuspidal collars the
sectional curvature lies in `[-1/2, -1/8]`. The curvature-scale consequences are elementary and
hold on every smooth manifold, with or without boundary:
* a lower bound `sec ≥ -1` on the unit ball gives `1 ≤ R_p`;
* one plane at a point `q` with `sec ≤ -κ` and `(s²)⁻¹ < κ`, `d(p, q) ≤ s`, gives `R_p ≤ s`;
* hence `R_p < 3` at a point carrying a plane with `sec ≤ -1/8`, and `R_p ≤ D + 3` when such a
  point lies within `D + 1.01` (BSA01.c), in particular `R_p < ∞`;
* BCP05.a: a zero ball `B(z, R⁰)` with `R⁰ ≤ V ρ`, `n ρ < R_z`, `V < n` cannot contain a point with
  a plane of curvature `≤ -1/8` unless `R_z < 3`, `ρ < 3/n` and `R⁰ < 3V/n`.
Only ONE negative plane is assumed (the blueprint has the full upper bound `sec ≤ -1/8`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- BSA01: the sectional lower bound `-1` on the unit ball gives curvature scale at least `1`. -/
theorem one_le_curvatureRadius_of_sectional_ball (g : SmoothRiemannianMetric I M) (p : M)
    (hsec : ∀ q ∈ riemannianBallOf g p 1, SectionalBoundedBelowAt g q (-1)) :
    1 ≤ curvatureRadius g p := by
  have h := ofReal_le_curvatureRadius g (p := p) (r := 1) one_pos (by
    intro q hq
    simpa only [one_pow, inv_one] using hsec q hq)
  rwa [ENNReal.ofReal_one] at h

/-- One plane at `q` with sectional curvature at most `-κ`, `(s²)⁻¹ < κ`, bounds the curvature
scale of every point within `s` of `q`. -/
theorem curvatureRadius_le_of_negative_plane (g : SmoothRiemannianMetric I M) {p q : M}
    {s κ : ℝ} (hs : 0 < s) (hq : riemannianEDistOf g p q ≤ ENNReal.ofReal s)
    (v w : TangentSpace I q)
    (hgram : 0 < g.inner q v v * g.inner q w w - g.inner q v w ^ 2)
    (hκ : (s ^ 2)⁻¹ < κ)
    (hneg : metricRm04StandardAt g q v w w v ≤
      -κ * (g.inner q v v * g.inner q w w - g.inner q v w ^ 2)) :
    curvatureRadius g p ≤ ENNReal.ofReal s := by
  apply curvatureRadius_le_of_not_sectionalBoundedBelowAt g hs hq
  intro hsec
  have h := hsec v w
  nlinarith

/-- BSA01.b, upper half: a plane with sectional curvature at most `-1/8` at `p` gives `R_p < 3`. -/
theorem curvatureRadius_lt_three_of_negative_plane (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p)
    (hgram : 0 < g.inner p v v * g.inner p w w - g.inner p v w ^ 2)
    (hneg : metricRm04StandardAt g p v w w v ≤
      -(1 / 8) * (g.inner p v v * g.inner p w w - g.inner p v w ^ 2)) :
    curvatureRadius g p < 3 := by
  have h := curvatureRadius_le_of_negative_plane g (p := p) (s := 29 / 10) (by norm_num)
    (by rw [riemannianEDistOf_self]; exact zero_le) v w hgram (by norm_num) hneg
  refine h.trans_lt ?_
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- BSA01.c: a point within `D + 1.01` carrying a plane with sectional curvature at most `-1/8`
gives `R_p ≤ D + 3`. -/
theorem curvatureRadius_le_add_three_of_negative_plane (g : SmoothRiemannianMetric I M)
    {p q : M} {D : ℝ} (hD : 0 ≤ D)
    (hq : riemannianEDistOf g p q ≤ ENNReal.ofReal (D + 101 / 100))
    (v w : TangentSpace I q)
    (hgram : 0 < g.inner q v v * g.inner q w w - g.inner q v w ^ 2)
    (hneg : metricRm04StandardAt g q v w w v ≤
      -(1 / 8) * (g.inner q v v * g.inner q w w - g.inner q v w ^ 2)) :
    curvatureRadius g p ≤ ENNReal.ofReal (D + 3) := by
  have hs : (0 : ℝ) < D + 3 := by linarith
  apply curvatureRadius_le_of_negative_plane g hs
    (hq.trans (ENNReal.ofReal_le_ofReal (by linarith))) v w hgram _ hneg
  have h9 : (9 : ℝ) ≤ (D + 3) ^ 2 := by nlinarith
  calc ((D + 3) ^ 2)⁻¹ ≤ (9 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h9
    _ < 1 / 8 := by norm_num

/-- BSA01.c: such a point makes the curvature scale finite. -/
theorem curvatureRadius_ne_top_of_negative_plane (g : SmoothRiemannianMetric I M)
    {p q : M} {D : ℝ} (hD : 0 ≤ D)
    (hq : riemannianEDistOf g p q ≤ ENNReal.ofReal (D + 101 / 100))
    (v w : TangentSpace I q)
    (hgram : 0 < g.inner q v v * g.inner q w w - g.inner q v w ^ 2)
    (hneg : metricRm04StandardAt g q v w w v ≤
      -(1 / 8) * (g.inner q v v * g.inner q w w - g.inner q v w ^ 2)) :
    curvatureRadius g p ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (curvatureRadius_le_add_three_of_negative_plane g hD hq v w hgram hneg)

/-- BCP05.a: a ball `B(z, R⁰)` with `R⁰ ≤ V ρ`, `n ρ < R_z` and `V < n` that contains a point with
a plane of sectional curvature at most `-1/8` forces `R_z < 3`, `ρ < 3/n` and `R⁰ < 3V/n`. -/
theorem zeroBall_small_of_negative_plane (g : SmoothRiemannianMetric I M) {z x : M}
    {R₀ V ρ n : ℝ} (hx : x ∈ riemannianBallOf g z R₀) (hR₀ : R₀ ≤ V * ρ) (hρ : 0 < ρ)
    (hVn : V < n) (hscale : ENNReal.ofReal (n * ρ) < curvatureRadius g z)
    (v w : TangentSpace I x)
    (hgram : 0 < g.inner x v v * g.inner x w w - g.inner x v w ^ 2)
    (hneg : metricRm04StandardAt g x v w w v ≤
      -(1 / 8) * (g.inner x v v * g.inner x w w - g.inner x v w ^ 2)) :
    curvatureRadius g z < 3 ∧ ρ < 3 / n ∧ R₀ < 3 * V / n := by
  have hR₀pos : 0 < R₀ := by
    have h : riemannianEDistOf g z x < ENNReal.ofReal R₀ := hx
    exact ENNReal.ofReal_pos.mp (zero_le.trans_lt h)
  have hVpos : 0 < V := pos_of_mul_pos_left (hR₀pos.trans_le hR₀) hρ.le
  have hn : 0 < n := hVpos.trans hVn
  set s := max (V * ρ) (29 / 10) with hsdef
  have hs : 0 < s := lt_max_of_lt_right (by norm_num)
  have hzx : riemannianEDistOf g z x ≤ ENNReal.ofReal s :=
    (le_of_lt hx).trans (ENNReal.ofReal_le_ofReal (hR₀.trans (le_max_left _ _)))
  have hκ : (s ^ 2)⁻¹ < 1 / 8 := by
    have h : (29 / 10 : ℝ) ^ 2 ≤ s ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (le_max_right _ _) 2
    calc (s ^ 2)⁻¹ ≤ ((29 / 10 : ℝ) ^ 2)⁻¹ := inv_anti₀ (by norm_num) h
      _ < 1 / 8 := by norm_num
  have hR := curvatureRadius_le_of_negative_plane g hs hzx v w hgram hκ hneg
  have hns : n * ρ < s :=
    (ENNReal.ofReal_lt_ofReal_iff hs).mp (hscale.trans_le hR)
  have hVρ : V * ρ < n * ρ := mul_lt_mul_of_pos_right hVn hρ
  have hs29 : s = 29 / 10 := by
    rcases max_choice (V * ρ) (29 / 10) with h | h
    · rw [hsdef, h] at hns
      exact absurd hns (not_lt.mpr hVρ.le)
    · exact h
  rw [hs29] at hR hns
  refine ⟨hR.trans_lt ?_, ?_, ?_⟩
  · rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  · rw [lt_div_iff₀ hn]
    linarith
  · rw [lt_div_iff₀ hn]
    nlinarith

end DifferentialGeometry.Geometry.Collapse
