import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottConvergence
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleGeometry

set_option autoImplicit false
open Filter

namespace GC.MetricGeometry.PointedGHConverges

universe u v w
variable {X : ℕ → Type u} [mX : ∀ n, MetricSpace (X n)]
variable {Y : Type v} [mY : MetricSpace Y] {p : ∀ n, X n} {q : Y}

theorem rescale (h : PointedGHConverges p q) (c : ℝ) (hc : 0 < c) :
    @PointedGHConverges X (fun n => (mX n).rescale c hc) Y (mY.rescale c hc) p q := by
  refine ⟨(mY.rescale_completeSpace_iff c hc).mpr h.complete_space, ?_⟩
  intro R ε hε hεR
  have he : 0 < ε / c := div_pos hε hc
  have heR : ε / c < R / c := (div_lt_div_iff_of_pos_right hc).mpr hεR
  filter_upwards [h.eventually_approx he heR] with n hn
  obtain ⟨f⟩ := hn
  have g := f.rescale c hc ((mX n).rescale c hc) (mY.rescale c hc)
    (fun _ _ => rfl) (fun _ _ => rfl)
  simpa only [mul_div_cancel₀ _ hc.ne'] using Nonempty.intro g

theorem eventually_approx_fixed_target (h : PointedGHConverges p q)
    {C : Type w} [MetricSpace C] {o : C} {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1)
    (g : KleinerLottApprox q o (min (δ / 100) (1 / (2 * (2 * (δ⁻¹ + δ) + 4))))) :
    ∀ᶠ n in atTop, Nonempty (KleinerLottApprox (p n) o δ) := by
  let U := δ⁻¹ + δ
  let S := 2 * U + 4
  let ε := min (δ / 100) (1 / (2 * S))
  have hU : 0 < U := by dsimp [U]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hε : 0 < ε := g.error_pos
  have hεsmall : ε ≤ δ / 100 := min_le_left _ _
  have hεS : ε * (2 * S) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2 * S)).mp (min_le_right _ _)
  have hSinv : S < ε⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ hε).mpr
    nlinarith [mul_pos hε hS]
  have h3 : 3 * ε < S := by dsimp [S]; linarith
  have hεR : ε < S := by linarith
  filter_upwards [h.eventually_approx hε hεR] with n hn
  obtain ⟨f⟩ := hn
  have h8 : 2 * (ε + 3 * ε) < U := by
    dsimp [U]
    linarith [inv_pos.mpr hδ]
  have hUS : U ≤ S := by dsimp [S]; linarith
  have hUεS : U + ε ≤ S := by dsimp [S]; linarith
  have k := f.comp (g.toClosedBall h3 hSinv) h8 hUS hUεS
  have heδ : 2 * (ε + 3 * ε) ≤ δ / 4 := by linarith
  have hδU : δ / 4 < U := by dsimp [U]; linarith [inv_pos.mpr hδ]
  exact ⟨(k.enlargeError heδ hδU).toKleinerLott hδ hδone⟩

theorem eventually_rescaled_approx_fixed_target (h : PointedGHConverges p q)
    (R : ℝ) (hR : 0 < R) {C : Type w} [MetricSpace C] {o : C} {δ : ℝ}
    (hδ : 0 < δ) (hδone : δ < 1)
    (g : @KleinerLottApprox Y C (mY.rescale R⁻¹ (inv_pos.mpr hR)) _ q o
      (min (δ / 100) (1 / (2 * (2 * (δ⁻¹ + δ) + 4))))) :
    ∀ᶠ n in atTop, Nonempty (@KleinerLottApprox (X n) C
      ((mX n).rescale R⁻¹ (inv_pos.mpr hR)) _ (p n) o δ) :=
  @eventually_approx_fixed_target X (fun n => (mX n).rescale R⁻¹ (inv_pos.mpr hR))
    Y (mY.rescale R⁻¹ (inv_pos.mpr hR)) p q (h.rescale R⁻¹ (inv_pos.mpr hR))
    C _ o δ hδ hδone g

end GC.MetricGeometry.PointedGHConverges
