import DifferentialGeometry.Geometry.Collapse.MetricRank.ThinOnlyRank
import DifferentialGeometry.Geometry.Metric.L2Product

/-!
# A thin plane chart is a Kleiner-Lott approximation (S-FIXTURE-C1, K1, file 5)

Generic metric-space lemma used by the lattice torus (and reusable by other thin-fibre fixtures):
if a map `ell : X → A` into a normed space satisfies, on the ball `B(p, Rδ⁻¹)`,
`‖ell q - ell q'‖ ≤ d(q, q') ≤ ‖ell q - ell q'‖ + D` with `D ≤ Rδ`, `ell p = 0`, and every
`u` with `‖u‖ < Rδ⁻¹` is a value of `ell` on that ball, then `R⁻¹ ell` is a Kleiner-Lott
`δ`-approximation of the rescaled metric `R⁻¹ d` into `A ×₂ PUnit` at `p ↦ (0, ★)`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace GC.MetricGeometry

theorem prod_punit_dist_FXC1 {A : Type*} [NormedAddCommGroup A] (a b : WithLp 2 (A × PUnit.{1})) :
    dist a b = ‖a.fst - b.fst‖ := by
  have h := WithLp.prod_dist_sq_eq_add_sq a b
  have h0 : dist a.snd b.snd = 0 := dist_eq_zero.mpr (Subsingleton.elim _ _)
  have h1 : dist a.fst b.fst = ‖a.fst - b.fst‖ := dist_eq_norm _ _
  rw [h0, h1] at h
  have h2 : dist a b ^ 2 = ‖a.fst - b.fst‖ ^ 2 := by rw [h]; ring
  exact (sq_eq_sq₀ dist_nonneg (norm_nonneg _)).mp h2

/-- **A thin chart is a Kleiner-Lott approximation** into `A ×₂ PUnit` of the rescaled metric. -/
def kleinerLott_of_thin_chart_FXC1 {X : Type*} [m : MetricSpace X] {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] {p : X} {R δ D : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hδ1 : δ < 1) (ell : X → A) (hp : ell p = 0)
    (hdist : ∀ q ∈ ball p (R * δ⁻¹), ∀ q' ∈ ball p (R * δ⁻¹),
      ‖ell q - ell q'‖ ≤ dist q q' ∧ dist q q' ≤ ‖ell q - ell q'‖ + D)
    (hD : D ≤ R * δ)
    (hcov : ∀ u : A, ‖u‖ < R * δ⁻¹ → ∃ q ∈ ball p (R * δ⁻¹), ell q = u) :
    @KleinerLottApprox X (WithLp 2 (A × PUnit.{1})) (m.rescale R⁻¹ (inv_pos.mpr hR)) _ p
      (WithLp.toLp 2 ((0 : A), PUnit.unit)) δ := by
  have hRi := inv_pos.mpr hR
  have hball : ∀ x : X, R⁻¹ * dist x p < δ⁻¹ → x ∈ ball p (R * δ⁻¹) := by
    intro x hx
    rw [mem_ball]
    rwa [inv_mul_lt_iff₀ hR] at hx
  refine @KleinerLottApprox.mk X (WithLp 2 (A × PUnit.{1})) (m.rescale R⁻¹ hRi) _ p _ δ hδ hδ1
    (fun x => WithLp.toLp 2 (R⁻¹ • ell x, PUnit.unit)) ?_ ?_ ?_
  · simp [hp]
  · intro x hx x' hx'
    have h := hdist x (hball x hx) x' (hball x' hx')
    rw [prod_punit_dist_FXC1]
    simp only [WithLp.toLp_fst]
    change |‖R⁻¹ • ell x - R⁻¹ • ell x'‖ - R⁻¹ * dist x x'| ≤ δ
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hRi, ← mul_sub, abs_mul,
      abs_of_pos hRi]
    have h3 : |‖ell x - ell x'‖ - dist x x'| ≤ D := by
      rw [abs_le]; constructor <;> linarith [h.1, h.2]
    calc R⁻¹ * |‖ell x - ell x'‖ - dist x x'| ≤ R⁻¹ * (R * δ) :=
          mul_le_mul_of_nonneg_left (h3.trans hD) hRi.le
      _ = δ := by field_simp
  · intro y hy
    have hy1 : ‖y.fst‖ < δ⁻¹ - δ := by
      have h : dist y (WithLp.toLp 2 ((0 : A), PUnit.unit)) = ‖y.fst‖ := by
        rw [prod_punit_dist_FXC1]
        simp
      rw [← h]
      exact hy
    obtain ⟨q, hq, hqy⟩ := hcov (R • y.fst) (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
      exact mul_lt_mul_of_pos_left (by linarith) hR)
    have hq' : q ∈ @ball X (m.rescale R⁻¹ hRi).toPseudoMetricSpace p δ⁻¹ := by
      have hq2 : dist q p < R * δ⁻¹ := hq
      change R⁻¹ * dist q p < δ⁻¹
      rwa [inv_mul_lt_iff₀ hR]
    have himg : y ∈ (fun x => (WithLp.toLp 2 (R⁻¹ • ell x, PUnit.unit) :
        WithLp 2 (A × PUnit.{1}))) '' @ball X (m.rescale R⁻¹ hRi).toPseudoMetricSpace p δ⁻¹ := by
      refine ⟨q, hq', ?_⟩
      change (WithLp.toLp 2 (R⁻¹ • ell q, PUnit.unit) : WithLp 2 (A × PUnit.{1})) = y
      rw [hqy, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
      rfl
    rw [Metric.infDist_zero_of_mem himg]
    exact hδ.le

end GC.MetricGeometry
