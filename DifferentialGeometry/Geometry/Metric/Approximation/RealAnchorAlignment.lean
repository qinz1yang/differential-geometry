import DifferentialGeometry.Geometry.Metric.Approximation.DirectedSplittingCompatibility
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Euclidean anchor alignment in dimension one and the raw alignment of a rank-one splitting
(FC20 for `n = 1`; EGP03, the rank-one rows of TCP02)

Blueprint `master207B.tex`: FC20 (`lem:fibration-euclidean-alignment`, lines 1397–1423), FC21
(1425–1442), EGP03 (`lem:fibration-edge-raw-alignment`, 4897–4941), TCP02
(`lem:fibration-first-raw-alignment`, 5311–5368) and SGP02 (4410–4481).

* `exists_sign_of_real_anchor_alignment` (FC20, `n = 1`): a map of the open interval `(-2a, 2a)`
  fixing `0` with additive distortion `δ` is within `4 δ` of `t ↦ σ t` on `[-a, a]` for one sign `σ`
  (the blueprint's constant `24 n δ` and its smallness hypothesis `δ ≤ a/20` are not needed in
  dimension one).
* `exists_unit_row_alignment_of_splittingCompatible` (FC21 with AC76's witness): if a rank-one
  splitting `φ` is `τ`-compatible with a rank-`k` splitting `ψ` at the same point
  (`SplittingCompatible`, the output of AC76 `exists_splitting_compatibility_parameter`), then one
  unit row `w` (a coisometry `ℝ^k → ℝ`) satisfies `|φ₁ - ⟪w, ψ₁⟫| ≤ 5 τ` wherever
  `|⟪w, ψ₁⟫| ≤ τ⁻¹/2`. For `k = 1` the row is a sign: `exists_sign_alignment_of_splittingCompatible_one_one`,
  which is EGP03's (ER) for the recentred, rescaled splittings (the translation `c_j` and the scale
  `s_j` are carried by the recentred first coordinate `s_j (u_j - u_j(p_i))`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace GC.MetricGeometry

/-- FC20 in dimension one. -/
theorem exists_sign_of_real_anchor_alignment {f : ℝ → ℝ} {a δ : ℝ} (ha : 0 < a)
    (h0 : f 0 = 0)
    (hdist : ∀ v w : ℝ, |v| < 2 * a → |w| < 2 * a → |(|f v - f w| - |v - w|)| ≤ δ) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ v : ℝ, |v| ≤ a → |f v - σ * v| ≤ 4 * δ := by
  have haa : |a| < 2 * a := by rw [abs_of_pos ha]; linarith
  have h0a : |(0 : ℝ)| < 2 * a := by rw [abs_zero]; linarith
  -- normalize the sign by the value at `a`
  obtain ⟨σ, hσ, hFa⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 ≤ σ * f a := by
    by_cases h : 0 ≤ f a
    · exact ⟨1, Or.inl rfl, by linarith⟩
    · exact ⟨-1, Or.inr rfl, by linarith⟩
  have hσsq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have habsσ (t : ℝ) : |σ * t| = |t| := by
    rcases hσ with rfl | rfl <;> simp
  let F : ℝ → ℝ := fun t => σ * f t
  have hFd (v w : ℝ) (hv : |v| < 2 * a) (hw : |w| < 2 * a) : |(|F v - F w| - |v - w|)| ≤ δ := by
    have h := hdist v w hv hw
    have he : F v - F w = σ * (f v - f w) := by simp only [F]; ring
    rwa [he, habsσ]
  have hF0 (v : ℝ) (hv : |v| < 2 * a) : |(|F v| - |v|)| ≤ δ := by
    have h := hFd v 0 hv h0a
    simpa only [F, h0, mul_zero, sub_zero] using h
  have hFa' : a - δ ≤ F a ∧ F a ≤ a + δ := by
    have h := abs_le.mp (hF0 a haa)
    rw [abs_of_nonneg hFa, abs_of_pos ha] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  refine ⟨σ, hσ, fun v hv => ?_⟩
  have hv2 : |v| < 2 * a := by linarith
  have hva : v ≤ a := (abs_le.mp hv).2
  have hFv := abs_le.mp (hF0 v hv2)
  have hFva := abs_le.mp (hFd v a hv2 haa)
  have hvaa : |v - a| = a - v := by rw [abs_of_nonpos (by linarith)]; ring
  rw [hvaa] at hFva
  have hgoal : |F v - v| ≤ 4 * δ := by
    rcases le_or_gt 0 (F v) with hF | hF <;> rcases le_or_gt 0 v with hv0 | hv0
    · rw [abs_of_nonneg hF, abs_of_nonneg hv0] at hFv
      rw [abs_le]; constructor <;> linarith [hFv.1, hFv.2]
    · -- `F v ≥ 0 > v`: forced to be small
      rw [abs_of_nonneg hF, abs_of_neg hv0] at hFv
      have hva' : -a ≤ v := (abs_le.mp hv).1
      have hd : |F v - F a| ≤ a + v + 2 * δ := by
        rw [abs_le]; constructor <;> linarith [hFv.1, hFv.2, hFa'.1, hFa'.2]
      have hsmall : -v ≤ 3 / 2 * δ := by linarith [hFva.1]
      rw [abs_le]; constructor <;> linarith [hFv.1, hFv.2]
    · -- `F v < 0 ≤ v`: forced to be small
      rw [abs_of_neg hF, abs_of_nonneg hv0] at hFv
      have hd : |F v - F a| = F a - F v := by rw [abs_of_neg (by linarith)]; ring
      rw [hd] at hFva
      have hsmall : v ≤ 3 / 2 * δ := by linarith [hFva.2, hFa'.1]
      rw [abs_le]; constructor <;> linarith [hFv.1, hFv.2]
    · rw [abs_of_neg hF, abs_of_neg hv0] at hFv
      rw [abs_le]; constructor <;> linarith [hFv.1, hFv.2]
  have he : f v - σ * v = σ * (F v - v) := by
    simp only [F]; rw [mul_sub, ← mul_assoc, hσsq, one_mul]
  rw [he, habsσ]
  exact hgoal

theorem norm_euclideanSpace_fin_one (v : EuclideanSpace ℝ (Fin 1)) : ‖v‖ = |v 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]

theorem euclideanSpace_fin_one_eq_single (v : EuclideanSpace ℝ (Fin 1)) :
    v = EuclideanSpace.single 0 (v 0) := by
  ext i
  rw [Subsingleton.elim i 0]
  simp

variable {X A B : Type*} [MetricSpace X] [MetricSpace A] [MetricSpace B]

/-- AC76's compatibility witness for a rank-one splitting `φ` and a rank-`k` splitting `ψ` gives one
unit row `w` aligning their real coordinates (FC21 with FC20, `n = 1`). -/
theorem exists_unit_row_alignment_of_splittingCompatible {p : X} {a₀ : A} {b₀ : B} {k : ℕ}
    {δ ε τ : ℝ}
    (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), a₀)) δ)
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀)) ε)
    (hcomp : SplittingCompatible φ ψ τ) :
    ∃ w : EuclideanSpace ℝ (Fin k), ‖w‖ = 1 ∧ ∀ x ∈ ball p τ⁻¹,
      |⟪w, (ψ.toFun x).fst⟫_ℝ| ≤ τ⁻¹ / 2 →
        |(φ.toFun x).fst 0 - ⟪w, (ψ.toFun x).fst⟫_ℝ| ≤ 5 * τ := by
  obtain ⟨-, Q, E, Fac, hQ⟩ := hcomp
  have hτ : 0 < τ := E.error_pos
  let g : ℝ → ℝ := fun t => E.toFun (EuclideanSpace.single 0 t) 0
  have hnorm1 (t : ℝ) : ‖EuclideanSpace.single (0 : Fin 1) t‖ = |t| := by
    rw [PiLp.norm_single, Real.norm_eq_abs]
  have hg0 : g 0 = 0 := by
    simp only [g]
    rw [show EuclideanSpace.single (0 : Fin 1) (0 : ℝ) = 0 by simp, E.basepoint]
    rfl
  have hgE (t : ℝ) : E.toFun (EuclideanSpace.single 0 t) = EuclideanSpace.single 0 (g t) :=
    euclideanSpace_fin_one_eq_single _
  have hgd (v v' : ℝ) (hv : |v| < 2 * (τ⁻¹ / 2)) (hv' : |v'| < 2 * (τ⁻¹ / 2)) :
      |(|g v - g v'| - |v - v'|)| ≤ τ := by
    have hmv : EuclideanSpace.single (0 : Fin 1) v ∈ ball (0 : EuclideanSpace ℝ (Fin 1)) τ⁻¹ := by
      rw [mem_ball, dist_zero_right, hnorm1]; linarith
    have hmv' : EuclideanSpace.single (0 : Fin 1) v' ∈ ball (0 : EuclideanSpace ℝ (Fin 1)) τ⁻¹ := by
      rw [mem_ball, dist_zero_right, hnorm1]; linarith
    have h := E.distortion _ hmv _ hmv'
    rw [hgE, hgE, dist_eq_norm, dist_eq_norm, norm_euclideanSpace_fin_one,
      norm_euclideanSpace_fin_one] at h
    simpa using h
  obtain ⟨σ, hσ, hfc⟩ := exists_sign_of_real_anchor_alignment (f := g) (a := τ⁻¹ / 2) (δ := τ)
    (by positivity) hg0 hgd
  -- the row
  let e₀ : WithLp 2 (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin (k - 1))) :=
    WithLp.toLp 2 (EuclideanSpace.single 0 1, 0)
  let w : EuclideanSpace ℝ (Fin k) := σ • Q.symm e₀
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have he₀ : ‖e₀‖ = 1 := by
    have h := WithLp.prod_norm_sq_eq_of_L2 e₀
    simp only [e₀, WithLp.toLp_fst, WithLp.toLp_snd, norm_zero, PiLp.norm_single, norm_one] at h
    nlinarith [norm_nonneg e₀]
  have hw : ‖w‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hσabs, one_mul, LinearIsometryEquiv.norm_map, he₀]
  have hinner (u : EuclideanSpace ℝ (Fin k)) : ⟪w, u⟫_ℝ = σ * (Q u).fst 0 := by
    rw [real_inner_smul_left, ← Q.inner_map_map, LinearIsometryEquiv.apply_symm_apply,
      WithLp.prod_inner_apply]
    simp only [e₀, inner_zero_left, add_zero,
      EuclideanSpace.inner_single_left, map_one, one_mul]
    rfl
  refine ⟨w, hw, fun x hx hsmall => ?_⟩
  set u := (Q (ψ.toFun x).fst).fst with hu
  have hσsq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hu0 : |u 0| ≤ τ⁻¹ / 2 := by
    rw [hinner, abs_mul, hσabs, one_mul] at hsmall
    exact hsmall
  have hclose : |E.toFun u 0 - (φ.toFun x).fst 0| ≤ τ := by
    have h1 := hQ x hx
    have h2 := WithLp.dist_fst_le
      (WithLp.toLp 2 (E.toFun (Q (ψ.toFun x).fst).fst,
        Fac.toFun (WithLp.toLp 2 ((Q (ψ.toFun x).fst).snd, (ψ.toFun x).snd)))) (φ.toFun x)
    rw [dist_eq_norm, norm_euclideanSpace_fin_one] at h2
    simp only [WithLp.toLp_fst] at h2
    exact h2.trans h1
  have hEu : E.toFun u 0 = g (u 0) := by
    simp only [g]
    rw [← euclideanSpace_fin_one_eq_single u]
  have hfcu := hfc (u 0) hu0
  rw [hinner]
  have hgoal : (φ.toFun x).fst 0 - σ * u 0 =
      ((φ.toFun x).fst 0 - E.toFun u 0) + (g (u 0) - σ * u 0) := by rw [hEu]; ring
  rw [hgoal]
  calc _ ≤ |(φ.toFun x).fst 0 - E.toFun u 0| + |g (u 0) - σ * u 0| := abs_add_le _ _
    _ ≤ τ + 4 * τ := by
        apply add_le_add _ hfcu
        rw [abs_sub_comm]; exact hclose
    _ = 5 * τ := by ring

/-- EGP03's (ER) kernel: for two rank-one splittings at the same point, AC76's compatibility gives
one sign. -/
theorem exists_sign_alignment_of_splittingCompatible_one_one {p : X} {a₀ : A} {b₀ : B}
    {δ ε τ : ℝ}
    (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), a₀)) δ)
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), b₀)) ε)
    (hcomp : SplittingCompatible φ ψ τ) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ ball p τ⁻¹, |(ψ.toFun x).fst 0| ≤ τ⁻¹ / 2 →
      |(φ.toFun x).fst 0 - σ * (ψ.toFun x).fst 0| ≤ 5 * τ := by
  obtain ⟨w, hw, hal⟩ := exists_unit_row_alignment_of_splittingCompatible φ ψ hcomp
  have hw0 : |w 0| = 1 := by rw [← norm_euclideanSpace_fin_one, hw]
  refine ⟨w 0, (abs_eq (by norm_num)).mp hw0, fun x hx hsmall => ?_⟩
  have hin : ⟪w, (ψ.toFun x).fst⟫_ℝ = w 0 * (ψ.toFun x).fst 0 := by
    rw [euclideanSpace_fin_one_eq_single w, EuclideanSpace.inner_single_left]
    simp
  rw [← hin]
  apply hal x hx
  rw [hin, abs_mul, hw0, one_mul]
  exact hsmall

end GC.MetricGeometry
