import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusEdgeChartSTR

/-!
# S-SOLIDTORUS2 (suffix `_STR`), G3 part 1: the planar factors of the ball ratio

The rim face function must descend to the edge base (`CornerDescended74`): on a neighbourhood of
the rim fibre the ball ratio must be a function of the edge coordinate `t`. With `u = Re q`,
`r = ‖q‖` one has `4 t (1 - t) = λ₁ (κ - u)`, `λ₁ = 2r/((r - u)(r + κ))`
(`four_t_STR`). The ball ratio is therefore replaced by `Λ (κ - u)`, `Λ = (1 - ρ) + ρ λ₁ > 0` with a
smooth cutoff `ρ = η₁(u) η₂(‖q‖²)` equal to `1` near the rim fibres and supported where `r > u`
(so `λ₁` is smooth there).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

/-- `λ₁(q) = 2 r / ((r - u)(r + κ))`, `r = ‖q‖`, `u = Re q`. -/
def lam1_STR (q : ℂ) : ℝ := 2 * ‖q‖ / ((‖q‖ - q.re) * (‖q‖ + kap_STR))

theorem four_t_STR {q : ℂ} (hk : kap_STR < ‖q‖) (hre : q.re < ‖q‖) :
    4 * tOf_STR q * (1 - tOf_STR q) = lam1_STR q * (kap_STR - q.re) := by
  have hr : 0 < ‖q‖ := lt_trans (by norm_num [kap_STR]) hk
  have hpos : 0 < ‖q‖ - q.re := sub_pos.mpr hre
  have hk0 : 0 < kap_STR := by norm_num [kap_STR]
  have hsq : ‖q‖ ^ 2 = q.re ^ 2 + q.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hc := cR_pos_STR hk
  have hc2 := cR_sq_STR hk
  have hv2 : q.im ^ 2 = (‖q‖ - q.re) * (‖q‖ + q.re) := by nlinarith [hsq]
  have h1 : 4 * tOf_STR q * (1 - tOf_STR q) = 1 - (zOf_STR q / cR_STR ‖q‖) ^ 2 := by
    unfold tOf_STR
    ring
  rw [h1, div_pow, hc2, zOf_STR, div_pow, hv2, lam1_STR]
  have hk1 : ‖q‖ - kap_STR ≠ 0 := (sub_pos.mpr hk).ne'
  have hk2 : ‖q‖ + kap_STR ≠ 0 := by linarith
  field_simp
  ring


/-! ## The cutoff and the mixed positive factor `Λ` -/

/-- Cutoff in `Re q`: `1` for `u ≤ κ + 1/50`, `0` for `u ≥ κ + 1/25`. -/
def eta1_STR (u : ℝ) : ℝ := Real.smoothTransition ((kap_STR + 1 / 25 - u) / (1 / 50))

/-- Cutoff in `‖q‖²`: `0` for `m ≤ 4/5`, `1` for `m ≥ 17/20`. -/
def eta2_STR (m : ℝ) : ℝ := Real.smoothTransition ((m - 4 / 5) / (1 / 20))

/-- The cutoff `ρ(q) = η₁(Re q) η₂(‖q‖²)`. -/
def cut_STR (q : ℂ) : ℝ := eta1_STR q.re * eta2_STR (‖q‖ ^ 2)

theorem cut_nonneg_STR (q : ℂ) : 0 ≤ cut_STR q :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem cut_le_one_STR (q : ℂ) : cut_STR q ≤ 1 := by
  unfold cut_STR
  have h1 := Real.smoothTransition.le_one ((kap_STR + 1 / 25 - q.re) / (1 / 50))
  have h2 := Real.smoothTransition.le_one ((‖q‖ ^ 2 - 4 / 5) / (1 / 20))
  have h3 := Real.smoothTransition.nonneg ((kap_STR + 1 / 25 - q.re) / (1 / 50))
  have h4 := Real.smoothTransition.nonneg ((‖q‖ ^ 2 - 4 / 5) / (1 / 20))
  unfold eta1_STR eta2_STR
  nlinarith

theorem cut_support_STR {q : ℂ} (h : cut_STR q ≠ 0) :
    q.re < kap_STR + 1 / 25 ∧ 4 / 5 < ‖q‖ ^ 2 := by
  by_contra hcon
  apply h
  rw [not_and_or] at hcon
  unfold cut_STR eta1_STR eta2_STR
  rcases hcon with h1 | h2
  · have h0 : Real.smoothTransition ((kap_STR + 1 / 25 - q.re) / (1 / 50)) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by
        have := not_lt.mp h1
        have h50 : (kap_STR + 1 / 25 - q.re) / (1 / 50) = 50 * (kap_STR + 1 / 25 - q.re) := by
          field_simp
        rw [h50]
        linarith)
    rw [h0, zero_mul]
  · have h0 : Real.smoothTransition ((‖q‖ ^ 2 - 4 / 5) / (1 / 20)) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by
        have := not_lt.mp h2
        have h20 : (‖q‖ ^ 2 - 4 / 5) / (1 / 20) = 20 * (‖q‖ ^ 2 - 4 / 5) := by
          field_simp
        rw [h20]
        linarith)
    rw [h0, mul_zero]

theorem cut_eq_one_STR {q : ℂ} (h1 : q.re ≤ kap_STR + 1 / 50) (h2 : 17 / 20 ≤ ‖q‖ ^ 2) :
    cut_STR q = 1 := by
  unfold cut_STR eta1_STR eta2_STR
  rw [Real.smoothTransition.one_of_one_le (by
      have h50 : (kap_STR + 1 / 25 - q.re) / (1 / 50) = 50 * (kap_STR + 1 / 25 - q.re) := by
        field_simp
      rw [h50]
      linarith), Real.smoothTransition.one_of_one_le (by
      have h20 : (‖q‖ ^ 2 - 4 / 5) / (1 / 20) = 20 * (‖q‖ ^ 2 - 4 / 5) := by
        field_simp
      rw [h20]
      linarith), one_mul]

theorem contDiff_cut_STR : ContDiff ℝ ∞ cut_STR := by
  unfold cut_STR eta1_STR eta2_STR
  have hre : ContDiff ℝ ∞ (fun q : ℂ => q.re) := Complex.reCLM.contDiff
  have hn : ContDiff ℝ ∞ (fun q : ℂ => ‖q‖ ^ 2) := contDiff_norm_sq ℝ
  exact (Real.smoothTransition.contDiff.comp
      (((contDiff_const.sub hre).div_const (1 / 50)))).mul
    (Real.smoothTransition.contDiff.comp ((hn.sub contDiff_const).div_const (1 / 20)))


/-- The positive factor `Λ = (1 - ρ) + ρ λ₁`. -/
def lamMix_STR (q : ℂ) : ℝ := (1 - cut_STR q) + cut_STR q * lam1_STR q

theorem support_lt_STR {q : ℂ} (h : cut_STR q ≠ 0) : q.re < ‖q‖ ∧ kap_STR < ‖q‖ := by
  obtain ⟨h1, h2⟩ := cut_support_STR h
  have hk : kap_STR + 1 / 25 = 21 / 25 := by norm_num [kap_STR]
  rw [hk] at h1
  have hn := norm_nonneg q
  have hlt : (21 / 25 : ℝ) < ‖q‖ := by nlinarith
  exact ⟨by linarith, by norm_num [kap_STR]; linarith⟩

theorem lam1_pos_STR {q : ℂ} (h : cut_STR q ≠ 0) : 0 < lam1_STR q := by
  obtain ⟨h1, h2⟩ := support_lt_STR h
  have hk0 : 0 < kap_STR := by norm_num [kap_STR]
  unfold lam1_STR
  apply div_pos
  · linarith
  · exact mul_pos (sub_pos.mpr h1) (by linarith)

theorem lamMix_pos_STR (q : ℂ) : 0 < lamMix_STR q := by
  unfold lamMix_STR
  by_cases h : cut_STR q = 0
  · rw [h]
    norm_num
  · have hp := lam1_pos_STR h
    have h0 : 0 < cut_STR q := lt_of_le_of_ne (cut_nonneg_STR q) (Ne.symm h)
    have h1 := cut_le_one_STR q
    nlinarith [mul_pos h0 hp]

theorem lam1_eq_of_cut_STR {q : ℂ} (h : cut_STR q = 1) : lamMix_STR q = lam1_STR q := by
  unfold lamMix_STR
  rw [h]
  ring

theorem contDiffAt_lam1_STR {q : ℂ} (h1 : q.re < ‖q‖) (hq : kap_STR < ‖q‖) :
    ContDiffAt ℝ ∞ lam1_STR q := by
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, norm_zero] at hq
    norm_num [kap_STR] at hq
  have hn : ContDiffAt ℝ ∞ (fun q : ℂ => ‖q‖) q := contDiffAt_norm ℝ hq0
  have hk0 : 0 < kap_STR := by norm_num [kap_STR]
  unfold lam1_STR
  refine (contDiffAt_const.mul hn).div ?_ ?_
  · exact (hn.sub Complex.reCLM.contDiff.contDiffAt).mul (hn.add contDiffAt_const)
  · exact (mul_pos (sub_pos.mpr h1) (by linarith)).ne'

theorem contDiff_lamMix_STR : ContDiff ℝ ∞ lamMix_STR := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hO : q.re < 17 / 20 ∧ 3 / 4 < ‖q‖ ^ 2
  · obtain ⟨h1, h2⟩ := hO
    have hn := norm_nonneg q
    have hlt : (17 / 20 : ℝ) < ‖q‖ := by nlinarith
    have hq : kap_STR < ‖q‖ := by norm_num [kap_STR]; linarith
    have hl := contDiffAt_lam1_STR (by linarith) hq
    unfold lamMix_STR
    exact (contDiffAt_const.sub contDiff_cut_STR.contDiffAt).add
      (contDiff_cut_STR.contDiffAt.mul hl)
  · have hF : IsClosed {q : ℂ | q.re ≤ kap_STR + 1 / 25 ∧ 4 / 5 ≤ ‖q‖ ^ 2} :=
      (isClosed_le Complex.continuous_re continuous_const).inter
        (isClosed_le continuous_const (continuous_norm.pow 2))
    have hqF : q ∉ {q : ℂ | q.re ≤ kap_STR + 1 / 25 ∧ 4 / 5 ≤ ‖q‖ ^ 2} := by
      rintro ⟨h1, h2⟩
      apply hO
      have hk : kap_STR + 1 / 25 = 21 / 25 := by norm_num [kap_STR]
      rw [hk] at h1
      exact ⟨by linarith, by linarith⟩
    have hev : ∀ᶠ q' in nhds q, lamMix_STR q' = 1 := by
      filter_upwards [hF.isOpen_compl.mem_nhds hqF] with q' hq'
      have : cut_STR q' = 0 := by
        by_contra hne
        obtain ⟨a, b⟩ := cut_support_STR hne
        exact hq' ⟨a.le, b.le⟩
      unfold lamMix_STR
      rw [this]
      ring
    exact contDiffAt_const.congr_of_eventuallyEq hev

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
