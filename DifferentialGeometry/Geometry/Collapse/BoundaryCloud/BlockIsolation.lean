import DifferentialGeometry.Analysis.InnerProductSpace.AffineMarkerSpectralSection

/-!
# Global physical boundary-block isolation (blueprint 207B, BCG04, B:9132–9200)

Kernels of BCG04 (and the stage induction reused by BCG05):
* `starProjection_stages_eq_of_contributors`: through finitely many stages
  `f (j+1) = f j + t j • (g j - f j)`, a coordinate block keeps the constant value `c` provided every
  active stage output `g j` is a zero of a weighted spectral section whose active centers have block
  `c` and whose active planes lie in the block kernel (the "entire contributor list" of BCG04/BCG05).
  The per-stage spectral identity is W4-GAF's GAF03 core
  `Submodule.starProjection_eq_of_weighted_normal_section_eq_zero`.
* `two_mul_lt_reference_radius`, `reference_radius_ge_of_scale_chain`: the (AM) arithmetic
  `R_a ≥ (108/625) ρ(p) > 2 r_∂`.
* `norm_sub_lt_of_isolation`, `norm_segment_sub_le`: the error `ε_∂ = 20 c₃ r_∂` and its segment form.
-/

set_option autoImplicit false
open scoped BigOperators

namespace DifferentialGeometry.Geometry.Collapse.BoundaryCloud

section Stages

variable {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup K]
  [NormedSpace ℝ K]

/-- Stage induction for a linear block functional: if every active stage output keeps the block
value `c` (when the input has it), so do all stage maps. -/
theorem block_eq_of_stages (J : H →L[ℝ] K) (c : K) (f g : ℕ → H) (t : ℕ → ℝ) (n : ℕ)
    (hstep : ∀ j < n, f (j + 1) = f j + t j • (g j - f j))
    (hout : ∀ j < n, t j ≠ 0 → J (f j) = c → J (g j) = c)
    (h0 : J (f 0) = c) : ∀ j ≤ n, J (f j) = c := by
  intro j
  induction j with
  | zero => exact fun _ => h0
  | succ j ih =>
    intro hj
    have hjn : j < n := Nat.lt_of_succ_le hj
    have hfj := ih hjn.le
    rw [hstep j hjn]
    by_cases ht : t j = 0
    · rw [ht, zero_smul, add_zero, hfj]
    · exact ContinuousLinearMap.blend_apply_eq_of_projection_eq J (hout j hjn ht hfj) (Or.inr hfj)

end Stages

section Spectral

variable {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- BCG04/BCG05 stage kernel with the ENTIRE contributor list: at every active stage the output is
a zero of the weighted spectral section built from contributors whose centers have block `c` and
whose planes lie in the block kernel. Then every stage map has block `c`. With `c = 0` this is the
boundary-block isolation of BCG04; with `V = ℝ ∙ e`, `c = e` it is the exact marker of BCG05. -/
theorem starProjection_stages_eq_of_contributors (V : Submodule ℝ H) (c : H)
    (f g : ℕ → H) (t : ℕ → ℝ) (n : ℕ) (s : Set ℝ) (hs : (1 : ℝ) ∈ s)
    (hstep : ∀ j < n, f (j + 1) = f j + t j • (g j - f j))
    (hcontrib : ∀ j < n, t j ≠ 0 → V.starProjection (f j) = c →
      ∃ (S : Finset A) (L : A → Submodule ℝ H) (x : A → H) (w : A → ℝ),
        ∑ i ∈ S, w i = 1 ∧ (∀ i ∈ S, w i ≠ 0 → L i ≤ Vᗮ) ∧
        (∀ i ∈ S, w i ≠ 0 → V.starProjection (x i) = c) ∧
        ∑ i ∈ S, w i • (⨆ a ∈ s, Module.End.eigenspace
          (∑ k ∈ S, w k • (L k)ᗮ.starProjection).toLinearMap a).starProjection (g j - x i) = 0)
    (h0 : V.starProjection (f 0) = c) : ∀ j ≤ n, V.starProjection (f j) = c := by
  refine block_eq_of_stages V.starProjection c f g t n hstep ?_ h0
  intro j hj ht hfj
  obtain ⟨S, L, x, w, hw, hL, hx, hzero⟩ := hcontrib j hj ht hfj
  exact Submodule.starProjection_eq_of_weighted_normal_section_eq_zero V c S L x w hw hL hx s hs
    (g j) hzero

end Spectral

/-- The (AM) chain of CFS28 as used in BCG04: `σ_x ≥ (3/5)ρ(p)`, `σ_u ≥ (3/5)σ_x`,
`ρ(q_u) ≥ (3/5)σ_u` and the full reference marker `R_a ≥ (4/5)ρ(q_u)` give `R_a ≥ (108/625)ρ(p)`. -/
theorem reference_radius_ge_of_scale_chain {ρp σx σu ρq R : ℝ}
    (hx : 3 / 5 * ρp ≤ σx) (hu : 3 / 5 * σx ≤ σu) (hq : 3 / 5 * σu ≤ ρq) (hR : 4 / 5 * ρq ≤ R) :
    108 / 625 * ρp ≤ R := by
  linarith

/-- BCG04's scale step: on the large-scale region `ρ(p) > 20 r_∂` every model reference has
`R_a > 2 r_∂`, so by BCG01 no boundary support meets its domain. -/
theorem two_mul_lt_reference_radius {ρp R r : ℝ} (hR : 108 / 625 * ρp ≤ R) (hρ : 20 * r < ρp)
    (hr : 0 ≤ r) : 2 * r < R := by
  linarith

variable {K : Type*} [NormedAddCommGroup K]

/-- The global block error of BCG04: zero on the large-scale region, and `< c₃ ρ(p) ≤ 20 c₃ r_∂`
elsewhere; no global upper bound on `ρ` is used. -/
theorem norm_sub_lt_of_isolation {a A : K} {ρp r c₃ : ℝ} (hc₃ : 0 < c₃) (hr : 0 < r)
    (hzero : 20 * r < ρp → a = 0 ∧ A = 0) (herr : ‖a - A‖ < c₃ * ρp) :
    ‖a - A‖ < 20 * c₃ * r := by
  by_cases hρ : 20 * r < ρp
  · obtain ⟨ha, hA⟩ := hzero hρ
    rw [ha, hA, sub_self, norm_zero]
    positivity
  · have h := mul_le_mul_of_nonneg_left (le_of_not_gt hρ) hc₃.le
    linarith

/-- Segment form: the block error of `(1-s)F + sE` against `F` is at most that of `E`. -/
theorem norm_segment_sub_le [NormedSpace ℝ K] (a A : K) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖((1 - s) • A + s • a) - A‖ ≤ ‖a - A‖ := by
  have h : ((1 - s) • A + s • a) - A = s • (a - A) := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hs.2

end DifferentialGeometry.Geometry.Collapse.BoundaryCloud
