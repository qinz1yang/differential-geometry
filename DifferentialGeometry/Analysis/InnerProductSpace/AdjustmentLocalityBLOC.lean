import DifferentialGeometry.Analysis.InnerProductSpace.AdjustmentFactorization
import Mathlib.Analysis.Convex.Segment

/-!
# Blend induction for a block functional through adjustment maps (BCG04 / BCG05)

Blueprint `master207B.tex`, BCG04 (B:9132) and BCG05 (B:9202); external draft 61 §3.3–3.5 (CHAIN),
disposition D61-8. The adjustment along a closed subspace `Q` with smoothing map `a` and cutoff `ψ`
is `Ψ z = z + ψ z • (π_Q (a (π_Q z)) − π_Q z)` (`adjustmentMap Q (π_Q ∘ a) ψ`), and the chain is
`g₀ = F`, `g_j = Ψ_j ∘ g_{j−1}`. For a continuous linear map `J` that kills `Qᗮ` (the stage space
retains the whole block, `H_∂ ≤ Q_j`):

* `clm_apply_starProjection_of_orth_le_ker_BLOC`: `J ∘ π_Q = J`;
* `clm_adjustmentMap_BLOC`: `J (Ψ z) = J z + ψ z • (J (a (π_Q z)) − J z)` (exact);
* `adjustmentMap_level_BLOC`: `J z = c` and `ψ z ≠ 0 → J (a (π_Q z)) = c` give `J (Ψ z) = c`
  (the blend of `c` with `c`); `adjustmentMap_eq_BLOC`: `J ∘ Ψ = J` at such a point;
  `adjustmentMap_id_eq_BLOC`, `id_stage_value_BLOC`: an inactive stage (`a = id`) never moves `J`;
* `chain_level_BLOC` (a sequence of stages) and `chain3_level_BLOC` (the three stages of (CHAIN):
  `J g₁ = J g₂ = J g₃ = c`); BCG04 uses `c = 0`, BCG05 `J = v_b`, `c = 1`;
* the segment `[u, w]` (from `F` to `E`): `segment_level_BLOC` (`J ≡ c` on it) and
  `segment_norm_sub_le_BLOC` (`‖J (q − u)‖ ≤ ‖J (w − u)‖`).
-/

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If `J` kills `Qᗮ`, then `J ∘ π_Q = J`. -/
theorem clm_apply_starProjection_of_orth_le_ker_BLOC (Q : Submodule ℝ H)
    [Q.HasOrthogonalProjection] (J : H →L[ℝ] F) (hQ : Qᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F))
    (w : H) : J (Q.starProjection w) = J w := by
  have h : J (w - Q.starProjection w) = 0 := hQ (Q.sub_starProjection_mem_orthogonal w)
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

/-- **The block formula of one adjustment**: if `J` kills `Qᗮ`, then
`J (Ψ z) = J z + ψ z • (J (a (π_Q z)) − J z)`. -/
theorem clm_adjustmentMap_BLOC (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] (J : H →L[ℝ] F)
    (hQ : Qᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) (a : H → H) (ψ : H → ℝ) (z : H) :
    J (adjustmentMap Q (fun y => Q.starProjection (a y)) ψ z) =
      J z + ψ z • (J (a (Q.starProjection z)) - J z) := by
  rw [adjustmentMap_apply, map_add, map_smul, map_sub,
    clm_apply_starProjection_of_orth_le_ker_BLOC Q J hQ (a (Q.starProjection z)),
    clm_apply_starProjection_of_orth_le_ker_BLOC Q J hQ z]

/-- **One blend step keeps the level `c`**: if `J` kills `Qᗮ`, `J z = c`, and wherever the cutoff
is nonzero the smoothing output at the projected input has `J = c`, then `J (Ψ z) = c`. -/
theorem adjustmentMap_level_BLOC (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    (J : H →L[ℝ] F) (hQ : Qᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) (a : H → H) (ψ : H → ℝ) {z : H}
    {c : F} (hz : J z = c) (ha : ψ z ≠ 0 → J (a (Q.starProjection z)) = c) :
    J (adjustmentMap Q (fun y => Q.starProjection (a y)) ψ z) = c := by
  rw [clm_adjustmentMap_BLOC Q J hQ a ψ z, hz]
  by_cases hψ : ψ z = 0
  · rw [hψ, zero_smul, add_zero]
  · rw [ha hψ, sub_self, smul_zero, add_zero]

/-- **Exactness of one blend step**: under the hypotheses of `adjustmentMap_level_BLOC`,
`J (Ψ z) = J z`. -/
theorem adjustmentMap_eq_BLOC (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    (J : H →L[ℝ] F) (hQ : Qᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) (a : H → H) (ψ : H → ℝ) {z : H}
    (ha : ψ z ≠ 0 → J (a (Q.starProjection z)) = J z) :
    J (adjustmentMap Q (fun y => Q.starProjection (a y)) ψ z) = J z :=
  adjustmentMap_level_BLOC Q J hQ a ψ rfl ha

/-- **An inactive stage** (`a = id`) never moves `J` (any cutoff). -/
theorem adjustmentMap_id_eq_BLOC (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    (J : H →L[ℝ] F) (hQ : Qᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) (ψ : H → ℝ) (z : H) :
    J (adjustmentMap Q (fun y => Q.starProjection y) ψ z) = J z :=
  adjustmentMap_eq_BLOC Q J hQ (fun y => y) ψ fun _ =>
    clm_apply_starProjection_of_orth_le_ker_BLOC Q J hQ z

/-- The stage hypothesis of an inactive stage (`a = id`): `J z = c` gives `J (π_Q z) = c`. -/
theorem id_stage_value_BLOC (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] (J : H →L[ℝ] F)
    (hQ : Qᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) (ψ : H → ℝ) {z : H} {c : F} (hz : J z = c) :
    ψ z ≠ 0 → J (Q.starProjection z) = c := fun _ => by
  rw [clm_apply_starProjection_of_orth_le_ker_BLOC Q J hQ z, hz]

/-- **The blend induction along a sequence of stages**: `g (n + 1) = Ψ_n (g n)` with
`Ψ_n = adjustmentMap (Q n) (π_{Q n} ∘ a n) (ψ n)`, every `Q n` retaining the block (`(Q n)ᗮ ≤ ker J`),
`J (g 0) = c`, and at every stage (given `J = c` at its input) the smoothing output at the projected
input has `J = c` wherever the cutoff is nonzero: then `J (g n) = c` for all `n`. -/
theorem chain_level_BLOC (Q : ℕ → Submodule ℝ H) [∀ n, (Q n).HasOrthogonalProjection]
    (J : H →L[ℝ] F) (hQ : ∀ n, (Q n)ᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) (a : ℕ → H → H)
    (ψ : ℕ → H → ℝ) (g : ℕ → H)
    (hg : ∀ n, g (n + 1) = adjustmentMap (Q n) (fun y => (Q n).starProjection (a n y)) (ψ n) (g n))
    {c : F} (h0 : J (g 0) = c)
    (ha : ∀ n, J (g n) = c → ψ n (g n) ≠ 0 → J (a n ((Q n).starProjection (g n))) = c) :
    ∀ n, J (g n) = c := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [hg n]
    exact adjustmentMap_level_BLOC (Q n) J (hQ n) (a n) (ψ n) ih (ha n ih)

/-- **The three stages of (CHAIN)**: `g₁ = Ψ₁ u`, `g₂ = Ψ₂ g₁`, `g₃ = Ψ₃ g₂` (`u = F(p)`). If every
`Q_j` retains the block, `J u = c`, and at each stage (given `J = c` at its input) the smoothing
output at the projected stage input has `J = c` wherever that stage's cutoff is nonzero, then
`J g₁ = J g₂ = J g₃ = c` (an inactive stage: `id_stage_value_BLOC`). -/
theorem chain3_level_BLOC (Q₁ Q₂ Q₃ : Submodule ℝ H) [Q₁.HasOrthogonalProjection]
    [Q₂.HasOrthogonalProjection] [Q₃.HasOrthogonalProjection] (J : H →L[ℝ] F)
    (hQ₁ : Q₁ᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) (hQ₂ : Q₂ᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F))
    (hQ₃ : Q₃ᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) (a₁ a₂ a₃ : H → H) (ψ₁ ψ₂ ψ₃ : H → ℝ) (u : H)
    {c : F} (hu : J u = c) (h₁ : ψ₁ u ≠ 0 → J (a₁ (Q₁.starProjection u)) = c)
    (h₂ : J (adjustmentMap Q₁ (fun y => Q₁.starProjection (a₁ y)) ψ₁ u) = c →
      ψ₂ (adjustmentMap Q₁ (fun y => Q₁.starProjection (a₁ y)) ψ₁ u) ≠ 0 →
      J (a₂ (Q₂.starProjection (adjustmentMap Q₁ (fun y => Q₁.starProjection (a₁ y)) ψ₁ u))) = c)
    (h₃ : J (adjustmentMap Q₂ (fun y => Q₂.starProjection (a₂ y)) ψ₂
        (adjustmentMap Q₁ (fun y => Q₁.starProjection (a₁ y)) ψ₁ u)) = c →
      ψ₃ (adjustmentMap Q₂ (fun y => Q₂.starProjection (a₂ y)) ψ₂
        (adjustmentMap Q₁ (fun y => Q₁.starProjection (a₁ y)) ψ₁ u)) ≠ 0 →
      J (a₃ (Q₃.starProjection (adjustmentMap Q₂ (fun y => Q₂.starProjection (a₂ y)) ψ₂
        (adjustmentMap Q₁ (fun y => Q₁.starProjection (a₁ y)) ψ₁ u)))) = c) :
    J (adjustmentMap Q₁ (fun y => Q₁.starProjection (a₁ y)) ψ₁ u) = c ∧
    J (adjustmentMap Q₂ (fun y => Q₂.starProjection (a₂ y)) ψ₂
      (adjustmentMap Q₁ (fun y => Q₁.starProjection (a₁ y)) ψ₁ u)) = c ∧
    J (adjustmentMap Q₃ (fun y => Q₃.starProjection (a₃ y)) ψ₃
      (adjustmentMap Q₂ (fun y => Q₂.starProjection (a₂ y)) ψ₂
        (adjustmentMap Q₁ (fun y => Q₁.starProjection (a₁ y)) ψ₁ u))) = c := by
  have g₁ := adjustmentMap_level_BLOC Q₁ J hQ₁ a₁ ψ₁ hu h₁
  have g₂ := adjustmentMap_level_BLOC Q₂ J hQ₂ a₂ ψ₂ g₁ (h₂ g₁)
  exact ⟨g₁, g₂, adjustmentMap_level_BLOC Q₃ J hQ₃ a₃ ψ₃ g₂ (h₃ g₂)⟩

/-- **The segment keeps the level**: `J u = c` and `J w = c` give `J ≡ c` on `[u, w]`. -/
theorem segment_level_BLOC (J : H →L[ℝ] F) {u w : H} {c : F} (hu : J u = c) (hw : J w = c) :
    ∀ q ∈ segment ℝ u w, J q = c := by
  rintro q ⟨s, t, -, -, hst, rfl⟩
  rw [map_add, map_smul, map_smul, hu, hw, ← add_smul, hst, one_smul]

/-- **The segment error**: every `q ∈ [u, w]` has `‖J (q − u)‖ ≤ ‖J (w − u)‖`. -/
theorem segment_norm_sub_le_BLOC (J : H →L[ℝ] F) {u w : H} :
    ∀ q ∈ segment ℝ u w, ‖J (q - u)‖ ≤ ‖J (w - u)‖ := by
  rintro q ⟨s, t, hs, ht, hst, rfl⟩
  have hq : s • u + t • w - u = t • (w - u) := by
    rw [show s = 1 - t by linarith, sub_smul, one_smul, smul_sub]
    abel
  have ht1 : t ≤ 1 := by linarith
  rw [hq, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  exact mul_le_of_le_one_left (norm_nonneg _) ht1

end DifferentialGeometry.Analysis
