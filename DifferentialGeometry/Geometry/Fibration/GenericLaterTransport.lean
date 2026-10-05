import DifferentialGeometry.Analysis.InnerProductSpace.AdjustmentFactorization
import DifferentialGeometry.Geometry.Fibration.GenericMarkedPatchChart

/-!
# CGP08 on naive data: the later transports `Θ_j` through the FC32 factorization

Blueprint `master207B.tex`, CGP08 (`thm:fibration-final-bases-no-merging`, B:4259–4316); external
draft 59 §4, sixth and seventh steps (disposition D59-5). The stages are FC32 adjustments
`Ψ_k = adjustmentMap Q_k P_k ψ_k` with `Q₁ = H ⊇ Q₂ ⊇ Q₃`, `g₂ = Ψ₂ ∘ g₁`, `E = Ψ₃ ∘ g₂`,
`f_j = π_j g_j`. The later transports are `Θ₁ = Ψ₃ ∘ Ψ₂` on `V₁⁰`, `Θ₂ = Ψ₃₂` on `V₂⁰`, `Θ₃ = id`.

The third-stage cutoff descends to `Q₂` (`ψ₃ = ψ' ∘ π₂`, the chain's
`third_stage_factors_through_Q2` field; `Q₃ ≤ Q₂` alone does not give it). Then `ψ₃ ∘ π₂ = ψ₃`
(`cutoff_comp_starProjection_of_factor_BPRE`) and `Ψ₃₂ = Ψ₃` on `Q₂`, so the factorization is
`π₂ E = Ψ₃ ∘ π₂ g₂ = Θ₂ ∘ f₂` (`stage_two_final_factor_BPRE`). It is NEVER `π₂ g₂ = π₂ E`.

* `adjustmentMap_factor_eq_of_mem_BPRE`: the draft's `Ψ₃₂ = adjustmentMap Q₃ P₃ ψ'` agrees with `Ψ₃`
  on `Q₂`, hence on `V₂⁰ ⊆ Z₂ ⊆ Q₂`.
* Block retention: `adjustmentMap_retains_block_BPRE` (a coordinate killing `Q` is unchanged by an
  adjustment along `Q`), `theta_one_retains_block_BPRE` (`Θ₁` keeps every block killing `Q₂`),
  `starProjection_adjustmentMap_comm_BPRE` (`π₂ Ψ₃ = Ψ₃ π₂`).
* Smoothness on the earlier base: `adjustmentMap_add_orthogonal_BPRE` (`Ψ₃` commutes with
  translations by `Q₂ᗮ`), `contDiffAt_adjustmentMap_starProjection_BPRE` (`Ψ₃` smooth at `y` ⇒
  smooth at `π₂ y`: CFS18 at `g₂ p` gives `Θ₂` smooth at `f₂ p`),
  `contDiffAt_of_mem_image_BPRE` (exhaustion `V ⊆ g(B⁶)` transfers pointwise smoothness).
* Generic `Θ` on the marked patches `V_i = markedPatch_BPRE Z u_i v_i R_i ℓ_i` with retained
  blocks: `mem_markedPatch_of_retained_BPRE`, `injOn_theta_BPRE` (no merging),
  `theta_image_inter_marked_BPRE` (`W ∩ {marked i} = Θ(V_i)`), `theta_inverse_on_patch_BPRE`
  (`Θ⁻¹ = φ_i ∘ κ_i` on `Θ(V_i)`), `theta_patch_param_BPRE` (`Θ ∘ φ_i` is a smooth graph over the
  same ball with the same coordinate inverse).
* Carrier statements: `rf_fiber_eq_BPRE` ((RF) on `D_j = B⁶ ∩ f⁻¹(V_j⁰)`),
  `ker_comp_eq_of_left_inverse_BPRE` / `ker_fderiv_comp_eq_of_local_left_inverse_BPRE` (kernels from a
  local left inverse `φ_i ∘ κ_i`), `chart_comp_final_eq_BPRE` (`κ_i ∘ π_jE = κ_i ∘ f_j`: the
  threshold-5 submersion in the chart `κ_i` is the stage one), `mem_markedPatch_of_full_marker_BPRE`
  (`f_j(U⁵) ⊆ V_j⁰` with strict slack, the original threshold-5 domain, not shrunk).
* Assemblies: `cgp08_stage_two_BPRE`, `cgp08_stage_one_BPRE`.

Restricted fibres only: nothing here is a whole-fibre equality on `M` (that needs GAF06/GAF07).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Function
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis

section Adjustment

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A coordinate killing `Q` is unchanged by an adjustment along `Q` with `Q`-valued smoothing. -/
theorem adjustmentMap_retains_block_BPRE {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] {P : H → H} (hP : ∀ z, P z ∈ Q)
    (ψ : H → ℝ) (b : H →L[ℝ] F) (hb : ∀ q ∈ Q, b q = 0) (x : H) :
    b (adjustmentMap Q P ψ x) = b x := by
  rw [adjustmentMap_apply, map_add, map_smul,
    hb _ (Q.sub_mem (hP _) (Q.starProjection_apply_mem x)), smul_zero, add_zero]

/-- `Θ₁ = Ψ₃ ∘ Ψ₂` keeps every block killing `Q₂` (`Q₃ ≤ Q₂`). -/
theorem theta_one_retains_block_BPRE {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q₂ Q₃ : Submodule ℝ H) [Q₂.HasOrthogonalProjection] [Q₃.HasOrthogonalProjection]
    (h32 : Q₃ ≤ Q₂) {P₂ P₃ : H → H} (hP₂ : ∀ z, P₂ z ∈ Q₂) (hP₃ : ∀ z, P₃ z ∈ Q₃)
    (ψ₂ ψ₃ : H → ℝ) (b : H →L[ℝ] F) (hb : ∀ q ∈ Q₂, b q = 0) (x : H) :
    b (adjustmentMap Q₃ P₃ ψ₃ (adjustmentMap Q₂ P₂ ψ₂ x)) = b x := by
  rw [adjustmentMap_retains_block_BPRE Q₃ hP₃ ψ₃ b (fun q hq => hb q (h32 hq)),
    adjustmentMap_retains_block_BPRE Q₂ hP₂ ψ₂ b hb]

/-- A cutoff that factors through `π₂` is invariant under `π₂`. -/
theorem cutoff_comp_starProjection_of_factor_BPRE (Q₂ : Submodule ℝ H)
    [Q₂.HasOrthogonalProjection] (ψ' : H → ℝ) (z : H) :
    (ψ' ∘ Q₂.starProjection) (Q₂.starProjection z) = (ψ' ∘ Q₂.starProjection) z := by
  simp only [comp_apply, Submodule.starProjection_eq_self_iff.mpr (Q₂.starProjection_apply_mem z)]

/-- **The draft's `Ψ₃₂` is `Ψ₃` on `Q₂`.** For `ψ₃ = ψ' ∘ π₂` and a point `y ∈ Q₂` (e.g. a
point of the stage-two zero set, `zeroSet_subset_stageQ`), `Ψ₃₂ y = adjustmentMap Q₃ P₃ ψ' y`
equals `Ψ₃ y`; so `Θ₂ = Ψ₃₂|V₂⁰ = Ψ₃|V₂⁰`. -/
theorem adjustmentMap_factor_eq_of_mem_BPRE (Q₂ Q₃ : Submodule ℝ H) [Q₂.HasOrthogonalProjection]
    [Q₃.HasOrthogonalProjection] (P₃ : H → H) (ψ' : H → ℝ) {y : H} (hy : y ∈ Q₂) :
    adjustmentMap Q₃ P₃ ψ' y = adjustmentMap Q₃ P₃ (ψ' ∘ Q₂.starProjection) y := by
  rw [adjustmentMap_apply, adjustmentMap_apply, comp_apply,
    Submodule.starProjection_eq_self_iff.mpr hy]

/-- **FC32 with a `π₂`-invariant cutoff:** `π₂ ∘ Ψ₃ = Ψ₃ ∘ π₂`. -/
theorem starProjection_adjustmentMap_comm_BPRE (Q₂ Q₃ : Submodule ℝ H)
    [Q₂.HasOrthogonalProjection] [Q₃.HasOrthogonalProjection] (h32 : Q₃ ≤ Q₂) {P : H → H}
    (hP : ∀ z, P z ∈ Q₃) {ψ : H → ℝ} (hψ : ∀ z, ψ (Q₂.starProjection z) = ψ z) (x : H) :
    Q₂.starProjection (adjustmentMap Q₃ P ψ x) = adjustmentMap Q₃ P ψ (Q₂.starProjection x) := by
  have hfun : ψ = ψ ∘ Q₂.starProjection := funext fun z => (hψ z).symm
  have h := starProjection_adjustmentMap_of_le Q₃ h32 hP ψ x
  rwa [← hfun] at h

/-- **The stage-two factorization** `π₂ E = Θ₂ ∘ f₂`: for `E = Ψ₃ ∘ g₂` with the `π₂`-invariant
third cutoff, `π₂ (E p) = Ψ₃ (π₂ (g₂ p))` at EVERY point. (No identity `π₂ g₂ = π₂ E` is used or
implied.) -/
theorem stage_two_final_factor_BPRE {M : Type*} (Q₂ Q₃ : Submodule ℝ H)
    [Q₂.HasOrthogonalProjection] [Q₃.HasOrthogonalProjection] (h32 : Q₃ ≤ Q₂) {P₃ : H → H}
    (hP₃ : ∀ z, P₃ z ∈ Q₃) {ψ₃ : H → ℝ} (hψ : ∀ z, ψ₃ (Q₂.starProjection z) = ψ₃ z)
    (g₂ : M → H) (p : M) :
    Q₂.starProjection (adjustmentMap Q₃ P₃ ψ₃ (g₂ p)) =
      adjustmentMap Q₃ P₃ ψ₃ (Q₂.starProjection (g₂ p)) :=
  starProjection_adjustmentMap_comm_BPRE Q₂ Q₃ h32 hP₃ hψ (g₂ p)

/-- `Ψ₃` commutes with translations by `Q₂ᗮ` (`π₂`-invariant cutoff, `Q₃ ≤ Q₂`). -/
theorem adjustmentMap_add_orthogonal_BPRE (Q₂ Q₃ : Submodule ℝ H) [Q₂.HasOrthogonalProjection]
    [Q₃.HasOrthogonalProjection] (h32 : Q₃ ≤ Q₂) (P : H → H) {ψ : H → ℝ}
    (hψ : ∀ z, ψ (Q₂.starProjection z) = ψ z) {n : H} (hn : n ∈ Q₂ᗮ) (z : H) :
    adjustmentMap Q₃ P ψ (z + n) = adjustmentMap Q₃ P ψ z + n := by
  have hn₂ : Q₂.starProjection n = 0 := (Submodule.starProjection_apply_eq_zero_iff Q₂).mpr hn
  have hn₃ : Q₃.starProjection n = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff Q₃).mpr (Submodule.orthogonal_le h32 hn)
  have hψn : ψ (z + n) = ψ z := by
    rw [← hψ (z + n), map_add, hn₂, add_zero, hψ]
  rw [adjustmentMap_apply, adjustmentMap_apply, hψn, map_add Q₃.starProjection, hn₃, add_zero]
  abel

/-- **Smoothness on the earlier base.** With the `π₂`-invariant third cutoff, if `Ψ₃` is smooth at
`y` then it is smooth at `π₂ y`. -/
theorem contDiffAt_adjustmentMap_starProjection_BPRE (Q₂ Q₃ : Submodule ℝ H)
    [Q₂.HasOrthogonalProjection] [Q₃.HasOrthogonalProjection] (h32 : Q₃ ≤ Q₂) (P : H → H)
    {ψ : H → ℝ} (hψ : ∀ z, ψ (Q₂.starProjection z) = ψ z) {y : H}
    (hy : ContDiffAt ℝ ∞ (adjustmentMap Q₃ P ψ) y) :
    ContDiffAt ℝ ∞ (adjustmentMap Q₃ P ψ) (Q₂.starProjection y) := by
  set n : H := y - Q₂.starProjection y with hn
  have hnmem : n ∈ Q₂ᗮ := Q₂.sub_starProjection_mem_orthogonal y
  have hfun : adjustmentMap Q₃ P ψ = fun z => adjustmentMap Q₃ P ψ (z + n) - n := by
    funext z
    rw [adjustmentMap_add_orthogonal_BPRE Q₂ Q₃ h32 P hψ hnmem, add_sub_cancel_right]
  have hpt : Q₂.starProjection y + n = y := by rw [hn]; abel
  rw [hfun]
  have hy' : ContDiffAt ℝ ∞ (adjustmentMap Q₃ P ψ) (Q₂.starProjection y + n) := by rwa [hpt]
  exact (ContDiffAt.comp (f := fun z : H => z + n) (Q₂.starProjection y) hy'
    (contDiffAt_id.add contDiffAt_const)).sub contDiffAt_const

end Adjustment

/-- Exhaustion transfers pointwise smoothness: if `V ⊆ g(B⁶)` and `Ψ` is smooth at every `g p`, it
is smooth at every point of `V`. -/
theorem contDiffAt_of_mem_image_BPRE {M H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (V : Set H) (g : M → H) (B : Set M) (Ψ : H → F)
    (hV : ∀ w ∈ V, ∃ p ∈ B, g p = w) (hΨ : ∀ p ∈ B, ContDiffAt ℝ ∞ Ψ (g p)) :
    ∀ w ∈ V, ContDiffAt ℝ ∞ Ψ w := by
  intro w hw
  obtain ⟨p, hp, rfl⟩ := hV w hw
  exact hΨ p hp

section Theta

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- A point of `Z` whose image under a block-retaining `Θ` satisfies the `i`-marked condition lies
in the `i`-patch. -/
theorem mem_markedPatch_of_retained_BPRE (Z : Set H) (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ) (R ℓ : ℝ)
    (Θ : H → H) {w : H} (hwZ : w ∈ Z) (hu : u (Θ w) = u w) (hv : v (Θ w) = v w)
    (hcond : Θ w ∈ markedCondition_BPRE u v R ℓ) : w ∈ markedPatch_BPRE Z u v R ℓ :=
  ⟨hwZ, hv ▸ hcond.1, hu ▸ hcond.2⟩

/-- **No merging.** If `Θ` retains every block on the patches of the family and each block is
injective on its patch (CGP07), `Θ` is injective on the union of the patches. -/
theorem injOn_theta_BPRE {ι : Type*} (Z : Set H) (u : ι → H →L[ℝ] E) (v : ι → H →L[ℝ] ℝ)
    (R ℓ : ι → ℝ) (Θ : H → H)
    (hret : ∀ i, ∀ w ∈ ⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k),
      u i (Θ w) = u i w ∧ v i (Θ w) = v i w)
    (hinj : ∀ i, InjOn (u i) (markedPatch_BPRE Z (u i) (v i) (R i) (ℓ i))) :
    InjOn Θ (⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k)) := by
  intro w₁ h₁ w₂ h₂ heq
  obtain ⟨i, hi⟩ := mem_iUnion.mp h₁
  obtain ⟨k, hk⟩ := mem_iUnion.mp h₂
  have hu₂ : u i w₂ = u i w₁ := by
    rw [← (hret i w₂ h₂).1, ← heq, (hret i w₁ h₁).1]
  have hv₂ : v i w₂ = v i w₁ := by
    rw [← (hret i w₂ h₂).2, ← heq, (hret i w₁ h₁).2]
  have hi₂ : w₂ ∈ markedPatch_BPRE Z (u i) (v i) (R i) (ℓ i) :=
    ⟨hk.1, hv₂ ▸ hi.2.1, hu₂ ▸ hi.2.2⟩
  exact hinj i hi hi₂ hu₂.symm

/-- **Patch identification.** `Θ(⋃ V_k) ∩ {v_i > .9R_i, |u_i| < 5.5ℓ_iR_i} = Θ(V_i)`. -/
theorem theta_image_inter_marked_BPRE {ι : Type*} (Z : Set H) (u : ι → H →L[ℝ] E)
    (v : ι → H →L[ℝ] ℝ) (R ℓ : ι → ℝ) (Θ : H → H)
    (hret : ∀ i, ∀ w ∈ ⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k),
      u i (Θ w) = u i w ∧ v i (Θ w) = v i w) (i : ι) :
    Θ '' (⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k)) ∩
        markedCondition_BPRE (u i) (v i) (R i) (ℓ i) =
      Θ '' markedPatch_BPRE Z (u i) (v i) (R i) (ℓ i) := by
  ext y
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hcond⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp hw
    exact ⟨w, mem_markedPatch_of_retained_BPRE Z (u i) (v i) (R i) (ℓ i) Θ hk.1
      (hret i w hw).1 (hret i w hw).2 hcond, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    have hwU : w ∈ ⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k) := mem_iUnion.mpr ⟨i, hw⟩
    refine ⟨⟨w, hwU, rfl⟩, ?_, ?_⟩
    · rw [(hret i w hwU).2]
      exact hw.2.1
    · rw [(hret i w hwU).1]
      exact hw.2.2

/-- **The inverse on a transported patch is `φ_i ∘ κ_i`.** With CGP07's chart inverse `φ_i` of
`κ_i = R_i⁻¹u_i` and a `Θ` retaining `u_i` on `V_i`, every `y ∈ Θ(V_i)` has
`φ_i(κ_i y) ∈ V_i` and `Θ(φ_i(κ_i y)) = y`. -/
theorem theta_inverse_on_patch_BPRE (Z : Set H) (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ) (R ℓ : ℝ)
    (Θ : H → H) (φ : E → H)
    (hinv : InvOn φ (R⁻¹ • u) (markedPatch_BPRE Z u v R ℓ) (ball 0 (11 / 2 * ℓ)))
    (hret : ∀ w ∈ markedPatch_BPRE Z u v R ℓ, u (Θ w) = u w) :
    ∀ y ∈ Θ '' markedPatch_BPRE Z u v R ℓ,
      φ ((R⁻¹ • u) y) ∈ markedPatch_BPRE Z u v R ℓ ∧ Θ (φ ((R⁻¹ • u) y)) = y := by
  rintro y ⟨w, hw, rfl⟩
  have hκ : (R⁻¹ • u) (Θ w) = (R⁻¹ • u) w := by
    rw [clm_smul_apply_BPRE, clm_smul_apply_BPRE, hret w hw]
  have h1 : φ ((R⁻¹ • u) w) = w := hinv.1 hw
  rw [hκ, h1]
  exact ⟨hw, rfl⟩

/-- **The transported patch is a smooth graph over the same ball with the same coordinate
inverse.** If `Θ` is smooth at every point of `V_i` and retains `u_i` there, then `Θ ∘ φ_i` is
smooth on `B(0, 5.5ℓ)`, lands in `Θ(V_i)`, and `κ_i ∘ Θ ∘ φ_i = id` there. -/
theorem theta_patch_param_BPRE (Z : Set H) (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ) (R ℓ : ℝ)
    (Θ : H → H) (φ : E → H) (hφ : ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * ℓ)))
    (hinv : InvOn φ (R⁻¹ • u) (markedPatch_BPRE Z u v R ℓ) (ball 0 (11 / 2 * ℓ)))
    (hmaps : MapsTo φ (ball 0 (11 / 2 * ℓ)) (markedPatch_BPRE Z u v R ℓ))
    (hΘ : ∀ w ∈ markedPatch_BPRE Z u v R ℓ, ContDiffAt ℝ ∞ Θ w)
    (hret : ∀ w ∈ markedPatch_BPRE Z u v R ℓ, u (Θ w) = u w) :
    ContDiffOn ℝ ∞ (Θ ∘ φ) (ball 0 (11 / 2 * ℓ)) ∧
      ∀ b ∈ ball (0 : E) (11 / 2 * ℓ),
        Θ (φ b) ∈ Θ '' markedPatch_BPRE Z u v R ℓ ∧ (R⁻¹ • u) (Θ (φ b)) = b := by
  refine ⟨fun b hb => (hΘ (φ b) (hmaps hb)).comp_contDiffWithinAt b (hφ b hb), fun b hb => ?_⟩
  refine ⟨⟨φ b, hmaps hb, rfl⟩, ?_⟩
  have h1 : (R⁻¹ • u) (φ b) = b := hinv.2 hb
  rw [clm_smul_apply_BPRE, hret (φ b) (hmaps hb), ← clm_smul_apply_BPRE, h1]

end Theta

section Carrier

/-- **(RF) on the restricted carrier.** On `D = B⁶ ∩ f⁻¹(V)`, with `π E = Θ ∘ f` there and `Θ`
injective on `V`, the final fibre over `Θ w₀` is the stage fibre over `w₀` (`w₀ ∈ V`). -/
theorem rf_fiber_eq_BPRE {M H Y : Type*} (f : M → H) (πE : M → Y) (Θ : H → Y) (V : Set H)
    (B6 : Set M) (hinj : InjOn Θ V) (hfac : ∀ p ∈ B6, f p ∈ V → πE p = Θ (f p)) {w₀ : H}
    (hw₀ : w₀ ∈ V) :
    {p | p ∈ B6 ∩ f ⁻¹' V ∧ πE p = Θ w₀} = {p | p ∈ B6 ∩ f ⁻¹' V ∧ f p = w₀} := by
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, and_congr_right_iff, and_imp]
  intro hp hpV
  rw [hfac p hp hpV]
  exact ⟨fun h => hinj hpV hw₀ h, fun h => by rw [h]⟩

/-- Kernels from a left inverse: `Λ ∘ B ∘ A = A` gives `ker (B ∘ A) = ker A`. -/
theorem ker_comp_eq_of_left_inverse_BPRE {R X F G : Type*} [Semiring R] [AddCommMonoid X]
    [AddCommMonoid F] [AddCommMonoid G] [Module R X] [Module R F] [Module R G]
    (A : X →ₗ[R] F) (B : F →ₗ[R] G) (Λ : G →ₗ[R] F) (h : Λ.comp (B.comp A) = A) :
    LinearMap.ker (B.comp A) = LinearMap.ker A := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · intro hx
    have := congrArg (fun T : X →ₗ[R] F => T x) h
    simp only [LinearMap.comp_apply, hx, map_zero] at this
    exact this.symm
  · intro hx
    rw [hx, map_zero]

/-- **Kernels on the carrier (normed form).** If `λ ∘ Θ ∘ f = f` near `p` (`λ = φ_i ∘ κ_i`), with
`f` differentiable at `p`, `Θ` at `f p`, `λ` at `Θ (f p)`, then `ker D(Θ ∘ f)(p) = ker Df(p)`. -/
theorem ker_fderiv_comp_eq_of_local_left_inverse_BPRE {X H G : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : X → H} {Θ : H → G} {lam : G → H} {p : X}
    (hf : DifferentiableAt ℝ f p) (hΘ : DifferentiableAt ℝ Θ (f p))
    (hlam : DifferentiableAt ℝ lam (Θ (f p))) (hleft : (fun y => lam (Θ (f y))) =ᶠ[𝓝 p] f) :
    LinearMap.ker (fderiv ℝ (Θ ∘ f) p : X →ₗ[ℝ] G) = LinearMap.ker (fderiv ℝ f p : X →ₗ[ℝ] H) := by
  rw [fderiv_comp p hΘ hf]
  refine ker_comp_eq_of_left_inverse_BPRE (fderiv ℝ f p : X →ₗ[ℝ] H)
    (fderiv ℝ Θ (f p) : H →ₗ[ℝ] G) (fderiv ℝ lam (Θ (f p)) : G →ₗ[ℝ] H) ?_
  have h1 : fderiv ℝ (fun y => lam (Θ (f y))) p = fderiv ℝ f p := hleft.fderiv_eq
  have h2 : fderiv ℝ (fun y => lam (Θ (f y))) p =
      (fderiv ℝ lam (Θ (f p))).comp ((fderiv ℝ Θ (f p)).comp (fderiv ℝ f p)) := by
    have := (hlam.hasFDerivAt.comp p (hΘ.hasFDerivAt.comp p hf.hasFDerivAt)).fderiv
    exact this
  rw [h2] at h1
  ext x
  have := congrArg (fun T : X →L[ℝ] H => T x) h1
  simpa using this

/-- **The threshold-5 map in the chart `κ_i` is the stage map in that chart.** If `π E = Θ ∘ f`
on a set and `Θ` retains the coordinate, then `κ ∘ π E = κ ∘ f` there; so `π_jE` is a submersion
in the chart `κ_i` exactly where `f_j` is. -/
theorem chart_comp_final_eq_BPRE {M H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f πE : M → H) (Θ : H → H) (κ : H →L[ℝ] E)
    (U : Set M) (hfac : ∀ p ∈ U, πE p = Θ (f p)) (hret : ∀ p ∈ U, κ (Θ (f p)) = κ (f p)) :
    ∀ p ∈ U, κ (πE p) = κ (f p) := fun p hp => by rw [hfac p hp, hret p hp]

/-- **Return to the original threshold-5 domain.** At a source point with full marker
(`u(F' p) = R η(p)`, `v(F' p) = R`) and `|η(p)| < 5ℓ`, cumulative error `≤ cρ ≤ (5/4)cR`, the
plateau `f p ∈ Z`, and `(5/4)c < 1/10`, `(5/4)c ≤ ℓ/2`: the stage image lies in the marked patch
with strict slack, `f(U⁵) ⊆ V⁰`. -/
theorem mem_markedPatch_of_full_marker_BPRE {M H E : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E] (Z : Set H) (u : H →L[ℝ] E)
    (hu : ‖u‖ ≤ 1) (v : H →L[ℝ] ℝ) (hv : ‖v‖ ≤ 1) (f F' : M → H) (η : M → E) (ρ : M → ℝ)
    {R ℓ c : ℝ} (hR : 0 < R) (hc : 0 ≤ c) {p : M} (hZ : f p ∈ Z) (huF : u (F' p) = R • η p)
    (hvF : v (F' p) = R) (hη : ‖η p‖ < 5 * ℓ) (herr : ‖f p - F' p‖ ≤ c * ρ p)
    (hρ : ρ p ≤ 5 / 4 * R) (hsmall : 5 / 4 * c < 1 / 10) (hsmallℓ : 5 / 4 * c ≤ ℓ / 2) :
    f p ∈ markedPatch_BPRE Z u v R ℓ := by
  refine ⟨hZ, marker_gt_of_err_BPRE f F' v hv ρ hR hc hvF herr hρ hsmall, ?_⟩
  have h1 : ‖u (f p - F' p)‖ ≤ c * (5 / 4 * R) :=
    (u.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hu).trans
      (herr.trans (mul_le_mul_of_nonneg_left hρ hc)))
  have h2 : ‖u (F' p)‖ = R * ‖η p‖ := by
    rw [huF, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  have h3 : u (f p) = u (F' p) + u (f p - F' p) := by rw [map_sub]; abel
  have h4 := norm_add_le (u (F' p)) (u (f p - F' p))
  rw [← h3, h2] at h4
  nlinarith

end Carrier

section Assembly

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- **CGP08, stage two (naive data).** Third stage `Ψ₃ = adjustmentMap Q₃ P₃ ψ₃` with
`Q₃ ≤ Q₂`, `Q₃`-valued `P₃` and `π₂`-invariant cutoff; edge patches
`V_i = markedPatch_BPRE Z u_i v_i R_i ℓ_i` whose blocks kill `Q₃`, with CGP07's injectivity.
Then: `π₂ E = Θ₂ ∘ f₂` everywhere (`E = Ψ₃ ∘ g₂`, `f₂ = π₂ g₂`, `Θ₂ = Ψ₃`); `Θ₂` is injective on
`V₂⁰ = ⋃ V_i`; `Θ₂(V₂⁰) ∩ {marked i} = Θ₂(V_i)`; on `D₂ = B⁶ ∩ f₂⁻¹(V₂⁰)` the final fibre over
`Θ₂ w₀` is the stage fibre over `w₀`; and `κ_i ∘ π₂E = κ_i ∘ f₂` everywhere. -/
theorem cgp08_stage_two_BPRE {M ι : Type*} (Q₂ Q₃ : Submodule ℝ H) [Q₂.HasOrthogonalProjection]
    [Q₃.HasOrthogonalProjection] (h32 : Q₃ ≤ Q₂) {P₃ : H → H} (hP₃ : ∀ z, P₃ z ∈ Q₃)
    {ψ₃ : H → ℝ} (hψ : ∀ z, ψ₃ (Q₂.starProjection z) = ψ₃ z) (g₂ : M → H) (B6 : Set M)
    (Z : Set H) (u : ι → H →L[ℝ] E) (v : ι → H →L[ℝ] ℝ) (R ℓ : ι → ℝ)
    (hu : ∀ i, ∀ q ∈ Q₃, u i q = 0) (hv : ∀ i, ∀ q ∈ Q₃, v i q = 0)
    (hinj : ∀ i, InjOn (u i) (markedPatch_BPRE Z (u i) (v i) (R i) (ℓ i))) :
    (∀ p, Q₂.starProjection (adjustmentMap Q₃ P₃ ψ₃ (g₂ p)) =
      adjustmentMap Q₃ P₃ ψ₃ (Q₂.starProjection (g₂ p))) ∧
    InjOn (adjustmentMap Q₃ P₃ ψ₃) (⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k)) ∧
    (∀ i, adjustmentMap Q₃ P₃ ψ₃ '' (⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k)) ∩
        markedCondition_BPRE (u i) (v i) (R i) (ℓ i) =
      adjustmentMap Q₃ P₃ ψ₃ '' markedPatch_BPRE Z (u i) (v i) (R i) (ℓ i)) ∧
    (∀ w₀ ∈ ⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k),
      {p | p ∈ B6 ∩ (fun q => Q₂.starProjection (g₂ q)) ⁻¹'
          (⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k)) ∧
        Q₂.starProjection (adjustmentMap Q₃ P₃ ψ₃ (g₂ p)) = adjustmentMap Q₃ P₃ ψ₃ w₀} =
      {p | p ∈ B6 ∩ (fun q => Q₂.starProjection (g₂ q)) ⁻¹'
          (⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k)) ∧
        Q₂.starProjection (g₂ p) = w₀}) ∧
    ∀ i p, u i (Q₂.starProjection (adjustmentMap Q₃ P₃ ψ₃ (g₂ p))) =
      u i (Q₂.starProjection (g₂ p)) := by
  have hfac := stage_two_final_factor_BPRE Q₂ Q₃ h32 hP₃ hψ g₂
  have hret : ∀ i, ∀ w ∈ ⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k),
      u i (adjustmentMap Q₃ P₃ ψ₃ w) = u i w ∧ v i (adjustmentMap Q₃ P₃ ψ₃ w) = v i w :=
    fun i w _ => ⟨adjustmentMap_retains_block_BPRE Q₃ hP₃ ψ₃ (u i) (hu i) w,
      adjustmentMap_retains_block_BPRE Q₃ hP₃ ψ₃ (v i) (hv i) w⟩
  have hΘinj := injOn_theta_BPRE Z u v R ℓ _ hret hinj
  refine ⟨hfac, hΘinj, theta_image_inter_marked_BPRE Z u v R ℓ _ hret, fun w₀ hw₀ => ?_,
    fun i p => ?_⟩
  · exact rf_fiber_eq_BPRE (fun q => Q₂.starProjection (g₂ q))
      (fun q => Q₂.starProjection (adjustmentMap Q₃ P₃ ψ₃ (g₂ q))) _ _ B6 hΘinj
      (fun p _ _ => hfac p) hw₀
  · exact chart_comp_final_eq_BPRE (fun q => Q₂.starProjection (g₂ q))
      (fun q => Q₂.starProjection (adjustmentMap Q₃ P₃ ψ₃ (g₂ q))) _ (u i) univ
      (fun p _ => hfac p)
      (fun p _ => adjustmentMap_retains_block_BPRE Q₃ hP₃ ψ₃ (u i) (hu i) _) p trivial

/-- **CGP08, stage one (naive data).** `Θ₁ = Ψ₃ ∘ Ψ₂` (`Q₁ = H`, `f₁ = g₁`, `E = Ψ₃ Ψ₂ g₁`);
circle patches whose blocks kill `Q₂`, with CGP07's injectivity. Then `Θ₁` is injective on
`V₁⁰`, identifies the patches, has (RF) on `D₁ = B⁶ ∩ g₁⁻¹(V₁⁰)`, and `κ_i ∘ E = κ_i ∘ g₁`. -/
theorem cgp08_stage_one_BPRE {M ι : Type*} (Q₂ Q₃ : Submodule ℝ H) [Q₂.HasOrthogonalProjection]
    [Q₃.HasOrthogonalProjection] (h32 : Q₃ ≤ Q₂) {P₂ P₃ : H → H} (hP₂ : ∀ z, P₂ z ∈ Q₂)
    (hP₃ : ∀ z, P₃ z ∈ Q₃) (ψ₂ ψ₃ : H → ℝ) (g₁ : M → H) (B6 : Set M)
    (Z : Set H) (u : ι → H →L[ℝ] E) (v : ι → H →L[ℝ] ℝ) (R ℓ : ι → ℝ)
    (hu : ∀ i, ∀ q ∈ Q₂, u i q = 0) (hv : ∀ i, ∀ q ∈ Q₂, v i q = 0)
    (hinj : ∀ i, InjOn (u i) (markedPatch_BPRE Z (u i) (v i) (R i) (ℓ i))) :
    InjOn (fun w => adjustmentMap Q₃ P₃ ψ₃ (adjustmentMap Q₂ P₂ ψ₂ w))
      (⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k)) ∧
    (∀ i, (fun w => adjustmentMap Q₃ P₃ ψ₃ (adjustmentMap Q₂ P₂ ψ₂ w)) ''
        (⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k)) ∩
        markedCondition_BPRE (u i) (v i) (R i) (ℓ i) =
      (fun w => adjustmentMap Q₃ P₃ ψ₃ (adjustmentMap Q₂ P₂ ψ₂ w)) ''
        markedPatch_BPRE Z (u i) (v i) (R i) (ℓ i)) ∧
    (∀ w₀ ∈ ⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k),
      {p | p ∈ B6 ∩ g₁ ⁻¹' (⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k)) ∧
        adjustmentMap Q₃ P₃ ψ₃ (adjustmentMap Q₂ P₂ ψ₂ (g₁ p)) =
          adjustmentMap Q₃ P₃ ψ₃ (adjustmentMap Q₂ P₂ ψ₂ w₀)} =
      {p | p ∈ B6 ∩ g₁ ⁻¹' (⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k)) ∧ g₁ p = w₀}) ∧
    ∀ i p, u i (adjustmentMap Q₃ P₃ ψ₃ (adjustmentMap Q₂ P₂ ψ₂ (g₁ p))) = u i (g₁ p) := by
  have hret : ∀ i, ∀ w ∈ ⋃ k, markedPatch_BPRE Z (u k) (v k) (R k) (ℓ k),
      u i (adjustmentMap Q₃ P₃ ψ₃ (adjustmentMap Q₂ P₂ ψ₂ w)) = u i w ∧
        v i (adjustmentMap Q₃ P₃ ψ₃ (adjustmentMap Q₂ P₂ ψ₂ w)) = v i w :=
    fun i w _ => ⟨theta_one_retains_block_BPRE Q₂ Q₃ h32 hP₂ hP₃ ψ₂ ψ₃ (u i) (hu i) w,
      theta_one_retains_block_BPRE Q₂ Q₃ h32 hP₂ hP₃ ψ₂ ψ₃ (v i) (hv i) w⟩
  have hΘinj := injOn_theta_BPRE Z u v R ℓ _ hret hinj
  refine ⟨hΘinj, theta_image_inter_marked_BPRE Z u v R ℓ _ hret, fun w₀ hw₀ => ?_,
    fun i p => theta_one_retains_block_BPRE Q₂ Q₃ h32 hP₂ hP₃ ψ₂ ψ₃ (u i) (hu i) (g₁ p)⟩
  exact rf_fiber_eq_BPRE g₁ (fun q => adjustmentMap Q₃ P₃ ψ₃ (adjustmentMap Q₂ P₂ ψ₂ (g₁ q)))
    (fun w => adjustmentMap Q₃ P₃ ψ₃ (adjustmentMap Q₂ P₂ ψ₂ w)) _ B6 hΘinj
    (fun p _ _ => rfl) hw₀

end Assembly

end DifferentialGeometry.Geometry.Collapse
