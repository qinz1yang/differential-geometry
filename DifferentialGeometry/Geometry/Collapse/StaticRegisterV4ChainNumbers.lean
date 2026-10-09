import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4NbBinding
import DifferentialGeometry.Geometry.Fibration.ActualAdjustmentChoice

/-!
# Register V4's stage values ARE numbers of the GAF02 chain; `C_ρ` dominates the chain's

Lane C14-REG-CHAIN (review 66, D66-3 and D66-5). The chain object `Gaf02Chain P Kj Ξ Γ S eg c cw`
(`Fibration/ActualStageChain.lean`) is indexed by its numbers; its field `numbers` is GAF01's
CHOICE in the kernel's form. Here the register's OWN stage choice `st : ClosedStage
(earlyDataSharedV4 K)` (PR04–PR09: `c_j, Γ_j, Σ_j, e_j` with `ε_j = Ξ_j(Γ_j)`) is shown to satisfy
those inequalities verbatim, so the chain is built on the register's values (no second call of
GAF01's existence theorem, no small quantity chosen after the family).

* constants: `bcut ≥ b_gaf`, `L₀ ≥ L_gaf`, `κ ≤ κ_gaf`, `C = gafGraphConst` for
  `earlyDataSharedV4 K`;
* `chain_stage_step_RGC`, `chain_stage_zero_RGC`: the two arithmetic steps of GAF01's reverse
  choice;
* `ClosedStage.chain_numbers_RGC`: the field `numbers` of `Gaf02Chain` at
  `(Ξ_j(Γ_j), Γ, Σ, e, c)`;
* `ClosedStage.chain_ranges_RGC`: FC27's three test ranges and CFS15's modulus / interior condition
  at the register's stage values (the hypotheses of the stage tests and of the native output);
* `ClosedStage.chain_scaleConstant_le_RGC` (D66-5, register-level comparison BEFORE `Δ, Λ`): EDP01's
  chain constant `100(L_gaf+1)(1 + b_gaf + c_w^{(0)}/Σ₀)` with the register's first-stage weight
  constant `c_w^{(0)} = stageCwAt_V4C st 0` is at most the register's
  `C_ρ = closedScaleConstantV4 D T st` whenever `T.Nb = maxNb_V4C`, `T.cw = maxCw_V4C` (PR10).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped Topology
open GC.MetricGeometry DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

/-! ### The constants of `earlyDataSharedV4 K` against the native rows' constants -/

/-- `b_cut ≥ b_gaf` (`P ≥ P_cgp ≥ 1`). -/
theorem earlyDataSharedV4_bcut_ge_RGC (K : ℕ) :
    gafCutoffConstant ≤ (earlyDataSharedV4 K).bcut := by
  have hP1 : 1 ≤ cgpProfileBound := cgpProfileBound_spec.1
  have hPP : cgpProfileBound ≤ (earlyDataSharedV4 K).P :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h4 : cgpProfileBound ^ 4 ≤ (earlyDataSharedV4 K).P ^ 4 :=
    pow_le_pow_left₀ (by linarith) hPP 4
  have hN : (earlyDataSharedV4 K).N = gafMultiplicity := rfl
  rw [gafCutoffConstant, ClosedEarlyData.bcut, hN]
  have hpos : (0 : ℝ) ≤ 10 ^ 4 * ((gafMultiplicity : ℝ) + 1) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h4 hpos
  linarith

/-- `L₀ ≥ L_gaf`. -/
theorem earlyDataSharedV4_L₀_ge_RGC (K : ℕ) : gafDerivativeBound ≤ (earlyDataSharedV4 K).L₀ :=
  le_max_right _ _

/-- `κ ≤ κ_gaf`. -/
theorem earlyDataSharedV4_κ_le_RGC (K : ℕ) : (earlyDataSharedV4 K).κ ≤ gafKappa := by
  have hP1 : 1 ≤ cgpProfileBound := cgpProfileBound_spec.1
  have hPP : cgpProfileBound ≤ (earlyDataSharedV4 K).P :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h2 : cgpProfileBound ^ 2 ≤ (earlyDataSharedV4 K).P ^ 2 :=
    pow_le_pow_left₀ (by linarith) hPP 2
  have hN : (earlyDataSharedV4 K).N = gafMultiplicity := rfl
  rw [gafKappa, ClosedEarlyData.κ, hN]
  have hpos : (0 : ℝ) < 1000 * ((gafMultiplicity : ℝ) + 1) * cgpProfileBound ^ 2 := by
    positivity
  apply one_div_le_one_div_of_le hpos
  have hm : (0 : ℝ) ≤ 1000 * ((gafMultiplicity : ℝ) + 1) := by positivity
  exact mul_le_mul_of_nonneg_left h2 hm

/-! ### GAF01's two arithmetic steps -/

/-- **One later stage of GAF01's reverse choice** (stages `2, 3`): with `y = c₁/A`,
`A = 16(1 + b)(1 + L₀)`, `c₀ ≤ y`, `ε < y`, `ε ≤ 1/10`, `Σ ≤ 1/2`, `e < ΓΣ/100`, `Γ ≤ c₁/16`, the
tube budget `c₀ + ((5/3)εΣ + (1+ε)c₀) < c₁` and the derivative budget hold. -/
theorem chain_stage_step_RGC {bc L₀ gc L c₀ c₁ Ξ S e Γ : ℝ} (hbc : 0 ≤ bc) (hL₀ : 0 ≤ L₀)
    (hgc : 0 ≤ gc) (hgcb : gc ≤ bc) (hL : 0 ≤ L) (hLL : L ≤ L₀) (hc₀ : 0 ≤ c₀) (hc₀1 : c₀ ≤ 1)
    (hc₀c : c₀ ≤ c₁ / (16 * (1 + bc) * (1 + L₀))) (hΞ : 0 ≤ Ξ)
    (hΞc : Ξ < c₁ / (16 * (1 + bc) * (1 + L₀))) (hΞ1 : Ξ ≤ 1 / 10) (hS : 0 ≤ S) (hS1 : S ≤ 1 / 2)
    (hΓc : Γ ≤ c₁ / 16) (he : e < Γ * S / 100) :
    (c₀ + (5 / 3 * Ξ * S + (1 + Ξ) * c₀)) < c₁ ∧
      ((5 / 3 * Ξ * S + (1 + Ξ) * c₀) * gc * (L + c₀) + Ξ * (L + c₀) + e + 2 * c₀) < c₁ := by
  set A : ℝ := 16 * (1 + bc) * (1 + L₀) with hA
  set y : ℝ := c₁ / A with hy
  have hA16 : 16 ≤ A := by
    have h1 : 1 ≤ (1 + bc) * (1 + L₀) := by nlinarith
    rw [hA]
    nlinarith
  have hApos : 0 < A := by linarith
  have hc₁ : c₁ = A * y := by rw [hy]; field_simp
  have hy0 : 0 < y := lt_of_le_of_lt hΞ hΞc
  have hc₁pos : 0 < c₁ := by rw [hc₁]; positivity
  -- the factor `X = (5/3)ΞΣ + (1+Ξ)c₀ ≤ 2y`
  have hΞS : Ξ * S ≤ y * (1 / 2) := mul_le_mul hΞc.le hS1 hS hy0.le
  have h1Ξ : (1 + Ξ) * c₀ ≤ (11 / 10) * y :=
    mul_le_mul (by linarith) hc₀c hc₀ (by norm_num)
  have hX : 5 / 3 * Ξ * S + (1 + Ξ) * c₀ ≤ 2 * y := by nlinarith
  have hX0 : 0 ≤ 5 / 3 * Ξ * S + (1 + Ξ) * c₀ := by positivity
  -- `gc (L + c₀) ≤ bc (L₀ + 1)`
  have hgL : gc * (L + c₀) ≤ bc * (L₀ + 1) :=
    mul_le_mul hgcb (by linarith) (by linarith) hbc
  have hgL0 : 0 ≤ gc * (L + c₀) := by positivity
  have hXg : (5 / 3 * Ξ * S + (1 + Ξ) * c₀) * gc * (L + c₀) ≤ 2 * y * (bc * (L₀ + 1)) := by
    rw [mul_assoc]
    exact mul_le_mul hX hgL hgL0 (by linarith)
  have hbL : 2 * y * (bc * (L₀ + 1)) ≤ c₁ / 8 := by
    rw [hc₁, hA]
    have : bc * (L₀ + 1) ≤ (1 + bc) * (1 + L₀) := by nlinarith
    nlinarith
  have hΞL : Ξ * (L + c₀) ≤ y * (L₀ + 1) :=
    mul_le_mul hΞc.le (by linarith) (by linarith) hy0.le
  have hyL : y * (L₀ + 1) ≤ c₁ / 16 := by
    rw [hc₁, hA]
    have : (L₀ + 1) ≤ (1 + bc) * (1 + L₀) := by nlinarith
    nlinarith
  have hΓS : Γ * S ≤ c₁ / 16 * (1 / 2) := mul_le_mul hΓc hS1 hS (by linarith)
  have hy16 : y ≤ c₁ / 16 := by
    rw [hc₁]
    nlinarith
  refine ⟨by linarith, by linarith⟩

/-- **The first stage of GAF01's reverse choice**: with `ε < c/A`, `Σ ≤ 1/2`, `e < ΓΣ/100`,
`Γ ≤ c/16`: `(5/3)εΣ < c` and the derivative budget `(5/3)εΣ b_gaf L_gaf + εL_gaf + e < c`. -/
theorem chain_stage_zero_RGC {bc L₀ gc L c Ξ S e Γ : ℝ} (hbc : 0 ≤ bc) (hL₀ : 0 ≤ L₀)
    (hgc : 0 ≤ gc) (hgcb : gc ≤ bc) (hL : 0 ≤ L) (hLL : L ≤ L₀) (hΞ : 0 ≤ Ξ)
    (hΞc : Ξ < c / (16 * (1 + bc) * (1 + L₀))) (hS : 0 ≤ S) (hS1 : S ≤ 1 / 2) (hΓ : 0 ≤ Γ)
    (hΓc : Γ ≤ c / 16) (he : e < Γ * S / 100) :
    5 / 3 * Ξ * S < c ∧ (5 / 3 * Ξ * S * gc * L + Ξ * L + e) < c := by
  set A : ℝ := 16 * (1 + bc) * (1 + L₀) with hA
  set y : ℝ := c / A with hy
  have hA16 : 16 ≤ A := by
    have h1 : 1 ≤ (1 + bc) * (1 + L₀) := by nlinarith
    rw [hA]
    nlinarith
  have hApos : 0 < A := by linarith
  have hc : c = A * y := by rw [hy]; field_simp
  have hy0 : 0 < y := lt_of_le_of_lt hΞ hΞc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hΞS : Ξ * S ≤ y * (1 / 2) := mul_le_mul hΞc.le hS1 hS hy0.le
  have hgL : gc * L ≤ bc * L₀ := mul_le_mul hgcb hLL hL hbc
  have hgL0 : 0 ≤ gc * L := by positivity
  have hXg : 5 / 3 * Ξ * S * gc * L ≤ 5 / 3 * (y * (1 / 2)) * (bc * L₀) := by
    have h := mul_le_mul hΞS hgL hgL0 (by positivity)
    nlinarith
  have hbL : 5 / 3 * (y * (1 / 2)) * (bc * L₀) ≤ c / 16 := by
    rw [hc, hA]
    have : bc * L₀ ≤ (1 + bc) * (1 + L₀) := by nlinarith
    nlinarith
  have hΞL : Ξ * L ≤ y * L₀ := mul_le_mul hΞc.le hLL hL hy0.le
  have hyL : y * L₀ ≤ c / 16 := by
    rw [hc, hA]
    have : L₀ ≤ (1 + bc) * (1 + L₀) := by nlinarith
    nlinarith
  have hΓS : Γ * S ≤ c / 16 * (1 / 2) := mul_le_mul hΓc hS1 hS (by linarith)
  have hy16 : y ≤ c / 16 := by
    rw [hc]
    nlinarith
  refine ⟨by linarith, by linarith⟩

/-! ### The register's stage values satisfy the chain's `numbers` -/

namespace ClosedStage

variable {K : ℕ} (st : ClosedStage (earlyDataSharedV4 K))

/-- The bounds of a stage value read off the register (`Ξ_j < min{1/10, c_j/A}`, `Σ_j < min{1/2,
Ξ_j/10⁴, Γ_j/200, Γ_j³/(100C_j)}`, `e_j < min{1/100, Γ_jΣ_j/100, Σ_j/1000}`, `Γ_j ≤ c_j/16`). -/
theorem stage_bounds_RGC (j : Fin 3) :
    0 < (earlyDataSharedV4 K).Ξ j (st.Γ j) ∧ (earlyDataSharedV4 K).Ξ j (st.Γ j) < 1 / 10 ∧
      (earlyDataSharedV4 K).Ξ j (st.Γ j) < st.c j / (16 * (1 + (earlyDataSharedV4 K).bcut) *
        (1 + (earlyDataSharedV4 K).L₀)) ∧
      0 < st.Sig j ∧ st.Sig j < 1 / 2 ∧ st.Sig j < (earlyDataSharedV4 K).Ξ j (st.Γ j) / 10000 ∧
      st.Sig j < st.Γ j / 200 ∧ st.Sig j < st.Γ j ^ 3 / (100 * gafGraphConst j) ∧
      0 < st.e j ∧ st.e j < 1 / 100 ∧ st.e j < st.Γ j * st.Sig j / 100 ∧
      st.e j < st.Sig j / 1000 ∧ 0 < st.Γ j ∧ st.Γ j ≤ st.c j / 16 ∧ 0 < st.c j := by
  have hΞ := st.Ξ_lt j
  have hS := st.Sig_lt j
  have he := st.e_lt j
  unfold closedAccuracyBound ClosedEarlyData.α at hΞ
  unfold closedSigmaBound at hS
  unfold closedErrorBound at he
  simp only [lt_min_iff] at hΞ hS he
  exact ⟨(earlyDataSharedV4 K).Ξ_pos j (st.Γ j) (st.Γ_pos j), hΞ.1, hΞ.2.1.1, st.Sig_pos j,
    hS.1, hS.2.1, hS.2.2.1, hS.2.2.2, st.e_pos j, he.1, he.2.1, he.2.2.1, st.Γ_pos j, st.Γ_le j,
    st.c_pos j⟩

/-- The reverse-choice bounds of the targets: `c₁ ≤ min{c₂/A, 3Σ₂/10, 4κ/5, 1/512}`,
`c₂ ≤ min{c₃/A, 3Σ₃/10, 4κ/5, 1/512}`, `c₃ < 1/512` (stage indices `0, 1, 2`). -/
theorem target_bounds_RGC :
    st.c 0 ≤ st.c 1 / (16 * (1 + (earlyDataSharedV4 K).bcut) * (1 + (earlyDataSharedV4 K).L₀)) ∧
      st.c 0 ≤ 3 * st.Sig 1 / 10 ∧ st.c 0 ≤ 4 * (earlyDataSharedV4 K).κ / 5 ∧
      st.c 0 ≤ 1 / 512 ∧
      st.c 1 ≤ st.c 2 / (16 * (1 + (earlyDataSharedV4 K).bcut) *
        (1 + (earlyDataSharedV4 K).L₀)) ∧
      st.c 1 ≤ 3 * st.Sig 2 / 10 ∧ st.c 1 ≤ 4 * (earlyDataSharedV4 K).κ / 5 ∧
      st.c 1 ≤ 1 / 512 ∧ st.c 2 < 1 / 512 := by
  have h1 := st.c₁_le
  have h2 := st.c₂_le
  have h3 := st.c₃_lt
  unfold closedNextTargetBound stageT ClosedEarlyData.α at h1 h2
  unfold closedC₃Bound at h3
  simp only [le_min_iff] at h1 h2
  simp only [lt_min_iff] at h3
  exact ⟨h1.2.1.2.1.1, h1.2.1.1, h1.2.2.1, h1.2.2.2.2, h2.2.1.2.1.1, h2.2.1.1, h2.2.2.1,
    h2.2.2.2.2, h3.1.2.2⟩

/-- **The register's stage values satisfy the chain's `numbers` field** (GAF01's CHOICE in the
kernel's form) at `Ξ_j = Ξ_j(Γ_j)`, `Γ`, `Σ`, `e`, `c`. -/
theorem chain_numbers_RGC :
    (∀ j, 0 < (earlyDataSharedV4 K).Ξ j (st.Γ j) ∧ 0 < st.Sig j ∧
        128 * ((earlyDataSharedV4 K).Ξ j (st.Γ j))⁻¹ * st.Sig j ≤ 1 / 5 ∧ 0 ≤ st.e j) ∧
      5 / 3 * (earlyDataSharedV4 K).Ξ 0 (st.Γ 0) * st.Sig 0 < st.c 0 ∧ st.c 0 ≤ 1 / 512 ∧
      (5 / 3 * (earlyDataSharedV4 K).Ξ 0 (st.Γ 0) * st.Sig 0 * gafCutoffConstant *
          gafDerivativeBound + (earlyDataSharedV4 K).Ξ 0 (st.Γ 0) * gafDerivativeBound +
          st.e 0) < st.c 0 ∧
      st.c 0 ≤ 4 * gafKappa / 5 ∧ st.c 0 ≤ 3 * st.Sig 1 / 10 ∧
      (st.c 0 + (5 / 3 * (earlyDataSharedV4 K).Ξ 1 (st.Γ 1) * st.Sig 1 +
          (1 + (earlyDataSharedV4 K).Ξ 1 (st.Γ 1)) * st.c 0)) < st.c 1 ∧ st.c 1 ≤ 1 / 512 ∧
      ((5 / 3 * (earlyDataSharedV4 K).Ξ 1 (st.Γ 1) * st.Sig 1 +
          (1 + (earlyDataSharedV4 K).Ξ 1 (st.Γ 1)) * st.c 0) * gafCutoffConstant *
          (gafDerivativeBound + st.c 0) +
          (earlyDataSharedV4 K).Ξ 1 (st.Γ 1) * (gafDerivativeBound + st.c 0) + st.e 1 +
          2 * st.c 0) < st.c 1 ∧
      st.c 1 ≤ 4 * gafKappa / 5 ∧ st.c 1 ≤ 3 * st.Sig 2 / 10 ∧
      (st.c 1 + (5 / 3 * (earlyDataSharedV4 K).Ξ 2 (st.Γ 2) * st.Sig 2 +
          (1 + (earlyDataSharedV4 K).Ξ 2 (st.Γ 2)) * st.c 1)) < st.c 2 ∧ st.c 2 ≤ 1 / 512 ∧
      ((5 / 3 * (earlyDataSharedV4 K).Ξ 2 (st.Γ 2) * st.Sig 2 +
          (1 + (earlyDataSharedV4 K).Ξ 2 (st.Γ 2)) * st.c 1) * gafCutoffConstant *
          (gafDerivativeBound + st.c 1) +
          (earlyDataSharedV4 K).Ξ 2 (st.Γ 2) * (gafDerivativeBound + st.c 1) + st.e 2 +
          2 * st.c 1) < st.c 2 := by
  have hb := earlyDataSharedV4_bcut_ge_RGC K
  have hL := earlyDataSharedV4_L₀_ge_RGC K
  have hκ := earlyDataSharedV4_κ_le_RGC K
  have hgc := gafCutoffConstant_nonneg
  have hLg : 0 ≤ gafDerivativeBound := by linarith only [one_le_gafDerivativeBound]
  have hbc : 0 ≤ (earlyDataSharedV4 K).bcut := hgc.trans hb
  have hL₀ : 0 ≤ (earlyDataSharedV4 K).L₀ := hLg.trans hL
  obtain ⟨hc01, hc0S, hc0κ, hc0, hc12, hc1S, hc1κ, hc1, hc2⟩ := st.target_bounds_RGC
  obtain ⟨hΞ0p, hΞ01, hΞ0c, hS0p, hS01, -, -, -, -, -, he0, -, hΓ0p, hΓ0c, -⟩ :=
    st.stage_bounds_RGC 0
  obtain ⟨hΞ1p, hΞ11, hΞ1c, hS1p, hS11, -, -, -, -, -, he1, -, hΓ1p, hΓ1c, -⟩ :=
    st.stage_bounds_RGC 1
  obtain ⟨hΞ2p, hΞ21, hΞ2c, hS2p, hS21, -, -, -, -, -, he2, -, hΓ2p, hΓ2c, -⟩ :=
    st.stage_bounds_RGC 2
  have hc0p := st.c_pos 0
  have hc1p := st.c_pos 1
  have k0 := chain_stage_zero_RGC hbc hL₀ hgc hb hLg hL hΞ0p.le hΞ0c hS0p.le hS01.le hΓ0p.le
    hΓ0c he0
  have k1 := chain_stage_step_RGC hbc hL₀ hgc hb hLg hL hc0p.le (by linarith) hc01 hΞ1p.le hΞ1c
    hΞ11.le hS1p.le hS11.le hΓ1c he1
  have k2 := chain_stage_step_RGC hbc hL₀ hgc hb hLg hL hc1p.le (by linarith) hc12 hΞ2p.le hΞ2c
    hΞ21.le hS2p.le hS21.le hΓ2c he2
  have hmo : ∀ j, 128 * ((earlyDataSharedV4 K).Ξ j (st.Γ j))⁻¹ * st.Sig j ≤ 1 / 5 := fun j => by
    obtain ⟨hΞp, -, -, -, -, hSΞ, -⟩ := st.stage_bounds_RGC j
    have h1 : 128 * ((earlyDataSharedV4 K).Ξ j (st.Γ j))⁻¹ * st.Sig j ≤
        128 * ((earlyDataSharedV4 K).Ξ j (st.Γ j))⁻¹ * ((earlyDataSharedV4 K).Ξ j (st.Γ j) /
          10000) :=
      mul_le_mul_of_nonneg_left hSΞ.le (mul_nonneg (by norm_num) (inv_nonneg.mpr hΞp.le))
    have h2 : 128 * ((earlyDataSharedV4 K).Ξ j (st.Γ j))⁻¹ *
        ((earlyDataSharedV4 K).Ξ j (st.Γ j) / 10000) = 128 / 10000 := by
      field_simp
    linarith
  exact ⟨fun j => ⟨(st.stage_bounds_RGC j).1, st.Sig_pos j, hmo j, (st.e_pos j).le⟩, k0.1, hc0,
    k0.2, hc0κ.trans (by linarith), hc0S, k1.1, hc1, k1.2, hc1κ.trans (by linarith), hc1S, k2.1,
    hc2.le, k2.2⟩

/-- **FC27's three test ranges and CFS15's modulus at the register's stage values**: `Γ_j < 1`,
`Σ_j < Γ_j/200`, `Σ_j < Γ_j³/(100C_j)` with the graph moduli `(C_TCP, C_EGP, C_SGP)`,
`e_j < min{1/100, Γ_jΣ_j/100, Σ_j/1000}`, CFS15's jet-order-`K` modulus at `Γ_j`, and CFS12's
interior condition at the buffer `Ξ_j(Γ_j)⁻¹`. -/
theorem chain_ranges_RGC (j : Fin 3) :
    0 < st.Γ j ∧ st.Γ j < 1 ∧ 0 < st.Sig j ∧ st.Sig j < st.Γ j / 200 ∧
      st.Sig j < st.Γ j ^ 3 / (100 * gafGraphConst j) ∧ 0 < st.e j ∧ st.e j < 1 / 100 ∧
      st.e j < st.Γ j * st.Sig j / 100 ∧ st.e j < st.Sig j / 1000 ∧
      Cfs15ModulusAtV2 (gafStageDim j) K (5 / 3) ((earlyDataSharedV4 K).Ξ j) (st.Γ j) ∧
      st.Γ j * ((80 * (5 / 3) + 31) * ((earlyDataSharedV4 K).Ξ j (st.Γ j))⁻¹ + 2) < 1 := by
  obtain ⟨-, -, -, hSp, -, -, hSΓ, hSC, hep, he1, heΓ, heS, hΓp, hΓc, -⟩ := st.stage_bounds_RGC j
  obtain ⟨-, -, -, hc0, -, -, -, hc1, hc2⟩ := st.target_bounds_RGC
  have hcj : st.c j ≤ 1 / 512 := by
    fin_cases j
    · exact hc0
    · exact hc1
    · exact hc2.le
  exact ⟨hΓp, by linarith, hSp, hSΓ, hSC, hep, he1, heΓ, heS,
    (earlyDataSharedV4_fields_VAL6 K).2.2.2.2.2.2.1 st j,
    (earlyDataSharedV4_stage_mean_VAL6 st j).1⟩

/-- `Σ₁ ≤ ε₁/10⁴` (EDP01's numeric input from the same stage choice). -/
theorem sig_zero_le_RGC : st.Sig 0 ≤ (earlyDataSharedV4 K).Ξ 0 (st.Γ 0) / 10000 :=
  (st.stage_bounds_RGC 0).2.2.2.2.2.1.le

end ClosedStage

/-! ### D66-5: the register's `C_ρ` dominates the chain's EDP01 constant -/

/-- The first stage multiplicity is at least one. -/
theorem one_le_stageNbAt_zero_RGC {D : ClosedEarlyData} (st : ClosedStage D) :
    1 ≤ stageNbAt_V4C st 0 := by
  unfold stageNbAt_V4C
  have hb := st.one_le_stageBufferAt_V4C 0
  have h1 : (1 : ℝ) ≤ (1 + 2 * (5 / 3) * 165 * stageBufferAt_V4C st 0) ^ gafStageDim 0 :=
    one_le_pow₀ (by linarith)
  exact h1.trans (Nat.le_ceil _)

/-- **Domination of EDP01's chain constant by the register's `C_ρ`** (D66-5; derived at the stage,
BEFORE `Δ, Λ`): with PR10's binding `T.Nb = maxNb_V4C`, `T.cw = maxCw_V4C`, the constant
`100(L_gaf + 1)(1 + b_gaf + 1·c_w^{(0)}/Σ₀)` of `Gaf02Chain.edp01_GAF8` at the register's
first-stage weight constant `c_w^{(0)} = stageCwAt_V4C st 0` is at most
`closedScaleConstantV4 D T st`. -/
theorem ClosedStage.chain_scaleConstant_le_RGC {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)} (hNb : T.Nb = maxNb_V4C)
    (hcw : T.cw = maxCw_V4C) (st : ClosedStage (earlyDataSharedV4 K)) :
    100 * (gafDerivativeBound + 1) *
        (1 + gafCutoffConstant + 1 * stageCwAt_V4C st 0 / st.Sig 0) ≤
      closedScaleConstantV4 (earlyDataSharedV4 K) T st := by
  unfold closedScaleConstantV4
  rw [hNb, hcw]
  have hS := st.Sig_pos 0
  have hcw0 := stageCwAt_nonneg_V4C st 0
  have hcm := stageCwAt_le_max_V4C st 0
  have hnm := stageNbAt_le_max_V4C st 0
  have hn1 := one_le_stageNbAt_zero_RGC st
  have hmc : 0 ≤ maxCw_V4C st := maxCw_nonneg_V4C st
  have hprod : 1 * stageCwAt_V4C st 0 ≤ maxNb_V4C st * maxCw_V4C st :=
    mul_le_mul (hn1.trans hnm) hcm hcw0 (by linarith)
  have hdiv : 1 * stageCwAt_V4C st 0 / st.Sig 0 ≤ maxNb_V4C st * maxCw_V4C st / st.Sig 0 :=
    div_le_div_of_nonneg_right hprod hS.le
  have hb := earlyDataSharedV4_bcut_ge_RGC K
  have hL := earlyDataSharedV4_L₀_ge_RGC K
  have hLg := one_le_gafDerivativeBound
  have hgc := gafCutoffConstant_nonneg
  have h1 : 1 + gafCutoffConstant + 1 * stageCwAt_V4C st 0 / st.Sig 0 ≤
      1 + (earlyDataSharedV4 K).bcut + maxNb_V4C st * maxCw_V4C st / st.Sig 0 := by linarith
  have h0 : 0 ≤ 1 + gafCutoffConstant + 1 * stageCwAt_V4C st 0 / st.Sig 0 := by
    have : 0 ≤ 1 * stageCwAt_V4C st 0 / st.Sig 0 := div_nonneg (by linarith) hS.le
    linarith
  have h2 : 100 * (gafDerivativeBound + 1) ≤ 100 * ((earlyDataSharedV4 K).L₀ + 1) := by linarith
  exact mul_le_mul h2 h1 h0 (by linarith)

/-- The stage radii increase: `Σ₀ < Σ₁ < Σ₂` (from `Σ_j < Γ_j/200`, `Γ_j ≤ c_j/16`,
`c_j ≤ 3Σ_{j+1}/10`). -/
theorem ClosedStage.sig_lt_RGC {K : ℕ} (st : ClosedStage (earlyDataSharedV4 K)) :
    st.Sig 0 < st.Sig 1 ∧ st.Sig 1 < st.Sig 2 := by
  obtain ⟨-, hc0S, -, -, -, hc1S, -, -, -⟩ := st.target_bounds_RGC
  obtain ⟨-, -, -, -, -, -, hS0, -, -, -, -, -, -, hΓ0, -⟩ := st.stage_bounds_RGC 0
  obtain ⟨-, -, -, -, -, -, hS1, -, -, -, -, -, -, hΓ1, -⟩ := st.stage_bounds_RGC 1
  have h1 := st.Sig_pos 1
  have h2 := st.Sig_pos 2
  constructor <;> linarith

/-- **Domination of every stage output's (SMV) constant by the register's `C_ρ`** (D66-5): the
native output of stage `j` (`ClosedStage.stageOutput_RGC`, weight constant `c_w^{(j)}`, radius
`Σ_jρ ∘ sel`) has (SMV) `‖ℓ ∘ Da‖ ≤ 2c_w^{(j)}β/(Σ_jρ)`; its constant `2c_w^{(j)}/Σ_j` is at most
`C_ρ/100`, `C_ρ = closedScaleConstantV4 D T st` with PR10's `T.Nb = maxNb_V4C`, `T.cw = maxCw_V4C`
(fixed at the stage, before `Δ, Λ`). -/
theorem ClosedStage.smv_le_scaleConstant_RGC {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)} (hNb : T.Nb = maxNb_V4C)
    (hcw : T.cw = maxCw_V4C) (st : ClosedStage (earlyDataSharedV4 K)) (j : Fin 3) :
    2 * stageCwAt_V4C st j / st.Sig j ≤ closedScaleConstantV4 (earlyDataSharedV4 K) T st / 100 := by
  unfold closedScaleConstantV4
  rw [hNb, hcw]
  have hS0 := st.Sig_pos 0
  have hSj := st.Sig_pos j
  have hS0j : st.Sig 0 ≤ st.Sig j := by
    obtain ⟨h01, h12⟩ := st.sig_lt_RGC
    fin_cases j
    · exact le_rfl
    · exact h01.le
    · exact (h01.trans h12).le
  have hcwj := stageCwAt_nonneg_V4C st j
  have hcm := stageCwAt_le_max_V4C st j
  have hnm := stageNbAt_le_max_V4C st 0
  have hn1 := one_le_stageNbAt_zero_RGC st
  have hmc : 0 ≤ maxCw_V4C st := maxCw_nonneg_V4C st
  have hprod : stageCwAt_V4C st j ≤ maxNb_V4C st * maxCw_V4C st := by
    have := mul_le_mul (hn1.trans hnm) hcm hcwj (by linarith)
    linarith
  have hd1 : stageCwAt_V4C st j / st.Sig j ≤ stageCwAt_V4C st j / st.Sig 0 :=
    div_le_div_of_nonneg_left hcwj hS0 hS0j
  have hd2 : stageCwAt_V4C st j / st.Sig 0 ≤ maxNb_V4C st * maxCw_V4C st / st.Sig 0 :=
    div_le_div_of_nonneg_right hprod hS0.le
  have hb : 0 ≤ (earlyDataSharedV4 K).bcut :=
    gafCutoffConstant_nonneg.trans (earlyDataSharedV4_bcut_ge_RGC K)
  have hL : 1 ≤ (earlyDataSharedV4 K).L₀ := (earlyDataSharedV4 K).one_le_L₀
  have hq : 0 ≤ maxNb_V4C st * maxCw_V4C st / st.Sig 0 :=
    div_nonneg (mul_nonneg (maxNb_nonneg_V4C st) hmc) hS0.le
  have h2 : 2 * stageCwAt_V4C st j / st.Sig j = 2 * (stageCwAt_V4C st j / st.Sig j) := by ring
  rw [h2]
  have hX : 2 * (maxNb_V4C st * maxCw_V4C st / st.Sig 0) ≤
      100 * ((earlyDataSharedV4 K).L₀ + 1) *
        (1 + (earlyDataSharedV4 K).bcut + maxNb_V4C st * maxCw_V4C st / st.Sig 0) / 100 := by
    have : 2 * (1 + (earlyDataSharedV4 K).bcut + maxNb_V4C st * maxCw_V4C st / st.Sig 0) ≤
        ((earlyDataSharedV4 K).L₀ + 1) *
          (1 + (earlyDataSharedV4 K).bcut + maxNb_V4C st * maxCw_V4C st / st.Sig 0) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have e : 100 * ((earlyDataSharedV4 K).L₀ + 1) *
        (1 + (earlyDataSharedV4 K).bcut + maxNb_V4C st * maxCw_V4C st / st.Sig 0) / 100 =
        ((earlyDataSharedV4 K).L₀ + 1) *
          (1 + (earlyDataSharedV4 K).bcut + maxNb_V4C st * maxCw_V4C st / st.Sig 0) := by ring
    rw [e]
    linarith
  linarith

end DifferentialGeometry.Geometry.Collapse
