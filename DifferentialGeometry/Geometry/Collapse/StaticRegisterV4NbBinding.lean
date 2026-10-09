import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4Staged

/-!
# Register V4: ONE `N_b, c_w` binding for every stage, `C_ρ` and the `inf` constants
(lane FC39-V4C; external reviews 57 item 4 and 60 "CFS11")

**The constant.** CFS11 as delivered (`nb_cw_stage_selection_GAFS3`) is the RELAXED version: its
multiplicity bound is `N_b = ⌈(1 + 550 b)^{k}⌉` with the listed-index radius `165 b r`
(`2·(5/3)·165 = 550`; `165 > 80·(5/3) + 31 = 493/3`), not the sharp `(1 + (4930/9) b)^{k}`
(`2·(5/3)·(493/3) = 4930/9`). Review 60 accepts the coarse version on the condition that the
register's `N_b` slot, `C_ρ = 100(L₀+1)(1 + b_cut + N_b c_w/Σ₁)` and every later budget use the
SAME `N_b`. No Lean file of the tree uses the sharp constant (checked 2026-10-05 09:30), so the
binding is to the delivered `165` version.

**Per stage (review 57, item 4: PR10 read `N_b, c_w` at the first stage only).** This file records
`N_b^{(j)} = ⌈(1 + 550 b_j)^{k_j}⌉`, `c_w^{(j)}` (the weight constant of
`nb_cw_stage_selection_GAFS3` at `(j, b_j)`) with `b_j = Ξ_j(Γ_j)⁻¹` for each of the three stages
and takes the MAXIMA
`maxNb_V4C`, `maxCw_V4C`; the stage-cloud conclusions of CFS11–CFS12 hold at EVERY stage with these
maxima (`nb_cw_slots_max_V4C`), and the strategy `rowsStrategyNbMaxV4C D` puts them in the slots,
so the register's `C_ρ` dominates every stage.

**Cloud-cover `N_b` versus the whole-support count.** `T.Nb` (PR10) bounds the number of listed
stage-cloud balls meeting a ball of the cloud (CFS11). The early `N` of PR01 (`D.N`, bound by
`gafMultiplicity` in the validity record and, for TCP01's whole closed-support list, by lane
C14-COUNT's `N_TCP`) is a different slot; neither is used for the other.

**The `inf` of two strategies (review 60, §6.7).** `ClosedThresholdsV4.inf U₁ U₂` takes `N_b, c_w,
I₁`, LPA02's output and `H` from `U₁` (`inf_constants_V4C`), and `ClosedStrategyBelowV4` does not
mention these five, so a consumer that only reads "below" never reads them. Joint use is covered as
follows: in `rowsStrategyV4 = (scale ⊓ partialRows) ⊓ circleRows` all three records have `N_b = c_w
= 0`, LPA02 output `V = T₀` and `H α = α` (`rowsStrategyV4_constants_V4C`: the left choice equals
every component), `I₁` is the scale record's `∫₀¹ sinh²` (the two row records carry the unread
placeholder `1`); the final strategy fixes `N_b, c_w, I₁` by the realization's `Refines` equalities
(`Nb_eq`, `cw_eq`, `I₁_eq`) and REPLACES LPA02's output and `H` by the realization's own. For
`C_ρ` an explicit domination is proved: if the left record's `N_b, c_w` dominate the right
record's, the meet's `C_ρ` dominates the right record's, so the budget `C_ρ Δ Λ < 10⁻⁶` at the meet
gives it for the right record (`closedScaleConstantV4_inf_ge_right_V4C`,
`regScale_Cρ_of_le_V4C`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ### The delivered constant -/

/-- CFS11's delivered constant is the relaxed one: `2·(5/3)·165 = 550`. -/
theorem cfs11_relaxed_constant_V4C : (2 * (5 / 3) * 165 : ℝ) = 550 := by norm_num

/-- The relaxed listed-index radius `165` exceeds the sharp `80·(5/3) + 31 = 493/3`. -/
theorem cfs11_relaxed_radius_V4C : (80 * (5 / 3) + 31 : ℝ) < 165 := by norm_num

/-- The sharp constant would be `2·(5/3)·(80·(5/3) + 31) = 4930/9 < 550`: the relaxed `N_b`
dominates the sharp one at every buffer `b ≥ 0` and dimension `k`. -/
theorem cfs11_sharp_le_relaxed_V4C {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    (1 + 2 * (5 / 3) * (80 * (5 / 3) + 31) * b) ^ k ≤ (1 + 2 * (5 / 3) * 165 * b) ^ k := by
  apply pow_le_pow_left₀ (by positivity)
  nlinarith

/-! ### Per-stage buffers and constants -/

/-- Stage `j`'s buffer `b_j = Ξ_j(Γ_j)⁻¹` (B:10108–10113). -/
def stageBufferAt_V4C {D : ClosedEarlyData} (st : ClosedStage D) (j : Fin 3) : ℝ :=
  (D.Ξ j (st.Γ j))⁻¹

theorem ClosedStage.one_le_stageBufferAt_V4C {D : ClosedEarlyData} (st : ClosedStage D)
    (j : Fin 3) : 1 ≤ stageBufferAt_V4C st j := by
  have hpos := D.Ξ_pos j (st.Γ j) (st.Γ_pos j)
  have hlt : D.Ξ j (st.Γ j) < 1 / 10 := (st.Ξ_lt j).trans_le (min_le_left _ _)
  exact one_le_inv₀ hpos |>.mpr (by linarith)

/-- Stage `j`'s cloud multiplicity `N_b^{(j)} = ⌈(1 + 550 b_j)^{k_j}⌉` (CFS11, relaxed). -/
def stageNbAt_V4C {D : ClosedEarlyData} (st : ClosedStage D) (j : Fin 3) : ℝ :=
  (⌈(1 + 2 * (5 / 3) * 165 * stageBufferAt_V4C st j) ^ gafStageDim j⌉₊ : ℝ)

/-- Stage `j`'s weight constant `c_w^{(j)}` (CFS12, `nb_cw_stage_selection_GAFS3` at `(j, b_j)`). -/
def stageCwAt_V4C {D : ClosedEarlyData} (st : ClosedStage D) (j : Fin 3) : ℝ :=
  Classical.choose nb_cw_stage_selection_GAFS3 j (stageBufferAt_V4C st j)

theorem stageCwAt_nonneg_V4C {D : ClosedEarlyData} (st : ClosedStage D) (j : Fin 3) :
    0 ≤ stageCwAt_V4C st j :=
  (Classical.choose_spec nb_cw_stage_selection_GAFS3 j (stageBufferAt_V4C st j)
    (st.one_le_stageBufferAt_V4C j)).1

/-- PR10's `N_b`: the maximum of the three stage multiplicities. -/
def maxNb_V4C {D : ClosedEarlyData} (st : ClosedStage D) : ℝ :=
  max (stageNbAt_V4C st 0) (max (stageNbAt_V4C st 1) (stageNbAt_V4C st 2))

/-- PR10's `c_w`: the maximum of the three stage weight constants. -/
def maxCw_V4C {D : ClosedEarlyData} (st : ClosedStage D) : ℝ :=
  max (stageCwAt_V4C st 0) (max (stageCwAt_V4C st 1) (stageCwAt_V4C st 2))

theorem stageNbAt_le_max_V4C {D : ClosedEarlyData} (st : ClosedStage D) (j : Fin 3) :
    stageNbAt_V4C st j ≤ maxNb_V4C st := by
  unfold maxNb_V4C
  fin_cases j
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem stageCwAt_le_max_V4C {D : ClosedEarlyData} (st : ClosedStage D) (j : Fin 3) :
    stageCwAt_V4C st j ≤ maxCw_V4C st := by
  unfold maxCw_V4C
  fin_cases j
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem maxNb_nonneg_V4C {D : ClosedEarlyData} (st : ClosedStage D) : 0 ≤ maxNb_V4C st :=
  (Nat.cast_nonneg _).trans (stageNbAt_le_max_V4C st 0)

theorem maxCw_nonneg_V4C {D : ClosedEarlyData} (st : ClosedStage D) : 0 ≤ maxCw_V4C st :=
  (stageCwAt_nonneg_V4C st 0).trans (stageCwAt_le_max_V4C st 0)

/-- The first stage's constants are register V4's `sharedNb_VAL6`, `sharedCw_VAL6`. -/
theorem stageNbAt_zero_V4C {D : ClosedEarlyData} (st : ClosedStage D) :
    stageNbAt_V4C st 0 = sharedNb_VAL6 st ∧ stageCwAt_V4C st 0 = sharedCw_VAL6 st :=
  ⟨rfl, rfl⟩

/-- On `earlyDataSharedV4 K` every stage meets CFS12's interior condition at its buffer. -/
theorem ClosedStage.interior_stageBufferAt_V4C {K : ℕ} (st : ClosedStage (earlyDataSharedV4 K))
    (j : Fin 3) : st.Γ j * ((80 * (5 / 3) + 31) * stageBufferAt_V4C st j + 2) < 1 :=
  (earlyDataSharedV4_stage_mean_VAL6 st j).1

/-- **CFS11–CFS12 at EVERY stage with PR10's maxima** (`nb_cw_stage_selection_GAFS3` at `(j, b_j)`,
weakened from `N_b^{(j)}, c_w^{(j)}` to `maxNb_V4C, maxCw_V4C`): on every final family in FC07's
range, for every selection over the enlarged stage-`j` cloud, every `Σ` with `128 b_j Σ ≤ 1/5`,
every quality `Γ` with CFS12's interior condition at `b_j` and every plane field of the stage
dimension with the (CS) tests, every finite disjoint selection has multiplicity at most
`maxNb_V4C S` with (LM), and under the tube inclusion its weight derivatives are at most
`maxCw_V4C S / r_x`. -/
theorem nb_cw_slots_max_V4C {D : ClosedEarlyData} (S : ClosedStage D) (j : Fin 3) :
    ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
      (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
      (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
      (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
      (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
        εr e T V vs ζ Λz),
      0 ≤ Λ → 1 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → e ≤ 1 / 8 →
      1000000 * Δ * Λ < 1 / 100000 →
      ∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
      (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero j,
        cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero j)
          (sel x) = x) →
      ∀ sg : ℝ, 0 < sg → 128 * stageBufferAt_V4C S j * sg ≤ 1 / 5 →
      ∀ Γ : ℝ, 0 < Γ → Γ * ((80 * (5 / 3) + 31) * stageBufferAt_V4C S j + 2) < 1 →
      ∀ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
        Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero j,
        Module.finrank ℝ (plane x) = gafStageDim j) →
      (∀ x ∈ gafCloud P.toLocalChartFamily P.zero j,
        hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero j ∩
            ball x (sg * ρ (sel x) / Γ))
          ((AffineSubspace.mk' x (plane x) :
              Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
            ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) →
      ∀ (I : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (hI : I.Finite), I ⊆ gafCloud P.toLocalChartFamily P.zero j →
        I.PairwiseDisjoint (fun i => ball i (sg * ρ (sel i))) →
        (∀ x ∈ gafCloud P.toLocalChartFamily P.zero j,
          ((I ∩ {i | (closedBall i (80 * stageBufferAt_V4C S j * (sg * ρ (sel i))) ∩
              ball x (30 * stageBufferAt_V4C S j * (sg * ρ (sel x)))).Nonempty}).ncard : ℝ) ≤
            maxNb_V4C S ∧
          ∀ i ∈ I, (closedBall i (80 * stageBufferAt_V4C S j * (sg * ρ (sel i))) ∩
              ball x (30 * stageBufferAt_V4C S j * (sg * ρ (sel x)))).Nonempty →
            sg * ρ (sel x) / (5 / 3) ≤ sg * ρ (sel i) ∧
            sg * ρ (sel i) ≤ (5 / 3) * (sg * ρ (sel x)) ∧
            dist i x < 165 * stageBufferAt_V4C S j * (sg * ρ (sel x))) ∧
        ((⋃ x ∈ gafCloud P.toLocalChartFamily P.zero j,
            ball x (8 * stageBufferAt_V4C S j * (sg * ρ (sel x)))) ⊆
          ⋃ i ∈ I, ball i (20 * stageBufferAt_V4C S j * (sg * ρ (sel i))) →
          ∀ x ∈ gafCloud P.toLocalChartFamily P.zero j,
          ∀ y ∈ ball x (8 * stageBufferAt_V4C S j * (sg * ρ (sel x))),
            (∑ i ∈ hI.toFinset, ‖fderiv ℝ (fun y' => ballCutoff i
                (40 * stageBufferAt_V4C S j * (sg * ρ (sel i)))
                (2 * (40 * stageBufferAt_V4C S j * (sg * ρ (sel i)))) y' /
                (∑ a ∈ hI.toFinset, ballCutoff a (40 * stageBufferAt_V4C S j * (sg * ρ (sel a)))
                  (2 * (40 * stageBufferAt_V4C S j * (sg * ρ (sel a)))) y')) y‖) ≤
              maxCw_V4C S / (sg * ρ (sel x))) := by
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ sel hsel sg hsg hbsg Γ hΓ hint plane hdim hcloud I hI hIc hId
  have h := (Classical.choose_spec nb_cw_stage_selection_GAFS3 j (stageBufferAt_V4C S j)
    (S.one_le_stageBufferAt_V4C j)).2 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ
    δ εr e T V vs ζ Λz P hΛ hΔ hμ hτ he hLΛ sel hsel sg hsg hbsg Γ hΓ hint plane hdim hcloud I hI
    hIc hId
  refine ⟨fun x hx => ?_, fun hcov x hx y hy => ?_⟩
  · obtain ⟨h1, h2⟩ := h.1 x hx
    exact ⟨h1.trans (stageNbAt_le_max_V4C S j), h2⟩
  · refine (h.2 hcov x hx y hy).trans ?_
    have hr : 0 < sg * ρ (sel x) := mul_pos hsg (hρ (sel x))
    exact div_le_div_of_nonneg_right (stageCwAt_le_max_V4C S j) hr.le

/-! ### The strategy with PR10's maxima -/

/-- The rows strategy of register V4 with PR10's maxima `maxNb_V4C, maxCw_V4C` in the `N_b, c_w`
slots (every stage dominated). -/
def rowsStrategyNbMaxV4C (D : ClosedEarlyData) : ClosedThresholdsV4 D :=
  { rowsStrategyV4 D with
    Nb := maxNb_V4C
    Nb_nonneg := maxNb_nonneg_V4C
    cw := maxCw_V4C
    cw_nonneg := maxCw_nonneg_V4C }

/-- Changing `N_b, c_w` keeps every request of the rows strategy. -/
theorem rowsStrategyNbMaxV4C_below_V4C (D : ClosedEarlyData) :
    ClosedStrategyBelowV4 (rowsStrategyNbMaxV4C D) (rowsStrategyV4 D) where
  lc18_le := le_rfl
  circleUp_le := fun _ _ _ _ _ => le_rfl
  β₂Up_le := fun _ _ _ => le_rfl
  ΔLow_ge := fun _ _ _ _ => le_rfl
  errorsUp_le := fun _ _ _ => le_rfl
  sectionUp_le := fun _ _ _ _ => le_rfl
  lfr29W_le := fun _ _ _ _ _ => le_rfl
  endpointUp_le := fun _ _ _ _ _ _ => le_rfl
  σcolUp_le := fun _ _ _ _ _ _ _ => le_rfl
  scaleUp_le := fun _ _ _ _ => le_rfl
  wUp_le := fun _ _ _ _ _ => le_rfl
  splitUp_le := fun _ _ _ _ _ => le_rfl
  β₁Up_le := fun _ _ _ _ _ _ => le_rfl
  T₀Low_ge := fun _ _ _ _ _ _ _ => le_rfl
  LmaxLow_ge := fun _ _ _ _ _ _ => le_rfl
  tailLow_ge := fun _ _ _ _ _ _ _ => le_rfl

/-- **`C_ρ` with ONE `N_b`** (PR10, B:10120): at every register of a strategy whose `N_b, c_w` slots
are PR10's maxima, `C_ρ = 100(L₀+1)(1 + b_cut + N_b c_w/Σ₁)` with `N_b = maxNb_V4C ≥ N_b^{(j)}` at
every stage `j`, and the register's budget `C_ρ Δ Λ < 10⁻⁶` holds with this SAME `N_b`. -/
theorem ClosedRegisterV4.scaleConstant_maxNb_V4C {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) (R : ClosedRegisterV4 D T) :
    closedScaleConstantV4 D T R.stage = 100 * (D.L₀ + 1) *
      (1 + D.bcut + maxNb_V4C R.stage * maxCw_V4C R.stage / R.stage.Sig 0) ∧
    (∀ j, stageNbAt_V4C R.stage j ≤ T.Nb R.stage ∧ stageCwAt_V4C R.stage j ≤ T.cw R.stage) ∧
    100 * (D.L₀ + 1) * (1 + D.bcut + maxNb_V4C R.stage * maxCw_V4C R.stage / R.stage.Sig 0) *
      R.later.excl.Δ * R.later.scale.Λ < 1 / 10 ^ 6 := by
  have hC : closedScaleConstantV4 D T R.stage = 100 * (D.L₀ + 1) *
      (1 + D.bcut + maxNb_V4C R.stage * maxCw_V4C R.stage / R.stage.Sig 0) := by
    unfold closedScaleConstantV4
    rw [hNb, hcw]
  refine ⟨hC, fun j => ⟨hNb ▸ stageNbAt_le_max_V4C R.stage j,
    hcw ▸ stageCwAt_le_max_V4C R.stage j⟩, ?_⟩
  rw [← hC]
  exact R.later.regScale_Cρ

/-! ### The `inf` constants and the domination of `C_ρ` -/

/-- `ClosedThresholdsV4.inf` takes `N_b, c_w, I₁`, LPA02's output and `H` from the LEFT record. -/
theorem ClosedThresholdsV4.inf_constants_V4C {D : ClosedEarlyData} (U₁ U₂ : ClosedThresholdsV4 D) :
    (U₁.inf U₂).Nb = U₁.Nb ∧ (U₁.inf U₂).cw = U₁.cw ∧ (U₁.inf U₂).I₁ = U₁.I₁ ∧
      (U₁.inf U₂).lpa02V = U₁.lpa02V ∧ (U₁.inf U₂).H = U₁.H :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Domination of `C_ρ` in a meet**: if the left record's `N_b, c_w` dominate the right record's,
the meet's `C_ρ` dominates the right record's `C_ρ`. -/
theorem closedScaleConstantV4_inf_ge_right_V4C {D : ClosedEarlyData} {U₁ U₂ : ClosedThresholdsV4 D}
    (hNb : ∀ st, U₂.Nb st ≤ U₁.Nb st) (hcw : ∀ st, U₂.cw st ≤ U₁.cw st) (st : ClosedStage D) :
    closedScaleConstantV4 D U₂ st ≤ closedScaleConstantV4 D (U₁.inf U₂) st := by
  unfold closedScaleConstantV4
  have hL : 0 ≤ 100 * (D.L₀ + 1) := by have := D.one_le_L₀; positivity
  apply mul_le_mul_of_nonneg_left _ hL
  have hS := st.Sig_pos 0
  have hm : U₂.Nb st * U₂.cw st ≤ (U₁.inf U₂).Nb st * (U₁.inf U₂).cw st :=
    mul_le_mul (hNb st) (hcw st) (U₂.cw_nonneg st) (U₁.Nb_nonneg st)
  have := div_le_div_of_nonneg_right hm hS.le
  linarith

/-- **The budget transfers along a domination of `C_ρ`**: `C_ρ(U) Δ Λ < 10⁻⁶` at a register of `T`
and `C_ρ(U') ≤ C_ρ(T)` give the same budget for `U'` at the register's `Δ, Λ`. -/
theorem regScale_Cρ_of_le_V4C {D : ClosedEarlyData} {T U : ClosedThresholdsV4 D}
    (R : ClosedRegisterV4 D T) (h : closedScaleConstantV4 D U R.stage ≤
      closedScaleConstantV4 D T R.stage) :
    closedScaleConstantV4 D U R.stage * R.later.excl.Δ * R.later.scale.Λ < 1 / 10 ^ 6 := by
  have hΔ := R.later.Δ_pos_VAL6
  have hΛ := R.later.Λ_pos
  have hDL : 0 < R.later.excl.Δ * R.later.scale.Λ := mul_pos hΔ hΛ
  have h1 := mul_le_mul_of_nonneg_right h hDL.le
  have h2 := R.later.regScale_Cρ
  rw [mul_assoc] at h2 ⊢
  linarith

/-- **The constants of the rows strategy**: in `rowsStrategyV4 = (scale ⊓ partialRows) ⊓
circleRows` every component has `N_b = c_w = 0`, LPA02 output `V = T₀` and `H α = α` (the left
choice of `inf` equals every component); `I₁` is the scale record's `∫₀¹ sinh²` (the row records
carry the unread placeholder `1`). -/
theorem rowsStrategyV4_constants_V4C (D : ClosedEarlyData) :
    (rowsStrategyV4 D).Nb = (scaleStrategyV4 D).Nb ∧
      (rowsStrategyV4 D).Nb = (partialRowsStrategyV4 D).Nb ∧
      (rowsStrategyV4 D).Nb = (circleRowsStrategyV4 D).Nb ∧
      (rowsStrategyV4 D).cw = (partialRowsStrategyV4 D).cw ∧
      (rowsStrategyV4 D).cw = (circleRowsStrategyV4 D).cw ∧
      (rowsStrategyV4 D).lpa02V = (partialRowsStrategyV4 D).lpa02V ∧
      (rowsStrategyV4 D).lpa02V = (circleRowsStrategyV4 D).lpa02V ∧
      (rowsStrategyV4 D).H = (partialRowsStrategyV4 D).H ∧
      (rowsStrategyV4 D).H = (circleRowsStrategyV4 D).H ∧
      (rowsStrategyV4 D).I₁ = ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 ∧
      (partialRowsStrategyV4 D).I₁ = 1 ∧ (circleRowsStrategyV4 D).I₁ = 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The record with PR10's maxima -/

/-- **The partial closed validity on register V4 with ONE `N_b, c_w` binding at every stage**: at
the early data `earlyDataSharedV4 K`, on every closed standing sequence, one strategy `T` at which
the whole record `PartialClosedThresholdValidityV4Rows` holds, whose `N_b, c_w` slots are PR10's
maxima over the three stages, and at EVERY register `C_ρ` is computed from that `N_b` (dominating
each stage's `N_b^{(j)}, c_w^{(j)}`) and meets `C_ρ Δ Λ < 10⁻⁶`. -/
theorem exists_partialClosedThresholdValidityV4Rows_nbmax_V4C (K : ℕ) (hK : 10 ≤ K)
    (A : ℝ → ℝ) (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T,
        closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage =
          100 * ((earlyDataSharedV4 K).L₀ + 1) * (1 + (earlyDataSharedV4 K).bcut +
            maxNb_V4C R.stage * maxCw_V4C R.stage / R.stage.Sig 0) ∧
        (∀ j, stageNbAt_V4C R.stage j ≤ T.Nb R.stage ∧ stageCwAt_V4C R.stage j ≤ T.cw R.stage) ∧
        closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage * R.later.excl.Δ *
          R.later.scale.Λ < 1 / 10 ^ 6 := by
  obtain ⟨hN, hP, hPs, hPz, hL₀, hΞ, hΞr, hC⟩ := earlyDataSharedV4_fields_VAL6 K
  obtain ⟨T, hTU, hH, hlc, hfam⟩ :=
    exists_closed_realization_VAL6 K hK A hA Wseq gseq hf hg
      (rowsStrategyNbMaxV4C (earlyDataSharedV4 K))
  have hb : ClosedStrategyBelowV4 T (rowsStrategyV4 (earlyDataSharedV4 K)) :=
    hTU.below_VAL6.trans_VAL6 (rowsStrategyNbMaxV4C_below_V4C _)
  have hsc : ClosedStrategyBelowV4 T (scaleStrategyV4 (earlyDataSharedV4 K)) :=
    hb.trans_VAL6 ((ClosedThresholdsV4.inf_below_left_VAL6 _ _).trans_VAL6
      (ClosedThresholdsV4.inf_below_left_VAL6 _ _))
  refine ⟨T, ⟨⟨hN, hP, hPs, hPz, hL₀, hΞ, hΞr, hlc, hTU.I₁_eq, fun m p => ?_, fun _ => hfam⟩,
    hC, closedScaleBudgetV4_of_below_VAL6 hsc,
    fun _ _ _ _ hεr hΛz _ _ F => closedRowOuts_of_below_VAL6 hC hb F hεr hΛz⟩,
    hTU.Nb_eq, hTU.cw_eq, fun R => ?_⟩
  · rw [hH m]
    exact closed_standing_clauses_VAL K A Wseq gseq hg m p
  · obtain ⟨h1, h2, h3⟩ := R.scaleConstant_maxNb_V4C hTU.Nb_eq hTU.cw_eq
    refine ⟨h1, h2, ?_⟩
    rw [h1]
    exact h3

end DifferentialGeometry.Geometry.Collapse
