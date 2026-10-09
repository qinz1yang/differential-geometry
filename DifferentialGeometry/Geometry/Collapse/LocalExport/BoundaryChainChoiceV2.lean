import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainChoice
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutoffTwo
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedTransfer
import DifferentialGeometry.Geometry.Fibration.ActualStageChainRoughData

/-!
# BCG03: GAF01's CHOICE for the boundary chain, v2, with the CHOICE validity record (BAUG-Dd)

Target `boundaryChain_choice_V2_BAUGD` of `TargetsBoundary-A-v3.lean.txt` (review 66 D66-3, review
69 D69-3 / D69-5; numeric sync of review 76 N76-4): supersedes G4's `boundaryChain_choice_BAUGD`,
which dropped the (OS) / (JA) evidence. From the jet order `Kj`, the cap `c_adj` and the explicit
early constants `(b_cut, κ, L₀)` only:

* `boundaryChainCutoffConst_BAUGD` — the chain's ONE cutoff constant `max(b₀, b₁, b₂)`;
* `BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj` — the CHOICE evidence of ONE numeric
  choice: per-stage quality relations (ProducerDP v3: `Σ < Γ/250`, `Σ < Γ³/(125(C_j + 2P_*))`),
  GAF01's (OS) with `Ω = gafGraphOmega_BAS`, the one-sheet budget, CGP06's rank margin,
  `Σ_j < Ξ_j/10⁴`, `0 ≤ c_w`, (JA) `c₂ < c_adj`, `c₂ < 1/1000`, and E4's `c₂ < 10⁻⁵` (N76-4,
  chosen at the early CHOICE node);
* **`boundaryChain_choice_V2_BAUGD`**; consumer `boundaryChain_choice_V2_actual_BAUGD` at the
  chain's actual constants (`b_cut = boundaryChainCutoffConst_BAUGD`, `κ = cutoffKappa_BAUGP2`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Topology
open GC.MetricGeometry DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

/-- **The chain's ONE cutoff constant** `b_cut = max(b₀, b₁, b₂)` (CFS31 for `ψ₀`, CFS23 for `ψ₁`,
CFS22 for `ψ₂`); numerical, fixed before every parameter. -/
def boundaryChainCutoffConst_BAUGD : ℝ :=
  max cutoffZeroConst_BAUGD (max cutoffOneConst_BAUGP2 cutoffTwoConst_BAUGP2)

theorem boundaryChainCutoffConst_nonneg_BAUGD : 0 ≤ boundaryChainCutoffConst_BAUGD :=
  le_max_of_le_left cutoffZeroConst_nonneg_BAUGD

/-- **The CHOICE validity of the chain's numbers** (closed `Gaf02RoughData` numeric part and
`Gaf02RoughDataJA`): per-stage quality relations, GAF01's (OS) with `Ω = gafGraphOmega_BAS`, the
one-sheet budget (SN), CGP06's rank margin, `Σ_j < Ξ_j/10⁴`, `0 ≤ c_w`, (JA) `c₂ < c_adj`,
`c₂ < 1/1000` and E4's `c₂ < 10⁻⁵` (review 76 N76-4). -/
structure BoundaryChainChoiceValidity_BAUGD (Ξ Γ Sg eg c cw : Fin 3 → ℝ) (cadj : ℝ) : Prop where
  quality : ∀ j, 0 < Γ j ∧ Γ j < 1 ∧ Sg j < Γ j / 250 ∧ 0 < eg j ∧ eg j < 1 / 100 ∧
    eg j < Γ j * Sg j / 100
  graph : Sg 0 < Γ 0 ^ 3 / (125 * (tcpGraphConst + 2 * bmConst_BAUGC)) ∧
    Sg 1 < Γ 1 ^ 3 / (125 * (egpGraphConst + 2 * bmConst_BAUGC)) ∧
    Sg 2 < Γ 2 ^ 3 / (125 * (sgpGraphBound + 2 * bmConst_BAUGC))
  os : ∀ j, Ξ j < 1 / (1000 * (gafGraphOmega_BAS + 1)) ∧ eg j < Sg j / 1000 ∧
    2 * eg j < 1 / (48 * gafGraphOmega_BAS)
  one_sheet : ∀ j (Rr rx : ℝ), 0 < Rr → 9 / 20 * Sg j * Rr ≤ rx →
    (2 * eg j + 25 / 12 * (1 + gafGraphOmega_BAS) * Ξ j * Sg j) * Rr < Sg j * Rr / 100 ∧
      Sg j * Rr / 100 < rx / 4 ∧ Ξ j < 1 / (2 * gafGraphOmega_BAS)
  rank_margin : ∀ j (ν : ℝ), ν ≤ eg j → ν + eg j ≤ 1 / (48 * gafGraphOmega_BAS)
  sigma_le : ∀ j, Sg j < Ξ j / 10000
  cw_nonneg : ∀ j, 0 ≤ cw j
  c_lt_adj : c 2 < cadj
  c_two_lt : c 2 < 1 / 1000
  c_two_lt_E4 : c 2 < 1 / 100000

/-- The positive graph constants of the three stages, enlarged for the plane producer (`5/4`
margin for `Σ' = 5Σ/4`, the boundary profile `2P_*`, and `Σ < Γ/250`). -/
def boundaryChoiceGraphConst_BAUGD : Fin 3 → ℝ :=
  ![2 * (tcpGraphConst + 2 * bmConst_BAUGC) + 3, 2 * (egpGraphConst + 2 * bmConst_BAUGC) + 3,
    2 * (sgpGraphBound + 2 * bmConst_BAUGC) + 3]

/-- The plane producer's graph constant of stage `j`. -/
def boundaryPlaneGraphConst_BAUGD : Fin 3 → ℝ :=
  ![tcpGraphConst + 2 * bmConst_BAUGC, egpGraphConst + 2 * bmConst_BAUGC,
    sgpGraphBound + 2 * bmConst_BAUGC]

theorem boundaryPlaneGraphConst_pos_BAUGD (j : Fin 3) : 0 < boundaryPlaneGraphConst_BAUGD j := by
  have hP := one_le_bmConst_BAUGC
  fin_cases j
  · have := one_le_tcpGraphConst
    change 0 < tcpGraphConst + 2 * bmConst_BAUGC
    linarith
  · have := egpGraphConst_pos_KC4
    change 0 < egpGraphConst + 2 * bmConst_BAUGC
    linarith
  · have := sgpGraphBound_pos_GAF8
    change 0 < sgpGraphBound + 2 * bmConst_BAUGC
    linarith

theorem boundaryChoiceGraphConst_eq_BAUGD (j : Fin 3) :
    boundaryChoiceGraphConst_BAUGD j = 2 * boundaryPlaneGraphConst_BAUGD j + 3 := by
  fin_cases j <;> rfl

/-- The size relations from the enlarged graph constant: `Σ < Γ³/(100 C')` with `0 < Γ ≤ 1`
gives `Σ < Γ/250` and `Σ < Γ³/(125 C)`. -/
theorem sigma_lt_of_graph_BAUGD {Sg Γ C : ℝ} (hC : 0 < C) (hΓ : 0 < Γ) (hΓ1 : Γ ≤ 1)
    (h : Sg < Γ ^ 3 / (100 * (2 * C + 3))) : Sg < Γ / 250 ∧ Sg < Γ ^ 3 / (125 * C) := by
  have hΓ3 : 0 < Γ ^ 3 := by positivity
  have hΓ3le : Γ ^ 3 ≤ Γ := by
    have : Γ ^ 3 = Γ * Γ ^ 2 := by ring
    rw [this]
    exact mul_le_of_le_one_right hΓ.le (pow_le_one₀ hΓ.le hΓ1)
  constructor
  · calc Sg < Γ ^ 3 / (100 * (2 * C + 3)) := h
      _ ≤ Γ / 250 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  · calc Sg < Γ ^ 3 / (100 * (2 * C + 3)) := h
      _ ≤ Γ ^ 3 / (125 * C) := by
        apply div_le_div_of_nonneg_left hΓ3.le (by positivity)
        nlinarith

/-- **GAF01's CHOICE for the boundary chain, v2**: from `Kj`, `c_adj` and the explicit early
constants `(b_cut, κ, L₀)` only — the CFS15 moduli and the native-output preconditions per stage,
the CHOICE validity record, and the `numbers` clause of `BoundaryGaf02Chain` verbatim for every
`c_w ≥ 0` chosen by the native outputs. -/
theorem boundaryChain_choice_V2_BAUGD (Kj : ℕ) {cadj bcut κ L₀ : ℝ} (hcadj : 0 < cadj)
    (hb : 0 ≤ bcut) (hκ : 0 < κ) (hL : 0 ≤ L₀) :
    ∃ (Ξf : Fin 3 → ℝ → ℝ) (Ξ Γ Sg eg c : Fin 3 → ℝ),
      (∀ j, Ξ j = Ξf j (Γ j) ∧ 0 < Ξ j ∧ Ξ j < 1 / 10 ∧
        Cfs15ModulusAtV2 (gafStageDim j) Kj (5 / 3) (Ξf j) (Γ j) ∧
        Γ j * ((80 * (5 / 3) + 31) * (Ξf j (Γ j))⁻¹ + 2) < 1 ∧ 0 < Sg j ∧
        128 * (Ξ j)⁻¹ * Sg j ≤ 1 / 5 ∧ 0 < c j ∧ c j ≤ 1 / 512) ∧
      c 0 ≤ c 1 ∧ c 1 ≤ c 2 ∧
      ∀ cw : Fin 3 → ℝ, (∀ j, 0 ≤ cw j) →
        BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj ∧
        ((∀ j, 0 < Ξ j ∧ 0 < Sg j ∧ 128 * (Ξ j)⁻¹ * Sg j ≤ 1 / 5 ∧ 0 ≤ eg j ∧
            Sg j ≤ Ξ j / 10000 ∧ 0 ≤ cw j) ∧
          5 / 3 * Ξ 0 * Sg 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
          (5 / 3 * Ξ 0 * Sg 0 * bcut * L₀ + Ξ 0 * L₀ + eg 0) < c 0 ∧
          c 0 ≤ 4 * κ / 5 ∧ c 0 ≤ 3 * Sg 1 / 10 ∧
          (c 0 + (5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
          ((5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0) * bcut * (L₀ + c 0) +
              Ξ 1 * (L₀ + c 0) + eg 1 + 2 * c 0) < c 1 ∧
          c 1 ≤ 4 * κ / 5 ∧ c 1 ≤ 3 * Sg 2 / 10 ∧
          (c 1 + (5 / 3 * Ξ 2 * Sg 2 + (1 + Ξ 2) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
          ((5 / 3 * Ξ 2 * Sg 2 + (1 + Ξ 2) * c 1) * bcut * (L₀ + c 1) +
              Ξ 2 * (L₀ + c 1) + eg 2 + 2 * c 1) < c 2) := by
  choose θ hθ Ξf hΞf using fun st : Fin 3 => cfs15_shared_modulus_GAFS4 (gafStageDim st) Kj
  have hpos : ∀ st Γ, 0 < Γ → Γ < θ st → 0 < Ξf st Γ := fun st Γ hΓ hθΓ => by
    obtain ⟨m, hm⟩ := ((hΞf st).2 Γ hΓ hθΓ).1
    rw [hm]
    positivity
  have hCg : ∀ j, 0 < boundaryChoiceGraphConst_BAUGD j := fun j => by
    rw [boundaryChoiceGraphConst_eq_BAUGD]
    have := boundaryPlaneGraphConst_pos_BAUGD j
    linarith
  have hΩ := one_le_gafGraphOmega_BAS
  have hcadj' : 0 < min cadj (1 / 100000) := lt_min hcadj (by norm_num)
  obtain ⟨c, Γ, S, eg, h⟩ := exists_three_stage_adjustment_choice_below Ξf θ hθ hpos
    (fun st => (hΞf st).1) _ hcadj' hb hκ hL hΩ hCg
  obtain ⟨hA, hB, hC, hj⟩ := h
  have hΞpos : ∀ j, 0 < Ξf j (Γ j) := fun j => hpos j (Γ j) (hj j).1.2.2.2.1 (hj j).1.1
  have hmo : ∀ j, 128 * (Ξf j (Γ j))⁻¹ * S j ≤ 1 / 5 := fun j => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hSΞ, -⟩ := (hj j).1
    have hΞj := hΞpos j
    have h1 : 128 * (Ξf j (Γ j))⁻¹ * S j ≤ 128 * (Ξf j (Γ j))⁻¹ * (Ξf j (Γ j) / 10000) :=
      mul_le_mul_of_nonneg_left hSΞ.le (mul_nonneg (by norm_num) (inv_nonneg.mpr hΞj.le))
    have h2 : 128 * (Ξf j (Γ j))⁻¹ * (Ξf j (Γ j) / 10000) = 128 / 10000 := by
      rw [show 128 * (Ξf j (Γ j))⁻¹ * (Ξf j (Γ j) / 10000) =
        128 / 10000 * ((Ξf j (Γ j))⁻¹ * Ξf j (Γ j)) by ring, inv_mul_cancel₀ hΞj.ne', mul_one]
    linarith only [h1, h2]
  have hν : ∀ j, eg j ≤ Γ j := fun j => by
    obtain ⟨-, -, -, hΓ, -, -, -, -, -, hS2, -, -, -, -, -, heΓ, -, -⟩ := (hj j).1
    have h' : Γ j * S j ≤ Γ j * 100 := mul_le_mul_of_nonneg_left (by linarith only [hS2]) hΓ.le
    linarith only [h', heΓ]
  have hc0 := (hj 0).1.2.1
  have hc1 := (hj 1).1.2.1
  have hb0 : 0 < 16 * (1 + bcut) * (1 + L₀) :=
    mul_pos (mul_pos (by norm_num) (by linarith only [hb])) (by linarith only [hL])
  have hb1 : 0 < 8 * (1 + L₀) := mul_pos (by norm_num) (by linarith only [hL])
  have ht₀ : (0 : ℝ) ≤ min (3 * S 0 / 10) (min (min (c 0 / (16 * (1 + bcut) * (1 + L₀)))
      ((1 / 2) / (8 * (1 + L₀)))) 1) :=
    le_min (by linarith only [(hj 0).1.2.2.2.2.2.2.2.2.1])
      (le_min (le_min (div_nonneg hc0.le hb0.le) (div_nonneg (by norm_num) hb1.le)) zero_le_one)
  have hS2 : ∀ j, S j ≤ 1 / 2 := fun j => (hj j).1.2.2.2.2.2.2.2.2.2.1.le
  have k₀ := (hj 0).2 0 0 (eg 0) (S 0) le_rfl ht₀ le_rfl ht₀ (hν 0) (hS2 0)
  have k₀v := k₀.1
  have k₀d := k₀.2.1
  simp only [mul_zero, add_zero, zero_add] at k₀v k₀d
  have k₁ := (hj 1).2 (c 0) (c 0) (eg 1) (S 1) hc0.le hC.2.1 hc0.le hC.2.1 (hν 1) (hS2 1)
  have k₂ := (hj 2).2 (c 1) (c 1) (eg 2) (S 2) hc1.le hB.2.1 hc1.le hB.2.1 (hν 2) (hS2 2)
  have hc512 : ∀ j, c j ≤ 1 / 512 := fun j => by
    fin_cases j
    · exact hC.2.2.2.2
    · exact hB.2.2.2.2
    · exact hA.2.2.le
  refine ⟨Ξf, fun j => Ξf j (Γ j), Γ, S, eg, c, fun j => ?_, hC.1, hB.1, fun cw hcw => ⟨?_, ?_⟩⟩
  · obtain ⟨hθΓ, hcj, -, hΓ, -, hΞ10, -, -, hS, -, -, -, -, -, -, -, -, -⟩ := (hj j).1
    obtain ⟨-, hat, hint, -⟩ := (hΞf j).2 (Γ j) hΓ hθΓ
    exact ⟨rfl, hΞpos j, hΞ10, hat, hint, hS, hmo j, hcj, hc512 j⟩
  · have hΓ1 : ∀ j, Γ j ≤ 1 := fun j => by
      obtain ⟨-, -, -, -, hΓc, -⟩ := (hj j).1
      linarith [hc512 j]
    have hsz : ∀ j, S j < Γ j / 250 ∧ S j < Γ j ^ 3 / (125 * boundaryPlaneGraphConst_BAUGD j) :=
      fun j => by
        obtain ⟨-, -, -, hΓ, -, -, -, -, -, -, -, -, hSC, -⟩ := (hj j).1
        rw [boundaryChoiceGraphConst_eq_BAUGD] at hSC
        exact sigma_lt_of_graph_BAUGD (boundaryPlaneGraphConst_pos_BAUGD j) hΓ (hΓ1 j) hSC
    refine ⟨fun j => ?_, ⟨(hsz 0).2, (hsz 1).2, (hsz 2).2⟩, fun j => ?_, fun j Rr rx hRr hrx => ?_,
      fun j ν hνe => ?_, fun j => (hj j).1.2.2.2.2.2.2.2.2.2.2.1, hcw,
      hA.1.trans_le (min_le_left _ _), hA.2.1, hA.1.trans_le (min_le_right _ _)⟩
    · obtain ⟨-, -, -, hΓ, -, -, -, -, -, -, -, -, -, he, he1, heΓ, -⟩ := (hj j).1
      exact ⟨hΓ, by linarith [hΓ1 j, hc512 j, (hj j).1.2.2.2.2.1], (hsz j).1, he, he1, heΓ⟩
    · obtain ⟨-, -, -, -, -, -, -, hΞΩ, -, -, -, -, -, -, -, -, heS, he48⟩ := (hj j).1
      exact ⟨hΞΩ, heS, he48⟩
    · obtain ⟨-, -, -, -, -, -, -, hΞΩ, hS, -, -, -, -, he, -, -, heS, -⟩ := (hj j).1
      have hΞj := hΞpos j
      have hΩ1 : 0 < gafGraphOmega_BAS + 1 := by linarith
      have hΞ' : (1 + gafGraphOmega_BAS) * Ξf j (Γ j) < 1 / 1000 := by
        rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 1000 * (gafGraphOmega_BAS + 1))] at hΞΩ
        nlinarith
      have hSR : 0 < S j * Rr := mul_pos hS hRr
      refine ⟨?_, ?_, ?_⟩
      · have h1 : 25 / 12 * (1 + gafGraphOmega_BAS) * Ξf j (Γ j) * S j ≤
            25 / 12 * (1 / 1000) * S j := by
          have := mul_le_mul_of_nonneg_right hΞ'.le hS.le
          nlinarith
        have h2 : 2 * eg j + 25 / 12 * (1 + gafGraphOmega_BAS) * Ξf j (Γ j) * S j < S j / 100 := by
          nlinarith
        have := mul_lt_mul_of_pos_right h2 hRr
        nlinarith
      · nlinarith
      · rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 1000 * (gafGraphOmega_BAS + 1))] at hΞΩ
        rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * gafGraphOmega_BAS)]
        nlinarith
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, he48⟩ := (hj j).1
      linarith
  · exact ⟨fun j => ⟨hΞpos j, (hj j).1.2.2.2.2.2.2.2.2.1, hmo j,
        (hj j).1.2.2.2.2.2.2.2.2.2.2.2.2.2.1.le, (hj j).1.2.2.2.2.2.2.2.2.2.2.1.le, hcw j⟩,
      k₀v, hC.2.2.2.2, k₀d, hC.2.2.1, hC.2.1.trans (min_le_left _ _), k₁.1, hB.2.2.2.2, k₁.2.1,
      hB.2.2.1, hB.2.1.trans (min_le_left _ _), k₂.1, hA.2.2.le, k₂.2.1⟩

/-- **Consumer: the CHOICE at the chain's actual early constants** (`b_cut =
boundaryChainCutoffConst_BAUGD`, `κ = cutoffKappa_BAUGP2`, any `L₀ ≥ 0`), with `b_cut` dominating
the three cutoff constants and `κ > 0`. -/
theorem boundaryChain_choice_V2_actual_BAUGD (Kj : ℕ) {cadj L₀ : ℝ} (hcadj : 0 < cadj)
    (hL : 0 ≤ L₀) :
    cutoffZeroConst_BAUGD ≤ boundaryChainCutoffConst_BAUGD ∧
    cutoffOneConst_BAUGP2 ≤ boundaryChainCutoffConst_BAUGD ∧
    cutoffTwoConst_BAUGP2 ≤ boundaryChainCutoffConst_BAUGD ∧
    ∃ (Ξf : Fin 3 → ℝ → ℝ) (Ξ Γ Sg eg c : Fin 3 → ℝ), (∀ j, Ξ j = Ξf j (Γ j)) ∧
      ∀ cw : Fin 3 → ℝ, (∀ j, 0 ≤ cw j) → BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj := by
  refine ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _), ?_⟩
  obtain ⟨Ξf, Ξ, Γ, Sg, eg, c, h1, -, -, h⟩ := boundaryChain_choice_V2_BAUGD Kj (L₀ := L₀) hcadj
    boundaryChainCutoffConst_nonneg_BAUGD cutoffKappa_pos_BAUGP2 hL
  exact ⟨Ξf, Ξ, Γ, Sg, eg, c, fun j => (h1 j).1, fun cw hcw => (h cw hcw).1⟩

end DifferentialGeometry.Geometry.Collapse
