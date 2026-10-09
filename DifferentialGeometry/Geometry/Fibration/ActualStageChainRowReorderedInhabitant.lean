import DifferentialGeometry.Geometry.Fibration.ActualStageChainRowReordered
import DifferentialGeometry.Geometry.Fibration.ActualStageChainInhabitant

/-!
# The reordered GAF02 producer on a nonempty closed family (lane C14-CHAIN-INST, G2b)

`gaf02_chain_row_reordered_CHI` (`ActualStageChainRowReordered.lean`) has 51 packet premises. This
file shows that they can all hold at once, on a nonempty closed family, at the producer's own
thresholds: the satisfiability check of the producer's hypothesis group.

* `dihedralTinyRowPackets_CHI`: the dihedral `LocalChartPacketsC14` fixture on `RP³ # RP³`
  (`LocalChartPacketsDihedralInhabitant.lean`) at the values `Λ = μ = τ = σc = ε = βc = b = s = b' =
  s' = γ = εr = v_s = Λz = 0`, `K = 0`, `Δ = 1200`, `δ = 1/2`, `e = 1/100`,
  `T = V = 1600·10⁶·1200`, splitting qualities `β₁ = 0`, `β₂`, `β₃ = 3/20`
  (`dihedralTinyRowBeta_CHI`), and `γc, L_max, σs, ζ` free.
* `exists_gaf02Chain_row_dihedralTiny_CHI`: with `ν = 1/20`, `c_adj = 1` and
  `β₂ = min(σ/3, η₂, 1/(2·10⁶))` (after the producer's `σ, η₂`), `γc = γ₀`, `σs, ζ` half of the
  minimum of their upper bounds and `L_max` the maximum of its lower bounds, every premise of the
  producer holds; the producer then yields a `Gaf02Chain` on the fixture with constant selections.
  All the `β₂`-premises are met by `0 < β₂`, with no conflict between `3β₂ ≤ σ`, `β₂ ≤ η₂`,
  `β₂ < 10⁻⁶` and the later thresholds.
* Consumer `gaf02_core_row_dihedralTiny_CHI`: the chain's GAF02 CORE theorems on that chain.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- The splitting qualities of the producer instance: `β₁ = 0`, `β₂`, `β₃ = 3/20` (`= 3ν`,
`ν = 1/20`), all others `0`. -/
def dihedralTinyRowBeta_CHI (β₂ : ℝ) : ℕ → ℝ := fun n => if n = 2 then β₂ else if n = 3 then 3 / 20
  else 0

/-- `β₁ = 0`. -/
theorem dihedralTinyRowBeta_one_CHI (β₂ : ℝ) : dihedralTinyRowBeta_CHI β₂ 1 = 0 := by
  simp [dihedralTinyRowBeta_CHI]

/-- `β₂` is the given value. -/
theorem dihedralTinyRowBeta_two_CHI (β₂ : ℝ) : dihedralTinyRowBeta_CHI β₂ 2 = β₂ := by
  simp [dihedralTinyRowBeta_CHI]

/-- `β₃ = 3/20`. -/
theorem dihedralTinyRowBeta_three_CHI (β₂ : ℝ) : dihedralTinyRowBeta_CHI β₂ 3 = 3 / 20 := by
  simp [dihedralTinyRowBeta_CHI]

/-- The splitting qualities are `≤ 1/4` once `β₂ ≤ 1/4`. -/
theorem dihedralTinyRowBeta_le_CHI {β₂ : ℝ} (h : β₂ ≤ 1 / 4) :
    ∀ j, 1 ≤ j → j ≤ 3 → dihedralTinyRowBeta_CHI β₂ j ≤ 1 / 4 := by
  intro j hj1 hj3
  interval_cases j <;> simp [dihedralTinyRowBeta_CHI] <;> linarith

/-- The dihedral family at the producer's values: `Λ = μ = τ = σc = ε = βc = b = s = b' = s' = γ =
εr = v_s = Λz = 0`, `K = 0`, `Δ = 1200`, `δ = 1/2`, `e = 1/100`, `T = V = 1600·10⁶·1200`, `β` as in
`dihedralTinyRowBeta_CHI β₂`, and `γc, L_max, σs, ζ` free. -/
abbrev dihedralTinyRowPackets_CHI (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4) :
    LocalChartPacketsC14 dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
      dihedralTinyRho_CHI dihedralTinyRho_pos_CHI 0 (dihedralTinyRowBeta_CHI β₂) 1200 σs 0 0 0 0 0
      0 0 0 γc 0 Lmax 0 0 (1 / 2) 0 (1 / 100) (1600 * (1000000 * 1200)) (1600 * (1000000 * 1200))
      0 ζ 0 :=
  dihedralTinyPackets_CHI (dihedralTinyRowBeta_le_CHI h) (by norm_num) (by norm_num) (by norm_num)
    le_rfl (by norm_num) (by norm_num) (by norm_num) le_rfl

/-- **G2b: the premises of the reordered GAF02 producer hold together on a nonempty closed
family.** At `ν = 1/20`, `c_adj = 1`, with `β₂ = min(σ/3, η₂, 1/(2·10⁶))` chosen after the
producer's thresholds `σ, η₂`, `γc = γ₀`, `σs` and `ζ` half of the minimum of their upper bounds
and `L_max` the maximum of its lower bounds, all 51 premises of `gaf02_chain_row_reordered_CHI`
hold on the dihedral fixture (`dihedralTinyRowPackets_CHI`, `RP³ # RP³`), and the producer gives a
`Gaf02Chain` on it with constant selections. -/
theorem exists_gaf02Chain_row_dihedralTiny_CHI (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02Chain (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).toLocalChartPackets Kj Ξ Γ S eg
        c cw),
      0 < β₂ ∧ 0 < γc ∧ 0 < σs ∧ 0 < ζ ∧ C.sel = fun _ _ => dihedralTinyBase_CHI := by
  obtain ⟨θ, Ξ, c, Γ, S, eg, cw, hj, -, -, -, σ, η₂, γ₀, ηc, θt, hσ, -, hη₂, hγ₀, -, hηc, hθt,
    -, hrow⟩ := gaf02_chain_row_reordered_CHI Kj (ν := 1 / 20) (cadj := 1) (by norm_num)
      (by norm_num) one_pos
  obtain ⟨-, -, -, -, -, -, -, heg0, -⟩ := hj 0
  obtain ⟨-, -, -, -, -, -, -, heg1, -⟩ := hj 1
  set β₂ : ℝ := min (min (σ / 3) η₂) (1 / 2000000) with hβ₂def
  have hβ₂ : 0 < β₂ := by positivity
  have hβ₂s : β₂ ≤ 1 / 2000000 := min_le_right _ _
  have hβ₂σ : β₂ ≤ σ / 3 := (min_le_left _ _).trans (min_le_left _ _)
  have hβ₂η : β₂ ≤ η₂ := (min_le_left _ _).trans (min_le_right _ _)
  obtain ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, hη₁, -, hη₀₁, hθs, -, -, hη₀₂, hrow'⟩ :=
    hrow β₂ hβ₂ (by linarith) 1200 le_rfl
  set A : ℝ := eg 1 / (20 * egpGraphConst) with hAdef
  have hA : 0 < A := div_pos heg1 (mul_pos (by norm_num) egpGraphConst_pos_KC4)
  set mσ : ℝ := min (min (θt ^ 2 / 1000) (A ^ 2 / 10 ^ 8)) (θs ^ 2 / 10 ^ 6) with hmσdef
  have hmσ : 0 < mσ := by positivity
  set σs : ℝ := mσ / 2 with hσsdef
  have hσs : 0 < σs := by positivity
  have hσsm : σs < mσ := half_lt_self hmσ
  have hσs1 : σs ≤ θt ^ 2 / 1000 := hσsm.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hσs2 : σs ≤ A ^ 2 / 10 ^ 8 := hσsm.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hσs3 : σs < θs ^ 2 / 10 ^ 6 := hσsm.trans_le (min_le_right _ _)
  set mζ : ℝ := min (min (min (θt ^ 2 / 1000) (A ^ 2 / 10 ^ 8))
    (min (1 / (1000 * (1000000 * 1200))) (θs ^ 2 / 10 ^ 6))) (1 / (100 * (1000000 * 1200)))
    with hmζdef
  have hmζ : 0 < mζ := by positivity
  set ζ : ℝ := mζ / 2 with hζdef
  have hζ : 0 < ζ := by positivity
  have hζm : ζ < mζ := half_lt_self hmζ
  have hζ1 : ζ ≤ θt ^ 2 / 1000 :=
    hζm.le.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hζ2 : ζ ≤ A ^ 2 / 10 ^ 8 :=
    hζm.le.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hζ3 : ζ ≤ 1 / (1000 * (1000000 * 1200)) :=
    hζm.le.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hζ4 : ζ < θs ^ 2 / 10 ^ 6 :=
    hζm.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hζ5 : ζ < 1 / (100 * (1000000 * 1200)) := hζm.trans_le (min_le_right _ _)
  set Lmax : ℝ := max (4 * (10 + 2 * (2000000 * 1200) + 1200 / 3)) (max σ⁻¹ (max Lc₁ Lc₂))
    with hLdef
  have hL0 : 4 * (10 + 2 * (2000000 * (1200 : ℝ)) + 1200 / 3) ≤ Lmax := le_max_left _ _
  have hL1 : σ⁻¹ ≤ Lmax := (le_max_left _ _).trans (le_max_right _ _)
  have hL2 : Lc₁ ≤ Lmax := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hL3 : Lc₂ ≤ Lmax := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hq : β₂ ≤ 1 / 4 := by linarith
  have hθt2 : (0 : ℝ) ≤ θt ^ 2 / 1000 := by positivity
  obtain ⟨C, hC⟩ := hrow' (dihedralTinyRowPackets_CHI β₂ γ₀ Lmax σs ζ hq) le_rfl (by norm_num)
    (by norm_num) (by norm_num) hL0 (by norm_num) le_rfl le_rfl (by norm_num) le_rfl hθt2
    (by rw [zero_mul]; positivity) (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_two_CHI]; linarith)
    (by rw [dihedralTinyRowBeta_two_CHI]; exact hβ₂η)
    hγ₀.le hγ₀ le_rfl hηc.le hη₁.le (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₁.le) hσs hσs1
    (by positivity) hζ hζ1 (by positivity) (by norm_num) hL1 (by rw [mul_zero]; exact heg0)
    hη₀₁.le (by norm_num) (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀₁.le) hL2
    (by positivity) (by rw [zero_mul]; positivity) hσs2 (by positivity) hζ2 hζ3 (by positivity)
    (dihedralTinyRowBeta_two_CHI β₂) (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀₂.le) hL3
    hσs3 (by positivity) hζ4 hζ5 (by positivity) le_rfl (fun _ _ => dihedralTinyBase_CHI)
    (fun st x hx => by
      rw [gafCloudEnlarged_eq_empty_CHI _ (by fin_cases st <;> rfl)] at hx
      exact absurd hx (notMem_empty x))
  exact ⟨fun j => Ξ j (Γ j), Γ, S, eg, c, cw, β₂, γ₀, Lmax, σs, ζ, hq, C, hβ₂, hγ₀, hσs, hζ, hC⟩

/-- **Consumer** (the chain's GAF02 CORE theorems `stage_smooth`, `stage_error_lt` and `scale_pos`
on the producer's chain of `exists_gaf02Chain_row_dihedralTiny_CHI`): `E` is smooth,
`‖E − 𝓔⁰‖ < c₃ρ`, and the scale exit is positive. -/
theorem gaf02_core_row_dihedralTiny_CHI (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02Chain (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).toLocalChartPackets Kj Ξ Γ S eg
        c cw),
      0 < β₂ ∧
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag
        (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).toLocalChartFamily
        (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero => ℝ²)) ∞ C.E ∧
      (∀ p, ‖C.E p - cgpGlobalMap (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).toLocalChartFamily
        (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero p‖ < c 2 * dihedralTinyRho_CHI p) ∧
      ∀ p, 0 < C.scale p := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, hβ₂, -, -, -, -⟩ :=
    exists_gaf02Chain_row_dihedralTiny_CHI Kj
  exact ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, hβ₂, C.stage_smooth.2.2,
    C.stage_error_lt.2.2, fun p => (C.scale_pos p).2⟩

end DifferentialGeometry.Geometry.Collapse
