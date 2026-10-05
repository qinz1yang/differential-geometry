import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJARow
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJAApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainRowReorderedInhabitant

/-!
# The producer of `Gaf02ChainEJA` on a nonempty closed family (lane C14-CHAIN-INST)

`gaf02_chainEJA_row_GAFC` (`ActualStageChainEJARow.lean`, lane C14-GAF-C) builds a `Gaf02ChainEJA`
(a `Gaf02ChainE` whose numeric choice also has GAF01's (JA) part `c₃ < c_adj`, `c₃ < 1/1000`) from
the 51 packet premises of `gaf02_chainE_row_GAF8`. This file runs it on the dihedral
`LocalChartPacketsC14` fixture on `RP³ # RP³` (`dihedralTinyRowPackets_CHI`).

* `exists_gaf02ChainEJA_row_dihedralTiny_CHI`: for EVERY `c_adj > 0`, at `ν = 1/20`, with
  `β₂ = min(σ/3, η₂, 1/(2·10⁶))` after the producer's `σ, η₂`, `γc = γ₀`, `σs, ζ` half the minimum
  of their upper bounds and `L_max` the maximum of its lower bounds, all 51 premises hold and the
  producer yields a `Gaf02ChainEJA … c_adj` on the fixture at the base point
  `dihedralTinyBase_CHI`.
* `exists_gaf02ChainEJA_row_dihedralTiny_small_CHI`: the same at `c_adj = 10⁻⁵`; consumer of the
  object's (JA) accessors `c_lt_adj`, `Gaf02ChainEJA.ja_GAFC` (`c₃ < 10⁻⁵`, `Σ_j ≤ ε_j/10000`).

No premise mentions `c_adj` or the `c_j`, so a small `c_adj` only shrinks GAF01's choice; the
thresholds `σ, η₂, θ_t, θ_s, e_j` of that choice are then met by the adapted `β₂, σs, ζ, L_max`.
The fixture's circle, edge and slim families are empty: the instance checks joint satisfiability
of the premise group and of the object's fields, not a nonempty stage family.
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

/-- **`Gaf02ChainEJA` on a nonempty closed family, for every `c_adj > 0`.** At `ν = 1/20`, with
`β₂ = min(σ/3, η₂, 1/(2·10⁶))` chosen after the producer's thresholds `σ, η₂`, `γc = γ₀`, `σs` and
`ζ` half of the minimum of their upper bounds and `L_max` the maximum of its lower bounds, all 51
premises of `gaf02_chainEJA_row_GAFC` hold on the dihedral fixture, and the producer gives a
`Gaf02ChainEJA … c_adj` on it at the base point `dihedralTinyBase_CHI`. -/
theorem exists_gaf02ChainEJA_row_dihedralTiny_CHI (Kj : ℕ) {cadj : ℝ} (hcadj : 0 < cadj) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h) Kj Ξ Γ S eg c cw cadj),
      0 < β₂ ∧ 0 < γc ∧ 0 < σs ∧ 0 < ζ ∧ C.x₀ = dihedralTinyBase_CHI := by
  obtain ⟨θ, Ξ, c, Γ, S, eg, cw, hj, -, -, -, σ, η₂, γ₀, ηc, θt, hσ, -, hη₂, hγ₀, -, hηc, hθt,
    -, hrow⟩ := gaf02_chainEJA_row_GAFC Kj (ν := 1 / 20) (by norm_num) (by norm_num) hcadj
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
    hσs3 (by positivity) hζ4 hζ5 (by positivity) le_rfl dihedralTinyBase_CHI
  exact ⟨fun j => Ξ j (Γ j), Γ, S, eg, c, cw, β₂, γ₀, Lmax, σs, ζ, hq, C, hβ₂, hγ₀, hσs, hζ, hC⟩

/-- **Small `c_adj = 10⁻⁵`** (consumer of the (JA) accessors `c_lt_adj` and `ja_GAFC`): the
producer's premise group is still jointly satisfiable on the dihedral fixture, and the resulting
`Gaf02ChainEJA` has `c₃ < 10⁻⁵` and `Σ_j ≤ ε_j/10000`. -/
theorem exists_gaf02ChainEJA_row_dihedralTiny_small_CHI (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h) Kj Ξ Γ S eg c cw
        (1 / 100000)),
      0 < β₂ ∧ 0 < σs ∧ 0 < ζ ∧ C.x₀ = dihedralTinyBase_CHI ∧ c 2 < 1 / 100000 ∧
        ∀ j, S j ≤ Ξ j / 10000 := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, hβ₂, -, hσs, hζ, hx⟩ :=
    exists_gaf02ChainEJA_row_dihedralTiny_CHI Kj (cadj := 1 / 100000) (by norm_num)
  exact ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, hβ₂, hσs, hζ, hx, C.c_lt_adj, C.ja_GAFC.1⟩

end DifferentialGeometry.Geometry.Collapse
