import DifferentialGeometry.Geometry.Fibration.ActualStageCloudBudgetReordered
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdp01Reordered
import DifferentialGeometry.Geometry.Fibration.ActualStageChainRowReorderedInhabitant

/-!
# The reordered FC27 / EDP01 rows on a nonempty closed family (lane C14-CHAIN-INST, G6)

Satisfiability instances of the reordered rows (`β₂` after the first-test thresholds `σ, η₂`) on
the dihedral `LocalChartPacketsC14` fixture on `RP³ # RP³` (`dihedralTinyRowPackets_CHI`): with
`ν = 1/20`, `Δ = 1200`, `β₂ = min(σ/3, η₂, 1/(2·10⁶))` chosen after `σ, η₂`, `γc = γ₀`, `σs, ζ`
half the minimum of their upper bounds and `L_max` the maximum of its lower bounds, every premise
of the row holds at once, and the row's conclusion is obtained.

* GAF01's early ranges at `Γ_st = 1/1000` (`dihedralRowGamma_CHI`, `dihedralRowSigma_CHI`,
  `dihedralRowE_CHI`, `dihedralRow_ranges_CHI`), buffers `b_st = 1` ((DS) and CFS12's interior
  condition, `dihedralRow_buffer_CHI`).
* Helpers `dihedralRow_slim_numbers_CHI` (`σs, ζ` below their bounds), `dihedralRow_upper_CHI`.
* `fc27_row_reordered_dihedralTiny_CHI`, `fc27_row_nb_cw_reordered_dihedralTiny_CHI`,
  `fc27_row_nb_cw_interior_reordered_dihedralTiny_CHI`,
  `gaf02_edp01_row_reordered_dihedralTiny_CHI`.

The fixture's stage clouds are empty; the instances check the joint satisfiability of each row's
premise group, not a nonempty stage family.
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

/-- The stage graph constants are positive. -/
theorem gafGraphConst_pos_CHI (j : Fin 3) : 0 < gafGraphConst j := by
  fin_cases j
  · exact zero_lt_one.trans_le one_le_tcpGraphConst
  · exact egpGraphConst_pos_KC4
  · exact (by norm_num : (0 : ℝ) < 4000).trans_le four_le_sgpGraphBound_SGP4

/-- GAF01's quality at every stage of the instance: `Γ_st = 1/1000`. -/
def dihedralRowGamma_CHI : Fin 3 → ℝ := fun _ => 1 / 1000

/-- GAF01's radius ratio of the instance: half of `min(Γ/200, Γ³/(100 C_st))`. -/
def dihedralRowSigma_CHI : Fin 3 → ℝ := fun st =>
  min (dihedralRowGamma_CHI st / 200) (dihedralRowGamma_CHI st ^ 3 / (100 * gafGraphConst st)) / 2

/-- GAF01's accuracy of the instance: half of `min(1/100, ΓΣ/100, Σ/1000)`. -/
def dihedralRowE_CHI : Fin 3 → ℝ := fun st =>
  min (1 / 100) (min (dihedralRowGamma_CHI st * dihedralRowSigma_CHI st / 100)
    (dihedralRowSigma_CHI st / 1000)) / 2

/-- The instance's numbers lie in GAF01's early ranges (the inputs of the FC27 rows). -/
theorem dihedralRow_ranges_CHI :
    (∀ st, 0 < dihedralRowGamma_CHI st ∧ dihedralRowGamma_CHI st < 1) ∧
    (∀ st, 0 < dihedralRowSigma_CHI st ∧ dihedralRowSigma_CHI st <
      min (dihedralRowGamma_CHI st / 200)
        (dihedralRowGamma_CHI st ^ 3 / (100 * gafGraphConst st))) ∧
    ∀ st, 0 < dihedralRowE_CHI st ∧ dihedralRowE_CHI st < min (1 / 100)
      (min (dihedralRowGamma_CHI st * dihedralRowSigma_CHI st / 100)
        (dihedralRowSigma_CHI st / 1000)) := by
  have hG : ∀ st, 0 < dihedralRowGamma_CHI st := fun _ => by
    simp only [dihedralRowGamma_CHI]; norm_num
  have hS : ∀ st, 0 < dihedralRowSigma_CHI st ∧ dihedralRowSigma_CHI st <
      min (dihedralRowGamma_CHI st / 200)
        (dihedralRowGamma_CHI st ^ 3 / (100 * gafGraphConst st)) := fun st => by
    have hC := gafGraphConst_pos_CHI st
    have hm : 0 < min (dihedralRowGamma_CHI st / 200)
        (dihedralRowGamma_CHI st ^ 3 / (100 * gafGraphConst st)) := by
      have := hG st
      positivity
    exact ⟨half_pos hm, half_lt_self hm⟩
  refine ⟨fun st => ⟨hG st, by simp only [dihedralRowGamma_CHI]; norm_num⟩, hS, fun st => ?_⟩
  have hs := (hS st).1
  have hg := hG st
  have hm : 0 < min (1 / 100) (min (dihedralRowGamma_CHI st * dihedralRowSigma_CHI st / 100)
      (dihedralRowSigma_CHI st / 1000)) := by positivity
  exact ⟨half_pos hm, half_lt_self hm⟩

/-- The buffers `b_st = 1` satisfy (DS) `Γ_st ≤ d_1` and CFS12's interior condition
`Γ_st((80B + 31) + 2) < 1` at `Γ_st = 1/1000`. -/
theorem dihedralRow_buffer_CHI :
    (∀ st, dihedralRowGamma_CHI st ≤ min (1 / (8 * (5 / 3)))
      (min (1 / (4 * (128 * (fun _ : Fin 3 => (1 : ℝ)) st * (5 / 3) + 3)))
        (1 / (8 * (5 / 3 + 1))))) ∧
    ∀ st, dihedralRowGamma_CHI st *
      ((80 * (5 / 3) + 31) * (fun _ : Fin 3 => (1 : ℝ)) st + 2) < 1 := by
  refine ⟨fun st => ?_, fun st => ?_⟩
  · simp only [dihedralRowGamma_CHI, le_min_iff]
    norm_num
  · simp only [dihedralRowGamma_CHI]
    norm_num

/-- The slim / zero numbers of the instances: `σs` and `ζ` below all their upper bounds. -/
theorem dihedralRow_slim_numbers_CHI {θ θs A : ℝ} (hθ : 0 < θ) (hθs : 0 < θs) (hA : 0 < A) :
    ∃ σs ζ : ℝ, 0 < σs ∧ σs ≤ θ ^ 2 / 1000 ∧ σs ≤ A ^ 2 / 10 ^ 8 ∧ σs < θs ^ 2 / 10 ^ 6 ∧
      0 < ζ ∧ ζ ≤ θ ^ 2 / 1000 ∧ ζ ≤ A ^ 2 / 10 ^ 8 ∧ ζ ≤ 1 / (1000 * (1000000 * 1200)) ∧
      ζ < θs ^ 2 / 10 ^ 6 ∧ ζ < 1 / (100 * (1000000 * 1200)) := by
  have hm : 0 < min (min (θ ^ 2 / 1000) (A ^ 2 / 10 ^ 8)) (θs ^ 2 / 10 ^ 6) := by positivity
  have hn : 0 < min (min (min (θ ^ 2 / 1000) (A ^ 2 / 10 ^ 8))
      (min (1 / (1000 * (1000000 * 1200))) (θs ^ 2 / 10 ^ 6)))
      (1 / (100 * (1000000 * (1200 : ℝ)))) := by positivity
  have h1 := half_lt_self hm
  have h2 := half_lt_self hn
  exact ⟨_, _, half_pos hm, h1.le.trans ((min_le_left _ _).trans (min_le_left _ _)),
    h1.le.trans ((min_le_left _ _).trans (min_le_right _ _)), h1.trans_le (min_le_right _ _),
    half_pos hn, h2.le.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))),
    h2.le.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))),
    h2.le.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))),
    h2.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))),
    h2.trans_le (min_le_right _ _)⟩

/-- An upper bound of four numbers. -/
theorem dihedralRow_upper_CHI (a b c d : ℝ) : ∃ L : ℝ, a ≤ L ∧ b ≤ L ∧ c ≤ L ∧ d ≤ L :=
  ⟨max (max a b) (max c d), (le_max_left _ _).trans (le_max_left _ _),
    (le_max_right _ _).trans (le_max_left _ _), (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

/-- **The reordered FC27 row on the dihedral fixture.** At `ν = 1/20`, `Δ = 1200` and the
instance's `Γ, Σ, e`, with `β₂ = min(σ/3, η₂, 1/(2·10⁶))` after TCP06's thresholds, all premises of
`fc27_row_reordered_CHI` hold on the fixture and the row gives its planes. -/
theorem fc27_row_reordered_dihedralTiny_CHI :
    ∃ (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4),
      let P := dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h
      0 < β₂ ∧
      ∃ plane : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        ∀ st, ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          Module.finrank ℝ (plane st x) = gafStageDim st := by
  obtain ⟨Γ, sg, eg, hΓ, hsg, heg⟩ : ∃ Γ sg eg : Fin 3 → ℝ,
      (∀ st, 0 < Γ st ∧ Γ st < 1) ∧
      (∀ st, 0 < sg st ∧ sg st < min (Γ st / 200) (Γ st ^ 3 / (100 * gafGraphConst st))) ∧
      ∀ st, 0 < eg st ∧ eg st < min (1 / 100) (min (Γ st * sg st / 100) (sg st / 1000)) :=
    ⟨_, _, _, dihedralRow_ranges_CHI⟩
  obtain ⟨σ, η₂, γ₀, ηc, θ, η₁, ⟨hσ, -, hη₂, hγ₀, hηc, hθ, -, hη₁⟩, hrow⟩ :=
    fc27_row_reordered_CHI (Δ := 1200) (ν := 1 / 20) le_rfl (by norm_num) (by norm_num)
      Γ sg eg hΓ hsg heg
  have heg0 := (heg 0).1
  have hA : 0 < eg 1 / (20 * egpGraphConst) :=
    div_pos (heg 1).1 (mul_pos (by norm_num) egpGraphConst_pos_KC4)
  obtain ⟨β₂, hβ₂, hβ₂1, hβ₂σ, hβ₂η⟩ := fc27_row_order_satisfiable_CHI hσ hη₂
  obtain ⟨θs, Lc, η₀, Lc', η₀', ⟨hθs, -, -, hη₀, -, hη₀'⟩, hrow'⟩ := hrow β₂ hβ₂ hβ₂1
  obtain ⟨σs, ζ, hσs, hσs1, hσs2, hσs3, hζ, hζ1, hζ2, hζ3, hζ4, hζ5⟩ :=
    dihedralRow_slim_numbers_CHI hθ hθs hA
  obtain ⟨Lmax, hL0, hL1, hL2, hL3⟩ :=
    dihedralRow_upper_CHI (4 * (10 + 2 * (2000000 * 1200) + 1200 / 3)) σ⁻¹ Lc Lc'
  have hq : β₂ ≤ 1 / 4 := by linarith
  have hθ2 : (0 : ℝ) ≤ θ ^ 2 / 1000 := by positivity
  obtain ⟨plane, hplane⟩ := hrow' dihedralZeroSource dihedralTinyMetric_CHI
    dihedralTiny_hmetric_CHI dihedralTinyRho_CHI dihedralTinyRho_pos_CHI 0
    (dihedralTinyRowBeta_CHI β₂) σs 0 0 0 0 0 0 0 0 γ₀ 0 Lmax 0 0 (1 / 2) 0 (1 / 100)
    (1600 * (1000000 * 1200)) (1600 * (1000000 * 1200)) 0 ζ 0
    (dihedralTinyRowPackets_CHI β₂ γ₀ Lmax σs ζ hq) le_rfl (by norm_num) (by norm_num)
    (by norm_num) hL0 (by norm_num) le_rfl le_rfl (by norm_num) le_rfl hθ2
    (by rw [zero_mul]; positivity) (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_two_CHI]; linarith)
    (by rw [dihedralTinyRowBeta_two_CHI]; exact hβ₂η) hγ₀.le hγ₀ le_rfl hηc.le hη₁.le
    (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₁.le) hσs hσs1 (by positivity) hζ hζ1
    (by positivity) (by norm_num) hL1 (by rw [mul_zero]; exact heg0)
    (dihedralTinyRowBeta_two_CHI β₂) (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀.le) hL2
    hσs3 (by positivity) hζ4 hζ5 (by positivity)
    hη₀'.le (by norm_num) (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀'.le) hL3
    (by positivity) (by rw [zero_mul]; positivity) hσs2 (by positivity) hζ2 hζ3 (by positivity)
    (fun _ _ => dihedralTinyBase_CHI)
    (fun st x hx => by
      rw [gafCloudEnlarged_eq_empty_CHI _ (by fin_cases st <;> rfl)] at hx
      exact absurd hx (notMem_empty x))
  exact ⟨β₂, γ₀, Lmax, σs, ζ, hq, hβ₂, plane, fun st x hx => (hplane st x hx).1⟩

/-- **The reordered `N_b`/`c_w` FC27 row ((DS) buffers) on the dihedral fixture.** At
`ν = 1/20`, `Δ = 1200`, the instance's `Γ, Σ, e` and buffers `b_st = 1`, with
`β₂ = min(σ/3, η₂, 1/(2·10⁶))` after TCP06's thresholds, all premises of
`fc27_row_nb_cw_reordered_CHI` hold on the fixture and the row gives its weight constants and
planes. -/
theorem fc27_row_nb_cw_reordered_dihedralTiny_CHI :
    ∃ cw : Fin 3 → ℝ, (∀ st, 0 ≤ cw st) ∧
    ∃ (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4),
      let P := dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h
      0 < β₂ ∧
      ∃ plane : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        ∀ st, ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          Module.finrank ℝ (plane st x) = gafStageDim st := by
  obtain ⟨Γ, sg, eg, hΓ, hsg, heg, hΓb⟩ : ∃ Γ sg eg : Fin 3 → ℝ,
      (∀ st, 0 < Γ st ∧ Γ st < 1) ∧
      (∀ st, 0 < sg st ∧ sg st < min (Γ st / 200) (Γ st ^ 3 / (100 * gafGraphConst st))) ∧
      (∀ st, 0 < eg st ∧ eg st < min (1 / 100) (min (Γ st * sg st / 100) (sg st / 1000))) ∧
      ∀ st, Γ st ≤ min (1 / (8 * (5 / 3)))
        (min (1 / (4 * (128 * (fun _ : Fin 3 => (1 : ℝ)) st * (5 / 3) + 3)))
          (1 / (8 * (5 / 3 + 1)))) :=
    ⟨_, _, _, dihedralRow_ranges_CHI.1, dihedralRow_ranges_CHI.2.1, dihedralRow_ranges_CHI.2.2,
      dihedralRow_buffer_CHI.1⟩
  obtain ⟨cw, hcw, σ, η₂, γ₀, ηc, θ, η₁, ⟨hσ, -, hη₂, hγ₀, hηc, hθ, -, hη₁⟩, hrow⟩ :=
    fc27_row_nb_cw_reordered_CHI (Δ := 1200) (ν := 1 / 20) le_rfl (by norm_num) (by norm_num)
      Γ sg eg hΓ hsg heg (fun _ => 1) (fun _ => le_rfl) hΓb
  have heg0 := (heg 0).1
  have hA : 0 < eg 1 / (20 * egpGraphConst) :=
    div_pos (heg 1).1 (mul_pos (by norm_num) egpGraphConst_pos_KC4)
  obtain ⟨β₂, hβ₂, hβ₂1, hβ₂σ, hβ₂η⟩ := fc27_row_order_satisfiable_CHI hσ hη₂
  obtain ⟨θs, Lc, η₀, Lc', η₀', ⟨hθs, -, -, hη₀, -, hη₀'⟩, hrow'⟩ := hrow β₂ hβ₂ hβ₂1
  obtain ⟨σs, ζ, hσs, hσs1, hσs2, hσs3, hζ, hζ1, hζ2, hζ3, hζ4, hζ5⟩ :=
    dihedralRow_slim_numbers_CHI hθ hθs hA
  obtain ⟨Lmax, hL0, hL1, hL2, hL3⟩ :=
    dihedralRow_upper_CHI (4 * (10 + 2 * (2000000 * 1200) + 1200 / 3)) σ⁻¹ Lc Lc'
  have hq : β₂ ≤ 1 / 4 := by linarith
  have hθ2 : (0 : ℝ) ≤ θ ^ 2 / 1000 := by positivity
  obtain ⟨plane, hplane⟩ := hrow' dihedralZeroSource dihedralTinyMetric_CHI
    dihedralTiny_hmetric_CHI dihedralTinyRho_CHI dihedralTinyRho_pos_CHI 0
    (dihedralTinyRowBeta_CHI β₂) σs 0 0 0 0 0 0 0 0 γ₀ 0 Lmax 0 0 (1 / 2) 0 (1 / 100)
    (1600 * (1000000 * 1200)) (1600 * (1000000 * 1200)) 0 ζ 0
    (dihedralTinyRowPackets_CHI β₂ γ₀ Lmax σs ζ hq) le_rfl (by norm_num) (by norm_num)
    (by norm_num) hL0 (by norm_num) le_rfl le_rfl (by norm_num) le_rfl hθ2
    (by rw [zero_mul]; positivity) (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_two_CHI]; linarith)
    (by rw [dihedralTinyRowBeta_two_CHI]; exact hβ₂η) hγ₀.le hγ₀ le_rfl hηc.le hη₁.le
    (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₁.le) hσs hσs1 (by positivity) hζ hζ1
    (by positivity) (by norm_num) hL1 (by rw [mul_zero]; exact heg0)
    (dihedralTinyRowBeta_two_CHI β₂) (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀.le) hL2
    hσs3 (by positivity) hζ4 hζ5 (by positivity)
    hη₀'.le (by norm_num) (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀'.le) hL3
    (by positivity) (by rw [zero_mul]; positivity) hσs2 (by positivity) hζ2 hζ3 (by positivity)
    (fun _ _ => dihedralTinyBase_CHI)
    (fun st x hx => by
      rw [gafCloudEnlarged_eq_empty_CHI _ (by fin_cases st <;> rfl)] at hx
      exact absurd hx (notMem_empty x))
  exact ⟨cw, hcw, β₂, γ₀, Lmax, σs, ζ, hq, hβ₂, plane,
    fun st x hx => ((hplane st).1 x hx).1⟩

/-- **The reordered `N_b`/`c_w` FC27 row (interior condition) on the dihedral fixture.** At
`ν = 1/20`, `Δ = 1200`, the instance's `Γ, Σ, e` and buffers `b_st = 1`, with
`β₂ = min(σ/3, η₂, 1/(2·10⁶))` after TCP06's thresholds, all premises of
`fc27_row_nb_cw_interior_reordered_CHI` hold on the fixture and the row gives its weight constants
and planes. -/
theorem fc27_row_nb_cw_interior_reordered_dihedralTiny_CHI :
    ∃ cw : Fin 3 → ℝ, (∀ st, 0 ≤ cw st) ∧
    ∃ (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4),
      let P := dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h
      0 < β₂ ∧
      ∃ plane : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        ∀ st, ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
          Module.finrank ℝ (plane st x) = gafStageDim st := by
  obtain ⟨Γ, sg, eg, hΓ, hsg, heg, hΓb⟩ : ∃ Γ sg eg : Fin 3 → ℝ,
      (∀ st, 0 < Γ st ∧ Γ st < 1) ∧
      (∀ st, 0 < sg st ∧ sg st < min (Γ st / 200) (Γ st ^ 3 / (100 * gafGraphConst st))) ∧
      (∀ st, 0 < eg st ∧ eg st < min (1 / 100) (min (Γ st * sg st / 100) (sg st / 1000))) ∧
      ∀ st, Γ st * ((80 * (5 / 3) + 31) * (fun _ : Fin 3 => (1 : ℝ)) st + 2) < 1 :=
    ⟨_, _, _, dihedralRow_ranges_CHI.1, dihedralRow_ranges_CHI.2.1, dihedralRow_ranges_CHI.2.2,
      dihedralRow_buffer_CHI.2⟩
  obtain ⟨cw, hcw, σ, η₂, γ₀, ηc, θ, η₁, ⟨hσ, -, hη₂, hγ₀, hηc, hθ, -, hη₁⟩, hrow⟩ :=
    fc27_row_nb_cw_interior_reordered_CHI (Δ := 1200) (ν := 1 / 20) le_rfl (by norm_num)
      (by norm_num)
      Γ sg eg hΓ hsg heg (fun _ => 1) (fun _ => le_rfl) hΓb
  have heg0 := (heg 0).1
  have hA : 0 < eg 1 / (20 * egpGraphConst) :=
    div_pos (heg 1).1 (mul_pos (by norm_num) egpGraphConst_pos_KC4)
  obtain ⟨β₂, hβ₂, hβ₂1, hβ₂σ, hβ₂η⟩ := fc27_row_order_satisfiable_CHI hσ hη₂
  obtain ⟨θs, Lc, η₀, Lc', η₀', ⟨hθs, -, -, hη₀, -, hη₀'⟩, hrow'⟩ := hrow β₂ hβ₂ hβ₂1
  obtain ⟨σs, ζ, hσs, hσs1, hσs2, hσs3, hζ, hζ1, hζ2, hζ3, hζ4, hζ5⟩ :=
    dihedralRow_slim_numbers_CHI hθ hθs hA
  obtain ⟨Lmax, hL0, hL1, hL2, hL3⟩ :=
    dihedralRow_upper_CHI (4 * (10 + 2 * (2000000 * 1200) + 1200 / 3)) σ⁻¹ Lc Lc'
  have hq : β₂ ≤ 1 / 4 := by linarith
  have hθ2 : (0 : ℝ) ≤ θ ^ 2 / 1000 := by positivity
  obtain ⟨plane, hplane⟩ := hrow' dihedralZeroSource dihedralTinyMetric_CHI
    dihedralTiny_hmetric_CHI dihedralTinyRho_CHI dihedralTinyRho_pos_CHI 0
    (dihedralTinyRowBeta_CHI β₂) σs 0 0 0 0 0 0 0 0 γ₀ 0 Lmax 0 0 (1 / 2) 0 (1 / 100)
    (1600 * (1000000 * 1200)) (1600 * (1000000 * 1200)) 0 ζ 0
    (dihedralTinyRowPackets_CHI β₂ γ₀ Lmax σs ζ hq) le_rfl (by norm_num) (by norm_num)
    (by norm_num) hL0 (by norm_num) le_rfl le_rfl (by norm_num) le_rfl hθ2
    (by rw [zero_mul]; positivity) (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_two_CHI]; linarith)
    (by rw [dihedralTinyRowBeta_two_CHI]; exact hβ₂η) hγ₀.le hγ₀ le_rfl hηc.le hη₁.le
    (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₁.le) hσs hσs1 (by positivity) hζ hζ1
    (by positivity) (by norm_num) hL1 (by rw [mul_zero]; exact heg0)
    (dihedralTinyRowBeta_two_CHI β₂) (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀.le) hL2
    hσs3 (by positivity) hζ4 hζ5 (by positivity)
    hη₀'.le (by norm_num) (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀'.le) hL3
    (by positivity) (by rw [zero_mul]; positivity) hσs2 (by positivity) hζ2 hζ3 (by positivity)
    (fun _ _ => dihedralTinyBase_CHI)
    (fun st x hx => by
      rw [gafCloudEnlarged_eq_empty_CHI _ (by fin_cases st <;> rfl)] at hx
      exact absurd hx (notMem_empty x))
  exact ⟨cw, hcw, β₂, γ₀, Lmax, σs, ζ, hq, hβ₂, plane,
    fun st x hx => ((hplane st).1 x hx).1⟩


/-- **The reordered EDP01 row on the dihedral fixture.** At `ν = 1/20`, `c_adj = 1`, `Δ = 1200`,
with `β₂ = min(σ/3, η₂, 1/(2·10⁶))` after the producer's thresholds, all premises of
`gaf02_edp01_row_reordered_CHI` hold on the fixture; the row gives a chain with constant
selections whose scale is differentiable and positive. -/
theorem gaf02_edp01_row_reordered_dihedralTiny_CHI (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02Chain (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).toLocalChartPackets Kj Ξ Γ S eg
        c cw),
      0 < β₂ ∧ C.sel = (fun _ _ => dihedralTinyBase_CHI) ∧
        ∀ p, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) C.scale p ∧ 0 < C.scale p := by
  obtain ⟨θ, Ξ, c, Γ, S, eg, cw, hj, -, -, -, σ, η₂, γ₀, ηc, θt, hσ, -, hη₂, hγ₀, -, hηc, hθt,
    -, hrow⟩ := gaf02_edp01_row_reordered_CHI Kj (ν := 1 / 20) (cadj := 1) (by norm_num)
      (by norm_num) one_pos
  obtain ⟨-, -, -, -, -, -, -, heg0, -⟩ := hj 0
  obtain ⟨-, -, -, -, -, -, -, heg1, -⟩ := hj 1
  have hA : 0 < eg 1 / (20 * egpGraphConst) :=
    div_pos heg1 (mul_pos (by norm_num) egpGraphConst_pos_KC4)
  obtain ⟨β₂, hβ₂, hβ₂1, hβ₂σ, hβ₂η⟩ := fc27_row_order_satisfiable_CHI hσ hη₂
  obtain ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, hη₁, -, hη₀₁, hθs, -, -, hη₀₂, hrow'⟩ :=
    hrow β₂ hβ₂ hβ₂1 1200 le_rfl
  obtain ⟨σs, ζ, hσs, hσs1, hσs2, hσs3, hζ, hζ1, hζ2, hζ3, hζ4, hζ5⟩ :=
    dihedralRow_slim_numbers_CHI hθt hθs hA
  obtain ⟨Lmax, hL0, hL1, hL2, hL3⟩ :=
    dihedralRow_upper_CHI (4 * (10 + 2 * (2000000 * 1200) + 1200 / 3)) σ⁻¹ Lc₁ Lc₂
  have hq : β₂ ≤ 1 / 4 := by linarith
  have hθt2 : (0 : ℝ) ≤ θt ^ 2 / 1000 := by positivity
  obtain ⟨C, hC, -, hC2⟩ := hrow' (dihedralTinyRowPackets_CHI β₂ γ₀ Lmax σs ζ hq) le_rfl
    (by norm_num) (by norm_num) (by norm_num) hL0 (by norm_num) le_rfl le_rfl (by norm_num)
    le_rfl hθt2 (by rw [zero_mul]; positivity) (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_two_CHI]; linarith)
    (by rw [dihedralTinyRowBeta_two_CHI]; exact hβ₂η)
    hγ₀.le hγ₀ le_rfl hηc.le hη₁.le (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₁.le) hσs
    hσs1 (by positivity) hζ hζ1 (by positivity) (by norm_num) hL1
    (by rw [mul_zero]; exact heg0) hη₀₁.le (by norm_num)
    (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀₁.le) hL2 (by positivity)
    (by rw [zero_mul]; positivity) hσs2 (by positivity) hζ2 hζ3 (by positivity)
    (dihedralTinyRowBeta_two_CHI β₂) (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀₂.le) hL3
    hσs3 (by positivity) hζ4 hζ5 (by positivity) le_rfl (fun _ _ => dihedralTinyBase_CHI)
    (fun st x hx => by
      rw [gafCloudEnlarged_eq_empty_CHI _ (by fin_cases st <;> rfl)] at hx
      exact absurd hx (notMem_empty x))
  exact ⟨fun j => Ξ j (Γ j), Γ, S, eg, c, cw, β₂, γ₀, Lmax, σs, ζ, hq, C, hβ₂, hC,
    fun p => ⟨(hC2 p).1, (hC2 p).2.2.2⟩⟩

end DifferentialGeometry.Geometry.Collapse
