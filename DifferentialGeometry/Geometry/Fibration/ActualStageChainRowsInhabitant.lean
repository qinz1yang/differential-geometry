import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJAInhabitant
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJARealization
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpHeightApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpBlocksApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainReplacement
import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroFaces
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimImage
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroBlock

/-!
# Chain rows on one nonempty closed instance (lane C14-CHAIN-INST, G4)

The satisfiability check of the delivered chain rows: on ONE `Gaf02ChainEJA` built by
`gaf02_chainEJA_row_GAFC` at `c_adj = 10⁻⁵` on the dihedral final family `LocalChartPacketsC14Z`
(`RP³ # RP³`, `dihedralRowZ_CHI`), every row below is applied with ALL of its hypotheses
discharged:

* EDP01 (`Gaf02ChainE.edp01_GAFC`; its inputs `0 ≤ c_w`, `Σ₁ ≤ ε₁/10000` from the rough data);
* EDP02's low branch (`Gaf02Chain.low_branch_EDPE`, `c₃ < 10⁻⁵`) and
  `Gaf02Chain.final_eq_original_of_empty_EDPE`;
* the EDP-E (A)-class rows `Gaf02Chain.edge_height_EH_EDPE`, `Gaf02Chain.edge_homotopy_conorm_EDPE`
  (`0 < γc ≤ 1/100`, `βc ≤ 10⁻⁵`), `edp04_trace_compact_C14_EDPE` (`μ, τ ≤ 10⁻⁸`, `σc ≤ 1/1000`,
  `b·1000Δ ≤ 1`), with `ϑ = κΔ < 10⁻⁶`, `0 ≤ ε < 1`;
* FDC01 (`fdc01_chain_replacement_FDC`: `L_max ≥ L_c`, `b, β₁ ≤ η₀`, `s < 10⁻⁶`, `μ, τ ≤ 10⁻⁸`,
  `σc ≤ 10⁻¹²`, `μΔ < 10⁻⁴`), with `L_c` chosen by the same producer order (after `Δ, β₂`);
* ZSP01 (ZE) on `Gaf02ChainE` (`Gaf02ChainE.zsp01_ZE_GAF8`) at the fixture's zero ball;
* ZSP03 on the final family (`zsp03_zero_face_inactive_C14Z_ZSP35`: empty circle, edge and slim
  families) and ZSP04 (`Gaf02Chain.zsp04_slab_image_ZSP35`); GAF01's (JA) (`Gaf02ChainEJA.ja_GAFC`).

Results: `exists_gaf02ChainEJA_rowsZ_dihedralTiny_CHI` (the instance, with `0 < γc ≤ 1/100` and
`L_max ≥ fdcLc_CHI β₂`), `gaf02_rows_dihedralTiny_CHI` (the rows on every packet of that type, given
those numbers and the empty stage families), `exists_gaf02_rows_dihedralTiny_CHI` (both together).
No two hypotheses conflict. The fixture's circle, edge and slim families are empty, so the
index-quantified clauses (edge rows, FDC01, GAF06) are vacuous here; their numeric hypothesis
packages are what is checked. GAF06 / GAF07 (`c₃ < 1/1000`) are covered by `Gaf02ChainEJA`'s
hypothesis-free forms (`gaf06_GAFC`, `gaf07_*_interface_GAFC`).

Pitfall (for consumers of a concrete fixture): the rows are stated on a VARIABLE `PZ`. Applied to
the concrete fixture inside a large goal, matching the different parent-projection paths
(`P.circle` vs `P.toLocalChartPackets.circle`) unfolds the fixture and times out; `Exists.choose`
terms with syntactically different proof arguments also time out (hence `le_twelveHundred_CHI`).
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

/-- The final closed family `LocalChartPacketsC14Z` on the dihedral source at the producer's
values (the `C14Z` form of `dihedralTinyRowPackets_CHI`). -/
def dihedralRowZ_CHI (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4) :
    LocalChartPacketsC14Z dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
      dihedralTinyRho_CHI dihedralTinyRho_pos_CHI 0 (dihedralTinyRowBeta_CHI β₂) 1200 σs 0 0 0 0 0
      0 0 0 γc 0 Lmax 0 0 (1 / 2) 0 (1 / 100) (1600 * (1000000 * 1200)) (1600 * (1000000 * 1200))
      0 ζ 0 dihedralTinyOrientation_CHI :=
  dihedralTinyPacketsC14Z_CHI (dihedralTinyRowBeta_le_CHI h) (by norm_num) (by norm_num)
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) le_rfl

/-- `100 ≤ 1200`, one fixed proof term for FDC01's `Δ`-hypothesis. -/
theorem le_twelveHundred_CHI : (100 : ℝ) ≤ 1200 := by norm_num

/-- FDC01's replacement threshold `L_c` of `fdc01_chain_replacement_FDC` at `Δ = 1200` and the
edge quality `b` (`0` outside `(0, 10⁻⁶)`), as an opaque number. -/
def fdcLc_CHI (b : ℝ) : ℝ :=
  if hb : 0 < b ∧ b < 1 / 1000000 then
    (fdc01_chain_replacement_FDC (Δ := 1200) le_twelveHundred_CHI hb.1 hb.2).choose
  else 0

/-- **The instance**: `gaf02_chainEJA_row_GAFC` at `ν = 1/20`, `c_adj = 10⁻⁵`, run on the dihedral
final family with `β₂ = min(σ/3, η₂, 1/(2·10⁶))`, `γc = min(γ₀, 1/100)`, `σs, ζ` half the minimum
of their upper bounds and `L_max` the maximum of its lower bounds and of FDC01's `L_c`. -/
theorem exists_gaf02ChainEJA_rowsZ_dihedralTiny_CHI (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZ_CHI β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      0 < β₂ ∧ β₂ < 1 / 1000000 ∧ C.x₀ = dihedralTinyBase_CHI ∧ 0 < γc ∧ γc ≤ 1 / 100 ∧
        fdcLc_CHI β₂ ≤ Lmax := by
  obtain ⟨θ, Ξ, c, Γ, S, eg, cw, hj, -, -, -, σ, η₂, γ₀, ηc, θt, hσ, -, hη₂, hγ₀, -, hηc, hθt,
    -, hrow⟩ := gaf02_chainEJA_row_GAFC Kj (ν := 1 / 20) (cadj := 1 / 100000) (by norm_num)
      (by norm_num) (by norm_num)
  obtain ⟨-, -, -, -, -, -, -, heg0, -⟩ := hj 0
  obtain ⟨-, -, -, -, -, -, -, heg1, -⟩ := hj 1
  set β₂ : ℝ := min (min (σ / 3) η₂) (1 / 2000000) with hβ₂def
  have hβ₂ : 0 < β₂ := by positivity
  have hβ₂s : β₂ ≤ 1 / 2000000 := min_le_right _ _
  have hβ₂σ : β₂ ≤ σ / 3 := (min_le_left _ _).trans (min_le_left _ _)
  have hβ₂η : β₂ ≤ η₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hβ₂1 : β₂ < 1 / 1000000 := by linarith
  obtain ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, hη₁, -, hη₀₁, hθs, -, -, hη₀₂, hrow'⟩ :=
    hrow β₂ hβ₂ hβ₂1 1200 le_rfl
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
  set Lmax : ℝ := max (4 * (10 + 2 * (2000000 * 1200) + 1200 / 3))
    (max σ⁻¹ (max Lc₁ (max Lc₂ (fdcLc_CHI β₂)))) with hLdef
  have hL0 : 4 * (10 + 2 * (2000000 * (1200 : ℝ)) + 1200 / 3) ≤ Lmax := le_max_left _ _
  have hL1 : σ⁻¹ ≤ Lmax := (le_max_left _ _).trans (le_max_right _ _)
  have hL2 : Lc₁ ≤ Lmax := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hL3 : Lc₂ ≤ Lmax := (((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  have hLF : fdcLc_CHI β₂ ≤ Lmax := (((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  obtain ⟨γc, hγc, hγc1, hγcγ⟩ : ∃ x : ℝ, 0 < x ∧ x ≤ 1 / 100 ∧ x ≤ γ₀ :=
    ⟨min γ₀ (1 / 100), lt_min hγ₀ (by norm_num), min_le_right _ _, min_le_left _ _⟩
  have hq : β₂ ≤ 1 / 4 := by linarith
  have hθt2 : (0 : ℝ) ≤ θt ^ 2 / 1000 := by positivity
  obtain ⟨C, hC⟩ := hrow'
    (dihedralRowZ_CHI β₂ γc Lmax σs ζ hq).toLocalChartPacketsC14D.toLocalChartPacketsC14
    le_rfl (by norm_num) (by norm_num) (by norm_num) hL0 (by norm_num) le_rfl le_rfl (by norm_num)
    le_rfl hθt2
    (by rw [zero_mul]; positivity) (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_two_CHI]; linarith)
    (by rw [dihedralTinyRowBeta_two_CHI]; exact hβ₂η)
    hγ₀.le hγc hγcγ hηc.le hη₁.le (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₁.le) hσs
    hσs1
    (by positivity) hζ hζ1 (by positivity) (by norm_num) hL1 (by rw [mul_zero]; exact heg0)
    hη₀₁.le (by norm_num) (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀₁.le) hL2
    (by positivity) (by rw [zero_mul]; positivity) hσs2 (by positivity) hζ2 hζ3 (by positivity)
    (dihedralTinyRowBeta_two_CHI β₂) (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀₂.le) hL3
    hσs3 (by positivity) hζ4 hζ5 (by positivity) le_rfl dihedralTinyBase_CHI
  exact ⟨fun j => Ξ j (Γ j), Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, hq, C, hβ₂, hβ₂1, hC, hγc,
    hγc1, hLF⟩

/-- `fdcLc_CHI` is FDC01's threshold on `(0, 10⁻⁶)`. -/
theorem fdcLc_eq_CHI {b : ℝ} (hb : 0 < b) (hb1 : b < 1 / 1000000) :
    fdcLc_CHI b =
      (fdc01_chain_replacement_FDC (Δ := 1200) le_twelveHundred_CHI hb hb1).choose := by
  rw [fdcLc_CHI, dite_eq_left ⟨hb, hb1⟩]

section Generic

/-! The rows on ANY `LocalChartPacketsC14Z` of the dihedral fixture's type (a variable `PZ`; on the
concrete fixture the elaborator unfolds it when matching parent-projection paths). -/

variable {β₂ γc Lmax σs ζ : ℝ}
  (PZ : LocalChartPacketsC14Z dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
    dihedralTinyRho_CHI dihedralTinyRho_pos_CHI 0 (dihedralTinyRowBeta_CHI β₂) 1200 σs 0 0 0 0 0 0 0
    0 γc 0 Lmax 0 0 (1 / 2) 0 (1 / 100) (1600 * (1000000 * 1200)) (1600 * (1000000 * 1200)) 0 ζ 0
    dihedralTinyOrientation_CHI)

/-- **FDC01's replacement contract on the dihedral type**: with `L_max ≥ fdcLc_CHI β₂`, every
premise of `fdc01_chain_replacement_FDC` holds on `PZ`'s `C14D` projection and every chain on it. -/
theorem fdc01_dihedralTiny_CHI {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000)
    (C : Gaf02Chain PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14.toLocalChartPackets Kj Ξ Γ S
      eg c cw) (hLF : fdcLc_CHI β₂ ≤ Lmax) :
    ∀ i ∈ PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14.edge.centres,
      i ∈ scaledSplittingStratum.{0, 0} dihedralTinyRho_CHI dihedralTinyRho_pos_CHI
        (dihedralTinyRowBeta_CHI β₂) 1 →
      ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
        Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * 1200 ∧
        Nonempty (@KleinerLottApprox dihedralZeroSource (WithLp 2 (ℝ × Z))
          (dihedralTinyMetricSpace_CHI.rescale (dihedralTinyRho_CHI i)⁻¹
            (inv_pos.mpr (dihedralTinyRho_pos_CHI i))) _ i (WithLp.toLp 2 ((0 : ℝ), z))
          (dihedralTinyRowBeta_CHI β₂ 1))) →
      ∀ q ∈ ball i (100 * 1200 * dihedralTinyRho_CHI i),
      |PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14.edge.coord i q| ≤ 401 / 100 * 1200 →
      PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14.edge.smoothing q / dihedralTinyRho_CHI q ≤
        401 / 100 * 1200 →
      ∃ j : PZ.toLocalChartPacketsC14D.toLocalChartPackets.edge.finite_centres.toFinset,
        dist q j.1 < 7 * 1200 * dihedralTinyRho_CHI j.1 := by
  intro i hi hstr hns q hq hηq htq
  have hs := (fdc01_chain_replacement_FDC (Δ := 1200) le_twelveHundred_CHI hβ₂ hβ₂1).choose_spec
  rw [fdcLc_eq_CHI hβ₂ hβ₂1] at hLF
  obtain ⟨j, -, hqj, -⟩ := hs.choose_spec.2.2 dihedralZeroSource dihedralTinyMetric_CHI
    dihedralTiny_hmetric_CHI dihedralTinyRho_CHI dihedralTinyRho_pos_CHI 0
    (dihedralTinyRowBeta_CHI β₂) σs 0 0 0 0 0 0 0 0 γc 0 Lmax 0 0 (1 / 2) 0 (1 / 100)
    (1600 * (1000000 * 1200)) (1600 * (1000000 * 1200)) 0 ζ 0
    PZ.toLocalChartPacketsC14D Kj Ξ Γ S eg c cw C
    hs.choose_spec.2.1.le (by norm_num)
    (by rw [dihedralTinyRowBeta_one_CHI]; exact hs.choose_spec.2.1.le) hLF (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) i hi hstr hns q hq hηq htq
  exact ⟨j, hqj⟩

/-- **The chain rows on the dihedral type**, all hypotheses discharged from a `Gaf02ChainEJA` at
`c_adj = 10⁻⁵` (its rough data and (JA)), `0 < γc ≤ 1/100`, `L_max ≥ fdcLc_CHI β₂` and the empty
stage families. -/
theorem gaf02_rows_dihedralTiny_CHI {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000)
    (C : Gaf02ChainEJA PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw
      (1 / 100000)) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hLF : fdcLc_CHI β₂ ≤ Lmax)
    (h0 : PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14.toLocalChartPackets.circle.centres = ∅)
    (h1 : PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14.toLocalChartPackets.edge.centres = ∅)
    (h2 : PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14.toLocalChartPackets.slim.centres = ∅) :
    let L := PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14
    (c 2 < 1 / 100000 ∧ ∀ j, S j ≤ Ξ j / 10000) ∧
    (∀ p, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) C.toChain.scale p ∧ 0 < C.toChain.scale p) ∧
    (C.toChain.E = cgpGlobalMap L.toLocalChartFamily L.zero ∧
      C.toChain.scale = dihedralTinyRho_CHI) ∧
    (∀ p, L.edge.smoothing p / dihedralTinyRho_CHI p ≤ 7 / 2 * 1200 →
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (C.toChain.E p)) / C.toChain.scale p < 4 * 1200) ∧
    (∀ j ∈ L.edge.centres, 50 * (c 2 + 100 * (gafDerivativeBound + 1) *
      (1 + gafCutoffConstant + 1 * cw 0 / S 0) * 0 * 1200) < 1 / 1000) ∧
    (∀ j ∈ L.edge.centres, c 2 + 50 * (c 2 + 100 * (gafDerivativeBound + 1) *
      (1 + gafCutoffConstant + 1 * cw 0 / S 0) * 0 * 1200) < 1 / 500) ∧
    (∀ j ∈ L.edge.centres, ∃ Q : Set dihedralZeroSource, IsCompact Q) ∧
    (∀ i ∈ L.edge.centres,
      i ∈ scaledSplittingStratum.{0, 0} dihedralTinyRho_CHI dihedralTinyRho_pos_CHI
        (dihedralTinyRowBeta_CHI β₂) 1 →
      ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
        Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * 1200 ∧
        Nonempty (@KleinerLottApprox dihedralZeroSource (WithLp 2 (ℝ × Z))
          (dihedralTinyMetricSpace_CHI.rescale (dihedralTinyRho_CHI i)⁻¹
            (inv_pos.mpr (dihedralTinyRho_pos_CHI i))) _ i (WithLp.toLp 2 ((0 : ℝ), z))
          (dihedralTinyRowBeta_CHI β₂ 1))) →
      ∀ q ∈ ball i (100 * 1200 * dihedralTinyRho_CHI i),
      |L.edge.coord i q| ≤ 401 / 100 * 1200 →
      L.edge.smoothing q / dihedralTinyRho_CHI q ≤ 401 / 100 * 1200 →
      ∃ j : L.toLocalChartPackets.edge.finite_centres.toFinset,
        dist q j.1 < 7 * 1200 * dihedralTinyRho_CHI j.1) ∧
    (∀ k : L.zero.finite_centres.toFinset, ∀ p,
      ‖C.toChain.E p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap L.toLocalChartFamily L.zero p (.inr (.inr (.inr (.inl k))))‖ <
          200 * c 2 / (1600 * (1000000 * 1200)) *
            (L.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ∧
    (∀ k : L.zero.finite_centres.toFinset,
      {p | 9 / 10 * (L.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
          (C.toChain.E p (.inr (.inr (.inr (.inl k))))).snd ∧
        ((C.toChain.E p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 =
          2 / 5 * (C.toChain.E p (.inr (.inr (.inr (.inl k))))).snd} =
      {p | (L.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p = 2 / 5}) ∧
    IsCompact C.toChain.slimSlabImage_ZSP35 := by
  intro L
  have hcw : 0 ≤ cw 0 := C.rough.cw_nonneg 0
  have hSΞ : S 0 ≤ Ξ 0 / 10000 := (C.rough.sigma_le 0).le
  have hc : c 2 < 1 / 100000 := C.c_lt_adj
  have hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * 0 *
      1200 < (1 : ℝ) / 1000000 := by norm_num
  have hE := C.toChain.final_eq_original_of_empty_EDPE h0 h1 h2
  refine ⟨⟨hc, C.ja_GAFC.1⟩, fun p => ⟨(C.toGaf02ChainE.edp01_GAFC.2 p).1,
      (C.toGaf02ChainE.edp01_GAFC.2 p).2.2.2⟩, ⟨hE.1, hE.2.1⟩, (C.toChain.low_branch_EDPE hc).1,
    fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
    fdc01_dihedralTiny_CHI PZ hβ₂ hβ₂1 C.toChain hLF,
    fun k p => (C.toGaf02ChainE.zsp01_ZE_GAF8 k p).2.2.1, fun k => ?_,
    (C.toChain.zsp04_slab_image_ZSP35).2.1⟩
  · exact (C.toChain.edge_height_EH_EDPE hcw hSΞ hc hϑ le_rfl (by norm_num) hj).1
  · exact (C.toChain.edge_homotopy_conorm_EDPE hcw hSΞ hc hϑ le_rfl (by norm_num) hγc hγc1
      (by norm_num) hj).1
  · obtain ⟨Q, hQ, -⟩ := edp04_trace_compact_C14_EDPE C.toChain hcw hSΞ hc hϑ le_rfl
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hj
    exact ⟨Q, hQ⟩
  · exact (zsp03_zero_face_inactive_C14Z_ZSP35 (P := PZ) C.toChain h0 h1 h2 k).1

end Generic

/-- **G4: the chain rows hold on one nonempty closed instance** (`exists_…_rowsZ_…` +
`gaf02_rows_dihedralTiny_CHI`, the empty stage families by `rfl`). -/
theorem exists_gaf02_rows_dihedralTiny_CHI (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZ_CHI β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      let L := (dihedralRowZ_CHI β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
      (c 2 < 1 / 100000 ∧ ∀ j, S j ≤ Ξ j / 10000) ∧
      (∀ p, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) C.toChain.scale p ∧ 0 < C.toChain.scale p) ∧
      (C.toChain.E = cgpGlobalMap L.toLocalChartFamily L.zero ∧
        C.toChain.scale = dihedralTinyRho_CHI) ∧
      (∀ p, L.edge.smoothing p / dihedralTinyRho_CHI p ≤ 7 / 2 * 1200 →
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
          (C.toChain.E p)) / C.toChain.scale p < 4 * 1200) ∧
      (∀ j ∈ L.edge.centres, 50 * (c 2 + 100 * (gafDerivativeBound + 1) *
        (1 + gafCutoffConstant + 1 * cw 0 / S 0) * 0 * 1200) < 1 / 1000) ∧
      (∀ j ∈ L.edge.centres, c 2 + 50 * (c 2 + 100 * (gafDerivativeBound + 1) *
        (1 + gafCutoffConstant + 1 * cw 0 / S 0) * 0 * 1200) < 1 / 500) ∧
      (∀ j ∈ L.edge.centres, ∃ Q : Set dihedralZeroSource, IsCompact Q) ∧
      (∀ i ∈ L.edge.centres,
        i ∈ scaledSplittingStratum.{0, 0} dihedralTinyRho_CHI dihedralTinyRho_pos_CHI
          (dihedralTinyRowBeta_CHI β₂) 1 →
        ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
          Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * 1200 ∧
          Nonempty (@KleinerLottApprox dihedralZeroSource (WithLp 2 (ℝ × Z))
            (dihedralTinyMetricSpace_CHI.rescale (dihedralTinyRho_CHI i)⁻¹
              (inv_pos.mpr (dihedralTinyRho_pos_CHI i))) _ i (WithLp.toLp 2 ((0 : ℝ), z))
            (dihedralTinyRowBeta_CHI β₂ 1))) →
        ∀ q ∈ ball i (100 * 1200 * dihedralTinyRho_CHI i),
        |L.edge.coord i q| ≤ 401 / 100 * 1200 →
        L.edge.smoothing q / dihedralTinyRho_CHI q ≤ 401 / 100 * 1200 →
        ∃ j : L.toLocalChartPackets.edge.finite_centres.toFinset,
          dist q j.1 < 7 * 1200 * dihedralTinyRho_CHI j.1) ∧
      (∀ k : L.zero.finite_centres.toFinset, ∀ p,
        ‖C.toChain.E p (.inr (.inr (.inr (.inl k)))) -
          cgpGlobalMap L.toLocalChartFamily L.zero p (.inr (.inr (.inr (.inl k))))‖ <
            200 * c 2 / (1600 * (1000000 * 1200)) *
              (L.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ∧
      (∀ k : L.zero.finite_centres.toFinset,
        {p | 9 / 10 * (L.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
            (C.toChain.E p (.inr (.inr (.inr (.inl k))))).snd ∧
          ((C.toChain.E p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 =
            2 / 5 * (C.toChain.E p (.inr (.inr (.inr (.inl k))))).snd} =
        {p | (L.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial p = 2 / 5}) ∧
      IsCompact C.toChain.slimSlabImage_ZSP35 := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, hβ₂, hβ₂1, -, hγc, hγc1, hLF⟩ :=
    exists_gaf02ChainEJA_rowsZ_dihedralTiny_CHI Kj
  exact ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C,
    gaf02_rows_dihedralTiny_CHI (dihedralRowZ_CHI β₂ γc Lmax σs ζ h) hβ₂ hβ₂1 C hγc
      hγc1 hLF rfl rfl rfl⟩

end DifferentialGeometry.Geometry.Collapse
