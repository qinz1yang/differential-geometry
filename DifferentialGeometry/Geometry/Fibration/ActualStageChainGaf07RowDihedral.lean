import DifferentialGeometry.Geometry.Fibration.ActualStageChainRowsInhabitant
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07Row

/-!
# GAF07: all premises at once on a `K = 5` dihedral final-family fixture

Blueprint `master207B.tex`, GAF07 (B:6049–6165); the row `Gaf02ChainEJA.gaf07_row_GAFD` needs,
beyond the chain, the packet's TCP01 range (`β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10`) and, for the standard
smooth slim type, `K ≥ 5` and an orientation. Lane C14-CHAIN-INST's dihedral fixture
`dihedralRowZ_CHI` has `K = 0` and `β₂ ≤ 5·10⁻⁷`; this file reruns its construction at `K = 5`
with `β₂ ≤ 10⁻⁷`.

* `dihedralRowZ5_GAFD`: the dihedral `LocalChartPacketsC14Z` at `K = 5`.
* `exists_gaf02ChainEJA_rowsZ5_dihedralTiny_GAFD`: a chain with (JA) on it, `0 < β₂ ≤ 10⁻⁷`.
* `exists_gaf07_row_dihedralTiny_GAFD`: every premise of GAF07 holds there and the row holds. The
  three stage families of the fixture are EMPTY (stated), so the stage clauses are VACUOUS on it
  (known gap D71-7 / D70-8; review 75's non-empty fixtures are outstanding).
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

/-- The final closed family `LocalChartPacketsC14Z` on the dihedral source at the producer's values,
with packet jet order `K = 5` (the copy of `dihedralRowZ_CHI`, which has `K = 0`). -/
def dihedralRowZ5_GAFD (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4) :
    LocalChartPacketsC14Z dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
      dihedralTinyRho_CHI dihedralTinyRho_pos_CHI 0 (dihedralTinyRowBeta_CHI β₂) 1200 σs 5 0 0 0 0
      0 0 0 γc 0 Lmax 0 0 (1 / 2) 0 (1 / 100) (1600 * (1000000 * 1200)) (1600 * (1000000 * 1200))
      0 ζ 0 dihedralTinyOrientation_CHI :=
  dihedralTinyPacketsC14Z_CHI (dihedralTinyRowBeta_le_CHI h) (by norm_num) (by norm_num)
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) le_rfl

/-- **The `K = 5` instance** (copy of `exists_gaf02ChainEJA_rowsZ_dihedralTiny_CHI`):
`gaf02_chainEJA_row_GAFC` at `ν = 1/20`, `c_adj = 10⁻⁵`, run on the dihedral final family at
`K = 5` with `β₂ = min(σ/3, η₂, 10⁻⁷)` (TCP01's range), `γc = min(γ₀, 1/100)`, `σs, ζ` half the
minimum of their upper bounds and `L_max` the maximum of its lower bounds and of FDC01's `L_c`. -/
theorem exists_gaf02ChainEJA_rowsZ5_dihedralTiny_GAFD (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      0 < β₂ ∧ β₂ ≤ 1 / 10000000 ∧ C.x₀ = dihedralTinyBase_CHI ∧ 0 < γc ∧ γc ≤ 1 / 100 ∧
        fdcLc_CHI β₂ ≤ Lmax := by
  obtain ⟨θ, Ξ, c, Γ, S, eg, cw, hj, -, -, -, σ, η₂, γ₀, ηc, θt, hσ, -, hη₂, hγ₀, -, hηc, hθt,
    -, hrow⟩ := gaf02_chainEJA_row_GAFC Kj (ν := 1 / 20) (cadj := 1 / 100000) (by norm_num)
      (by norm_num) (by norm_num)
  obtain ⟨-, -, -, -, -, -, -, heg0, -⟩ := hj 0
  obtain ⟨-, -, -, -, -, -, -, heg1, -⟩ := hj 1
  set β₂ : ℝ := min (min (σ / 3) η₂) (1 / 10000000) with hβ₂def
  have hβ₂ : 0 < β₂ := by positivity
  have hβ₂s7 : β₂ ≤ 1 / 10000000 := min_le_right _ _
  have hβ₂s : β₂ ≤ 1 / 2000000 := by linarith
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
    (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ hq).toLocalChartPacketsC14D.toLocalChartPacketsC14
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
  exact ⟨fun j => Ξ j (Γ j), Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, hq, C, hβ₂, hβ₂s7, hC, hγc,
    hγc1, hLF⟩


/-- **All premises of GAF07 hold at once** on the dihedral final-family fixture at `K = 5`: a chain
with (JA) exists (`exists_gaf02ChainEJA_rowsZ5_dihedralTiny_GAFD`), the TCP01 range `β₂ ≤ 10⁻⁷`,
`γ + β₂ < 1/10` (here `γ = 0`) and `K ≥ 5` hold, the orientation is the fixture's own, and the whole
GAF07 row holds. The fixture's circle, edge and slim families are EMPTY (stated), so the stage
clauses are vacuous on it — the known acceptance gap (D71-7, D70-8). -/
theorem exists_gaf07_row_dihedralTiny_GAFD (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).circle.centres = ∅ ∧
        (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).edge.centres = ∅ ∧
        (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).slim.centres = ∅ ∧
        ∃ (hβ : dihedralTinyRowBeta_CHI β₂ 2 ≤ 1 / 10000000)
          (hd : (0 : ℝ) + dihedralTinyRowBeta_CHI β₂ 2 < 1 / 10) (h5 : 5 ≤ 5),
          type_of% (Gaf02ChainEJA.gaf07_row_GAFD C hβ hd h5 dihedralTinyOrientation_CHI) := by
  exact (exists_gaf02ChainEJA_rowsZ5_dihedralTiny_GAFD Kj).imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun C hC => ⟨rfl, rfl, rfl, (dihedralTinyRowBeta_two_CHI _).trans_le hC.2.1,
      by rw [zero_add, dihedralTinyRowBeta_two_CHI]; linarith [hC.2.1], le_rfl,
      by
        exact C.gaf07_row_GAFD ((dihedralTinyRowBeta_two_CHI _).trans_le hC.2.1)
          (by rw [zero_add, dihedralTinyRowBeta_two_CHI]; linarith [hC.2.1]) le_rfl
          dihedralTinyOrientation_CHI⟩

end DifferentialGeometry.Geometry.Collapse
