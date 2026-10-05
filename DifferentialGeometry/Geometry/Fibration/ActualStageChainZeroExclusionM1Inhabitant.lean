import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroExclusionM1Applications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainRowsInhabitant

/-!
# The actual-`M₁` zero exclusion on a nonempty closed instance (satisfiability check)

The consumers `eventually_fdc0{1,2,4}_M1_C14Z_EFC` add the parameter premises `εr < 1/2` and LC30's
`e ≤ 1/1000` to lane C14-FDCb's premise groups. The dihedral fixture of lane C14-CHAIN-INST
(`dihedralRowZ_CHI`, `RP³ # RP³`) has `e = 1/100`; this file uses the SAME fixture constructor
`dihedralTinyPacketsC14Z_CHI` at `e = 1/1000` (`dihedralRowZe_EFC`), reruns GAF02's producer
`gaf02_chainEJA_row_GAFC` on it (the only `e`-premise is `e < 1/40`), and applies the kernels.

* `dihedralRowZe_EFC`; `exists_gaf02ChainEJA_rowsZe_dihedralTiny_EFC` (for every `L'`, a chain with
  `L_max ≥ L'`, so any tail threshold `L_c` of the consumers is met);
* `zero_exclusion_M1_dihedralTiny_EFC` (on a variable `PZ` of the fixture's type): the kernels
  `Gaf02ChainE.relative_removal_zero_far_EFC` (`εr = 0 < 1/2`, `e = 1/1000`) and
  `Gaf02ChainE.fdc01_not_zero_of_mem_M1_EFC` (`μ = τ = 0`) with all premises discharged;
* `exists_zero_exclusion_M1_dihedralTiny_EFC`: the instance, with `β₂ ∈ (0, 10⁻⁶)` and
  `L' ≤ L_max`. (The consumers' premise `β₃ ≤ threeSplittingExclusionThreshold` concerns an opaque
  positive constant; the fixture's `β₃ = 3/20` is fixed by `ν = 1/20` and is not compared here.)

VACUOUS-TRUTH CHECK: the fixture's circle, edge and slim families are EMPTY and its one zero ball
covers the source (so `Z = M`, `M₁ = ∅`): the instance checks the joint satisfiability of the
parameter / family / chain premises, not the geometry of a nonempty edge family.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- The final closed family on the dihedral source at the producer's values with LC30's tolerance
`e = 1/1000` (`dihedralRowZ_CHI` has `e = 1/100`). -/
def dihedralRowZe_EFC (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4) :
    LocalChartPacketsC14Z dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
      dihedralTinyRho_CHI dihedralTinyRho_pos_CHI 0 (dihedralTinyRowBeta_CHI β₂) 1200 σs 0 0 0 0 0
      0 0 0 γc 0 Lmax 0 0 (1 / 2) 0 (1 / 1000) (1600 * (1000000 * 1200))
      (1600 * (1000000 * 1200)) 0 ζ 0 dihedralTinyOrientation_CHI :=
  dihedralTinyPacketsC14Z_CHI (dihedralTinyRowBeta_le_CHI h) (by norm_num) (by norm_num)
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) le_rfl

/-- **GAF02's producer on the `e = 1/1000` fixture**: `gaf02_chainEJA_row_GAFC` at `ν = 1/20`,
`c_adj = 10⁻⁵`, with `β₂ = min(σ/3, η₂, 1/(2·10⁶))`, `γc = γ₀`, `σs, ζ` half the minimum of their
upper bounds and `L_max` the maximum of its lower bounds and of an arbitrary `L'`. -/
theorem exists_gaf02ChainEJA_rowsZe_dihedralTiny_EFC (Kj : ℕ) (L' : ℝ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZe_EFC β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      0 < β₂ ∧ β₂ < 1 / 1000000 ∧ L' ≤ Lmax ∧ C.x₀ = dihedralTinyBase_CHI := by
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
    (max σ⁻¹ (max Lc₁ (max Lc₂ L'))) with hLdef
  have hL0 : 4 * (10 + 2 * (2000000 * (1200 : ℝ)) + 1200 / 3) ≤ Lmax := le_max_left _ _
  have hL1 : σ⁻¹ ≤ Lmax := (le_max_left _ _).trans (le_max_right _ _)
  have hL2 : Lc₁ ≤ Lmax := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hL3 : Lc₂ ≤ Lmax := (((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  have hLF : L' ≤ Lmax := (((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  have hq : β₂ ≤ 1 / 4 := by linarith
  have hθt2 : (0 : ℝ) ≤ θt ^ 2 / 1000 := by positivity
  obtain ⟨C, hC⟩ := hrow'
    (dihedralRowZe_EFC β₂ γ₀ Lmax σs ζ hq).toLocalChartPacketsC14D.toLocalChartPacketsC14
    le_rfl (by norm_num) (by norm_num) (by norm_num) hL0 (by norm_num) le_rfl le_rfl (by norm_num)
    le_rfl hθt2
    (by rw [zero_mul]; positivity) (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_two_CHI]; linarith)
    (by rw [dihedralTinyRowBeta_two_CHI]; exact hβ₂η)
    hγ₀.le hγ₀ le_rfl hηc.le hη₁.le (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₁.le) hσs
    hσs1
    (by positivity) hζ hζ1 (by positivity) (by norm_num) hL1 (by rw [mul_zero]; exact heg0)
    hη₀₁.le (by norm_num) (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀₁.le) hL2
    (by positivity) (by rw [zero_mul]; positivity) hσs2 (by positivity) hζ2 hζ3 (by positivity)
    (dihedralTinyRowBeta_two_CHI β₂) (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀₂.le) hL3
    hσs3 (by positivity) hζ4 hζ5 (by positivity) le_rfl dihedralTinyBase_CHI
  exact ⟨fun j => Ξ j (Γ j), Γ, S, eg, c, cw, β₂, γ₀, Lmax, σs, ζ, hq, C, hβ₂, hβ₂1, hLF, hC⟩

section Generic

variable {β₂ γc Lmax σs ζ : ℝ}
  (PZ : LocalChartPacketsC14Z dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
    dihedralTinyRho_CHI dihedralTinyRho_pos_CHI 0 (dihedralTinyRowBeta_CHI β₂) 1200 σs 0 0 0 0 0 0 0
    0 γc 0 Lmax 0 0 (1 / 2) 0 (1 / 1000) (1600 * (1000000 * 1200)) (1600 * (1000000 * 1200)) 0 ζ 0
    dihedralTinyOrientation_CHI)

/-- **The zero-exclusion kernels on the `e = 1/1000` dihedral type**, every premise discharged
(`εr = 0 < 1/2`, `e = 1/1000`, `μ = τ = 0`): for every slim set `Sl` the actual `M₂` is closed and
avoids the `.38`-zero balls, and a point of the actual `M₁` near an edge centre forces the centre
out of the zero stratum. -/
theorem zero_exclusion_M1_dihedralTiny_EFC {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (Ĉ : Gaf02ChainE PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw) :
    let L := PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14
    (∀ Z Sl M₁ M₂ : Set dihedralZeroSource,
      Z = ⋃ k : L.zero.finite_centres.toFinset, zspDomain_ZSP35 L.toLocalChartFamily L.zero k Ĉ.E →
      M₁ = (interior Z)ᶜ → M₂ = M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' Sl : Set M₁) →
      IsClosed M₂ ∧ ∀ q ∈ M₂, ∀ z (hz : z ∈ L.zero.centres),
        38 / 100 * (L.zero.zero z hz).radius ≤ dist q z) ∧
    ∀ i ∈ L.edge.centres, ∀ q ∈ ball i (100 * 1200 * dihedralTinyRho_CHI i),
      |L.edge.coord i q| ≤ 401 / 100 * 1200 →
      L.edge.smoothing q / dihedralTinyRho_CHI q ≤ 401 / 100 * 1200 →
      q ∈ (interior (⋃ k : L.zero.finite_centres.toFinset,
        zspDomain_ZSP35 L.toLocalChartFamily L.zero k Ĉ.E))ᶜ →
      i ∉ scaledSplittingStratum.{0, 0} dihedralTinyRho_CHI dihedralTinyRho_pos_CHI
        (dihedralTinyRowBeta_CHI β₂) 0 := by
  intro L
  have hεr : (0 : ℝ) < 1 / 2 := by norm_num
  refine ⟨fun Z Sl M₁ M₂ hZ hM₁ hM₂ =>
      Ĉ.relative_removal_zero_far_EFC hεr le_rfl hZ hM₁ hM₂, ?_⟩
  intro i hi q hq hηq htq hM₁
  exact Ĉ.fdc01_not_zero_of_mem_M1_EFC hεr (by norm_num) (by norm_num) hi hq hηq htq hM₁

end Generic

/-- **The instance**: on the `e = 1/1000` dihedral final family, for every `L'`, a chain with
`β₂ ∈ (0, 10⁻⁶)` and `L' ≤ L_max`, on which the zero-exclusion
kernels hold with all premises discharged. The fixture's edge family is empty
(`edge.centres = ∅`, so the edge-point premises are vacuous). -/
theorem exists_zero_exclusion_M1_dihedralTiny_EFC (Kj : ℕ) (L' : ℝ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZe_EFC β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      let L := (dihedralRowZe_EFC β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
      0 < β₂ ∧ β₂ < 1 / 1000000 ∧ L' ≤ Lmax ∧ L.edge.centres = ∅ ∧
      (∀ Z Sl M₁ M₂ : Set dihedralZeroSource,
        Z = ⋃ k : L.zero.finite_centres.toFinset,
          zspDomain_ZSP35 L.toLocalChartFamily L.zero k C.toGaf02ChainE.E →
        M₁ = (interior Z)ᶜ → M₂ = M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' Sl : Set M₁) →
        IsClosed M₂ ∧ ∀ q ∈ M₂, ∀ z (hz : z ∈ L.zero.centres),
          38 / 100 * (L.zero.zero z hz).radius ≤ dist q z) := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, hβ₂, hβ₂1, hL, -⟩ :=
    exists_gaf02ChainEJA_rowsZe_dihedralTiny_EFC Kj L'
  refine ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, hβ₂, hβ₂1, hL, rfl,
    (zero_exclusion_M1_dihedralTiny_EFC (dihedralRowZe_EFC β₂ γc Lmax σs ζ h)
      C.toGaf02ChainE).1⟩

end DifferentialGeometry.Geometry.Collapse
