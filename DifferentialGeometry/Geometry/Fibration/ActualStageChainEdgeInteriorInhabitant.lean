import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeInteriorApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroExclusionM1Inhabitant

/-!
# The interior of the actual `X₂` on a nonempty closed instance (satisfiability check)

The consumers `interior_edgeBase_eq_C14Z_EFC` / `fdc03_relative_removal_C14Z_EFC` carry the numeric
premises of EDP-E's rim rank: `Δ ≥ 2`, `c₃ < 10⁻⁵`, `C_ρΛΔ < 10⁻⁶`, `0 ≤ ε < 1`, `0 < γc ≤ 1/100`,
`βc ≤ 10⁻⁵`. On the `e = 1/1000` dihedral fixture of group G1
(`dihedralRowZe_EFC`; `Λ = ε = βc = 0`, `Δ = 1200`) GAF02's producer is rerun with
`γc = min(γ₀, 1/100)` (the producer only needs `0 < γc ≤ γ₀`) and `c_adj = 10⁻⁵`, so every
premise holds at once.

* `exists_gaf02ChainEJA_rowsZe_gc_dihedralTiny_EFC`;
* `edge_interior_dihedralTiny_EFC` (on a variable `PZ` of the fixture's type, every premise
  discharged) and the instance `exists_edge_interior_dihedralTiny_EFC`.

VACUOUS-TRUTH CHECK: the fixture's edge family is EMPTY, so `X₂ = ∅` and the equality is `∅ = ∅`:
the instance checks joint satisfiability of the parameter / family / chain premises only.
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

/-- **GAF02's producer on the `e = 1/1000` fixture with `γc ≤ 1/100`**: `gaf02_chainEJA_row_GAFC`
at `ν = 1/20`, `c_adj = 10⁻⁵`, with `β₂ = min(σ/3, η₂, 1/(2·10⁶))`, `γc = min(γ₀, 1/100)`,
`σs, ζ` half the minimum of their
upper bounds and `L_max` the maximum of its lower bounds and of an arbitrary `L'`. -/
theorem exists_gaf02ChainEJA_rowsZe_gc_dihedralTiny_EFC (Kj : ℕ) (L' : ℝ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZe_EFC β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      0 < β₂ ∧ β₂ < 1 / 1000000 ∧ L' ≤ Lmax ∧ 0 < γc ∧ γc ≤ 1 / 100 ∧
      C.x₀ = dihedralTinyBase_CHI := by
  obtain ⟨θ, Ξ, c, Γ, S, eg, cw, hj, -, -, -, σ, η₂, γ₀, ηc, θt, hσ, -, hη₂, hγ₀, -, hηc, hθt,
    -, hrow⟩ := gaf02_chainEJA_row_GAFC Kj (ν := 1 / 20) (cadj := 1 / 100000) (by norm_num)
      (by norm_num) (by norm_num)
  obtain ⟨-, -, -, -, -, -, -, heg0, -⟩ := hj 0
  obtain ⟨-, -, -, -, -, -, -, heg1, -⟩ := hj 1
  set γ' : ℝ := min γ₀ (1 / 100) with hγ'def
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
    (dihedralRowZe_EFC β₂ γ' Lmax σs ζ hq).toLocalChartPacketsC14D.toLocalChartPacketsC14
    le_rfl (by norm_num) (by norm_num) (by norm_num) hL0 (by norm_num) le_rfl le_rfl (by norm_num)
    le_rfl hθt2
    (by rw [zero_mul]; positivity) (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_three_CHI]; norm_num)
    (by rw [dihedralTinyRowBeta_two_CHI]; linarith)
    (by rw [dihedralTinyRowBeta_two_CHI]; exact hβ₂η)
    hγ₀.le (lt_min hγ₀ (by norm_num)) (min_le_left _ _) hηc.le hη₁.le
    (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₁.le) hσs
    hσs1
    (by positivity) hζ hζ1 (by positivity) (by norm_num) hL1 (by rw [mul_zero]; exact heg0)
    hη₀₁.le (by norm_num) (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀₁.le) hL2
    (by positivity) (by rw [zero_mul]; positivity) hσs2 (by positivity) hζ2 hζ3 (by positivity)
    (dihedralTinyRowBeta_two_CHI β₂) (by rw [dihedralTinyRowBeta_one_CHI]; exact hη₀₂.le) hL3
    hσs3 (by positivity) hζ4 hζ5 (by positivity) le_rfl dihedralTinyBase_CHI
  exact ⟨fun j => Ξ j (Γ j), Γ, S, eg, c, cw, β₂, γ', Lmax, σs, ζ, hq, C, hβ₂, hβ₂1,
    hLF, lt_min hγ₀ (by norm_num), min_le_right _ _, hC⟩

section Generic

variable {β₂ γc Lmax σs ζ : ℝ}
  (PZ : LocalChartPacketsC14Z dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
    dihedralTinyRho_CHI dihedralTinyRho_pos_CHI 0 (dihedralTinyRowBeta_CHI β₂) 1200 σs 0 0 0 0 0 0 0
    0 γc 0 Lmax 0 0 (1 / 2) 0 (1 / 1000) (1600 * (1000000 * 1200)) (1600 * (1000000 * 1200)) 0 ζ 0
    dihedralTinyOrientation_CHI)

/-- **The interior of the actual `X₂` on the dihedral type**, every numeric premise discharged
(`Δ = 1200`, `Λ = ε = βc = 0`, `c₃ < 10⁻⁵` from (JA) with `c_adj = 10⁻⁵`, `0 < γc ≤ 1/100`). -/
theorem edge_interior_dihedralTiny_EFC {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02ChainEJA PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw
      (1 / 100000)) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) :
    interior ({x | (gafStageQ PZ.toLocalChartPackets.toLocalChartFamily
          PZ.toLocalChartPackets.zero 1).starProjection (C.toChain.E x) ∈
            C.toChain.finalBase_BAS 1 ∧
        ∃ k : PZ.toLocalChartPackets.edge.finite_centres.toFinset,
          9 / 10 * dihedralTinyRho_CHI k.1 < blockMarkerCLM (V := fun _ : CGPTag
              PZ.toLocalChartPackets.toLocalChartFamily PZ.toLocalChartPackets.zero => ℝ²)
            (.inr (.inr (.inl k))) ((gafStageQ PZ.toLocalChartPackets.toLocalChartFamily
              PZ.toLocalChartPackets.zero 1).starProjection (C.toChain.E x)) ∧
          ‖blockVectorCLM (V := fun _ : CGPTag PZ.toLocalChartPackets.toLocalChartFamily
              PZ.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
            ((gafStageQ PZ.toLocalChartPackets.toLocalChartFamily
              PZ.toLocalChartPackets.zero 1).starProjection (C.toChain.E x))‖ <
          4 * 1200 * blockMarkerCLM (V := fun _ : CGPTag PZ.toLocalChartPackets.toLocalChartFamily
              PZ.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k)))
            ((gafStageQ PZ.toLocalChartPackets.toLocalChartFamily
              PZ.toLocalChartPackets.zero 1).starProjection (C.toChain.E x))} ∩
      ({p | PZ.edge.smoothing p / dihedralTinyRho_CHI p ≤ 7 / 20 * 1200} ∪
        {p | 0 < C.toChain.scale p ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
          PZ.toLocalChartPackets.toLocalChartFamily PZ.toLocalChartPackets.zero (C.toChain.E p)) /
            C.toChain.scale p ≤ 4 * 1200})) =
    {x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector PZ.toLocalChartPackets.toLocalChartFamily
        PZ.toLocalChartPackets.zero (C.toChain.E x)) / C.toChain.scale x < 4 * 1200} ∩
      {x | ∃ k : PZ.toLocalChartPackets.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag PZ.toLocalChartPackets.toLocalChartFamily
            PZ.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (C.toChain.E x) =
          dihedralTinyRho_CHI k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag PZ.toLocalChartPackets.toLocalChartFamily
            PZ.toLocalChartPackets.zero => ℝ²) (.inr (.inr (.inl k))) (C.toChain.E x)‖ <
          4 * 1200 * dihedralTinyRho_CHI k.1} := by
  have hΔ : (2 : ℝ) ≤ 1200 := by norm_num
  have hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * 0 * 1200 <
      (1 : ℝ) / 1000000 := by rw [mul_zero, zero_mul]; norm_num
  have hε : (0 : ℝ) < 1 := by norm_num
  have hβ : (0 : ℝ) ≤ 1 / 100000 := by norm_num
  exact interior_edgeBase_eq_C14Z_EFC (P := PZ) C.toGaf02ChainE hΔ C.c_lt_adj hϑ le_rfl hε hγc hγc1
    hβ

end Generic

/-- **The instance**: on the `e = 1/1000` dihedral final family, for every `L'`, a chain with
`β₂ ∈ (0, 10⁻⁶)`, `L' ≤ L_max` and `0 < γc ≤ 1/100` — every premise of
`edge_interior_dihedralTiny_EFC` (hence of `interior_edgeBase_eq_C14Z_EFC` and
`fdc03_relative_removal_C14Z_EFC`) — to which that theorem applies.
The fixture's edge family is empty (`edge.centres = ∅`: vacuous geometry). -/
theorem exists_edge_interior_dihedralTiny_EFC (Kj : ℕ) (L' : ℝ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZe_EFC β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      0 < β₂ ∧ β₂ < 1 / 1000000 ∧ L' ≤ Lmax ∧ 0 < γc ∧ γc ≤ 1 / 100 ∧
      (dihedralRowZe_EFC β₂ γc Lmax σs ζ h).edge.centres = ∅ ∧ C.x₀ = dihedralTinyBase_CHI := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, hβ₂, hβ₂1, hL, hγc, hγc1, hC⟩ :=
    exists_gaf02ChainEJA_rowsZe_gc_dihedralTiny_EFC Kj L'
  exact ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, hβ₂, hβ₂1, hL, hγc, hγc1, rfl, hC⟩

end DifferentialGeometry.Geometry.Collapse
