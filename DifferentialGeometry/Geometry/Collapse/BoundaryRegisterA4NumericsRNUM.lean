import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterRowNumericsApplicationsRNUM
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsFinalApplicationsBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesCore

/-!
# Register-level numerics of A4, FC43 and (R1) on the boundary route (S-REG-NUM2, G4b)

Continuation of `BoundaryRegisterRowNumericsRNUM` / `...ApplicationsRNUM` (no new field, no new
structure).

* `BoundaryEarlyOver_BSTD1.a4_numerics_RNUM`: the numerical premises of the BASES core
  (`basesCore_BBP`: `β 2 ≤ 10⁻⁷`, `γ ≤ 1/2`, `σ_c ≤ 1/4`, `b ≤ 1/(1000Δ)`) and of the circle chart
  (`γ + β 2 < 1/10`) from the early choice and the producer's prefix `P` (`P.β₂_le7`,
  `P.γ_le_γT`, `P.σc_le10`; `b` from `b < s/10⁵`, `s < b'/10⁵`, `b' < 1/(10⁶Δ)`).
* `exists_boundaryRegister_rowPremises_index_RNUM`: the row premises of
  `exists_boundaryRegister_rowPremises_RNUM` together with the TAIL INDEX clause of O-WF's
  `source_buffered_OWF` (`32·10⁶Δ ≤ n`, `n = m + 1` the supply index): a larger `n₀`.
* `r1_of_theta_le_RNUM`: N76-2's (R1) `16 P_* θ ≤ eg j` from `θ ≤ ϑ₀` and a CHI record with
  `ϑ₀ ≤ min_j eg j/(16 P_*)` (the certificate's `χ`).
* consumers: `BoundaryGaf02ChainE.basesCore_register_RNUM` (the BASES core from the register facts),
  `fc43_row_register_RNUM` (FC43's conjunction on a chain, with the `r_∂` block of the register).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-! ### The early choice: A4's numerical premises -/

namespace BoundaryEarlyOver_BSTD1

variable {Θ : BoundaryProducerThresholds_BSTD1} (E : BoundaryEarlyOver_BSTD1 Θ)

/-- A4's numerical premises read off the early choice and the producer's prefix `P`:
`β 2 ≤ 10⁻⁷`, `γ ≤ 1/2`, `γ + β 2 < 1/10`, `σ_c ≤ 1/4`, `b ≤ 1/(1000Δ)`. -/
theorem a4_numerics_RNUM {P : C14PreFinal}
    (hEP : E.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1) :
    E.β 2 ≤ 1 / 10000000 ∧ E.γ ≤ 1 / 2 ∧ E.γ + E.β 2 < 1 / 10 ∧ E.σc ≤ 1 / 4 ∧
      E.b ≤ 1 / (1000 * E.Δ) := by
  have eβ₂ : E.β₂ = P.β₂ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.β₂) hEP
  have eγ : E.γ = P.γ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.γ) hEP
  have eσc : E.σc = P.σc := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.σc) hEP
  have hβ : E.β 2 ≤ 1 / 10000000 := by
    rw [E.β_two, eβ₂]
    exact P.β₂_le7
  have hγ : E.γ ≤ 1 / 20 := by
    rw [eγ]
    linarith [P.γ_le_γT, P.γT_le]
  have hΔ := E.Δ_pos
  have hb : E.b ≤ 1 / (1000 * E.Δ) := by
    have h3 := E.b'_lt
    rw [lt_div_iff₀ (by positivity)] at h3
    rw [le_div_iff₀ (by positivity)]
    have h12 : E.b ≤ E.b' / 10000000000 := by linarith [E.b_lt_s, E.s_lt_b']
    have hb0 := E.b_pos
    nlinarith [mul_le_mul_of_nonneg_right h12 (by positivity : (0 : ℝ) ≤ 1000 * E.Δ)]
  exact ⟨hβ, by linarith, by linarith, by rw [eσc]; linarith [P.σc_le10], hb⟩

end BoundaryEarlyOver_BSTD1

/-! ### (R1) of N76-2 -/

/-- N76-2's (R1): `16 P_* θ ≤ eg j` for every `θ ≤ ϑ₀` when the CHI record has
`ϑ₀ ≤ min_j eg j/(16 P_*)` (the record of the D76-2 certificate). -/
theorem r1_of_theta_le_RNUM {ϑ₀ θ : ℝ} {eg : Fin 3 → ℝ}
    (hϑ : ϑ₀ ≤ min (eg 0) (min (eg 1) (eg 2)) / (16 * bmConst_BAUGC)) (hθ : θ ≤ ϑ₀) :
    ∀ j, 16 * bmConst_BAUGC * θ ≤ eg j := by
  have hP0 : 0 < 16 * bmConst_BAUGC := by linarith [one_le_bmConst_BAUGC]
  intro j
  have h1 : θ * (16 * bmConst_BAUGC) ≤ min (eg 0) (min (eg 1) (eg 2)) :=
    (le_div_iff₀ hP0).1 (hθ.trans hϑ)
  have hj : min (eg 0) (min (eg 1) (eg 2)) ≤ eg j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  linarith

/-! ### The tail index -/

/-- **The row premises of `exists_boundaryRegister_rowPremises_RNUM` and O-WF's tail index**: on
every member `m ≥ n₀` also `32·10⁶Δ ≤ m + 1` (the supply index; the premise of
`source_buffered_OWF`). -/
theorem exists_boundaryRegister_rowPremises_index_RNUM {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
    {egOf : Ch → Fin 3 → ℝ} (EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf)
    (Sq : BoundaryStandingSequence_BSTD1 K A
      (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar) (c2 : ℝ) :
    EW.θ < 1 / 100 ∧ ∃ V : ℝ, ∃ R : BoundaryRegisterOverXBA_BSTD2 EW.early V,
      0 < R.rd ∧ R.rd < 1 / 10000 ∧ 20 * (c2 + 1) * R.rd < 1 / 1000000 ∧
      ∃ n₀ : ℕ, ∀ m, n₀ ≤ m → BoundaryMemberOutputXBA_BSTD2 Sq m R ∧
        1000 * boundaryCounterexampleRatio Sq.δ₀ (m + 1) ^ 2 <
          EW.early.w / (2 * (1 + 2 * EW.early.Λ⁻¹) ^ 3) * min (1 / 2) (R.rd / 4) ^ 2 ∧
        32 * (1000000 * EW.early.Δ) ≤ ((m + 1 : ℕ) : ℝ) := by
  obtain ⟨hθ, V, R, h1, h2, h3, n₀, hmem⟩ := exists_boundaryRegister_rowPremises_RNUM EW Sq c2
  refine ⟨hθ, V, R, h1, h2, h3, max n₀ ⌈32 * (1000000 * EW.early.Δ)⌉₊, fun m hm => ?_⟩
  obtain ⟨hm1, hm2⟩ := hmem m ((le_max_left _ _).trans hm)
  refine ⟨hm1, hm2, ?_⟩
  have hc : 32 * (1000000 * EW.early.Δ) ≤ (m : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hm)
  have hm' : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  linarith

/-! ### Consumers -/

variable {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
  {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
  {egOf : Ch → Fin 3 → ℝ} {EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf}
  {Sq : BoundaryStandingSequence_BSTD1 K A
    (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar}
  {V : ℝ} {R : BoundaryRegisterOverXBA_BSTD2 EW.early V} {m : ℕ}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W m).pieceInterior ⊤) 3}
  {S : BoundarySupply K A EW.early.β R.βd R.εN EW.early.Λ EW.early.w EW.early.Δ EW.early.σs
    EW.early.σc EW.early.μ EW.early.b EW.early.s EW.early.b' EW.early.s' EW.early.ε EW.early.γc
    EW.early.βc R.Lmax EW.early.τ EW.early.γ R.δlocal EW.early.εr EW.early.e EW.early.T V
    EW.early.vs EW.early.ζ EW.early.Λz EW.θ (Sq.W m) (Sq.g m)
    (boundaryCounterexampleRatio Sq.δ₀ (m + 1)) (m + 1) (Sq.B m) oM}
  {Γ Sg eg : Fin 3 → ℝ} {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg}
  {Kj : ℕ} {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The BASES core of the chain from the register facts**: `β 2 ≤ 10⁻⁷`, `γ ≤ 1/2`,
`σ_c ≤ 1/4`, `b ≤ 1/(1000Δ)` (A4's core premises) from `a4_numerics_RNUM`. -/
theorem basesCore_register_RNUM {P : C14PreFinal}
    (hEP : EW.early.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1) :
    Nonempty (BoundaryGaf02BasesCore_BIFc C.toChain) := by
  obtain ⟨hβ, hγ, -, hσ, hb⟩ := EW.early.toBoundaryEarlyOver_BSTD1.a4_numerics_RNUM hEP
  exact ⟨C.basesCore_BBP hβ hγ hσ hb⟩

/-- **FC43's conjunction on the chain at the register** (A4 output `hA4` as the hypothesis): the
`r_∂` block `hrd hrd4 hrdc hprem hθ` of `fc43_rowAll_V2b_BGR` from the register. -/
theorem fc43_row_register_RNUM
    (hA4 : ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs)
    (hrd : R.rd ≤ (bdryRdRequest_RNUM (c 2)).rd V R.δlocal R.Lmax R.βd R.εN R.Hd)
    (hmem : BoundaryMemberOutputXBA_BSTD2 Sq m R) :
    type_of% (C.fc43_rowAll_V2b_BGR hA4 (rd := R.rd) R.rd_pos
      R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM
      (R.toBoundaryRegisterOver_BSTD1.rd_mul_lt_of_request_RNUM hrd) hmem.1.1.2 EW.θ_lt) :=
  C.fc43_rowAll_V2b_BGR hA4 R.rd_pos R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM
    (R.toBoundaryRegisterOver_BSTD1.rd_mul_lt_of_request_RNUM hrd) hmem.1.1.2 EW.θ_lt

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
