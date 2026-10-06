import DifferentialGeometry.Geometry.Collapse.BoundaryEarlyThreeBetacRNUM
import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterA4NumericsRNUM
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesV2bProductionOWF

/-!
# The three row-readiness records (lane S-REG-NUM3, G8)

Review 77 (D77-4, D77-9; questions 2 and 4): RNUM's suppliers do not have the quantifiers of the
statements H1 / H2, so the numerical evidence that the boundary rows consume is stated as THREE
records of concrete inequalities (no named predicate, no geometric success field), each bound to
the object it is about:

* `EarlyRowReady_RNUM E Cρ` (early evidence): on ONE early choice `E` (read through the stored
  choice `EW.early`) and the ONE constant `Cρ = 100 (b_der + 1)(1 + b_cut + c_w(0)/Σ₀)` of the
  CHOICE: `e < 1/1000` (N76-6), `Cρ Λ Δ < 10⁻⁶` (N76-9), `3 β_c ≤ β₂` (F1; G9), `β₂ ≤ 10⁻⁷`
  and `γ ≤ 1/20` (A4). Everything else the rows and A4 read from the early choice is a FIELD of it
  (`μ ≤ 10⁻⁸` is `μ_le8`, `σ_c ≤ 10⁻³` is `σc_le_milli`, `τ ≤ 10⁻⁸` follows from `τ_sqrt` and
  `ε < 1/100` (`tau_le_RNUM`), `b ≤ 1/(1000Δ)` from `b < s/10⁵`, `s < b'/10⁵`, `b' < 1/(10⁶Δ)`).
* `RegisterRowReady_RNUM R c₂` (register evidence): on the SAME register `R` and the CHOICE's
  `c₂`: `20 (c₂ + 1) r_∂ < 10⁻⁶` (BCG06, FC43, E4). `0 < r_∂` is `R.rd_pos`, `r_∂ < 1/10000` is
  `R.rd_phys` (`rd_lt_ten_thousandth_RNUM`), `θ < 1/100` is `EW.θ_lt`.
* `MemberRowReady_RNUM E m` (member evidence): the index bound `32 · 10⁶ Δ ≤ m + 1` of A4's
  source-buffering clause. The member's small quantities (`1000 δ_{m+1}² < w/(2(1+2Λ⁻¹)³) ·
  min(1/2, r_∂/4)²`, N76-3) are NOT repeated: they are the projection `hm.1.1.2` of the member
  output (`memberPremise_RNUM`).

Producers (each in the premises of its own supplier, with its own quantifier order):
`exists_boundaryEarlyWithChoice_ready_RNUM` (early; from the G9 producer and the requests
`bdryRowRequests_RNUM`), `exists_register_ready_RNUM` (register and members; from the late request
`bdryRdRequest_RNUM c₂` and the tail index) and the composite `exists_ready_package_RNUM`.
Consumers from the records alone (plus the chain's CHOICE validity): `a4_whole_ready_RNUM`
(A4 whole, with the three early premises `μ`, `τ`, `σ_c`), `bcg07_row_ready_RNUM` (the whole row,
F1 inside), `rim_mem_source_zero_ready_RNUM`, `bcg06_row_ready_RNUM`, `fc43_row_ready_RNUM`,
`exists_edgeParent_ready_RNUM`, `actualZeroDomain_cover_ready_RNUM`.
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

/-! ### The three records -/

/-- **Early row readiness** (evidence class (a) of D77-4): the numerical facts about ONE early
choice `E` and the CHOICE's constant `Cρ` that the early choice's fields do not give. -/
structure EarlyRowReady_RNUM {Θ : BoundaryProducerThresholds_BSTD1}
    {χ : BoundaryChainThresholds_BSTD2} (E : BoundaryEarlyOverX_BSTD2 Θ χ) (Cρ : ℝ) : Prop where
  e_lt : E.e < 1 / 1000
  hC : Cρ * E.Λ * E.Δ < 1 / 1000000
  three_βc : 3 * E.βc ≤ E.β₂
  β₂_le7 : E.β₂ ≤ 1 / 10000000
  γ_le : E.γ ≤ 1 / 20

/-- **Register row readiness** (evidence class (b)): the condition between the register's `r_∂`
and the CHOICE's `c₂`. -/
structure RegisterRowReady_RNUM {Θ : BoundaryProducerThresholds_BSTD1}
    {E : BoundaryEarlyOver_BSTD1 Θ} {V : ℝ} (R : BoundaryRegisterOver_BSTD1 E V) (c2 : ℝ) :
    Prop where
  rd_mul : 20 * (c2 + 1) * R.rd < 1 / 1000000

/-- **Member row readiness** (evidence class (c)): the tail-index clause of A4. -/
structure MemberRowReady_RNUM {Θ : BoundaryProducerThresholds_BSTD1}
    (E : BoundaryEarlyOver_BSTD1 Θ) (m : ℕ) : Prop where
  index : 32 * (1000000 * E.Δ) ≤ ((m + 1 : ℕ) : ℝ)

/-! ### Facts read off the early choice -/

/-- A4's `τ ≤ 10⁻⁸` from the early choice's own `τ_sqrt` and `ε < 1/100`. -/
theorem tau_le_RNUM {Θ : BoundaryProducerThresholds_BSTD1} (E : BoundaryEarlyOver_BSTD1 Θ) :
    E.τ ≤ 1 / 10 ^ 8 := by
  have h1 := E.τ_sqrt
  have hε := E.ε_lt
  have hε0 := E.ε_pos
  have hs : 0 ≤ Real.sqrt E.τ := Real.sqrt_nonneg _
  have hτ : Real.sqrt E.τ ^ 2 = E.τ := Real.sq_sqrt E.τ_pos.le
  have h2 : Real.sqrt E.τ ≤ 1 / 10 ^ 4 := by nlinarith
  rw [← hτ]
  nlinarith

/-- A4's `b ≤ 1/(1000 Δ)` from `b < s/10⁵`, `s < b'/10⁵`, `b' < 1/(10⁶ Δ)`. -/
theorem b_le_inv_RNUM {Θ : BoundaryProducerThresholds_BSTD1} (E : BoundaryEarlyOver_BSTD1 Θ) :
    E.b ≤ 1 / (1000 * E.Δ) := by
  have hΔ := E.Δ_pos
  have h3 := E.b'_lt
  rw [lt_div_iff₀ (by positivity)] at h3
  rw [le_div_iff₀ (by positivity)]
  have h12 : E.b ≤ E.b' / 10000000000 := by linarith [E.b_lt_s, E.s_lt_b']
  have hb0 := E.b_pos
  nlinarith [mul_le_mul_of_nonneg_right h12 (by positivity : (0 : ℝ) ≤ 1000 * E.Δ)]

namespace EarlyRowReady_RNUM

variable {Θ : BoundaryProducerThresholds_BSTD1} {χ : BoundaryChainThresholds_BSTD2}
  {E : BoundaryEarlyOverX_BSTD2 Θ χ} {Cρ : ℝ} (ea : EarlyRowReady_RNUM E Cρ)

include ea in
/-- **F1's numerical premises** (besides `c₂ < 10⁻⁵`): `3 β_c ≤ β 2`, `β 2 < 1`, `0 ≤ γ ≤ 3/4`,
and `Cρ Λ Δ < 10⁻⁶`. -/
theorem f1_premises_RNUM : 3 * E.βc ≤ E.β 2 ∧ E.β 2 < 1 ∧ 0 ≤ E.γ ∧ E.γ ≤ 3 / 4 ∧
    Cρ * E.Λ * E.Δ < 1 / 1000000 := by
  have h2 : E.β 2 = E.β₂ := E.β_two
  refine ⟨by rw [h2]; exact ea.three_βc, ?_, E.γ_pos.le, by linarith [ea.γ_le], ea.hC⟩
  rw [h2]
  linarith [ea.β₂_le7]

include ea in
/-- **F3's numerical premises**: `ε_r < 1/2`, `e ≤ 1/1000`. -/
theorem f3_premises_RNUM : E.εr < 1 / 2 ∧ E.e ≤ 1 / 1000 :=
  ⟨E.toBoundaryEarlyOver_BSTD1.εr_lt_half_RNUM, ea.e_lt.le⟩

include ea in
/-- **A4's numerical premises read off the early choice** (in the order of
`exists_boundaryGaf02BasesV2b_OWF`, without `5 ≤ K`, the tail index, `c 2 < 10⁻⁵` and `hC`):
`β 2 ≤ 10⁻⁷`, `γ ≤ 1/2`, `γ + β 2 < 1/10`, `μ ≤ 10⁻⁸`, `τ ≤ 10⁻⁸`, `σ_c ≤ 10⁻³`,
`b ≤ 1/(1000Δ)`, `0 ≤ ε`, `ε < 1`, `0 < γ_c`, `γ_c ≤ 1/100`, `β_c ≤ 10⁻⁵`. -/
theorem a4_premises_RNUM : E.β 2 ≤ 1 / 10000000 ∧ E.γ ≤ 1 / 2 ∧ E.γ + E.β 2 < 1 / 10 ∧
    E.μ ≤ 1 / 10 ^ 8 ∧ E.τ ≤ 1 / 10 ^ 8 ∧ E.σc ≤ 1 / 1000 ∧ E.b ≤ 1 / (1000 * E.Δ) ∧
    0 ≤ E.ε ∧ E.ε < 1 ∧ 0 < E.γc ∧ E.γc ≤ 1 / 100 ∧ E.βc ≤ 1 / 100000 := by
  have h2 : E.β 2 = E.β₂ := E.β_two
  obtain ⟨hε0, hε, hγc, hγc1, hβc1⟩ := E.toBoundaryEarlyOver_BSTD1.edgeParent_numerics_RNUM
  refine ⟨by rw [h2]; exact ea.β₂_le7, by linarith [ea.γ_le], ?_, E.μ_le8,
    tau_le_RNUM E.toBoundaryEarlyOver_BSTD1, E.σc_le_milli,
    b_le_inv_RNUM E.toBoundaryEarlyOver_BSTD1, hε0, hε, hγc, hγc1, hβc1⟩
  rw [h2]
  linarith [ea.β₂_le7, ea.γ_le]

end EarlyRowReady_RNUM

namespace RegisterRowReady_RNUM

variable {Θ : BoundaryProducerThresholds_BSTD1} {E : BoundaryEarlyOver_BSTD1 Θ} {V : ℝ}
  {R : BoundaryRegisterOver_BSTD1 E V} {c2 : ℝ} (rr : RegisterRowReady_RNUM R c2)

include rr in
/-- **E4's `r_∂` block** (BCG04-07, FC43): `0 < r_∂`, `r_∂ < 1/10000`, `20 (c₂ + 1) r_∂ < 10⁻⁶`. -/
theorem rdBlock_RNUM : 0 < R.rd ∧ R.rd < 1 / 10000 ∧ 20 * (c2 + 1) * R.rd < 1 / 1000000 :=
  ⟨R.rd_pos, R.rd_lt_ten_thousandth_RNUM, rr.rd_mul⟩

end RegisterRowReady_RNUM

/-- The member's small quantity (N76-3) is the projection `hm.1.1.2` of the member output: it is
not repeated in `MemberRowReady_RNUM`. -/
theorem memberPremise_RNUM {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
    {egOf : Ch → Fin 3 → ℝ} {EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf}
    {Sq : BoundaryStandingSequence_BSTD1 K A
      (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar}
    {V : ℝ} {R : BoundaryRegisterOverXBA_BSTD2 EW.early V} {m : ℕ}
    (hm : BoundaryMemberOutputXBA_BSTD2 Sq m R) :
    1000 * boundaryCounterexampleRatio Sq.δ₀ (m + 1) ^ 2 <
      EW.early.w / (2 * (1 + 2 * EW.early.Λ⁻¹) ^ 3) * min (1 / 2) (R.rd / 4) ^ 2 :=
  hm.1.1.2

/-! ### Producers -/

/-- **Producer of the early evidence** (a): for every choice `c`, CHI record `χ` with
`χ.eg = egOf c`, legal (BA) error and every constant `Cρ`, a stored-choice early choice with
exactly these data whose `EW.early` is `EarlyRowReady_RNUM` at `Cρ` (the G9 producer with the
requests `bdryRowRequests_RNUM Cρ`: `3 β_c ≤ β₂`, `e < 1/1000`, N76-9, and the prefix's
`β₂ ≤ 10⁻⁷`, `γ ≤ γ_T ≤ 1/20`). -/
theorem exists_boundaryEarlyWithChoice_ready_RNUM (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) {Ch : Type}
    (egOf : Ch → Fin 3 → ℝ) (c : Ch) (χ : BoundaryChainThresholds_BSTD2) (heg : χ.eg = egOf c)
    {θ νBA : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1 / 100) (hθχ : θ ≤ χ.ϑ₀) (hν : 0 < νBA)
    (hν1 : νBA < 1 / 1000000) (hν3 : 3 * νBA ≤ threeSplittingExclusionThreshold.{0, 0})
    (Cρ : ℝ) :
    ∃ EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf, EW.choice = c ∧ EW.χ = χ ∧ EW.θ = θ ∧
      EW.νBA = νBA ∧ EarlyRowReady_RNUM EW.early.toBoundaryEarlyOverX_BSTD2 Cρ := by
  have h := exists_boundaryEarlyWithChoice_of_three_RNUM K hK A hA egOf c χ heg hθ hθ1 hθχ hν
    hν1 hν3 (bdryRowRequests_RNUM Cρ)
  obtain ⟨EW, hc, hχ, hθ', hν', h3, P, hM, hEP⟩ := h
  have eβ₂ : EW.early.β₂ = P.β₂ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.β₂) hEP
  have eγ : EW.early.γ = P.γ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.γ) hEP
  exact ⟨EW, hc, hχ, hθ', hν',
    ⟨e_lt_milli_of_prefix_RNUM EW.early.toBoundaryEarlyOver_BSTD1 hEP,
      hC_of_early_request_RNUM EW.early.toBoundaryEarlyOver_BSTD1 hEP hM, h3,
      by rw [eβ₂]; exact P.β₂_le7, by rw [eγ]; linarith [P.γ_le_γT, P.γT_le]⟩⟩

/-- **Producer of the register and member evidence** (b), (c): for every stored-choice early choice
`EW`, standing sequence `Sq` and constant `c₂` there are `V`, a register `R` and `n₀` such that
`R` is `RegisterRowReady_RNUM` at `c₂` and every member `m ≥ n₀` carries the member output and
`MemberRowReady_RNUM`. -/
theorem exists_register_ready_RNUM {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
    {egOf : Ch → Fin 3 → ℝ} (EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf)
    (Sq : BoundaryStandingSequence_BSTD1 K A
      (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar) (c2 : ℝ) :
    ∃ V : ℝ, ∃ R : BoundaryRegisterOverXBA_BSTD2 EW.early V,
      RegisterRowReady_RNUM R.toBoundaryRegisterOver_BSTD1 c2 ∧
      ∃ n₀ : ℕ, ∀ m, n₀ ≤ m → BoundaryMemberOutputXBA_BSTD2 Sq m R ∧
        MemberRowReady_RNUM EW.early.toBoundaryEarlyOver_BSTD1 m := by
  obtain ⟨V, -, R, -, -, -, -, hrd, n₀, hR⟩ :=
    exists_boundarySequenceAssignmentWC_req_BSTD2 EW Sq (bdryRdRequest_RNUM c2)
  refine ⟨V, R, ⟨R.toBoundaryRegisterOver_BSTD1.rd_mul_lt_of_request_RNUM hrd⟩,
    max n₀ ⌈32 * (1000000 * EW.early.Δ)⌉₊, fun m hm => ⟨hR m ((le_max_left _ _).trans hm), ?_⟩⟩
  have hc : 32 * (1000000 * EW.early.Δ) ≤ (m : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hm)
  have hm' : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact ⟨hc.trans hm'⟩

/-- **The composite producer**: the early evidence at `Cρ`, then for EVERY standing sequence the
register and member evidence at `c₂` (the same constants as the CHOICE's: `Cρ` and `c₂` are
parameters, bound to the choice at the use site). -/
theorem exists_ready_package_RNUM (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) {Ch : Type}
    (egOf : Ch → Fin 3 → ℝ) (c : Ch) (χ : BoundaryChainThresholds_BSTD2) (heg : χ.eg = egOf c)
    {θ νBA : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1 / 100) (hθχ : θ ≤ χ.ϑ₀) (hν : 0 < νBA)
    (hν1 : νBA < 1 / 1000000) (hν3 : 3 * νBA ≤ threeSplittingExclusionThreshold.{0, 0})
    (Cρ c2 : ℝ) :
    ∃ EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf, EW.choice = c ∧ EW.χ = χ ∧ EW.θ = θ ∧
      EW.νBA = νBA ∧ EarlyRowReady_RNUM EW.early.toBoundaryEarlyOverX_BSTD2 Cρ ∧
      ∀ Sq : BoundaryStandingSequence_BSTD1 K A
        (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar,
        ∃ V : ℝ, ∃ R : BoundaryRegisterOverXBA_BSTD2 EW.early V,
          RegisterRowReady_RNUM R.toBoundaryRegisterOver_BSTD1 c2 ∧
          ∃ n₀ : ℕ, ∀ m, n₀ ≤ m → BoundaryMemberOutputXBA_BSTD2 Sq m R ∧
            MemberRowReady_RNUM EW.early.toBoundaryEarlyOver_BSTD1 m := by
  obtain ⟨EW, hc, hχ, hθ', hν', hea⟩ := exists_boundaryEarlyWithChoice_ready_RNUM K hK A hA egOf c
    χ heg hθ hθ1 hθχ hν hν1 hν3 Cρ
  exact ⟨EW, hc, hχ, hθ', hν', hea, fun Sq => exists_register_ready_RNUM EW Sq c2⟩

/-! ### Consumers: the rows from the three records -/

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

include C in
/-- **A4 whole from the three records**: every numerical premise of
`exists_boundaryGaf02BasesV2b_OWF` is supplied by `EarlyRowReady_RNUM` (with `μ ≤ 10⁻⁸`, `τ ≤ 10⁻⁸`,
`σ_c ≤ 10⁻³` read off the early choice), the member's index record, `K ≥ 10` and the CHOICE
validity (`c 2 < 10⁻⁵`). -/
theorem a4_whole_ready_RNUM
    (hval : BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj)
    (ea : EarlyRowReady_RNUM EW.early.toBoundaryEarlyOverX_BSTD2
      (100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0)))
    (mr : MemberRowReady_RNUM EW.early.toBoundaryEarlyOver_BSTD1 m) :
    ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs := by
  obtain ⟨hβ2, hγ, hd, hμ, hτ, hσc, hb, hε0, hε, hγc, hγc1, hβc1⟩ := ea.a4_premises_RNUM
  exact C.exists_boundaryGaf02BasesV2b_OWF hβ2 hγ hd (by omega) mr.index hμ hτ hσc hb
    hval.c_two_lt_E4 ea.hC hε0 hε hγc hγc1 hβc1

/-- **BCG06 from the register record**: `20 (c 2 + 1) r_∂ < 10⁻⁶` from `RegisterRowReady_RNUM`,
`r_∂ < 1/10000` from the register, `θ < 1/100` from `EW`, the member premise from `hm`. -/
theorem bcg06_row_ready_RNUM
    (rr : RegisterRowReady_RNUM R.toBoundaryRegisterOver_BSTD1 (c 2))
    (hmem : BoundaryMemberOutputXBA_BSTD2 Sq m R) :
    type_of% (C.bcg06_rowAll_BGR (rd := R.rd) R.rd_pos
      R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM rr.rd_mul hmem.1.1.2 EW.θ_lt) :=
  C.bcg06_rowAll_BGR R.rd_pos R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM rr.rd_mul
    hmem.1.1.2 EW.θ_lt

/-- **FC43's conjunction from the register record** (A4 output `hA4` as the hypothesis). -/
theorem fc43_row_ready_RNUM
    (hA4 : ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs)
    (rr : RegisterRowReady_RNUM R.toBoundaryRegisterOver_BSTD1 (c 2))
    (hmem : BoundaryMemberOutputXBA_BSTD2 Sq m R) :
    type_of% (C.fc43_rowAll_V2b_BGR hA4 (rd := R.rd) R.rd_pos
      R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM rr.rd_mul hmem.1.1.2 EW.θ_lt) :=
  C.fc43_rowAll_V2b_BGR hA4 R.rd_pos R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM
    rr.rd_mul hmem.1.1.2 EW.θ_lt

/-- **BCG07 F1 (07.0b) from the early record**: the six premises of
`rim_mem_source_zero_OF1` (`3 β_c ≤ β 2`, `β 2 < 1`, `0 ≤ γ ≤ 3/4`, `c 2 < 10⁻⁵`, N76-9). -/
theorem rim_mem_source_zero_ready_RNUM
    (hval : BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj)
    (ea : EarlyRowReady_RNUM EW.early.toBoundaryEarlyOverX_BSTD2
      (100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0)))
    (Bs : BoundaryGaf02BasesV2 C.toChain) {p : (Sq.W m).Carrier} (hp : p ∈ Bs.source 1)
    (hT : C.toChain.heightRatio p = 4 * EW.early.Δ) : p ∈ Bs.source 0 := by
  obtain ⟨h3, hβ2, hγ0, hγ34, hC⟩ := ea.f1_premises_RNUM
  exact C.rim_mem_source_zero_OF1 h3 hβ2 hγ0 hγ34 hval.c_two_lt_E4 hC Bs hp hT

/-- **BCG07, the whole row, from the three records**: every numerical premise of `bcg07_row_BGR`
(F1's six, F3's `ε_r < 1/2` and `e ≤ 1/1000`, E4's `r_∂` block with `θ < 1/100`, the member
premise `hm.1.1.2`) is supplied by `EarlyRowReady_RNUM`, `RegisterRowReady_RNUM`, the register, `EW`
and `hm`. -/
theorem bcg07_row_ready_RNUM
    (hval : BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj)
    (ea : EarlyRowReady_RNUM EW.early.toBoundaryEarlyOverX_BSTD2
      (100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0)))
    (rr : RegisterRowReady_RNUM R.toBoundaryRegisterOver_BSTD1 (c 2))
    (hmem : BoundaryMemberOutputXBA_BSTD2 Sq m R) {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) :
    type_of% (C.bcg07_row_BGR (rd := R.rd) ea.f1_premises_RNUM.1 ea.f1_premises_RNUM.2.1
      ea.f1_premises_RNUM.2.2.1 ea.f1_premises_RNUM.2.2.2.1 hval.c_two_lt_E4
      ea.f1_premises_RNUM.2.2.2.2 ea.f3_premises_RNUM.1 ea.f3_premises_RNUM.2 R.rd_pos
      R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM rr.rd_mul hmem.1.1.2 EW.θ_lt WF) :=
  C.bcg07_row_BGR ea.f1_premises_RNUM.1 ea.f1_premises_RNUM.2.1 ea.f1_premises_RNUM.2.2.1
    ea.f1_premises_RNUM.2.2.2.1 hval.c_two_lt_E4 ea.f1_premises_RNUM.2.2.2.2
    ea.f3_premises_RNUM.1 ea.f3_premises_RNUM.2 R.rd_pos
    R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM rr.rd_mul hmem.1.1.2 EW.θ_lt WF

/-- **The open edge parent from the early record**: `c 2 < 10⁻⁵`, N76-9, `0 ≤ ε < 1`,
`0 < γ_c ≤ 1/100`, `β_c ≤ 10⁻⁵`. -/
theorem exists_edgeParent_ready_RNUM
    (hval : BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj)
    (ea : EarlyRowReady_RNUM EW.early.toBoundaryEarlyOverX_BSTD2
      (100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0)))
    (Bc : BoundaryGaf02BasesCore_BIFc C.toChain) (U : Set (Sq.W m).Carrier) (hU : IsOpen U)
    (hcut : Bc.source 1 = U ∩ {p | C.toChain.heightRatio p ≤ 4 * EW.early.Δ})
    (hsub : U ⊆ C.toChain.stageMap 1 ⁻¹' Bc.base 1)
    (hrk : ∀ p ∈ U, C.toChain.stageRank_BIFc 1 p = 1) :
    Nonempty (BoundaryEdgeParent_BIFc C.toChain Bc.source Bc.base) := by
  obtain ⟨hε0, hε, hγc, hγc1, hβc1⟩ := EW.early.toBoundaryEarlyOver_BSTD1.edgeParent_numerics_RNUM
  exact C.exists_edgeParent_of_core_BAUGD hval.c_two_lt_E4 ea.hC hε0 hε hγc hγc1 hβc1 Bc U hU
    hcut hsub hrk

/-- **ZSP02 `zero_cover` on the boundary chain from the early record** (`e ≤ 1/1000`). -/
theorem actualZeroDomain_cover_ready_RNUM
    (ea : EarlyRowReady_RNUM EW.early.toBoundaryEarlyOverX_BSTD2
      (100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0))) (k : S.ZeroIdx_BAUGC)
    (q : (Sq.W m).pieceInterior ⊤)
    (hq : (letI := inducedMetricSpace S.completion.metric; dist q k.1) <
      38 / 100 * S.zeroRadius_BAUGC k) :
    q.val ∈ interior (C.toChain.actualZeroDomain_BIFc k) :=
  C.actualZeroDomain_cover_BGR ea.e_lt.le k q hq

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
