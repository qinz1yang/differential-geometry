import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterRowNumericsRNUM
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsFinalBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRimSourceZeroOF1
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeParentOfCore
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBcg07RowBGR

/-!
# Consumers of the boundary register-level numerics (S-REG-NUM2, G4, part 2)

The rows of the boundary route applied at the parameters of ONE tail member of the stored-choice
assignment (`EW`, `Sq`, `R`, `m`, the supply `S` of the member, a chain `C` over it): every
numerical premise is read off the register / the producer's prefix by the theorems of
`BoundaryRegisterRowNumericsRNUM`.

* `bcg04_row_register_RNUM`, `bcg05_row_register_RNUM`, `bcg06_row_register_RNUM`: BCG04 / BCG05 /
  BCG06 (`bcg0k_rowAll_BGR`) with `r_∂ := R.rd`: the member premise (N76-3) is the member output,
  `θ < 1/100` is `EW.θ_lt`, `r_∂ < 1/10000` is `R.rd_phys`, and BCG06's `20 (c 2 + 1) r_∂ < 10⁻⁶`
  comes from the late request `bdryRdRequest_RNUM (c 2)` (the hypothesis `hrd` is exactly what
  `exists_boundaryRegister_rowPremises_RNUM`'s assignment theorem provides).
* `rim_mem_source_zero_register_RNUM`: BCG07 F1 (07.0b) conjunct 1 with its six premises:
  `β 2 < 1`, `0 ≤ γ ≤ 3/4` from the early choice, `c 2 < 10⁻⁵` from the CHOICE validity
  (N76-4), `C_ρ Λ Δ < 10⁻⁶` (N76-9) from the staged request `bdryRowRequests_RNUM C_ρ` met by the
  producer's prefix, and `3 β_c ≤ β₂` — the ONE premise the register does not store (PENDING
  field `three_βc_le_β₂`; an explicit hypothesis here).
* `bcg07_row_register_RNUM`, `bcg07_row_extras_register_RNUM`: BCG07's whole row and its BCF01
  complement (`bcg07_row_BGR`, `bcg07_row_extras_BGR`) with all numerical premises read off the
  register (F1's six as above, `ε_r < 1/2`, `e ≤ 1/1000`, the `r_∂` block, `θ < 1/100`).
* `actualZeroDomain_cover_register_RNUM`: ZSP02's `zero_cover` on the boundary chain, with
  `e ≤ 1/1000` (N76-6) from the producer's prefix.
* `exists_edgeParent_register_RNUM`: the open edge parent on the chain with ALL its numerical
  premises discharged (`c 2 < 10⁻⁵`, N76-9, `0 ≤ ε < 1`, `0 < γ_c ≤ 1/100`, `β_c ≤ 10⁻⁵`).
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

/-- **BCG04 at the register**: `r_∂ = R.rd`; the member premise is the member output. -/
theorem bcg04_row_register_RNUM (hmem : BoundaryMemberOutputXBA_BSTD2 Sq m R) :
    type_of% (C.bcg04_rowAll_BGR (rd := R.rd) R.rd_pos hmem.1.1.2) :=
  C.bcg04_rowAll_BGR R.rd_pos hmem.1.1.2

/-- **BCG05 at the register**: `r_∂ < 1/10000` from `R.rd_phys`, `θ < 1/100` from `EW.θ_lt`. -/
theorem bcg05_row_register_RNUM (hmem : BoundaryMemberOutputXBA_BSTD2 Sq m R) :
    type_of% (C.bcg05_rowAll_BGR (rd := R.rd) R.rd_pos
      R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM hmem.1.1.2 EW.θ_lt) :=
  C.bcg05_rowAll_BGR R.rd_pos R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM
    hmem.1.1.2 EW.θ_lt

/-- **BCG06 at the register**: as BCG05, and `20 (c 2 + 1) r_∂ < 10⁻⁶` from the late request
`bdryRdRequest_RNUM (c 2)` met by the register (`hrd`). -/
theorem bcg06_row_register_RNUM
    (hrd : R.rd ≤ (bdryRdRequest_RNUM (c 2)).rd V R.δlocal R.Lmax R.βd R.εN R.Hd)
    (hmem : BoundaryMemberOutputXBA_BSTD2 Sq m R) :
    type_of% (C.bcg06_rowAll_BGR (rd := R.rd) R.rd_pos
      R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM
      (R.toBoundaryRegisterOver_BSTD1.rd_mul_lt_of_request_RNUM hrd) hmem.1.1.2 EW.θ_lt) :=
  C.bcg06_rowAll_BGR R.rd_pos R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM
    (R.toBoundaryRegisterOver_BSTD1.rd_mul_lt_of_request_RNUM hrd) hmem.1.1.2 EW.θ_lt

/-- **BCG07 F1 (07.0b) conjunct 1 at the register**: the rim of the edge source lies in the circle
source. The six premises: `3 β_c ≤ β₂` (PENDING register field; hypothesis `h3βc`), `β 2 < 1`,
`0 ≤ γ ≤ 3/4` (early choice), `c 2 < 10⁻⁵` (CHOICE validity, N76-4), `C_ρ Λ Δ < 10⁻⁶` (N76-9, the
request `bdryRowRequests_RNUM C_ρ` met by the producer's prefix `P`). -/
theorem rim_mem_source_zero_register_RNUM
    (hval : BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj)
    (h3βc : 3 * EW.early.βc ≤ EW.early.β₂) {P : C14PreFinal}
    (hEP : EW.early.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1)
    (hM : (bdryRowRequests_RNUM (100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0))).toC14.Meets P)
    (Bs : BoundaryGaf02BasesV2 C.toChain) {p : (Sq.W m).Carrier} (hp : p ∈ Bs.source 1)
    (hT : C.toChain.heightRatio p = 4 * EW.early.Δ) : p ∈ Bs.source 0 := by
  obtain ⟨hβ2, hγ0, hγ34⟩ := EW.early.toBoundaryEarlyOver_BSTD1.f1_numerics_RNUM
  have hC := hC_of_early_request_RNUM EW.early.toBoundaryEarlyOver_BSTD1 hEP hM
  exact C.rim_mem_source_zero_OF1 (by rw [EW.early.β_two]; exact h3βc) hβ2 hγ0 hγ34
    hval.c_two_lt_E4 hC Bs hp hT

/-- **The open edge parent on the chain, all numerical premises discharged**: `c 2 < 10⁻⁵`
(CHOICE validity), N76-9 (request met by the prefix `P`), `0 ≤ ε < 1`, `0 < γ_c ≤ 1/100`,
`β_c ≤ 10⁻⁵` (early choice). -/
theorem exists_edgeParent_register_RNUM
    (hval : BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj) {P : C14PreFinal}
    (hEP : EW.early.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1)
    (hM : (bdryRowRequests_RNUM (100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0))).toC14.Meets P)
    (Bc : BoundaryGaf02BasesCore_BIFc C.toChain) (U : Set (Sq.W m).Carrier) (hU : IsOpen U)
    (hcut : Bc.source 1 = U ∩ {p | C.toChain.heightRatio p ≤ 4 * EW.early.Δ})
    (hsub : U ⊆ C.toChain.stageMap 1 ⁻¹' Bc.base 1)
    (hrk : ∀ p ∈ U, C.toChain.stageRank_BIFc 1 p = 1) :
    Nonempty (BoundaryEdgeParent_BIFc C.toChain Bc.source Bc.base) := by
  obtain ⟨hε0, hε, hγc, hγc1, hβc1⟩ := EW.early.toBoundaryEarlyOver_BSTD1.edgeParent_numerics_RNUM
  have hC := hC_of_early_request_RNUM EW.early.toBoundaryEarlyOver_BSTD1 hEP hM
  exact C.exists_edgeParent_of_core_BAUGD hval.c_two_lt_E4 hC hε0 hε hγc hγc1 hβc1 Bc U hU hcut
    hsub hrk

/-- **ZSP02 `zero_cover` on the boundary chain at the register** (N76-6): `e ≤ 1/1000` is the
producer's prefix `P` (`P.e_lt3`). -/
theorem actualZeroDomain_cover_register_RNUM {P : C14PreFinal}
    (hEP : EW.early.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1) (k : S.ZeroIdx_BAUGC)
    (q : (Sq.W m).pieceInterior ⊤)
    (hq : (letI := inducedMetricSpace S.completion.metric; dist q k.1) <
      38 / 100 * S.zeroRadius_BAUGC k) :
    q.val ∈ interior (C.toChain.actualZeroDomain_BIFc k) :=
  C.actualZeroDomain_cover_BGR (e_lt_milli_of_prefix_RNUM EW.early.toBoundaryEarlyOver_BSTD1 hEP).le
    k q hq

/-- **BCG07, the whole row, at the register**: every numerical premise of `bcg07_row_BGR` (F1's
six, F3's `ε_r < 1/2` and `e ≤ 1/1000`, E4's `r_∂` block with `θ < 1/100`) read off the register /
the producer's prefix; the PENDING register field `3 β_c ≤ β 2` is the hypothesis `h3βc`. -/
theorem bcg07_row_register_RNUM
    (hval : BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj)
    (h3βc : 3 * EW.early.βc ≤ EW.early.β 2) {P : C14PreFinal}
    (hEP : EW.early.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1)
    (hM : (bdryRowRequests_RNUM (100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0))).toC14.Meets P)
    (hrd : R.rd ≤ (bdryRdRequest_RNUM (c 2)).rd V R.δlocal R.Lmax R.βd R.εN R.Hd)
    (hmem : BoundaryMemberOutputXBA_BSTD2 Sq m R) {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) :
    type_of% (C.bcg07_row_BGR (rd := R.rd) h3βc
      EW.early.toBoundaryEarlyOver_BSTD1.f1_numerics_RNUM.1
      EW.early.toBoundaryEarlyOver_BSTD1.f1_numerics_RNUM.2.1
      EW.early.toBoundaryEarlyOver_BSTD1.f1_numerics_RNUM.2.2 hval.c_two_lt_E4
      (hC_of_early_request_RNUM EW.early.toBoundaryEarlyOver_BSTD1 hEP hM)
      EW.early.toBoundaryEarlyOver_BSTD1.εr_lt_half_RNUM
      (e_lt_milli_of_prefix_RNUM EW.early.toBoundaryEarlyOver_BSTD1 hEP).le R.rd_pos
      R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM
      (R.toBoundaryRegisterOver_BSTD1.rd_mul_lt_of_request_RNUM hrd) hmem.1.1.2 EW.θ_lt WF) :=
  C.bcg07_row_BGR h3βc EW.early.toBoundaryEarlyOver_BSTD1.f1_numerics_RNUM.1
    EW.early.toBoundaryEarlyOver_BSTD1.f1_numerics_RNUM.2.1
    EW.early.toBoundaryEarlyOver_BSTD1.f1_numerics_RNUM.2.2 hval.c_two_lt_E4
    (hC_of_early_request_RNUM EW.early.toBoundaryEarlyOver_BSTD1 hEP hM)
    EW.early.toBoundaryEarlyOver_BSTD1.εr_lt_half_RNUM
    (e_lt_milli_of_prefix_RNUM EW.early.toBoundaryEarlyOver_BSTD1 hEP).le R.rd_pos
    R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM
    (R.toBoundaryRegisterOver_BSTD1.rd_mul_lt_of_request_RNUM hrd) hmem.1.1.2 EW.θ_lt WF

/-- **BCG07's complement used by BCF01, at the register** (`ε_r < 1/2` and the `r_∂` block). -/
theorem bcg07_row_extras_register_RNUM
    (hrd : R.rd ≤ (bdryRdRequest_RNUM (c 2)).rd V R.δlocal R.Lmax R.βd R.εN R.Hd)
    (hmem : BoundaryMemberOutputXBA_BSTD2 Sq m R) {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) :
    type_of% (C.bcg07_row_extras_BGR (rd := R.rd)
      EW.early.toBoundaryEarlyOver_BSTD1.εr_lt_half_RNUM R.rd_pos
      R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM
      (R.toBoundaryRegisterOver_BSTD1.rd_mul_lt_of_request_RNUM hrd) hmem.1.1.2 EW.θ_lt WF) :=
  C.bcg07_row_extras_BGR EW.early.toBoundaryEarlyOver_BSTD1.εr_lt_half_RNUM R.rd_pos
    R.toBoundaryRegisterOver_BSTD1.rd_lt_ten_thousandth_RNUM
    (R.toBoundaryRegisterOver_BSTD1.rd_mul_lt_of_request_RNUM hrd) hmem.1.1.2 EW.θ_lt WF

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
