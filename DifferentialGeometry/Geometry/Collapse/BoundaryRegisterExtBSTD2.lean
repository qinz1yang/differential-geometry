import DifferentialGeometry.Geometry.Collapse.BoundarySequenceAssignmentBSTD1
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementRegisterBCF2K
import DifferentialGeometry.Geometry.Fibration.ActualStageChainRow

/-!
# The extended boundary register: every numerical premise the boundary rows carry (lane BSTD2, G1)

Review 69 / addendum item 8 (D69-3, D69-12): the boundary rows carry explicit numerical premises
on the register's parameters; each must be discharged by the register at a LEGAL node of its
order `γ | βc γc | β₂ Δ | σc ε μ τ s b' s' | σ Λ | w | b σs vs | β ζ cap | T e | (sequence) V δ |
L_max β_∂ ε_N H_∂ r_∂ | n₀`. Here, on the SAME early choice, the SAME tail and the SAME member
output as `exists_boundarySequenceAssignment_BSTD1`:

* `BoundaryChainThresholds_BSTD2` (`χ`): the numbers of the CHI producer that rows read — `ν`
  (`3ν ≤ thr`), the graph errors `e_j`, the FIRST thresholds `σ η₂ γ₀ ηc θt ϑ₀` (constants: fixed
  before every register parameter) and the LATE thresholds `η₁ Lc₁ η₀₁ θs Lc₂ η₀₂` (functions of
  `(β₂, Δ)`: read after the node `β₂ Δ`).
* `BoundaryEarlyOverX_BSTD2 Θ χ`: the early choice with every new clause on the node where it is
  read: BCF02's `σc ≤ 1/1000`, `μΔ < 10⁻⁴`, `b ≤ η(Δ)`, `3b ≤ σ(Δ)`, `β₂ < 10⁻⁶`, `T ≥ 1600·10⁶Δ`
  (`⊇ T ≥ 1000Δ`); the closed CHI block of `gaf02_chainE_row_GAF8` (first stage, edge stage, slim
  stage; `ζ ≤ 1/(1000·10⁶Δ)`, `cap` below the three `εr` bounds, `3ν ≤ β 3`, …); the per-stage
  graph clauses `1000·C_j·ΔΛ < e_j`; BCG05's `θ < 1/100` and A2's `θ ≤ ϑ₀` at `θ = ϑ_min`.
* `BoundaryRegisterOverX_BSTD2 E V`: the producer's `T ≤ V` and the late lower bounds of `L_max`
  (`σ(Δ)⁻¹`, `σ⁻¹`, `Lc₁`, `Lc₂`, the buffer `4(10 + 4·10⁶Δ + Δ/3)`), read after `V`.
* `BoundaryMemberOutputX_BSTD2 S n R`: the member output and the BCP04.a index clause
  `1140Δ ≤ 35(n+1)` (the member's index is `n + 1`), read on the tail.
* `exists_boundarySequenceAssignmentX_req_BSTD2`, `exists_boundarySequenceAssignmentX_BSTD2`.
* Premise blocks: `BoundaryRegisterOverX_BSTD2.bcf02_premises_BSTD2` (BCF02's 18, in the order of
  `isCompact_edgePiece_BCF2K`), `.register_block_BSTD2` (A2-mk's block), `.chi_block_BSTD2`
  (`gaf02_chainE_row_GAF8` l.185–198 verbatim, in order),
  `BoundaryEarlyOverX_BSTD2.stage_graph_BSTD2`, `BoundaryEarlyOverX_BSTD2.theta_BSTD2`; all of them
  at one point:
  `BoundaryRegisterPremisesX_BSTD2 E R m` (a conclusion shape), `.premises_BSTD2`.
* Inhabitants: `chiRequests_BSTD2 χ` (the new clauses as STG requests, each read at its prefix) and
  `nonempty_boundaryEarlyChoicesX_BSTD2` (for EVERY `χ` and every `(K, A)`: the extended early
  choices are inhabited — all clauses jointly satisfiable in the register's order).

No clause is a row hypothesis; no `Δ > 100/β₂` with `β₂⁻¹ > 10⁶Δ`; no `1/r_∂` in an early constant.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter

namespace DifferentialGeometry.Geometry.Collapse

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-! ### The numbers of the CHI producer -/

/-- **The numbers of the CHI producer read by the boundary register** (`χ`): `ν` with `3ν ≤ thr`
(so `β 3 ∈ [3ν, thr]` is legal), the graph errors `e_j > 0`, the FIRST thresholds
`σ η₂ γ₀ ηc θt ϑ₀ > 0` (constants) and the LATE thresholds `η₁ Lc₁ η₀₁ θs Lc₂ η₀₂` as functions of
`(β₂, Δ)` (the upper ones positive). Closed instance: the outputs of `gaf02_chainE_row_GAF8`. -/
structure BoundaryChainThresholds_BSTD2 where
  ν : ℝ
  eg : Fin 3 → ℝ
  σ : ℝ
  η₂ : ℝ
  γ₀ : ℝ
  ηc : ℝ
  θt : ℝ
  ϑ₀ : ℝ
  η₁ : ℝ → ℝ → ℝ
  Lc₁ : ℝ → ℝ → ℝ
  η₀₁ : ℝ → ℝ → ℝ
  θs : ℝ → ℝ → ℝ
  Lc₂ : ℝ → ℝ → ℝ
  η₀₂ : ℝ → ℝ → ℝ
  ν_pos : 0 < ν
  three_ν_le : 3 * ν ≤ threeSplittingExclusionThreshold.{0, 0}
  eg_pos : ∀ j, 0 < eg j
  σ_pos : 0 < σ
  η₂_pos : 0 < η₂
  γ₀_pos : 0 < γ₀
  ηc_pos : 0 < ηc
  θt_pos : 0 < θt
  ϑ₀_pos : 0 < ϑ₀
  η₁_pos : ∀ β₂ Δ, 0 < η₁ β₂ Δ
  η₀₁_pos : ∀ β₂ Δ, 0 < η₀₁ β₂ Δ
  θs_pos : ∀ β₂ Δ, 0 < θs β₂ Δ
  η₀₂_pos : ∀ β₂ Δ, 0 < η₀₂ β₂ Δ

/-! ### The extended early choice -/

/-- **The extended early choice** over the producer thresholds `Θ` and the CHI numbers `χ`: an
early choice of lane BSTG-D1 with every clause the boundary rows carry, each on the node where it is
read (`χ`'s first thresholds are constants; its late thresholds are read at `(β₂, Δ)`, after the
node `β₂ Δ`; BCF02's `σ(Δ), η(Δ)` after `Δ`). -/
structure BoundaryEarlyOverX_BSTD2 (Θ : BoundaryProducerThresholds_BSTD1)
    (χ : BoundaryChainThresholds_BSTD2) extends BoundaryEarlyOver_BSTD1 Θ where
  /- node `γ | βc γc` -/
  γ_le_γ₀ : γ ≤ χ.γ₀
  γc_le_γ₀ : γc ≤ χ.γ₀
  βc_le_ηc : βc ≤ χ.ηc
  /- node `β₂ Δ` -/
  β₂_lt6 : β₂ < 1 / 1000000
  three_β₂_le_σ : 3 * β₂ ≤ χ.σ
  β₂_le_η₂ : β₂ ≤ χ.η₂
  /- node `σc ε μ τ s b' s'` (after `Δ`) -/
  σc_le_milli : σc ≤ 1 / 1000
  σc_le_θt : σc ≤ χ.θt ^ 2 / 1000
  σc_le_eg : σc ≤ (χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8
  μΔ_lt : μ * Δ < 1 / 10000
  μΔ_le_θt : μ * Δ ≤ χ.θt / 100
  μΔ_lt_eg : μ * Δ < χ.eg 1 / (20 * egpGraphConst) / 100
  /- node `σ Λ` -/
  Λ_lt_eg₀ : 1000 * tcpGraphConst * Δ * Λ < χ.eg 0
  Λ_lt_eg₁ : 1000 * egpGraphConst * Δ * Λ < χ.eg 1
  Λ_lt_eg₂ : 1000 * sgpGraphBound * Δ * Λ < χ.eg 2
  /- node `b σs vs` -/
  b_le_η : b ≤ bcf02Eta_BCF2K Δ
  three_b_le_σ : 3 * b ≤ bcf02Sigma_BCF2K Δ
  b_le_η₁ : b ≤ χ.η₁ β₂ Δ
  b_le_η₀₁ : b ≤ χ.η₀₁ β₂ Δ
  σs_le_θt : σs ≤ χ.θt ^ 2 / 1000
  σs_le_eg : σs ≤ (χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8
  σs_lt_θs : σs < χ.θs β₂ Δ ^ 2 / 10 ^ 6
  vs_le_θt : vs ≤ χ.θt / 100
  vs_lt_eg : vs < χ.eg 1 / (20 * egpGraphConst) / 100
  vs_lt_θs : vs < χ.θs β₂ Δ / 100
  /- node `β ζ cap` -/
  three_ν_le_β₃ : 3 * χ.ν ≤ β 3
  β₁_le_η₁ : β 1 ≤ χ.η₁ β₂ Δ
  β₁_le_η₀₁ : β 1 ≤ χ.η₀₁ β₂ Δ
  β₁_le_η₀₂ : β 1 ≤ χ.η₀₂ β₂ Δ
  ζ_le_θt : ζ ≤ χ.θt ^ 2 / 1000
  ζ_le_eg : ζ ≤ (χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8
  ζ_le_Δ : ζ ≤ 1 / (1000 * (1000000 * Δ))
  ζ_lt_θs : ζ < χ.θs β₂ Δ ^ 2 / 10 ^ 6
  cap_le_θt : cap ≤ χ.θt / 100
  cap_le_eg : cap ≤ χ.eg 1 / (20 * egpGraphConst) / (100 * (1000000 * Δ))
  cap_le_θs : cap ≤ χ.θs β₂ Δ / (100 * (1000000 * Δ))
  /- node `T e` -/
  T_ge_Δ : 1600 * (1000000 * Δ) ≤ T
  /- the early boundary layer (`θ = ϑ_min`) -/
  ϑmin_lt : min (ϑ 0) (min (ϑ 1) (ϑ 2)) < 1 / 100
  ϑmin_le : min (ϑ 0) (min (ϑ 1) (ϑ 2)) ≤ χ.ϑ₀

/-- **The extended early choices** over the exported boundary thresholds of `(K, A)`. -/
abbrev BoundaryEarlyChoicesX_BSTD2 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w)
    (χ : BoundaryChainThresholds_BSTD2) : Type :=
  BoundaryEarlyOverX_BSTD2 (bdryThresholds_BSTD1 K hK A hA) χ

namespace BoundaryEarlyOverX_BSTD2

variable {Θ : BoundaryProducerThresholds_BSTD1} {χ : BoundaryChainThresholds_BSTD2}
  (E : BoundaryEarlyOverX_BSTD2 Θ χ)

/-- `Δ > 10⁸` (from `100/β₂ < Δ` and `β₂ < 10⁻⁶`). -/
theorem Δ_gt_BSTD2 : 100000000 < E.Δ := by
  have h : 100000000 < 100 / E.β₂ := by
    rw [lt_div_iff₀ E.β₂_pos]
    linarith [E.β₂_lt6]
  linarith [E.Δ_gt]

/-- BCG05 (E3 / E4) and A2: the BA error `θ = ϑ_min` has `θ < 1/100` and `θ ≤ ϑ₀`. -/
theorem theta_BSTD2 : E.ϑmin < 1 / 100 ∧ E.ϑmin ≤ χ.ϑ₀ :=
  ⟨E.ϑmin_lt, E.ϑmin_le⟩

/-- **The per-stage graph clauses** `1000·C_j·ΔΛ < e_j` (`C_0 = tcpGraphConst`,
`C_1 = egpGraphConst`, `C_2 = sgpGraphBound`; the DP producer's / port targets' Λ clauses). -/
theorem stage_graph_BSTD2 :
    1000 * tcpGraphConst * E.Δ * E.Λ < χ.eg 0 ∧ 1000 * egpGraphConst * E.Δ * E.Λ < χ.eg 1 ∧
      1000 * sgpGraphBound * E.Δ * E.Λ < χ.eg 2 :=
  ⟨E.Λ_lt_eg₀, E.Λ_lt_eg₁, E.Λ_lt_eg₂⟩

end BoundaryEarlyOverX_BSTD2

/-! ### The extended register -/

/-- **The extended register** over `(E, V)`: lane BSTG-D1's register, the producer's fact `T ≤ V`
about its zero scale, and the late lower bounds of `L_max` read by the rows (BCF02's `σ(Δ)⁻¹`, the
CHI block's `σ⁻¹`, `Lc₁`, `Lc₂` and buffer). -/
structure BoundaryRegisterOverX_BSTD2 {Θ : BoundaryProducerThresholds_BSTD1}
    {χ : BoundaryChainThresholds_BSTD2} (E : BoundaryEarlyOverX_BSTD2 Θ χ) (V : ℝ) extends
    BoundaryRegisterOver_BSTD1 E.toBoundaryEarlyOver_BSTD1 V where
  T_le_V : E.T ≤ V
  Lmax_ge_bcf : (bcf02Sigma_BCF2K E.Δ)⁻¹ ≤ Lmax
  Lmax_ge_σ : χ.σ⁻¹ ≤ Lmax
  Lmax_ge_Lc₁ : χ.Lc₁ E.β₂ E.Δ ≤ Lmax
  Lmax_ge_Lc₂ : χ.Lc₂ E.β₂ E.Δ ≤ Lmax
  Lmax_ge_buf : 4 * (10 + 2 * (2000000 * E.Δ) + E.Δ / 3) ≤ Lmax

/-- **The output of one member on the extended register**: lane BSTG-D1's member output and the
BCP04.a index clause `1140Δ ≤ 35(n+1)` (the member's index is `n + 1`). -/
def BoundaryMemberOutputX_BSTD2 {Θ : BoundaryProducerThresholds_BSTD1}
    {χ : BoundaryChainThresholds_BSTD2} {K : ℕ} {A : ℝ → ℝ} {E : BoundaryEarlyOverX_BSTD2 Θ χ}
    {V : ℝ} (S : BoundaryStandingSequence_BSTD1 K A Θ.δStar) (n : ℕ)
    (R : BoundaryRegisterOverX_BSTD2 E V) : Prop :=
  BoundaryMemberOutput_BSTD1 S n R.toBoundaryRegisterOver_BSTD1 ∧
    1140 * E.Δ ≤ 35 * ((n + 1 : ℕ) : ℝ)

section Values

variable {Θ : BoundaryProducerThresholds_BSTD1} {χ : BoundaryChainThresholds_BSTD2}
  (E : BoundaryEarlyOverX_BSTD2 Θ χ)

/-- The late lower bound of `L_max` of the extension (reads `E` only). -/
def bdryLmaxX_BSTD2 : ℝ :=
  max (max (bcf02Sigma_BCF2K E.Δ)⁻¹ χ.σ⁻¹)
    (max (max (χ.Lc₁ E.β₂ E.Δ) (χ.Lc₂ E.β₂ E.Δ)) (4 * (10 + 2 * (2000000 * E.Δ) + E.Δ / 3)))

/-- The late requests with the extension's `L_max` lower bound added. -/
def BoundaryLateRequests_BSTD1.withX_BSTD2 (Rq : BoundaryLateRequests_BSTD1) :
    BoundaryLateRequests_BSTD1 :=
  { Rq with Lmax := fun V δ => max (Rq.Lmax V δ) (bdryLmaxX_BSTD2 E) }

/-- A register of lane BSTG-D1 over a zero scale `V ≥ T` whose `L_max` is above
`bdryLmaxX_BSTD2 E` is an extended register. -/
def BoundaryRegisterOverX_BSTD2.ofRegister_BSTD2 {V : ℝ}
    (R : BoundaryRegisterOver_BSTD1 E.toBoundaryEarlyOver_BSTD1 V) (hTV : E.T ≤ V)
    (h : bdryLmaxX_BSTD2 E ≤ R.Lmax) : BoundaryRegisterOverX_BSTD2 E V where
  toBoundaryRegisterOver_BSTD1 := R
  T_le_V := hTV
  Lmax_ge_bcf := ((le_max_left _ _).trans (le_max_left _ _)).trans h
  Lmax_ge_σ := ((le_max_right _ _).trans (le_max_left _ _)).trans h
  Lmax_ge_Lc₁ := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans h
  Lmax_ge_Lc₂ := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans h
  Lmax_ge_buf := ((le_max_right _ _).trans (le_max_right _ _)).trans h

end Values

/-! ### The assignment on the extended register -/

/-- **ONE per-sequence boundary assignment on the extended register, meeting late requests**: for
every extended early choice `E`, every standing sequence `S` and every late request record `Rq`,
the producer's `V ≥ T`, then an extended register over `(E, V)` meeting `Rq` (each request read in
the D61-11 order), then `n₀` with the extended member output on every member `n ≥ n₀`. -/
theorem exists_boundarySequenceAssignmentX_req_BSTD2 {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w}
    {χ : BoundaryChainThresholds_BSTD2} (E : BoundaryEarlyChoicesX_BSTD2 K hK A hA χ)
    (S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar)
    (Rq : BoundaryLateRequests_BSTD1) :
    ∃ V : ℝ, E.T ≤ V ∧ ∃ R : BoundaryRegisterOverX_BSTD2 E V,
      Rq.Lmax V R.δlocal ≤ R.Lmax ∧ R.βd ≤ Rq.βd V R.δlocal R.Lmax ∧
      R.εN = Rq.εN V R.δlocal R.Lmax ∧ Rq.H V R.δlocal R.Lmax R.βd R.εN ≤ R.Hd ∧
      R.rd ≤ Rq.rd V R.δlocal R.Lmax R.βd R.εN R.Hd ∧
      ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Nonempty (BoundaryMemberOutputX_BSTD2 S n R) := by
  obtain ⟨V, hTV, R, h1, h2, h3, h4, h5, n₀, hR⟩ :=
    exists_boundarySequenceAssignment_req_BSTD1 E.toBoundaryEarlyOver_BSTD1 S
      (BoundaryLateRequests_BSTD1.withX_BSTD2 E Rq)
  have hL : bdryLmaxX_BSTD2 E ≤ R.Lmax := (le_max_right _ _).trans h1
  refine ⟨V, hTV, BoundaryRegisterOverX_BSTD2.ofRegister_BSTD2 E R hTV hL,
    (le_max_left _ _).trans h1, h2, h3, h4, h5, max n₀ ⌈1140 * E.Δ / 35⌉₊, fun n hn => ?_⟩
  obtain ⟨hR'⟩ := hR n ((le_max_left _ _).trans hn)
  refine ⟨hR', ?_⟩
  have h1' : 1140 * E.Δ / 35 ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
  have h2' : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  linarith

/-- **ONE per-sequence boundary assignment on the extended register** (G1): for every extended
early choice and every standing sequence of BBR03 with `δ₀ ≤ δStar`, there are `V`, an extended
register `R` over `(E, V)` and `n₀` such that every member `n ≥ n₀` has the extended output. -/
theorem exists_boundarySequenceAssignmentX_BSTD2 {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w}
    {χ : BoundaryChainThresholds_BSTD2} (E : BoundaryEarlyChoicesX_BSTD2 K hK A hA χ)
    (S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar) :
    ∃ V : ℝ, ∃ R : BoundaryRegisterOverX_BSTD2 E V, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      Nonempty (BoundaryMemberOutputX_BSTD2 S n R) := by
  obtain ⟨V, -, R, -, -, -, -, -, hR⟩ :=
    exists_boundarySequenceAssignmentX_req_BSTD2 E S BoundaryLateRequests_BSTD1.trivial
  exact ⟨V, R, hR⟩

/-! ### The premise blocks discharged by the extended register -/

namespace BoundaryRegisterOverX_BSTD2

variable {Θ : BoundaryProducerThresholds_BSTD1} {χ : BoundaryChainThresholds_BSTD2}
  {E : BoundaryEarlyOverX_BSTD2 Θ χ} {V : ℝ} (R : BoundaryRegisterOverX_BSTD2 E V)

/-- **BCF02's eighteen numerical premises** (in the order of `isCompact_edgePiece_BCF2K`) at the
extended register, for every supply index `m` with `1140Δ ≤ 35m` (a tail member `n` has
`m = n + 1`). -/
theorem bcf02_premises_BSTD2 {m : ℕ} (hm : 1140 * E.Δ ≤ 35 * (m : ℝ)) :
    2 ≤ E.Δ ∧ 0 ≤ E.Λ ∧ E.μ ≤ 1 / 10 ^ 8 ∧ E.τ ≤ 1 / 10 ^ 8 ∧ E.σc ≤ 1 / 1000 ∧
      1140 * E.Δ ≤ 35 * (m : ℝ) ∧ 1000 * E.Δ ≤ E.T ∧ 0 ≤ E.σs ∧ E.σs ≤ 1 / 100 ∧
      E.b < 1 / 1000000 ∧ E.s < 1 / 1000000 ∧ E.β 2 < 1 / 1000000 ∧
      (bcf02Sigma_BCF2K E.Δ)⁻¹ ≤ R.Lmax ∧ E.b ≤ bcf02Eta_BCF2K E.Δ ∧
      3 * E.b ≤ bcf02Sigma_BCF2K E.Δ ∧ E.b * (2 * (20 * E.Δ + 1)) ≤ 1 ∧
      1000000 * E.Δ * E.Λ < 1 / 100000 ∧ E.μ * E.Δ < 1 / 10000 := by
  obtain ⟨hΔ, hΛ, hμ, hτ, hσs, hσs1, hb, hbH, hs, hLΛ⟩ :=
    bcf02_register_given_BCF2K E.toBoundaryEarlyOver_BSTD1
  have hT : 1000 * E.Δ ≤ E.T := by
    have := E.T_ge_Δ
    linarith
  refine ⟨hΔ, hΛ, hμ, hτ, E.σc_le_milli, hm, hT, hσs, hσs1, hb, hs, ?_, R.Lmax_ge_bcf, E.b_le_η,
    E.three_b_le_σ, hbH, hLΛ, E.μΔ_lt⟩
  rw [E.β_two]
  exact E.β₂_lt6

include R in
/-- **A2-mk's register block** (BAUG-A's nine smoothness inequalities, `1 ≤ Δ`, the unified Λ–Δ
clause) at the extended register, in A2-mk's order. -/
theorem register_block_BSTD2 :
    0 ≤ E.Λ ∧ 0 < E.Δ ∧ E.μ ≤ 1 / 100 ∧ E.τ ≤ 1 / 100 ∧ 100 * E.Δ * E.Λ ≤ 1 / 100 ∧ 0 ≤ V ∧
      0 < E.β 1 ∧ 0 < E.b ∧ E.e ≤ 1 / 10 ∧ 1 ≤ E.Δ ∧ 1000000 * E.Δ * E.Λ < 1 / 100000 := by
  obtain ⟨hΔ, hΛ, -, hτ, -, -, -, -, -, hLΛ⟩ :=
    bcf02_register_given_BCF2K E.toBoundaryEarlyOver_BSTD1
  have hV : 0 ≤ V := E.T_pos.le.trans R.T_le_V
  exact ⟨hΛ, by linarith, by linarith [E.μ_le], by linarith, by linarith [E.Λ_c3], hV,
    E.β₁_pos, E.b_pos, by linarith [E.e_lt], by linarith, hLΛ⟩

/-- **The closed CHI block** (`gaf02_chainE_row_GAF8`, l.185–198, verbatim and in order, with
`β₂ := E.β₂`, `Δ := E.Δ` and the late thresholds of `χ` at `(β₂, Δ)`; then `0 ≤ εr`) at the
extended register: first stage, edge stage, slim stage. -/
theorem chi_block_BSTD2 :
    0 ≤ E.Λ ∧ E.μ ≤ 1 / 100 ∧ E.τ ≤ 1 / 100 ∧ 1000000 * E.Δ * E.Λ < 1 / 100000 ∧
    4 * (10 + 2 * (2000000 * E.Δ) + E.Δ / 3) ≤ R.Lmax ∧ E.e < 1 / 40 ∧
    1600 * (1000000 * E.Δ) ≤ E.T ∧
    0 ≤ E.ε ∧ E.ε ≤ 1 ∧ 0 ≤ E.σc ∧ E.σc ≤ χ.θt ^ 2 / 1000 ∧ E.μ * E.Δ ≤ χ.θt / 100 ∧
    3 * χ.ν ≤ E.β 3 ∧ E.β 3 < 1 ∧
    3 * E.β 2 ≤ χ.σ ∧ E.β 2 ≤ χ.η₂ ∧ E.γ ≤ χ.γ₀ ∧ 0 < E.γc ∧ E.γc ≤ χ.γ₀ ∧ E.βc ≤ χ.ηc ∧
    E.b ≤ χ.η₁ E.β₂ E.Δ ∧ E.β 1 ≤ χ.η₁ E.β₂ E.Δ ∧ 0 < E.σs ∧
    E.σs ≤ χ.θt ^ 2 / 1000 ∧ E.vs ≤ χ.θt / 100 ∧ 0 < E.ζ ∧
    E.ζ ≤ χ.θt ^ 2 / 1000 ∧ E.εr ≤ χ.θt / 100 ∧ 20 * E.Λz ≤ E.T ∧ χ.σ⁻¹ ≤ R.Lmax ∧
    1000 * tcpGraphConst * E.Δ * E.Λ < χ.eg 0 ∧
    E.b ≤ χ.η₀₁ E.β₂ E.Δ ∧ E.s < 1 / 1000000 ∧ E.β 1 ≤ χ.η₀₁ E.β₂ E.Δ ∧
    χ.Lc₁ E.β₂ E.Δ ≤ R.Lmax ∧
    E.σc ≤ (χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 ∧
    E.μ * E.Δ < χ.eg 1 / (20 * egpGraphConst) / 100 ∧
    E.σs ≤ (χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 ∧
    E.vs < χ.eg 1 / (20 * egpGraphConst) / 100 ∧
    E.ζ ≤ (χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 ∧
    E.ζ ≤ 1 / (1000 * (1000000 * E.Δ)) ∧
    E.εr < χ.eg 1 / (20 * egpGraphConst) / (100 * (1000000 * E.Δ)) ∧
    E.β 2 = E.β₂ ∧ E.β 1 ≤ χ.η₀₂ E.β₂ E.Δ ∧
    χ.Lc₂ E.β₂ E.Δ ≤ R.Lmax ∧ E.σs < χ.θs E.β₂ E.Δ ^ 2 / 10 ^ 6 ∧
    E.vs < χ.θs E.β₂ E.Δ / 100 ∧ E.ζ < χ.θs E.β₂ E.Δ ^ 2 / 10 ^ 6 ∧
    E.ζ < 1 / (100 * (1000000 * E.Δ)) ∧ E.εr < χ.θs E.β₂ E.Δ / (100 * (1000000 * E.Δ)) ∧
    0 ≤ E.εr := by
  obtain ⟨hΔ2, hΛ, -, hτ, -, -, -, -, hs, hLΛ⟩ :=
    bcf02_register_given_BCF2K E.toBoundaryEarlyOver_BSTD1
  have hΔ := E.Δ_gt_BSTD2
  have hεr := E.εr_pos
  have hεrcap := E.εr_lt_cap
  have hβ3 : E.β 3 < 1 := by
    have := threeSplittingExclusionThreshold_lt.{0, 0}
    linarith [E.β_three]
  have hζ : 0 < E.ζ := E.β₁_pos.trans E.β₁_lt_ζ
  have hζΔ : E.ζ < 1 / (100 * (1000000 * E.Δ)) := by
    have h : 1 / (1000 * (1000000 * E.Δ)) < 1 / (100 * (1000000 * E.Δ)) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith
    exact E.ζ_le_Δ.trans_lt h
  have hTΛz : 20 * E.Λz ≤ E.T := E.T_ge
  refine ⟨hΛ, by linarith [E.μ_le], by linarith, hLΛ, R.Lmax_ge_buf, E.e_lt, E.T_ge_Δ,
    E.ε_pos.le, by linarith [E.ε_lt], E.σc_pos.le, E.σc_le_θt, E.μΔ_le_θt, E.three_ν_le_β₃, hβ3,
    by rw [E.β_two]; exact E.three_β₂_le_σ, by rw [E.β_two]; exact E.β₂_le_η₂, E.γ_le_γ₀,
    E.γc_pos, E.γc_le_γ₀, E.βc_le_ηc, E.b_le_η₁, E.β₁_le_η₁, E.σs_pos, E.σs_le_θt, E.vs_le_θt,
    hζ, E.ζ_le_θt, (hεrcap.trans_le E.cap_le_θt).le, hTΛz, R.Lmax_ge_σ, E.Λ_lt_eg₀, E.b_le_η₀₁,
    hs, E.β₁_le_η₀₁, R.Lmax_ge_Lc₁, E.σc_le_eg, E.μΔ_lt_eg, E.σs_le_eg, E.vs_lt_eg, E.ζ_le_eg,
    E.ζ_le_Δ, hεrcap.trans_le E.cap_le_eg, E.β_two, E.β₁_le_η₀₂, R.Lmax_ge_Lc₂, E.σs_lt_θs,
    E.vs_lt_θs, E.ζ_lt_θs, hζΔ, hεrcap.trans_le E.cap_le_θs, hεr.le⟩

end BoundaryRegisterOverX_BSTD2

/-- **Every numerical premise of the boundary rows at ONE register point** (a CONCLUSION shape,
never a hypothesis): BCF02's eighteen at the supply index `m`, A2-mk's register block, the
per-stage graph clauses, the closed CHI block and BCG05's `θ = ϑ_min < 1/100` with A2's
`θ ≤ ϑ₀`. -/
def BoundaryRegisterPremisesX_BSTD2 {Θ : BoundaryProducerThresholds_BSTD1}
    {χ : BoundaryChainThresholds_BSTD2} (E : BoundaryEarlyOverX_BSTD2 Θ χ) {V : ℝ}
    (R : BoundaryRegisterOverX_BSTD2 E V) (m : ℕ) : Prop :=
  (2 ≤ E.Δ ∧ 0 ≤ E.Λ ∧ E.μ ≤ 1 / 10 ^ 8 ∧ E.τ ≤ 1 / 10 ^ 8 ∧ E.σc ≤ 1 / 1000 ∧
    1140 * E.Δ ≤ 35 * (m : ℝ) ∧ 1000 * E.Δ ≤ E.T ∧ 0 ≤ E.σs ∧ E.σs ≤ 1 / 100 ∧
    E.b < 1 / 1000000 ∧ E.s < 1 / 1000000 ∧ E.β 2 < 1 / 1000000 ∧
    (bcf02Sigma_BCF2K E.Δ)⁻¹ ≤ R.Lmax ∧ E.b ≤ bcf02Eta_BCF2K E.Δ ∧
    3 * E.b ≤ bcf02Sigma_BCF2K E.Δ ∧ E.b * (2 * (20 * E.Δ + 1)) ≤ 1 ∧
    1000000 * E.Δ * E.Λ < 1 / 100000 ∧ E.μ * E.Δ < 1 / 10000) ∧
  (0 ≤ E.Λ ∧ 0 < E.Δ ∧ E.μ ≤ 1 / 100 ∧ E.τ ≤ 1 / 100 ∧ 100 * E.Δ * E.Λ ≤ 1 / 100 ∧ 0 ≤ V ∧
    0 < E.β 1 ∧ 0 < E.b ∧ E.e ≤ 1 / 10 ∧ 1 ≤ E.Δ ∧ 1000000 * E.Δ * E.Λ < 1 / 100000) ∧
  (1000 * tcpGraphConst * E.Δ * E.Λ < χ.eg 0 ∧ 1000 * egpGraphConst * E.Δ * E.Λ < χ.eg 1 ∧
    1000 * sgpGraphBound * E.Δ * E.Λ < χ.eg 2) ∧
  (0 ≤ E.Λ ∧ E.μ ≤ 1 / 100 ∧ E.τ ≤ 1 / 100 ∧ 1000000 * E.Δ * E.Λ < 1 / 100000 ∧
    4 * (10 + 2 * (2000000 * E.Δ) + E.Δ / 3) ≤ R.Lmax ∧ E.e < 1 / 40 ∧
    1600 * (1000000 * E.Δ) ≤ E.T ∧
    0 ≤ E.ε ∧ E.ε ≤ 1 ∧ 0 ≤ E.σc ∧ E.σc ≤ χ.θt ^ 2 / 1000 ∧ E.μ * E.Δ ≤ χ.θt / 100 ∧
    3 * χ.ν ≤ E.β 3 ∧ E.β 3 < 1 ∧
    3 * E.β 2 ≤ χ.σ ∧ E.β 2 ≤ χ.η₂ ∧ E.γ ≤ χ.γ₀ ∧ 0 < E.γc ∧ E.γc ≤ χ.γ₀ ∧ E.βc ≤ χ.ηc ∧
    E.b ≤ χ.η₁ E.β₂ E.Δ ∧ E.β 1 ≤ χ.η₁ E.β₂ E.Δ ∧ 0 < E.σs ∧
    E.σs ≤ χ.θt ^ 2 / 1000 ∧ E.vs ≤ χ.θt / 100 ∧ 0 < E.ζ ∧
    E.ζ ≤ χ.θt ^ 2 / 1000 ∧ E.εr ≤ χ.θt / 100 ∧ 20 * E.Λz ≤ E.T ∧ χ.σ⁻¹ ≤ R.Lmax ∧
    1000 * tcpGraphConst * E.Δ * E.Λ < χ.eg 0 ∧
    E.b ≤ χ.η₀₁ E.β₂ E.Δ ∧ E.s < 1 / 1000000 ∧ E.β 1 ≤ χ.η₀₁ E.β₂ E.Δ ∧
    χ.Lc₁ E.β₂ E.Δ ≤ R.Lmax ∧
    E.σc ≤ (χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 ∧
    E.μ * E.Δ < χ.eg 1 / (20 * egpGraphConst) / 100 ∧
    E.σs ≤ (χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 ∧
    E.vs < χ.eg 1 / (20 * egpGraphConst) / 100 ∧
    E.ζ ≤ (χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 ∧
    E.ζ ≤ 1 / (1000 * (1000000 * E.Δ)) ∧
    E.εr < χ.eg 1 / (20 * egpGraphConst) / (100 * (1000000 * E.Δ)) ∧
    E.β 2 = E.β₂ ∧ E.β 1 ≤ χ.η₀₂ E.β₂ E.Δ ∧
    χ.Lc₂ E.β₂ E.Δ ≤ R.Lmax ∧ E.σs < χ.θs E.β₂ E.Δ ^ 2 / 10 ^ 6 ∧
    E.vs < χ.θs E.β₂ E.Δ / 100 ∧ E.ζ < χ.θs E.β₂ E.Δ ^ 2 / 10 ^ 6 ∧
    E.ζ < 1 / (100 * (1000000 * E.Δ)) ∧ E.εr < χ.θs E.β₂ E.Δ / (100 * (1000000 * E.Δ)) ∧
    0 ≤ E.εr) ∧
  (E.ϑmin < 1 / 100 ∧ E.ϑmin ≤ χ.ϑ₀)

/-- **All premises hold at the extended register** (for every supply index `m` with
`1140Δ ≤ 35m`; a tail member `n` has `m = n + 1`). -/
theorem BoundaryRegisterOverX_BSTD2.premises_BSTD2 {Θ : BoundaryProducerThresholds_BSTD1}
    {χ : BoundaryChainThresholds_BSTD2} {E : BoundaryEarlyOverX_BSTD2 Θ χ} {V : ℝ}
    (R : BoundaryRegisterOverX_BSTD2 E V) {m : ℕ} (hm : 1140 * E.Δ ≤ 35 * (m : ℝ)) :
    BoundaryRegisterPremisesX_BSTD2 E R m :=
  ⟨R.bcf02_premises_BSTD2 hm, R.register_block_BSTD2, E.stage_graph_BSTD2, R.chi_block_BSTD2,
    E.theta_BSTD2⟩

/-- **Every tail member of the extended assignment carries all premises at its supply index
`n + 1`.** -/
theorem BoundaryMemberOutputX_BSTD2.premises_BSTD2 {Θ : BoundaryProducerThresholds_BSTD1}
    {χ : BoundaryChainThresholds_BSTD2} {K : ℕ} {A : ℝ → ℝ} {E : BoundaryEarlyOverX_BSTD2 Θ χ}
    {V : ℝ} {S : BoundaryStandingSequence_BSTD1 K A Θ.δStar} {n : ℕ}
    {R : BoundaryRegisterOverX_BSTD2 E V} (h : BoundaryMemberOutputX_BSTD2 S n R) :
    BoundaryRegisterPremisesX_BSTD2 E R (n + 1) :=
  R.premises_BSTD2 h.2

/-! ### The inhabitant -/

/-- **The new clauses as staged requests** (each read at its STG prefix: `γ, γc, βc` early, `β₂`
before `βc`, `σc, μ` at `C14PreScale` (∋ `β₂, Δ`), `Λ` at `C14PreEdge`, `b` at `C14PreVol`, `σs, vs`
at `C14PreSplit`, `ζ, β₁` at `C14PreSlim`, `cap` at `C14PreBeta`; every other request trivial). -/
def chiRequests_BSTD2 (χ : BoundaryChainThresholds_BSTD2) : C14StagedRequestsSTG where
  γ _ := χ.γ₀
  γc _ := χ.γ₀
  βc _ := χ.ηc
  β₂ _ := min (χ.σ / 3) χ.η₂
  Δ _ := 0
  σc _ := min (1 / 1000) (min (χ.θt ^ 2 / 1000) ((χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8))
  ε _ := 1
  μ p := min (1 / (100000 * p.Δ))
    (min (χ.θt / (100 * p.Δ)) (χ.eg 1 / (20 * egpGraphConst) / (200 * p.Δ)))
  τ _ := 1
  s _ := 1
  b' _ := 1
  s' _ := 1
  Λ p := min (χ.eg 0 / (2000 * tcpGraphConst * p.Δ))
    (min (χ.eg 1 / (2000 * egpGraphConst * p.Δ)) (χ.eg 2 / (2000 * sgpGraphBound * p.Δ)))
  w _ := 1
  b p := min (bcf02Eta_BCF2K p.Δ)
    (min (bcf02Sigma_BCF2K p.Δ / 3) (min (χ.η₁ p.β₂ p.Δ) (χ.η₀₁ p.β₂ p.Δ)))
  σs p := min (χ.θt ^ 2 / 1000)
    (min ((χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8) (χ.θs p.β₂ p.Δ ^ 2 / (2 * 10 ^ 6)))
  vs p := min (χ.θt / 100) (min (χ.eg 1 / (20 * egpGraphConst) / 200) (χ.θs p.β₂ p.Δ / 200))
  ζ p := min (χ.θt ^ 2 / 1000) (min ((χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8)
    (min (1 / (1000 * (1000000 * p.Δ))) (χ.θs p.β₂ p.Δ ^ 2 / (2 * 10 ^ 6))))
  β₁ p := min (χ.η₁ p.β₂ p.Δ) (min (χ.η₀₁ p.β₂ p.Δ) (χ.η₀₂ p.β₂ p.Δ))
  cap p := min (χ.θt / 100) (min (χ.eg 1 / (20 * egpGraphConst) / (100 * (1000000 * p.Δ)))
    (χ.θs p.β₂ p.Δ / (100 * (1000000 * p.Δ))))
  T _ := 0
  e _ := 1
  Lmax _ _ := 0
  γ_pos _ := χ.γ₀_pos
  γc_pos _ := χ.γ₀_pos
  βc_pos _ := χ.ηc_pos
  β₂_pos _ := lt_min (by linarith [χ.σ_pos]) χ.η₂_pos
  σc_pos _ := by
    have := χ.θt_pos
    have := χ.eg_pos 1
    have := egpGraphConst_pos_KC4
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  ε_pos _ := one_pos
  μ_pos p := by
    have := p.Δ_gt6
    have := χ.θt_pos
    have := χ.eg_pos 1
    have := egpGraphConst_pos_KC4
    have hΔ : 0 < p.Δ := by linarith
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  τ_pos _ := one_pos
  s_pos _ := one_pos
  b'_pos _ := one_pos
  s'_pos _ := one_pos
  Λ_pos p := by
    have := p.Δ_gt6
    have := χ.eg_pos 0
    have := χ.eg_pos 1
    have := χ.eg_pos 2
    have := egpGraphConst_pos_KC4
    have := sgpGraphBound_pos_GAF8
    have := one_le_tcpGraphConst
    have hΔ : 0 < p.Δ := by linarith
    have hC : 0 < tcpGraphConst := by linarith
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  w_pos _ := one_pos
  b_pos p := by
    have h6 := p.Δ_gt6
    obtain ⟨hσ, -, hη, -⟩ := bcf02_constants_spec_BCF2K (Δ := p.Δ) (by linarith)
    exact lt_min hη (lt_min (by positivity) (lt_min (χ.η₁_pos _ _) (χ.η₀₁_pos _ _)))
  σs_pos p := by
    have := χ.θt_pos
    have := χ.eg_pos 1
    have := egpGraphConst_pos_KC4
    have := χ.θs_pos p.β₂ p.Δ
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  vs_pos p := by
    have := χ.θt_pos
    have := χ.eg_pos 1
    have := egpGraphConst_pos_KC4
    have := χ.θs_pos p.β₂ p.Δ
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  ζ_pos p := by
    have := p.Δ_gt6
    have := χ.θt_pos
    have := χ.eg_pos 1
    have := egpGraphConst_pos_KC4
    have := χ.θs_pos p.β₂ p.Δ
    have hΔ : 0 < p.Δ := by linarith
    exact lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  β₁_pos p := lt_min (χ.η₁_pos _ _) (lt_min (χ.η₀₁_pos _ _) (χ.η₀₂_pos _ _))
  cap_pos p := by
    have := p.Δ_gt6
    have := χ.θt_pos
    have := χ.eg_pos 1
    have := egpGraphConst_pos_KC4
    have := χ.θs_pos p.β₂ p.Δ
    have hΔ : 0 < p.Δ := by linarith
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  e_pos _ := one_pos

/-- **The extended early choices are inhabited** for EVERY CHI record `χ` and every `(K, A)`:
lane BSTG-D1's staged inhabitant at the requests `chiRequests_BSTD2 χ` and the boundary layer
`ϑ ≡ min(1/200, ϑ₀)` carries every new clause (the STG prefix gives `β 3 = thr ≥ 3ν`,
`T ≥ 1600·10⁶Δ`, `β₂ ≤ 10⁻⁷`). All clauses are jointly satisfiable in the register's order. -/
theorem nonempty_boundaryEarlyChoicesX_BSTD2 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w)
    (χ : BoundaryChainThresholds_BSTD2) :
    Nonempty (BoundaryEarlyChoicesX_BSTD2 K hK A hA χ) := by
  let t : C14Tol :=
    { γT := 1
      θs := 1 / 2
      θe := 1 / 2
      θ2 := 1 / 2
      Cρ := 1
      e₁ := 1
      C₁ := 1
      γT_pos := one_pos
      γT_le := le_rfl
      θs_pos := by norm_num
      θs_lt := by norm_num
      θe_pos := by norm_num
      θe_lt := by norm_num
      θ2_pos := by norm_num
      θ2_lt := by norm_num
      Cρ_pos := one_pos
      e₁_pos := one_pos
      C₁_pos := one_pos }
  have hϑ : 0 < min (1 / 200 : ℝ) χ.ϑ₀ := lt_min (by norm_num) χ.ϑ₀_pos
  obtain ⟨E, hEϑ, -, -, -, P, -, hM, -, hEP⟩ :=
    exists_boundaryEarlyChoices_staged_BSTD1 K hK A hA t (fun _ => min (1 / 200 : ℝ) χ.ϑ₀)
      (fun _ => hϑ) 0 le_rfl 1 le_rfl (tcp01SupportBound + 1) le_rfl (chiRequests_BSTD2 χ)
  have eγ : E.γ = P.γ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.γ) hEP
  have eβc : E.βc = P.βc := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.βc) hEP
  have eγc : E.γc = P.γc := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.γc) hEP
  have eβ₂ : E.β₂ = P.β₂ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.β₂) hEP
  have eΔ : E.Δ = P.Δ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.Δ) hEP
  have eσc : E.σc = P.σc := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.σc) hEP
  have eμ : E.μ = P.μ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.μ) hEP
  have eΛ : E.Λ = P.Λ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.Λ) hEP
  have eb : E.b = P.b := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.b) hEP
  have eσs : E.σs = P.σs := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.σs) hEP
  have evs : E.vs = P.vs := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.vs) hEP
  have eβ : E.β = P.β := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.β) hEP
  have eζ : E.ζ = P.ζ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.ζ) hEP
  have ecap : E.cap = P.cap := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.cap) hEP
  have eT : E.T = P.T := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.T) hEP
  have hΔ := P.Δ_gt6
  have hΔ0 : 0 < P.Δ := by linarith
  have hC1 := egpGraphConst_pos_KC4
  have hC2 := sgpGraphBound_pos_GAF8
  have hC0 : 0 < tcpGraphConst := lt_of_lt_of_le one_pos one_le_tcpGraphConst
  have he0 := χ.eg_pos 0
  have he1 := χ.eg_pos 1
  have he2 := χ.eg_pos 2
  have hθs := χ.θs_pos P.β₂ P.Δ
  have hθt := χ.θt_pos
  -- the requests met by `P`, unfolded
  have hγ : P.γ ≤ χ.γ₀ := hM.γ_le
  have hγc : P.γc ≤ χ.γ₀ := hM.γc_le
  have hβc : P.βc ≤ χ.ηc := hM.βc_le
  have hβ₂ : P.β₂ ≤ min (χ.σ / 3) χ.η₂ := hM.β₂_le
  have hσc : P.σc ≤ min (1 / 1000) (min (χ.θt ^ 2 / 1000)
      ((χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8)) := hM.σc_le
  have hμ : P.μ ≤ min (1 / (100000 * P.Δ))
      (min (χ.θt / (100 * P.Δ)) (χ.eg 1 / (20 * egpGraphConst) / (200 * P.Δ))) := hM.μ_le
  have hΛ : P.Λ ≤ min (χ.eg 0 / (2000 * tcpGraphConst * P.Δ))
      (min (χ.eg 1 / (2000 * egpGraphConst * P.Δ)) (χ.eg 2 / (2000 * sgpGraphBound * P.Δ))) :=
    hM.Λ_le
  have hb : P.b ≤ min (bcf02Eta_BCF2K P.Δ)
      (min (bcf02Sigma_BCF2K P.Δ / 3) (min (χ.η₁ P.β₂ P.Δ) (χ.η₀₁ P.β₂ P.Δ))) := hM.b_le
  have hσs : P.σs ≤ min (χ.θt ^ 2 / 1000)
      (min ((χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8) (χ.θs P.β₂ P.Δ ^ 2 / (2 * 10 ^ 6))) :=
    hM.σs_le
  have hvs : P.vs ≤ min (χ.θt / 100)
      (min (χ.eg 1 / (20 * egpGraphConst) / 200) (χ.θs P.β₂ P.Δ / 200)) := hM.vs_le
  have hζ : P.ζ ≤ min (χ.θt ^ 2 / 1000) (min ((χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8)
      (min (1 / (1000 * (1000000 * P.Δ))) (χ.θs P.β₂ P.Δ ^ 2 / (2 * 10 ^ 6)))) := hM.ζ_le
  have hβ₁ : P.β 1 ≤ min (χ.η₁ P.β₂ P.Δ) (min (χ.η₀₁ P.β₂ P.Δ) (χ.η₀₂ P.β₂ P.Δ)) := hM.β₁_le
  have hcap : P.cap ≤ min (χ.θt / 100) (min (χ.eg 1 / (20 * egpGraphConst) /
      (100 * (1000000 * P.Δ))) (χ.θs P.β₂ P.Δ / (100 * (1000000 * P.Δ)))) := hM.cap_le
  -- the products `μΔ` and `CΔΛ`
  have hμΔ1 : P.μ * P.Δ ≤ 1 / 100000 := by
    have h := mul_le_mul_of_nonneg_right (hμ.trans (min_le_left _ _)) hΔ0.le
    have e : 1 / (100000 * P.Δ) * P.Δ = 1 / 100000 := by field_simp
    linarith
  have hμΔ2 : P.μ * P.Δ ≤ χ.θt / 100 := by
    have h := mul_le_mul_of_nonneg_right
      (hμ.trans ((min_le_right _ _).trans (min_le_left _ _))) hΔ0.le
    have e : χ.θt / (100 * P.Δ) * P.Δ = χ.θt / 100 := by field_simp
    linarith
  have hμΔ3 : P.μ * P.Δ ≤ χ.eg 1 / (20 * egpGraphConst) / 200 := by
    have h := mul_le_mul_of_nonneg_right
      (hμ.trans ((min_le_right _ _).trans (min_le_right _ _))) hΔ0.le
    have e : χ.eg 1 / (20 * egpGraphConst) / (200 * P.Δ) * P.Δ =
        χ.eg 1 / (20 * egpGraphConst) / 200 := by field_simp
    linarith
  have hgraph : ∀ (C e x : ℝ), 0 < C → 0 < e → x ≤ e / (2000 * C * P.Δ) →
      1000 * C * P.Δ * x < e := by
    intro C e x hC he hx
    have h := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ 1000 * C * P.Δ)
    have e' : 1000 * C * P.Δ * (e / (2000 * C * P.Δ)) = e / 2 := by field_simp; ring
    linarith
  have hζΔ : P.ζ ≤ 1 / (1000 * (1000000 * P.Δ)) :=
    hζ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hϑmin : min (min (1 / 200 : ℝ) χ.ϑ₀) (min (min (1 / 200 : ℝ) χ.ϑ₀)
      (min (1 / 200 : ℝ) χ.ϑ₀)) = min (1 / 200 : ℝ) χ.ϑ₀ := by simp
  have hϑ0 : E.ϑ 0 = min (1 / 200 : ℝ) χ.ϑ₀ := by rw [hEϑ]
  have hϑ1 : E.ϑ 1 = min (1 / 200 : ℝ) χ.ϑ₀ := by rw [hEϑ]
  have hϑ2 : E.ϑ 2 = min (1 / 200 : ℝ) χ.ϑ₀ := by rw [hEϑ]
  refine ⟨{ toBoundaryEarlyOver_BSTD1 := E
            γ_le_γ₀ := by rw [eγ]; exact hγ
            γc_le_γ₀ := by rw [eγc]; exact hγc
            βc_le_ηc := by rw [eβc]; exact hβc
            β₂_lt6 := by rw [eβ₂]; linarith [P.β₂_le7]
            three_β₂_le_σ := by rw [eβ₂]; linarith [hβ₂.trans (min_le_left _ _)]
            β₂_le_η₂ := by rw [eβ₂]; exact hβ₂.trans (min_le_right _ _)
            σc_le_milli := by rw [eσc]; exact hσc.trans (min_le_left _ _)
            σc_le_θt := by rw [eσc]; exact hσc.trans ((min_le_right _ _).trans (min_le_left _ _))
            σc_le_eg := by
              rw [eσc]; exact hσc.trans ((min_le_right _ _).trans (min_le_right _ _))
            μΔ_lt := by rw [eμ, eΔ]; linarith
            μΔ_le_θt := by rw [eμ, eΔ]; exact hμΔ2
            μΔ_lt_eg := by
              rw [eμ, eΔ]
              have : 0 < χ.eg 1 / (20 * egpGraphConst) := by positivity
              linarith
            Λ_lt_eg₀ := by
              rw [eΔ, eΛ]; exact hgraph _ _ _ hC0 he0 (hΛ.trans (min_le_left _ _))
            Λ_lt_eg₁ := by
              rw [eΔ, eΛ]
              exact hgraph _ _ _ hC1 he1 (hΛ.trans ((min_le_right _ _).trans (min_le_left _ _)))
            Λ_lt_eg₂ := by
              rw [eΔ, eΛ]
              exact hgraph _ _ _ hC2 he2 (hΛ.trans ((min_le_right _ _).trans (min_le_right _ _)))
            b_le_η := by rw [eb, eΔ]; exact hb.trans (min_le_left _ _)
            three_b_le_σ := by
              rw [eb, eΔ]; linarith [hb.trans ((min_le_right _ _).trans (min_le_left _ _))]
            b_le_η₁ := by
              rw [eb, eβ₂, eΔ]
              exact hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
            b_le_η₀₁ := by
              rw [eb, eβ₂, eΔ]
              exact hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
                (min_le_right _ _)))
            σs_le_θt := by rw [eσs]; exact hσs.trans (min_le_left _ _)
            σs_le_eg := by rw [eσs]; exact hσs.trans ((min_le_right _ _).trans (min_le_left _ _))
            σs_lt_θs := by
              rw [eσs, eβ₂, eΔ]
              have h := hσs.trans ((min_le_right _ _).trans (min_le_right _ _))
              have : 0 < χ.θs P.β₂ P.Δ ^ 2 := by positivity
              have e : χ.θs P.β₂ P.Δ ^ 2 / (2 * 10 ^ 6) = χ.θs P.β₂ P.Δ ^ 2 / 10 ^ 6 / 2 := by ring
              have : 0 < χ.θs P.β₂ P.Δ ^ 2 / 10 ^ 6 := by positivity
              linarith
            vs_le_θt := by rw [evs]; exact hvs.trans (min_le_left _ _)
            vs_lt_eg := by
              rw [evs]
              have h := hvs.trans ((min_le_right _ _).trans (min_le_left _ _))
              have : 0 < χ.eg 1 / (20 * egpGraphConst) := by positivity
              linarith
            vs_lt_θs := by
              rw [evs, eβ₂, eΔ]
              have h := hvs.trans ((min_le_right _ _).trans (min_le_right _ _))
              linarith
            three_ν_le_β₃ := by rw [eβ, P.β_three]; exact χ.three_ν_le
            β₁_le_η₁ := by rw [eβ, eβ₂, eΔ]; exact hβ₁.trans (min_le_left _ _)
            β₁_le_η₀₁ := by
              rw [eβ, eβ₂, eΔ]; exact hβ₁.trans ((min_le_right _ _).trans (min_le_left _ _))
            β₁_le_η₀₂ := by
              rw [eβ, eβ₂, eΔ]; exact hβ₁.trans ((min_le_right _ _).trans (min_le_right _ _))
            ζ_le_θt := by rw [eζ]; exact hζ.trans (min_le_left _ _)
            ζ_le_eg := by rw [eζ]; exact hζ.trans ((min_le_right _ _).trans (min_le_left _ _))
            ζ_le_Δ := by rw [eζ, eΔ]; exact hζΔ
            ζ_lt_θs := by
              rw [eζ, eβ₂, eΔ]
              have h := hζ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
                (min_le_right _ _)))
              have : 0 < χ.θs P.β₂ P.Δ ^ 2 / 10 ^ 6 := by positivity
              have e : χ.θs P.β₂ P.Δ ^ 2 / (2 * 10 ^ 6) = χ.θs P.β₂ P.Δ ^ 2 / 10 ^ 6 / 2 := by ring
              linarith
            cap_le_θt := by rw [ecap]; exact hcap.trans (min_le_left _ _)
            cap_le_eg := by
              rw [ecap, eΔ]; exact hcap.trans ((min_le_right _ _).trans (min_le_left _ _))
            cap_le_θs := by
              rw [ecap, eβ₂, eΔ]; exact hcap.trans ((min_le_right _ _).trans (min_le_right _ _))
            T_ge_Δ := by rw [eT, eΔ]; exact P.T_Δ
            ϑmin_lt := by
              rw [hϑ0, hϑ1, hϑ2, hϑmin]
              exact (min_le_left _ _).trans_lt (by norm_num)
            ϑmin_le := by
              rw [hϑ0, hϑ1, hϑ2, hϑmin]
              exact min_le_right _ _ }⟩

end DifferentialGeometry.Geometry.Collapse
