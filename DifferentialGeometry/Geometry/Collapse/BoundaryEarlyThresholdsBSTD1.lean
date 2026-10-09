import DifferentialGeometry.Geometry.Collapse.BoundaryPacketsOutBFRZSeqBSTD1
import DifferentialGeometry.Geometry.Collapse.BoundaryRegister
import DifferentialGeometry.Geometry.Fibration.ActualWholeSupportCount

/-!
# The boundary producer's early thresholds as top-level definitions (lane BSTG-D1, D61-11 D1)

Dispositions of task 61, D61-11 (draft §7.2): the per-sequence assignment
`exists_boundarySequenceAssignment (early) (S)` takes the early choices as an INPUT, so every
legal early choice must have a continuation. In the boundary staged adapter of lane BSTG
(`exists_bdry_staged_assignment_BSTG`) the early prefix is an OUTPUT, and its prefix record
`C14PreFinal` stores the producer's threshold outputs (`β₀ σ₀ Δ₀ …`) only with inequality facts.
Here the threshold outputs of the boundary producer (T3B on `LocalPacketsOnBFRZ` per member at the
counterexample index `n + 1`, `lc88_boundary_packets_BFRZ_out_succ_BSTD1`) are exported as
top-level Skolem data, by the `choose` / `dite` pattern of `exists_closed_realization_C14D_VAL6`
(each threshold a function of the parameters BEFORE it, guarded by the producer's conditions):

* `BdryParamsCollar_BSTD1 ⊂ … ⊂ BdryParamsZero_BSTD1 ⊂ BoundaryEarlyParams_BSTD1`: the producer's
  parameters, one structure per binder group (`γ βc γc | β₂ Δ | σc ε μ τ s b' s' | σ Λ | w |
  b σs vs | β ζ cap | T e`); a threshold reads only the structure BEFORE it (quantifier order
  by type).
* `BoundaryProducerThresholds_BSTD1`: `δStar a₂ β₀ σ₀ Δ₀ τ₀ bc₀ a₀ b₁ w₀ bd₀ b₀ εr δ' Λz` as such
  functions, with positivity and the producer's own output facts (`β₀ ≤ a₂`, `εr < 1/4`,
  `εr < cap`).
* `BoundaryEarlyOver_BSTD1 Θ`: the parameters with EXACTLY the producer's conditions read against
  `Θ`, the early boundary layer (D61-11 D4: `ϑ : Fin 3 → ℝ` (`ϑ₁ = ϑ 0`, `ϑ = min_j ϑ_j`), the stage
  constant `c₃ ≥ 0`, the profile constant `P_* ≥ 1`, the whole-list count `N ≥ N_TCP + 1`
  (`tcp01SupportBound`, lane C14-COUNT; never the number of boundary components)) and the boundary
  caps of lane BSTG (`w < ω₃/4`, `vs < ϑ₃/4`). No field states a continuation.
* `BoundaryStandingSequence_BSTD1 K A δStar`: one standing sequence of BBR03 (ratios `δ_{n+1}`,
  `0 < δ₀ ≤ δStar`, connected universe-`0` carriers, nearly cuspidal boundary, volume collapse,
  derivative control with `A`).
* `exists_bdryThresholds_BSTD1`: there are thresholds `Θ` such that EVERY early choice over `Θ` and
  EVERY standing sequence with `δ₀ ≤ Θ.δStar` have T3B-BFRZ's continuation (`V ≥ T`, `δ < δ'`, then
  for all `Lmax, βd, εN > 0` the per-member conclusion on a tail).
* `bdryThresholds_BSTD1 K hK A hA` (top-level `Classical.choose`), `BoundaryEarlyChoices_BSTD1`
  (early choices over it) and `bdry_early_continuation_BSTD1` (the continuation for every legal
  early choice: `early` is an input).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-! ### The producer's parameters, one structure per binder group -/

/-- The parameters of the binder groups `γ | βc γc`. -/
structure BdryParamsCollar_BSTD1 where
  γ : ℝ
  βc : ℝ
  γc : ℝ

/-- … then `β₂ Δ`. -/
structure BdryParamsScale_BSTD1 extends BdryParamsCollar_BSTD1 where
  β₂ : ℝ
  Δ : ℝ

/-- … then `σc ε μ τ s b' s'`. -/
structure BdryParamsEdge_BSTD1 extends BdryParamsScale_BSTD1 where
  σc : ℝ
  ε : ℝ
  μ : ℝ
  τ : ℝ
  s : ℝ
  b' : ℝ
  s' : ℝ

/-- … then `σ Λ`. -/
structure BdryParamsLip_BSTD1 extends BdryParamsEdge_BSTD1 where
  σ : ℝ
  Λ : ℝ

/-- … then `w`. -/
structure BdryParamsVol_BSTD1 extends BdryParamsLip_BSTD1 where
  w : ℝ

/-- … then `b σs vs`. -/
structure BdryParamsSlim_BSTD1 extends BdryParamsVol_BSTD1 where
  b : ℝ
  σs : ℝ
  vs : ℝ

/-- … then `β ζ cap`. -/
structure BdryParamsZero_BSTD1 extends BdryParamsSlim_BSTD1 where
  β : ℕ → ℝ
  ζ : ℝ
  cap : ℝ

/-- **All parameters of the boundary producer before the sequence** (the last group `T e`). -/
structure BoundaryEarlyParams_BSTD1 extends BdryParamsZero_BSTD1 where
  T : ℝ
  e : ℝ

/-! ### The exported thresholds -/

/-- **The boundary producer's threshold outputs as functions** (D61-11 D1): each output is a
function of the parameters before it (`β₀(γ)`, `σ₀, Δ₀ (γ βc γc)`, `τ₀, bc₀ (… β₂ Δ)`,
`a₀, b₁ (… s')`, `w₀ (… Λ)`, `bd₀ (… w)`, `b₀ (… vs)`, `εr, δ', Λz (… cap)`), with the producer's
own facts about its outputs. -/
structure BoundaryProducerThresholds_BSTD1 where
  δStar : ℝ
  a₂ : ℝ
  B0 : ℝ → ℝ
  S0 : BdryParamsCollar_BSTD1 → ℝ
  D0 : BdryParamsCollar_BSTD1 → ℝ
  T0 : BdryParamsScale_BSTD1 → ℝ
  BC : BdryParamsScale_BSTD1 → ℝ
  A0 : BdryParamsEdge_BSTD1 → ℝ
  B1 : BdryParamsEdge_BSTD1 → ℝ
  W0 : BdryParamsLip_BSTD1 → ℝ
  BD : BdryParamsVol_BSTD1 → ℝ
  BZ : BdryParamsSlim_BSTD1 → ℝ
  ER : BdryParamsZero_BSTD1 → ℝ
  DP : BdryParamsZero_BSTD1 → ℝ
  LZ : BdryParamsZero_BSTD1 → ℝ
  δStar_pos : 0 < δStar
  a₂_pos : 0 < a₂
  B0_pos : ∀ γ, 0 < B0 γ
  B0_le : ∀ γ, B0 γ ≤ a₂
  S0_pos : ∀ p, 0 < S0 p
  D0_pos : ∀ p, 0 < D0 p
  T0_pos : ∀ p, 0 < T0 p
  BC_pos : ∀ p, 0 < BC p
  A0_pos : ∀ p, 0 < A0 p
  B1_pos : ∀ p, 0 < B1 p
  W0_pos : ∀ p, 0 < W0 p
  BD_pos : ∀ p, 0 < BD p
  BZ_pos : ∀ p, 0 < BZ p
  ER_pos : ∀ p, 0 < ER p
  ER_lt : ∀ p, ER p < 1 / 4
  ER_lt_cap : ∀ p : BdryParamsZero_BSTD1, 0 < p.cap → ER p < p.cap
  DP_pos : ∀ p, 0 < DP p
  LZ_pos : ∀ p, 0 < LZ p

/-! ### Early choices over the thresholds -/

/-- **An early choice over the thresholds `Θ`** (D61-11 D1 + D4): the producer's parameters with
EXACTLY the producer's conditions, each read against `Θ` at the parameters before it; the early
boundary layer `ϑ` (three positive tolerances; `ϑ₁ = ϑ 0`, `ϑ₃ = ϑ 2`), `c₃ ≥ 0`, `P_* ≥ 1`,
`N ≥ N_TCP + 1`; and the boundary caps `w < ω₃/4`, `vs < ϑ₃/4`. -/
structure BoundaryEarlyOver_BSTD1 (Θ : BoundaryProducerThresholds_BSTD1) extends
    BoundaryEarlyParams_BSTD1 where
  γ_pos : 0 < γ
  γ_lt : γ < 1 / 10
  βc_pos : 0 < βc
  βc_lt : βc < γc / 1000
  γc_pos : 0 < γc
  γc_lt : γc < 1 / 100
  β₂_pos : 0 < β₂
  β₂_le : β₂ ≤ Θ.B0 γ
  β₂_lt : β₂ < 1 / 100
  Δ_gt : 100 / β₂ < Δ
  Δ_ge : Θ.D0 toBdryParamsCollar_BSTD1 ≤ Δ
  σc_pos : 0 < σc
  σc_le : σc ≤ Θ.S0 toBdryParamsCollar_BSTD1
  σc_lt : σc < 1
  ε_pos : 0 < ε
  ε_lt : ε < 1 / 100
  μ_pos : 0 < μ
  μ_le : μ ≤ 1 / 1000000
  τ_pos : 0 < τ
  τ_le : τ ≤ Θ.T0 toBdryParamsScale_BSTD1
  τ_sqrt : 140 * Real.sqrt τ < ε ^ 2 / 20
  ε_le8 : ε ≤ 1 / 10 ^ 8
  μ_le8 : μ ≤ 1 / 10 ^ 8
  s_pos : 0 < s
  s_lt : s < 1 / 100
  s_lt_b' : s < b' / 100000
  s_lt_s' : s < s' / 100000
  b'_lt : b' < 1 / (1000000 * Δ)
  s'_lt : s' < 1 / (1000000 * Δ)
  b'_lt_τ : b' < τ * Δ / 1000000000
  s'_lt_τ : s' < τ * Δ / 1000000000
  σ_pos : 0 < σ
  σ_le_a₂ : σ ≤ Θ.a₂
  σ_le_thr : σ ≤ threeSplittingExclusionThreshold.{0, 0}
  σ_le_a₀ : σ ≤ Θ.A0 toBdryParamsEdge_BSTD1
  Λ_pos : 0 < Λ
  Λ_c1 : Δ * Λ * 2000000 ≤ 1 / 100
  Λ_c2 : Λ < 1 / (1000000 * Δ)
  Λ_c3 : 100 * Δ * Λ ≤ 1 / 1000000
  budget : 2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000
  Λ_c5 : Λ < s' / (100000000 * Δ ^ 2)
  Λ_c6 : 100 * Δ * Λ ≤ 1 / 10 ^ 8
  w_pos : 0 < w
  w_lt : w < Θ.W0 toBdryParamsLip_BSTD1
  w_lt_pi : w < 4 * Real.pi / 3
  b_pos : 0 < b
  b_lt_s : b < s / 100000
  b_lt_bc₀ : b < Θ.BC toBdryParamsScale_BSTD1
  b_lt_b₁ : b < Θ.B1 toBdryParamsEdge_BSTD1
  b_inv : 100 * Δ < b⁻¹
  b_lt_bd₀ : b < Θ.BD toBdryParamsVol_BSTD1
  σs_pos : 0 < σs
  σs_le : σs ≤ 1 / 100
  vs_pos : 0 < vs
  β_two : β 2 = β₂
  β₁_pos : 0 < β 1
  β₁_lt_b₀ : β 1 < Θ.BZ toBdryParamsSlim_BSTD1
  β₁_lt : β 1 < 1
  β_three : β 3 ≤ threeSplittingExclusionThreshold.{0, 0}
  β₁_lt_ζ : β 1 < ζ
  ζ_lt : ζ < 1
  cap_pos : 0 < cap
  T_pos : 0 < T
  T_ge : 20 * Θ.LZ toBdryParamsZero_BSTD1 ≤ T
  e_pos : 0 < e
  e_lt : e < 1 / 40
  /-- D4: the three boundary tolerances `ϑ₁, ϑ₂, ϑ₃` (BR11). -/
  ϑ : Fin 3 → ℝ
  ϑ_pos : ∀ j, 0 < ϑ j
  /-- D4: the stage constant `c₃` (BRegPhysical's `ε_∂ = 20 c₃ r_∂`). -/
  c₃ : ℝ
  c₃_nonneg : 0 ≤ c₃
  /-- D4: the profile constant `P_*` (BCG.0). -/
  Pstar : ℝ
  one_le_Pstar : 1 ≤ Pstar
  /-- D4: the augmented whole-list count `N_int + 1` (never the number of boundary components). -/
  N : ℕ
  N_ge : tcp01SupportBound + 1 ≤ N
  w_lt_cap : w < boundaryVolumeCap
  vs_lt_ϑ : vs < ϑ 2 / 4

namespace BoundaryEarlyOver_BSTD1

variable {Θ : BoundaryProducerThresholds_BSTD1}

/-- The producer's radial output `εr` at the early choice. -/
def εr (E : BoundaryEarlyOver_BSTD1 Θ) : ℝ := Θ.ER E.toBdryParamsZero_BSTD1

/-- The producer's cone-error bound `δ'` at the early choice. -/
def δ' (E : BoundaryEarlyOver_BSTD1 Θ) : ℝ := Θ.DP E.toBdryParamsZero_BSTD1

/-- The producer's zero-scale output `Λz` at the early choice. -/
def Λz (E : BoundaryEarlyOver_BSTD1 Θ) : ℝ := Θ.LZ E.toBdryParamsZero_BSTD1

/-- `ϑ = min_j ϑ_j` (BRegPhysical). -/
def ϑmin (E : BoundaryEarlyOver_BSTD1 Θ) : ℝ := min (E.ϑ 0) (min (E.ϑ 1) (E.ϑ 2))

theorem ϑmin_pos (E : BoundaryEarlyOver_BSTD1 Θ) : 0 < E.ϑmin :=
  lt_min (E.ϑ_pos 0) (lt_min (E.ϑ_pos 1) (E.ϑ_pos 2))

theorem δ'_pos (E : BoundaryEarlyOver_BSTD1 Θ) : 0 < E.δ' := Θ.DP_pos _

theorem εr_pos (E : BoundaryEarlyOver_BSTD1 Θ) : 0 < E.εr := Θ.ER_pos _

theorem εr_lt_cap (E : BoundaryEarlyOver_BSTD1 Θ) : E.εr < E.cap := Θ.ER_lt_cap _ E.cap_pos

theorem Δ_pos (E : BoundaryEarlyOver_BSTD1 Θ) : 0 < E.Δ := by
  have h := E.Δ_gt
  have h0 : 0 < 100 / E.β₂ := div_pos (by norm_num) E.β₂_pos
  linarith

end BoundaryEarlyOver_BSTD1

/-! ### One standing sequence -/

/-- **One standing sequence of BBR03** at the ratios
`δ_{n+1} = boundaryCounterexampleRatio δ₀ (n+1)` with `0 < δ₀ ≤ δStar`: connected universe-`0`
carriers with nearly cuspidal boundary, volume collapse and derivative control with `A` (the
boundary producer's standing hypotheses). -/
structure BoundaryStandingSequence_BSTD1 (K : ℕ) (A : ℝ → ℝ) (δStar : ℝ) where
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  δ₀_le : δ₀ ≤ δStar
  W : ℕ → CompactCarrier.{0}
  conn : ∀ n, ConnectedSpace (W n).Carrier
  g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier
  B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))
  coll : ∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))
  der : ∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-! ### The Skolem export -/

/-- A guarded choice satisfies every property that both branches satisfy. -/
theorem dite_mem_BSTD1 {P : Prop} [Decidable P] {f : P → ℝ} {c : ℝ} (R : ℝ → Prop)
    (hf : ∀ h, R (f h)) (hc : R c) : R (if h : P then f h else c) := by
  by_cases h : P
  · rw [dite_eq_left h]
    exact hf h
  · rw [dite_eq_right h]
    exact hc

/-- **The boundary producer's thresholds, exported** (D61-11 D1; the `choose` / `dite` pattern of
`exists_closed_realization_C14D_VAL6`): there are thresholds `Θ` such that for EVERY early choice
`E` over `Θ` and EVERY standing sequence `S` with `δ₀ ≤ Θ.δStar` the producer's continuation holds:
`V ≥ T`, `δ < δ'`, and for all `Lmax, βd, εN > 0` every late member carries T3B-BFRZ's per-member
conclusion at the ratio `δ_{n+1}`, the BCP04.a index `n + 1` and exactly `E`'s parameters. -/
theorem exists_bdryThresholds_BSTD1 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ Θ : BoundaryProducerThresholds_BSTD1, ∀ (E : BoundaryEarlyOver_BSTD1 Θ)
      (S : BoundaryStandingSequence_BSTD1 K A Θ.δStar),
      ∃ V : ℝ, E.T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < E.δ' ∧ ∀ Lmax : ℝ, 0 < Lmax →
      ∀ βd εN : ℝ, 0 < βd → 0 < εN → ∀ᶠ n in atTop,
        BoundaryPacketsOutBFRZ_BSTD1 (S.W n) (S.g n) K A (boundaryCounterexampleRatio S.δ₀ (n + 1))
          (S.B n) ((n + 1 : ℕ) : ℝ) E.Λ E.w E.β E.Δ E.σs E.σc E.μ E.b E.s E.b' E.s' E.ε E.γc E.βc
          Lmax E.τ E.γ δ E.εr E.e E.T V E.vs E.ζ E.Λz βd εN := by
  classical
  obtain ⟨δStar, hδStar, a₂, ha₂, hP⟩ := lc88_boundary_packets_BFRZ_out_succ_BSTD1 K hK A hA
  -- `β₀ (γ)`
  let C1 : ℝ → Prop := fun γ => 0 < γ ∧ γ < 1 / 10
  have hP1 : ∀ (γ : ℝ) (hc : C1 γ), _ := fun γ hc => hP γ hc.1 hc.2
  choose β₀ hβ₀ hβ₀a hP using hP1
  let B0 : ℝ → ℝ := fun γ => if hc : C1 γ then β₀ γ hc else a₂
  -- `σ₀, Δ₀ (γ βc γc)`
  let C2 : BdryParamsCollar_BSTD1 → Prop := fun p =>
    C1 p.γ ∧ (0 < p.βc ∧ p.βc < p.γc / 1000 ∧ 0 < p.γc ∧ p.γc < 1 / 100)
  have hP2 : ∀ (p : BdryParamsCollar_BSTD1) (hc : C2 p), _ := fun p hc =>
    hP p.γ hc.1 p.βc p.γc hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  choose σ₀ hσ₀ Δ₀ hΔ₀ hP using hP2
  let S0 : BdryParamsCollar_BSTD1 → ℝ := fun p => if hc : C2 p then σ₀ p hc else 1
  let D0 : BdryParamsCollar_BSTD1 → ℝ := fun p => if hc : C2 p then Δ₀ p hc else 1
  -- `τ₀, bc₀ (… β₂ Δ)`
  let C3 : BdryParamsScale_BSTD1 → Prop := fun p =>
    C2 p.toBdryParamsCollar_BSTD1 ∧ (0 < p.β₂ ∧ p.β₂ ≤ B0 p.γ ∧ p.β₂ < 1 / 100 ∧
      100 / p.β₂ < p.Δ ∧ D0 p.toBdryParamsCollar_BSTD1 ≤ p.Δ)
  have hP3 : ∀ (p : BdryParamsScale_BSTD1) (hc : C3 p), _ := fun p hc =>
    hP p.toBdryParamsCollar_BSTD1 hc.1 p.β₂ p.Δ hc.2.1
      ((hc.2.2.1).trans_eq (dite_eq_left hc.1.1)) hc.2.2.2.1 hc.2.2.2.2.1
      ((dite_eq_left hc.1).symm.trans_le hc.2.2.2.2.2)
  choose τ₀ hτ₀ bc₀ hbc₀ hP using hP3
  let T0 : BdryParamsScale_BSTD1 → ℝ := fun p => if hc : C3 p then τ₀ p hc else 1
  let BC : BdryParamsScale_BSTD1 → ℝ := fun p => if hc : C3 p then bc₀ p hc else 1
  -- `a₀, b₁ (… σc ε μ τ s b' s')`
  let C4 : BdryParamsEdge_BSTD1 → Prop := fun p =>
    C3 p.toBdryParamsScale_BSTD1 ∧
    (0 < p.σc ∧ p.σc ≤ S0 p.toBdryParamsCollar_BSTD1 ∧ p.σc < 1 ∧ 0 < p.ε ∧ p.ε < 1 / 100 ∧
      0 < p.μ ∧ p.μ ≤ 1 / 1000000 ∧ 0 < p.τ ∧ p.τ ≤ T0 p.toBdryParamsScale_BSTD1 ∧
      140 * Real.sqrt p.τ < p.ε ^ 2 / 20 ∧ p.ε ≤ 1 / 10 ^ 8 ∧ p.μ ≤ 1 / 10 ^ 8) ∧
    (0 < p.s ∧ p.s < 1 / 100 ∧ p.s < p.b' / 100000 ∧ p.s < p.s' / 100000 ∧
      p.b' < 1 / (1000000 * p.Δ) ∧ p.s' < 1 / (1000000 * p.Δ) ∧
      p.b' < p.τ * p.Δ / 1000000000 ∧ p.s' < p.τ * p.Δ / 1000000000)
  have hP4 : ∀ (p : BdryParamsEdge_BSTD1) (hc : C4 p), _ := fun p hc =>
    hP p.toBdryParamsScale_BSTD1 hc.1 p.σc p.ε p.μ p.τ hc.2.1.1
      ((hc.2.1.2.1).trans_eq (dite_eq_left hc.1.1)) hc.2.1.2.2.1 hc.2.1.2.2.2.1
      hc.2.1.2.2.2.2.1 hc.2.1.2.2.2.2.2.1 hc.2.1.2.2.2.2.2.2.1 hc.2.1.2.2.2.2.2.2.2.1
      ((hc.2.1.2.2.2.2.2.2.2.2.1).trans_eq (dite_eq_left hc.1))
      hc.2.1.2.2.2.2.2.2.2.2.2.1 hc.2.1.2.2.2.2.2.2.2.2.2.2.1 hc.2.1.2.2.2.2.2.2.2.2.2.2.2
      p.s p.b' p.s' hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1
      hc.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2
  choose a₀ b₁ ha₀ hb₁ hP using hP4
  let A0 : BdryParamsEdge_BSTD1 → ℝ := fun p => if hc : C4 p then a₀ p hc else 1
  let B1 : BdryParamsEdge_BSTD1 → ℝ := fun p => if hc : C4 p then b₁ p hc else 1
  -- `w₀ (… σ Λ)`
  let C5 : BdryParamsLip_BSTD1 → Prop := fun p =>
    C4 p.toBdryParamsEdge_BSTD1 ∧
    (0 < p.σ ∧ p.σ ≤ a₂ ∧ p.σ ≤ threeSplittingExclusionThreshold.{0, 0} ∧
      p.σ ≤ A0 p.toBdryParamsEdge_BSTD1) ∧
    (0 < p.Λ ∧ p.Δ * p.Λ * 2000000 ≤ 1 / 100 ∧ p.Λ < 1 / (1000000 * p.Δ) ∧
      100 * p.Δ * p.Λ ≤ 1 / 1000000 ∧
      2 * p.ε + 300 * p.Δ * p.Λ + Real.sqrt (504000 / p.Δ + 3780 * p.τ) < p.γc / 1000 ∧
      p.Λ < p.s' / (100000000 * p.Δ ^ 2) ∧ 100 * p.Δ * p.Λ ≤ 1 / 10 ^ 8)
  have hP5 : ∀ (p : BdryParamsLip_BSTD1) (hc : C5 p), _ := fun p hc =>
    hP p.toBdryParamsEdge_BSTD1 hc.1 p.σ hc.2.1.1 hc.2.1.2.1 hc.2.1.2.2.1
      ((hc.2.1.2.2.2).trans_eq (dite_eq_left hc.1)) p.Λ hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1
      hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2
  choose w₀ hw₀ hP using hP5
  let W0 : BdryParamsLip_BSTD1 → ℝ := fun p => if hc : C5 p then w₀ p hc else 1
  -- `bd₀ (… w)`
  let C6 : BdryParamsVol_BSTD1 → Prop := fun p =>
    C5 p.toBdryParamsLip_BSTD1 ∧
    (0 < p.w ∧ p.w < W0 p.toBdryParamsLip_BSTD1 ∧ p.w < 4 * Real.pi / 3)
  have hP6 : ∀ (p : BdryParamsVol_BSTD1) (hc : C6 p), _ := fun p hc =>
    hP p.toBdryParamsLip_BSTD1 hc.1 p.w hc.2.1 ((hc.2.2.1).trans_eq (dite_eq_left hc.1))
      hc.2.2.2
  choose bd₀ hbd₀ hP using hP6
  let BD : BdryParamsVol_BSTD1 → ℝ := fun p => if hc : C6 p then bd₀ p hc else 1
  -- `b₀ (… b σs vs)`
  let C7 : BdryParamsSlim_BSTD1 → Prop := fun p =>
    C6 p.toBdryParamsVol_BSTD1 ∧
    (0 < p.b ∧ p.b < p.s / 100000 ∧ p.b < BC p.toBdryParamsScale_BSTD1 ∧
      p.b < B1 p.toBdryParamsEdge_BSTD1 ∧ 100 * p.Δ < p.b⁻¹ ∧ p.b < BD p.toBdryParamsVol_BSTD1) ∧
    (0 < p.σs ∧ p.σs ≤ 1 / 100 ∧ 0 < p.vs)
  have hP7 : ∀ (p : BdryParamsSlim_BSTD1) (hc : C7 p), _ := fun p hc =>
    hP p.toBdryParamsVol_BSTD1 hc.1 p.b hc.2.1.1 hc.2.1.2.1
      ((hc.2.1.2.2.1).trans_eq (dite_eq_left hc.1.1.1.1))
      ((hc.2.1.2.2.2.1).trans_eq (dite_eq_left hc.1.1.1)) hc.2.1.2.2.2.2.1
      ((hc.2.1.2.2.2.2.2).trans_eq (dite_eq_left hc.1)) p.σs p.vs hc.2.2.1 hc.2.2.2.1
      hc.2.2.2.2
  choose b₀ hb₀ hP using hP7
  let BZ : BdryParamsSlim_BSTD1 → ℝ := fun p => if hc : C7 p then b₀ p hc else 1
  -- `εr, δ', Λz (… β ζ cap)`
  let C8 : BdryParamsZero_BSTD1 → Prop := fun p =>
    C7 p.toBdryParamsSlim_BSTD1 ∧
    (p.β 2 = p.β₂ ∧ 0 < p.β 1 ∧ p.β 1 < BZ p.toBdryParamsSlim_BSTD1 ∧ p.β 1 < 1 ∧
      p.β 3 ≤ threeSplittingExclusionThreshold.{0, 0}) ∧
    (p.β 1 < p.ζ ∧ p.ζ < 1 ∧ 0 < p.cap)
  have hP8 : ∀ (p : BdryParamsZero_BSTD1) (hc : C8 p), _ := fun p hc =>
    hP p.toBdryParamsSlim_BSTD1 hc.1 p.β hc.2.1.1 hc.2.1.2.1
      ((hc.2.1.2.2.1).trans_eq (dite_eq_left hc.1)) hc.2.1.2.2.2.1 hc.2.1.2.2.2.2 p.ζ p.cap
      hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  choose εr δ' Λ' hεr hεr4 hεrcap hδ' hΛ' hP using hP8
  let ER : BdryParamsZero_BSTD1 → ℝ := fun p =>
    if hc : C8 p then εr p hc else if 0 < p.cap then min (1 / 8) (p.cap / 2) else 1 / 8
  let DP : BdryParamsZero_BSTD1 → ℝ := fun p => if hc : C8 p then δ' p hc else 1
  let LZ : BdryParamsZero_BSTD1 → ℝ := fun p => if hc : C8 p then Λ' p hc else 1
  -- the exported thresholds and their facts
  have hERpos : ∀ p, 0 < ER p := fun p => by
    refine dite_mem_BSTD1 (fun x => 0 < x) (fun hc => hεr p hc) ?_
    split_ifs with h
    · exact lt_min (by norm_num) (half_pos h)
    · norm_num
  have hERlt : ∀ p, ER p < 1 / 4 := fun p => by
    refine dite_mem_BSTD1 (fun x => x < 1 / 4) (fun hc => hεr4 p hc) ?_
    split_ifs
    · exact (min_le_left _ _).trans_lt (by norm_num)
    · norm_num
  have hERcap : ∀ p : BdryParamsZero_BSTD1, 0 < p.cap → ER p < p.cap := fun p hcap => by
    refine dite_mem_BSTD1 (fun x => x < p.cap) (fun hc => hεrcap p hc) ?_
    show (if 0 < p.cap then min (1 / 8) (p.cap / 2) else 1 / 8) < p.cap
    rw [ite_eq_left hcap]
    exact (min_le_right _ _).trans_lt (half_lt_self hcap)
  refine ⟨⟨δStar, a₂, B0, S0, D0, T0, BC, A0, B1, W0, BD, BZ, ER, DP, LZ, hδStar, ha₂,
    fun γ => dite_mem_BSTD1 (fun x => 0 < x) (hβ₀ γ) ha₂,
    fun γ => dite_mem_BSTD1 (fun x => x ≤ a₂) (hβ₀a γ) le_rfl,
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (hσ₀ p) one_pos,
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (hΔ₀ p) one_pos,
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (hτ₀ p) one_pos,
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (hbc₀ p) one_pos,
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (ha₀ p) one_pos,
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (hb₁ p) one_pos,
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (hw₀ p) one_pos,
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (hbd₀ p) one_pos,
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (hb₀ p) one_pos,
    hERpos, hERlt, hERcap,
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (hδ' p) one_pos,
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (hΛ' p) one_pos⟩, fun E S => ?_⟩
  -- the producer's conditions at `E`, stage by stage
  have hc1 : C1 E.γ := ⟨E.γ_pos, E.γ_lt⟩
  have hc2 : C2 E.toBdryParamsCollar_BSTD1 := ⟨hc1, E.βc_pos, E.βc_lt, E.γc_pos, E.γc_lt⟩
  have hc3 : C3 E.toBdryParamsScale_BSTD1 := ⟨hc2, E.β₂_pos, E.β₂_le, E.β₂_lt, E.Δ_gt, E.Δ_ge⟩
  have hc4 : C4 E.toBdryParamsEdge_BSTD1 :=
    ⟨hc3, ⟨E.σc_pos, E.σc_le, E.σc_lt, E.ε_pos, E.ε_lt, E.μ_pos, E.μ_le, E.τ_pos, E.τ_le,
      E.τ_sqrt, E.ε_le8, E.μ_le8⟩,
      ⟨E.s_pos, E.s_lt, E.s_lt_b', E.s_lt_s', E.b'_lt, E.s'_lt, E.b'_lt_τ, E.s'_lt_τ⟩⟩
  have hc5 : C5 E.toBdryParamsLip_BSTD1 :=
    ⟨hc4, ⟨E.σ_pos, E.σ_le_a₂, E.σ_le_thr, E.σ_le_a₀⟩,
      ⟨E.Λ_pos, E.Λ_c1, E.Λ_c2, E.Λ_c3, E.budget, E.Λ_c5, E.Λ_c6⟩⟩
  have hc6 : C6 E.toBdryParamsVol_BSTD1 := ⟨hc5, E.w_pos, E.w_lt, E.w_lt_pi⟩
  have hc7 : C7 E.toBdryParamsSlim_BSTD1 :=
    ⟨hc6, ⟨E.b_pos, E.b_lt_s, E.b_lt_bc₀, E.b_lt_b₁, E.b_inv, E.b_lt_bd₀⟩,
      ⟨E.σs_pos, E.σs_le, E.vs_pos⟩⟩
  have hc8 : C8 E.toBdryParamsZero_BSTD1 :=
    ⟨hc7, ⟨E.β_two, E.β₁_pos, E.β₁_lt_b₀, E.β₁_lt, E.β_three⟩, ⟨E.β₁_lt_ζ, E.ζ_lt, E.cap_pos⟩⟩
  have eLZ : LZ E.toBdryParamsZero_BSTD1 = Λ' E.toBdryParamsZero_BSTD1 hc8 := dite_eq_left hc8
  have hT : 20 * Λ' E.toBdryParamsZero_BSTD1 hc8 ≤ E.T := by
    rw [← eLZ]
    exact E.T_ge
  obtain ⟨V, hTV, δ, hδ, hδδ', hev⟩ := hP E.toBdryParamsZero_BSTD1 hc8 E.T E.T_pos hT E.e E.e_pos
    E.e_lt S.δ₀ S.δ₀_pos S.δ₀_le S.W S.g S.B S.coll S.der
  have eDP : E.δ' = δ' E.toBdryParamsZero_BSTD1 hc8 := dite_eq_left hc8
  have eER : E.εr = εr E.toBdryParamsZero_BSTD1 hc8 := dite_eq_left hc8
  have eΛz : E.Λz = Λ' E.toBdryParamsZero_BSTD1 hc8 := dite_eq_left hc8
  refine ⟨V, hTV, δ, hδ, hδδ'.trans_eq eDP.symm, fun Lmax hLmax βd εN hβd hεN => ?_⟩
  rw [eER, eΛz]
  exact hev Lmax hLmax βd εN hβd hεN

/-- **The exported boundary thresholds** (top-level Skolem data of the boundary producer). -/
def bdryThresholds_BSTD1 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    BoundaryProducerThresholds_BSTD1 :=
  Classical.choose (exists_bdryThresholds_BSTD1 K hK A hA)

/-- **The early choices of the boundary sequence assignment** (D61-11's `BoundaryEarlyChoices K A`):
the early choices over the exported thresholds. -/
abbrev BoundaryEarlyChoices_BSTD1 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) : Type :=
  BoundaryEarlyOver_BSTD1 (bdryThresholds_BSTD1 K hK A hA)

/-- **Every legal early choice has the producer's continuation** (D61-11 D1: `early` is an input):
for every early choice `E` and every standing sequence `S` with `δ₀ ≤ δStar` (the exported
`δStar`), the outputs `V ≥ T`, `δ < δ'`, then for all `Lmax, βd, εN > 0` T3B-BFRZ's per-member
conclusion on a tail, at exactly `E`'s parameters, the ratio `δ_{n+1}` and the index `n + 1`. -/
theorem bdry_early_continuation_BSTD1 {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w}
    (E : BoundaryEarlyChoices_BSTD1 K hK A hA)
    (S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar) :
    ∃ V : ℝ, E.T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < E.δ' ∧ ∀ Lmax : ℝ, 0 < Lmax →
      ∀ βd εN : ℝ, 0 < βd → 0 < εN → ∀ᶠ n in atTop,
        BoundaryPacketsOutBFRZ_BSTD1 (S.W n) (S.g n) K A (boundaryCounterexampleRatio S.δ₀ (n + 1))
          (S.B n) ((n + 1 : ℕ) : ℝ) E.Λ E.w E.β E.Δ E.σs E.σc E.μ E.b E.s E.b' E.s' E.ε E.γc E.βc
          Lmax E.τ E.γ δ E.εr E.e E.T V E.vs E.ζ E.Λz βd εN :=
  Classical.choose_spec (exists_bdryThresholds_BSTD1 K hK A hA) E S

end DifferentialGeometry.Geometry.Collapse
