import DifferentialGeometry.Geometry.Collapse.BoundaryEarlyOverXBABSTD2

/-!
# The assignment on the combined early choice (lane BSTD2, G2)

One register, one tail, the joint (BA) output.

On the combined early choice
`E : BoundaryEarlyOverXBA_BSTD2 (bdryThresholdsBA_BSTD2 K hK A hA θ ν) θ ν χ` (module G):

* `BoundaryRegisterOverXBA_BSTD2 E V`: the extended register over `E` (as an extended early choice)
  with the joint producer's late conditions `L_max ≥ σC⁻¹, σE⁻¹, σS⁻¹` and `ε_N ≤ θ²/(4·10⁷)`.
* `BoundaryMemberOutputXBA_BSTD2 S n R`: the extended member output AND the joint per-member
  conclusion at the ratio `δ_{n+1}`, the index `n + 1` and the error `θ` (text v3 H1's `hm`,
  verbatim); `.supply_BSTD2` (for every orientation ONE `BoundarySupply` at the member's data, the
  index `n + 1` and the (BA) error `θ`: text v3 H1's `Sup`), `.premises_BSTD2` (every numerical
  premise of the boundary rows at the supply index `n + 1`).
* `exists_boundarySequenceAssignmentXBA_req_BSTD2`, `exists_boundarySequenceAssignmentXBA_BSTD2`:
  for every combined early choice and every standing sequence with `δ₀ ≤ δStar`, the joint
  producer's `V ≥ T`, then a register over `(E, V)` (meeting late requests), then `n₀` with the
  combined member output on every member `n ≥ n₀`. One early choice, one register, one tail.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **The register of the combined early choice** over `(E, V)`: the extended register over `E`
(read as an extended early choice) with the joint producer's late conditions, read after `V`:
`L_max ≥ σC⁻¹, σE⁻¹, σS⁻¹` (lower) and `ε_N ≤ θ²/(4·10⁷)` (upper). -/
structure BoundaryRegisterOverXBA_BSTD2 {Θ : BoundaryProducerThresholdsBA_BSTD2} {θ ν : ℝ}
    {χ : BoundaryChainThresholds_BSTD2} (E : BoundaryEarlyOverXBA_BSTD2 Θ θ ν χ) (V : ℝ) extends
    BoundaryRegisterOverX_BSTD2 E.toBoundaryEarlyOverX_BSTD2 V where
  Lmax_ge_σC : Θ.σC⁻¹ ≤ Lmax
  Lmax_ge_σE : (Θ.SE E.toBdryParamsScale_BSTD1)⁻¹ ≤ Lmax
  Lmax_ge_σS : (Θ.SS E.toBdryParamsScale_BSTD1)⁻¹ ≤ Lmax
  εN_le_θ : εN ≤ θ ^ 2 / 40000000

/-- **The output of one member on the combined register**: the extended member output and the
joint (BA) per-member conclusion at the ratio `δ_{n+1}`, the index `n + 1`, exactly the register's
parameters and the (BA) error `θ` (text v3 H1's hypothesis `hm`, verbatim). -/
def BoundaryMemberOutputXBA_BSTD2 {Θ : BoundaryProducerThresholdsBA_BSTD2} {θ ν : ℝ}
    {χ : BoundaryChainThresholds_BSTD2} {K : ℕ} {A : ℝ → ℝ}
    {E : BoundaryEarlyOverXBA_BSTD2 Θ θ ν χ} {V : ℝ}
    (S : BoundaryStandingSequence_BSTD1 K A Θ.δStar) (n : ℕ)
    (R : BoundaryRegisterOverXBA_BSTD2 E V) : Prop :=
  BoundaryMemberOutputX_BSTD2 S n R.toBoundaryRegisterOverX_BSTD2 ∧
    BoundaryPacketsOutBA_BSTD2 (S.W n) (S.g n) K A (boundaryCounterexampleRatio S.δ₀ (n + 1))
      (S.B n) ((n + 1 : ℕ) : ℝ) E.Λ E.w E.β E.Δ E.σs E.σc E.μ E.b E.s E.b' E.s' E.ε E.γc E.βc
      R.Lmax E.τ E.γ R.δlocal E.εr E.e E.T V E.vs E.ζ E.Λz R.βd R.εN θ

section Output

variable {Θ : BoundaryProducerThresholdsBA_BSTD2} {θ ν : ℝ} {χ : BoundaryChainThresholds_BSTD2}
  {K : ℕ} {A : ℝ → ℝ} {E : BoundaryEarlyOverXBA_BSTD2 Θ θ ν χ} {V : ℝ}
  {S : BoundaryStandingSequence_BSTD1 K A Θ.δStar} {n : ℕ} {R : BoundaryRegisterOverXBA_BSTD2 E V}

/-- **ONE `BoundarySupply` per orientation at a tail member** (with BCG02's joint (BA)
certificates at the error `θ`): the member's carrier, metric, ratio `δ_{n+1}`, boundary and index
`n + 1`, exactly the register's parameters (text v3 H1's `Sup`). -/
theorem BoundaryMemberOutputXBA_BSTD2.supply_BSTD2 (h : BoundaryMemberOutputXBA_BSTD2 S n R)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) ((S.W n).pieceInterior ⊤) 3) :
    Nonempty (BoundarySupply K A E.β R.βd R.εN E.Λ E.w E.Δ E.σs E.σc E.μ E.b E.s E.b' E.s' E.ε
      E.γc E.βc R.Lmax E.τ E.γ R.δlocal E.εr E.e E.T V E.vs E.ζ E.Λz θ (S.W n) (S.g n)
      (boundaryCounterexampleRatio S.δ₀ (n + 1)) (n + 1) (S.B n) oM) :=
  h.2.supply_BSTD2 oM

/-- **Every numerical premise of the boundary rows at a tail member** (at its supply index
`n + 1`; lane BSTD2 G1's block on the extended register). -/
theorem BoundaryMemberOutputXBA_BSTD2.premises_BSTD2 (h : BoundaryMemberOutputXBA_BSTD2 S n R) :
    BoundaryRegisterPremisesX_BSTD2 E.toBoundaryEarlyOverX_BSTD2 R.toBoundaryRegisterOverX_BSTD2
      (n + 1) :=
  h.1.premises_BSTD2

end Output

/-! ### The assignment -/

/-- **ONE per-sequence boundary assignment on the combined register, meeting late requests**: for
`0 < θ < 1`, `0 < ν < 10⁻⁶`, every combined early choice `E` over the exported joint thresholds,
every standing sequence `S` with `δ₀ ≤ δStar` and every late request record `Rq`, the joint
producer's `V ≥ T`, then a combined register over `(E, V)` (`δ_local` the producer's cone error,
`L_max ≥ Rq`, `β_∂ ≤ Rq`, `ε_N ≤ Rq`, `H_∂ ≥ Rq`, `r_∂ ≤ Rq`, each read in the D61-11 order), then
`n₀` with the combined member output on every member `n ≥ n₀`. -/
theorem exists_boundarySequenceAssignmentXBA_req_BSTD2 {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {θ ν : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1 / 1000000) {χ : BoundaryChainThresholds_BSTD2}
    (E : BoundaryEarlyOverXBA_BSTD2 (bdryThresholdsBA_BSTD2 K hK A hA θ ν) θ ν χ)
    (S : BoundaryStandingSequence_BSTD1 K A (bdryThresholdsBA_BSTD2 K hK A hA θ ν).δStar)
    (Rq : BoundaryLateRequests_BSTD1) :
    ∃ V : ℝ, E.T ≤ V ∧ ∃ R : BoundaryRegisterOverXBA_BSTD2 E V,
      Rq.Lmax V R.δlocal ≤ R.Lmax ∧ R.βd ≤ Rq.βd V R.δlocal R.Lmax ∧
      R.εN ≤ Rq.εN V R.δlocal R.Lmax ∧ Rq.H V R.δlocal R.Lmax R.βd R.εN ≤ R.Hd ∧
      R.rd ≤ Rq.rd V R.δlocal R.Lmax R.βd R.εN R.Hd ∧
      ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → BoundaryMemberOutputXBA_BSTD2 S n R := by
  obtain ⟨V, hTV, δ, hδ, hδδ', hev⟩ :=
    bdry_early_continuationBA_BSTD2 hθ hθ1 hν hν1 E.toBoundaryEarlyOverBA_BSTD2 S
  obtain ⟨Lb, hLb⟩ : ∃ Lb : ℝ, Lb = max (bdryLmaxX_BSTD2 E.toBoundaryEarlyOverX_BSTD2)
      (max (bdryThresholdsBA_BSTD2 K hK A hA θ ν).σC⁻¹
        (max ((bdryThresholdsBA_BSTD2 K hK A hA θ ν).SE E.toBdryParamsScale_BSTD1)⁻¹
          ((bdryThresholdsBA_BSTD2 K hK A hA θ ν).SS E.toBdryParamsScale_BSTD1)⁻¹)) :=
    ⟨_, rfl⟩
  have hθ2 : 0 < θ ^ 2 / 40000000 := by positivity
  let Rq' : BoundaryLateRequests_BSTD1 :=
    { Rq with
      Lmax := fun V δ => max (Rq.Lmax V δ) Lb
      εN := fun V δ L => min (Rq.εN V δ L) (θ ^ 2 / 40000000)
      εN_pos := fun V δ L => lt_min (Rq.εN_pos V δ L) hθ2 }
  obtain ⟨R, hRδ, h1, h2, h3, h4, h5⟩ :=
    exists_boundaryRegisterOver_BSTD1 E.toBoundaryEarlyOver_BSTD1 V δ hδ hδδ' Rq'
  subst hRδ
  have h1' : max (Rq.Lmax V R.δlocal) Lb ≤ R.Lmax := h1
  have h3' : R.εN = min (Rq.εN V R.δlocal R.Lmax) (θ ^ 2 / 40000000) := h3
  have hL : Lb ≤ R.Lmax := (le_max_right _ _).trans h1'
  rw [hLb] at hL
  have hσC : (bdryThresholdsBA_BSTD2 K hK A hA θ ν).σC⁻¹ ≤ R.Lmax :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hσE : ((bdryThresholdsBA_BSTD2 K hK A hA θ ν).SE E.toBdryParamsScale_BSTD1)⁻¹ ≤ R.Lmax :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hL
  have hσS : ((bdryThresholdsBA_BSTD2 K hK A hA θ ν).SS E.toBdryParamsScale_BSTD1)⁻¹ ≤ R.Lmax :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hL
  have hεN : R.εN ≤ θ ^ 2 / 40000000 := h3'.trans_le (min_le_right _ _)
  let RB : BoundaryRegisterOverXBA_BSTD2 E V :=
    { toBoundaryRegisterOverX_BSTD2 :=
        BoundaryRegisterOverX_BSTD2.ofRegister_BSTD2 E.toBoundaryEarlyOverX_BSTD2 R hTV
          ((le_max_left _ _).trans hL)
      Lmax_ge_σC := hσC
      Lmax_ge_σE := hσE
      Lmax_ge_σS := hσS
      εN_le_θ := hεN }
  have hw' : 0 < E.w / (2 * (1 + 2 * E.Λ⁻¹) ^ 3) := by
    have := E.w_pos
    have := E.Λ_pos
    positivity
  have hX : 0 < E.w / (2 * (1 + 2 * E.Λ⁻¹) ^ 3) * min (1 / 2) (R.rd / 4) ^ 2 := by
    have : 0 < min (1 / 2 : ℝ) (R.rd / 4) := lt_min (by norm_num) (by linarith [R.rd_pos])
    positivity
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp ((hev R.Lmax R.Lmax_pos hσC hσE hσS R.βd R.εN
    R.βd_pos R.εN_pos hεN).and (eventually_bdry_ratio_sq_lt_BSTG S.δ₀_pos hX))
  refine ⟨V, hTV, RB, (le_max_left _ _).trans h1', h2, h3'.trans_le (min_le_left _ _), h4, h5,
    max n₀ ⌈1140 * E.Δ / 35⌉₊, fun n hn => ?_⟩
  obtain ⟨hBA, hprem⟩ := hn₀ n ((le_max_left _ _).trans hn)
  have hidx : 1140 * E.Δ ≤ 35 * ((n + 1 : ℕ) : ℝ) := by
    have h1'' : 1140 * E.Δ / 35 ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
    have h2'' : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    linarith
  exact ⟨⟨⟨hBA.toBFRZ_BSTD2, hprem⟩, hidx⟩, hBA⟩

/-- **ONE per-sequence boundary assignment on the combined register** (G2): for `0 < θ < 1`,
`0 < ν < 10⁻⁶`, every combined early choice and every standing sequence with `δ₀ ≤ δStar`, there
are `V`, a combined register `R` over `(E, V)` and `n₀` such that every member `n ≥ n₀` has the
combined output. -/
theorem exists_boundarySequenceAssignmentXBA_BSTD2 {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {θ ν : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1 / 1000000) {χ : BoundaryChainThresholds_BSTD2}
    (E : BoundaryEarlyOverXBA_BSTD2 (bdryThresholdsBA_BSTD2 K hK A hA θ ν) θ ν χ)
    (S : BoundaryStandingSequence_BSTD1 K A (bdryThresholdsBA_BSTD2 K hK A hA θ ν).δStar) :
    ∃ V : ℝ, ∃ R : BoundaryRegisterOverXBA_BSTD2 E V, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      BoundaryMemberOutputXBA_BSTD2 S n R := by
  obtain ⟨V, -, R, -, -, -, -, -, hR⟩ :=
    exists_boundarySequenceAssignmentXBA_req_BSTD2 hθ hθ1 hν hν1 E S
      BoundaryLateRequests_BSTD1.trivial
  exact ⟨V, R, hR⟩

end DifferentialGeometry.Geometry.Collapse
