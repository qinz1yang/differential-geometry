import DifferentialGeometry.Geometry.Collapse.BoundarySequenceAssignmentXBABSTD2
import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterExtConsumersBSTD2

/-!
# The stored CHOICE (lane BSTD2, G2)

One legal choice, one (BA) error, one early choice for the whole tail.

Review 69, D69-3: H1 must READ a legal CHOICE stored in the early choice (one choice for the whole
tail), never quantify chain constants. Lane BSTD2's order finding: the joint (BA) producer fixes the
(BA) error `θ` and `ν_BA` BEFORE its thresholds, so `θ` is CHOICE-level. The order of the boundary
route is `K, A ≺` (the choice's own early constants) `≺` CHOICE `≺ ν ≺` CHI first thresholds
`≺ θ, ν_BA ≺` joint thresholds `Θ_BA(K, A, θ, ν_BA) ≺ γ … e ≺ S ≺ V δ ≺ L_max β_∂ ε_N H_∂ r_∂ ≺ n₀`.

* `BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf` (text v3 §H's `BoundaryEarlyWithChainChoice`,
  generic in the choice type `Ch` with its graph errors `egOf : Ch → Fin 3 → ℝ`; at
  `Ch = BoundaryChainChoice_BIFc Kj bcut bder κ cadj`, `egOf = (·.eg)` it is that structure): the
  stored `choice`, the CHI record `χ` with the choice's `eg`, the (BA) error `0 < θ < 1/100`,
  `θ ≤ ϑ₀`, `0 < ν_BA < 10⁻⁶`, and the COMBINED early choice over `Θ_BA(K, A, θ, ν_BA)` and `χ`
  (module G) whose boundary layer has `ϑ_min = θ` (BCG05's / A2's `θ` and the (BA) error: ONE
  number).
* `exists_boundaryEarlyWithChoice_of_BSTD2` / `exists_boundaryEarlyWithChoice_BSTD2`: the
  producer — for EVERY choice `c` and every CHI record `χ` with `χ.eg = egOf c` (and every legal
  `θ, ν_BA`, any further staged requests) the stored-choice early choice exists with exactly these.
* `exists_boundarySequenceAssignmentWC_req_BSTD2`, `exists_boundarySequenceAssignmentWC_BSTD2`: ONE
  assignment `EW ↦ V ↦ R ↦ n₀` with the combined member output on the tail.
* Consumer `exists_boundarySequenceAssignmentWC_supply_BSTD2`: along that ONE assignment every tail
  member `m` carries text v3 H1's hypothesis `hm` verbatim, H1's `Sup` (for every orientation ONE
  `BoundarySupply` with the (BA) certificates at `EW.θ`, index `m + 1`), every numerical premise of
  the boundary rows at `m + 1`, and `EW.θ < 1/100`, `ϑ_min = EW.θ`.
* Inhabitant at the closed CHI record: `nonempty_boundaryEarlyWithChoice_closedChi_BSTD2`.
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

/-- **The early choice with the stored CHOICE** (D69-3; text v3 §H's
`BoundaryEarlyWithChainChoice`, generic in the choice type `Ch` with graph errors `egOf`): ONE legal
choice for the whole tail, the CHI record `χ` with the choice's `eg`, the (BA) error `θ` and
`ν_BA` fixed BEFORE the joint thresholds, and the combined early choice over
`Θ_BA(K, A, θ, ν_BA)` and `χ` with boundary layer `ϑ_min = θ`. -/
structure BoundaryEarlyWithChoice_BSTD2 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) {Ch : Type}
    (egOf : Ch → Fin 3 → ℝ) : Type where
  choice : Ch
  χ : BoundaryChainThresholds_BSTD2
  eg_eq : χ.eg = egOf choice
  θ : ℝ
  θ_pos : 0 < θ
  θ_lt : θ < 1 / 100
  θ_le : θ ≤ χ.ϑ₀
  νBA : ℝ
  νBA_pos : 0 < νBA
  νBA_lt : νBA < 1 / 1000000
  early : BoundaryEarlyOverXBA_BSTD2 (bdryThresholdsBA_BSTD2 K hK A hA θ νBA) θ νBA χ
  ϑmin_eq : early.ϑmin = θ

/-! ### The producer -/

/-- **The stored-choice early choice exists for every choice, CHI record and legal (BA) error**
(with any further staged requests `Rq`): for every choice `c`, every CHI record `χ` with
`χ.eg = egOf c`, every `0 < θ < 1/100` with `θ ≤ ϑ₀` and every `0 < ν_BA < 10⁻⁶` with
`3ν_BA ≤ thr`, there is a stored-choice early choice with exactly these, whose parameters are those
of ONE staged prefix meeting `Rq`. -/
theorem exists_boundaryEarlyWithChoice_of_BSTD2 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) {Ch : Type}
    (egOf : Ch → Fin 3 → ℝ) (c : Ch) (χ : BoundaryChainThresholds_BSTD2) (heg : χ.eg = egOf c)
    {θ νBA : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1 / 100) (hθχ : θ ≤ χ.ϑ₀) (hν : 0 < νBA)
    (hν1 : νBA < 1 / 1000000) (hν3 : 3 * νBA ≤ threeSplittingExclusionThreshold.{0, 0})
    (Rq : C14StagedRequestsSTG) :
    ∃ EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf, EW.choice = c ∧ EW.χ = χ ∧ EW.θ = θ ∧
      EW.νBA = νBA ∧ ∃ P : C14PreFinal, Rq.toC14.Meets P ∧
        EW.early.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1 := by
  obtain ⟨E, hEϑ, P, hM, hEP⟩ := exists_boundaryEarlyOverXBA_staged_BSTD2
    (bdryThresholdsBA_BSTD2 K hK A hA θ νBA) hθ hθ1 hν3 χ hθχ Rq
  exact ⟨⟨c, χ, heg, θ, hθ, hθ1, hθχ, νBA, hν, hν1, E, hEϑ⟩, rfl, rfl, rfl, rfl, P, hM, hEP⟩

/-- **The stored-choice early choice exists for every choice and every CHI record with the
choice's graph errors** (`θ = min(1/200, ϑ₀)`, `ν_BA = min(ν, 1/(2·10⁶))`). -/
theorem exists_boundaryEarlyWithChoice_BSTD2 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) {Ch : Type}
    (egOf : Ch → Fin 3 → ℝ) (c : Ch) (χ : BoundaryChainThresholds_BSTD2) (heg : χ.eg = egOf c) :
    ∃ EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf, EW.choice = c ∧ EW.χ = χ := by
  have hν3 : 3 * min χ.ν (1 / 2000000) ≤ threeSplittingExclusionThreshold.{0, 0} := by
    linarith [χ.three_ν_le, min_le_left χ.ν (1 / 2000000)]
  obtain ⟨EW, hc, hχ, -, -, -⟩ := exists_boundaryEarlyWithChoice_of_BSTD2 K hK A hA egOf c χ heg
    (θ := min (1 / 200) χ.ϑ₀) (νBA := min χ.ν (1 / 2000000)) (lt_min (by norm_num) χ.ϑ₀_pos)
    ((min_le_left _ _).trans_lt (by norm_num)) (min_le_right _ _)
    (lt_min χ.ν_pos (by norm_num)) ((min_le_right _ _).trans_lt (by norm_num)) hν3
    C14StagedRequestsSTG.trivial
  exact ⟨EW, hc, hχ⟩

/-! ### The assignment on the stored CHOICE -/

/-- **ONE assignment on the stored CHOICE, meeting late requests**: for every stored-choice early
choice `EW` and every standing sequence `Sq` with `δ₀ ≤ δStar(Θ_BA(K, A, EW.θ, EW.ν_BA))`, the
joint producer's `V ≥ T`, then ONE combined register over `(EW.early, V)` meeting `Rq`, then `n₀`
with the combined member output on every member `m ≥ n₀`. -/
theorem exists_boundarySequenceAssignmentWC_req_BSTD2 {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
    {egOf : Ch → Fin 3 → ℝ} (EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf)
    (Sq : BoundaryStandingSequence_BSTD1 K A (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar)
    (Rq : BoundaryLateRequests_BSTD1) :
    ∃ V : ℝ, EW.early.T ≤ V ∧ ∃ R : BoundaryRegisterOverXBA_BSTD2 EW.early V,
      Rq.Lmax V R.δlocal ≤ R.Lmax ∧ R.βd ≤ Rq.βd V R.δlocal R.Lmax ∧
      R.εN ≤ Rq.εN V R.δlocal R.Lmax ∧ Rq.H V R.δlocal R.Lmax R.βd R.εN ≤ R.Hd ∧
      R.rd ≤ Rq.rd V R.δlocal R.Lmax R.βd R.εN R.Hd ∧
      ∃ n₀ : ℕ, ∀ m, n₀ ≤ m → BoundaryMemberOutputXBA_BSTD2 Sq m R :=
  exists_boundarySequenceAssignmentXBA_req_BSTD2 EW.θ_pos (EW.θ_lt.trans (by norm_num))
    EW.νBA_pos EW.νBA_lt EW.early Sq Rq

/-- **ONE assignment on the stored CHOICE** (text v3 §H's `exists_boundarySequenceAssignmentWC`):
for every stored-choice early choice `EW` and every standing sequence `Sq`, there are `V`, ONE
combined register `R` over `(EW.early, V)` and `n₀` with the combined member output on every
member `m ≥ n₀` (one choice, one (BA) error, one register for the whole tail, by type). -/
theorem exists_boundarySequenceAssignmentWC_BSTD2 {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
    {egOf : Ch → Fin 3 → ℝ} (EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf)
    (Sq : BoundaryStandingSequence_BSTD1 K A (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar) :
    ∃ V : ℝ, ∃ R : BoundaryRegisterOverXBA_BSTD2 EW.early V, ∃ n₀ : ℕ, ∀ m, n₀ ≤ m →
      BoundaryMemberOutputXBA_BSTD2 Sq m R :=
  exists_boundarySequenceAssignmentXBA_BSTD2 EW.θ_pos (EW.θ_lt.trans (by norm_num)) EW.νBA_pos
    EW.νBA_lt EW.early Sq

/-! ### Consumers -/

/-- **Consumer: text v3 H1's inputs along the ONE assignment** — for every stored-choice early
choice `EW` and every standing sequence `Sq` there are `V`, ONE combined register `R` and `n₀` such
that every tail member `m` carries H1's hypothesis `hm` (verbatim: the extended member output and
the joint per-member conclusion at `δ_{m+1}`, index `m + 1`, error `EW.θ`), H1's supply (for every
orientation ONE `BoundarySupply` with the (BA) certificates at `EW.θ` and index `m + 1`), every
numerical premise of the boundary rows at the supply index `m + 1`, and BCG05's `θ < 1/100` with
`ϑ_min = θ` (the layer read by `r_∂` and the (BA) error are one number). -/
theorem exists_boundarySequenceAssignmentWC_supply_BSTD2 {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
    {egOf : Ch → Fin 3 → ℝ} (EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf)
    (Sq : BoundaryStandingSequence_BSTD1 K A (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar) :
    ∃ V : ℝ, ∃ R : BoundaryRegisterOverXBA_BSTD2 EW.early V, ∃ n₀ : ℕ, ∀ m, n₀ ≤ m →
      (BoundaryMemberOutputX_BSTD2 Sq m R.toBoundaryRegisterOverX_BSTD2 ∧
        BoundaryPacketsOutBA_BSTD2 (Sq.W m) (Sq.g m) K A (boundaryCounterexampleRatio Sq.δ₀ (m + 1))
          (Sq.B m) ((m + 1 : ℕ) : ℝ) EW.early.Λ EW.early.w EW.early.β EW.early.Δ EW.early.σs
          EW.early.σc EW.early.μ EW.early.b EW.early.s EW.early.b' EW.early.s' EW.early.ε
          EW.early.γc EW.early.βc R.Lmax EW.early.τ EW.early.γ R.δlocal EW.early.εr EW.early.e
          EW.early.T V EW.early.vs EW.early.ζ EW.early.Λz R.βd R.εN EW.θ) ∧
      (∀ oM : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W m).pieceInterior ⊤) 3,
        Nonempty (BoundarySupply K A EW.early.β R.βd R.εN EW.early.Λ EW.early.w EW.early.Δ
          EW.early.σs EW.early.σc EW.early.μ EW.early.b EW.early.s EW.early.b' EW.early.s'
          EW.early.ε EW.early.γc EW.early.βc R.Lmax EW.early.τ EW.early.γ R.δlocal EW.early.εr
          EW.early.e EW.early.T V EW.early.vs EW.early.ζ EW.early.Λz EW.θ (Sq.W m) (Sq.g m)
          (boundaryCounterexampleRatio Sq.δ₀ (m + 1)) (m + 1) (Sq.B m) oM)) ∧
      BoundaryRegisterPremisesX_BSTD2 EW.early.toBoundaryEarlyOverX_BSTD2
        R.toBoundaryRegisterOverX_BSTD2 (m + 1) ∧
      EW.θ < 1 / 100 ∧ EW.early.ϑmin = EW.θ := by
  obtain ⟨V, R, n₀, hR⟩ := exists_boundarySequenceAssignmentWC_BSTD2 EW Sq
  exact ⟨V, R, n₀, fun m hm => ⟨hR m hm, fun oM => (hR m hm).supply_BSTD2 oM,
    (hR m hm).premises_BSTD2, EW.θ_lt, EW.ϑmin_eq⟩⟩

/-- **Inhabitant at the closed CHI record**: for every jet order `Kj` and `c_adj > 0`, the CHI
record `χ` produced by `exists_chainThresholds_chainE_BSTD2` (GAF01's CHOICE at `ν = thr/3`,
`gaf02_chainE_row_GAF8`'s thresholds) is stored, with the choice `χ.eg`, in a stored-choice early
choice (the choice type here is the bare graph-error vector). -/
theorem nonempty_boundaryEarlyWithChoice_closedChi_BSTD2 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) (Kj : ℕ) {cadj : ℝ}
    (hcadj : 0 < cadj) :
    ∃ χ : BoundaryChainThresholds_BSTD2,
      ∃ EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA (fun e : Fin 3 → ℝ => e),
        EW.choice = χ.eg ∧ EW.χ = χ := by
  obtain ⟨-, -, -, -, -, χ, -, -⟩ := exists_chainThresholds_chainE_BSTD2 Kj hcadj
  obtain ⟨EW, hc, hχ⟩ :=
    exists_boundaryEarlyWithChoice_BSTD2 K hK A hA (fun e : Fin 3 → ℝ => e) χ.eg χ rfl
  exact ⟨χ, EW, hc, hχ⟩

end DifferentialGeometry.Geometry.Collapse
