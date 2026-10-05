import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14StagedSTG
import DifferentialGeometry.Geometry.Collapse.BoundaryPacketsOutBFRSeqIdx
import DifferentialGeometry.Geometry.Collapse.BoundaryRegister

/-!
# The boundary staged requests and ONE staged boundary assignment (lane BSTG)

Review 53 §6.2 / §8 (dispositions "Staged interface": a BOUNDARY staged adapter did not exist).
The index-corrected boundary producer T3B_IDX2 (`lc88_boundary_packets_BFR_BCG5_IDX2`; here through
its per-member form `lc88_boundary_packets_BFR_out_BQ_IDX4`, the same prefix and the same family)
has, after its first output `δStar`, literally the binder groups of the closed producer
(`a₂ | γ, β₀ | βc γc, σ₀ Δ₀ | β₂ Δ, τ₀ bc₀ | σc ε μ τ s b' s', a₀ b₁ | σ | Λ, w₀ | w, bd₀ | b |
σs vs, b₀ | β | ζ cap, εr δ' Λ' | T e`), so the closed admissible prefixes
`C14PreCirc … C14PreFinal` and the stage lemmas of the closed STG contract apply verbatim
(`β₂`'s request is read before `βc`, and `3βc ≤ β 2` is kept). After `e` the boundary producer
quantifies the sequence, outputs `V ≥ T` and `δ < δ'`, and takes `Lmax` and the cusp requests
`βd, εN` right before the tail.

* `C14StagedRequestsSTG.withBdryCaps_BSTG`: the boundary caps of the interior requests: `w`'s
  request is intersected with `ω₃/8` at the `w` stage (B:10445–10447, `w < w_cap = ω₃/4`; `w` is
  never re-chosen after `b`), `vs`'s request with `ϑ₃/8` (BCG02's value estimate needs the slim
  value error below `ϑ₃/4`, B:8887–8889; review 57 §3.4: the boundary PR14–PR17 block, `ϑ₃` an
  early boundary tolerance). `.meets_of_withBdryCaps_BSTG`.
* `C14BdryStagedRequestsBSTG`: an STG record for the interior requests and the boundary requests
  read AFTER `V` (the prefix `P` contains `β₁`): `βd, εN` (BR24's cusp quality and norm error,
  upper), `rd` (the physical scale `r∂`, upper, reading `βd, εN`) and `H` (the cusp test /
  Taylor length, LOWER). `.trivial`, `.inf`.
* `bdryβd_BSTG = min(Rq.βd, β₁/2)` (BR24: below `β₁`), `bdryεN_BSTG`, `bdryH_BSTG = max(1, Rq.H)`,
  `bdryRd_BSTG = min(Rq.rd, 1/(200 H∂))` (BRegPhysical's entry `1/(100H∂)`).
* `eventually_bdry_ratio_sq_lt_BSTG`, `bdry_premise_mono_BSTG`: the certificate premise
  `1000 δ_{n+1}² < w'·min(1/2, r/4)²` holds on a tail for a fixed `r > 0` and is monotone in `r`.
* `exists_bdry_staged_assignment_BSTG`: for every early tolerance record `t`, boundary tolerance
  `ϑ₃ > 0` and boundary request record `Rq`, ONE admissible prefix meeting `Rq`'s interior
  requests with `3βc ≤ β 2`, `w < ω₃/4`, `vs < ϑ₃/4`, such that on every boundary sequence (BBR03's
  ratios `δ_{n+1}`) with the outputs `V ≥ T`, `δ < δ'`, `Lmax = c14Lmax`, the cusp requests
  `βd < β₁`, `εN` and the physical data `r∂, H∂` (`100 H∂ r∂ < 1`), every late member satisfies the
  per-member conclusion `BoundaryPacketsOutBFR_BQ` of T3B_IDX2 at exactly these parameters AND the
  premise at `r∂` — ONE common tail on which every conditional certificate of the member (late `ρ`
  certificate, B3, B4 at lengths `≤ H∂`, B5) holds at every radius `≥ r∂`.

No `Δ > 100/β₂` together with `β₂⁻¹ > 10⁶Δ` is added (only the producer's `100/β₂ < Δ`), and
`r∂` is read only after `V` (no `1/r∂` in an early constant): review 53 §9's two forbidden
additions.
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

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-! ### The boundary caps of the interior requests -/

/-- **The boundary caps of the interior requests** (lane BSTG): `w`'s request (read at
`C14PreLip`) is intersected with `ω₃/8` (`w < w_cap = ω₃/4`, B:10445–10447) and `vs`'s request (read
at `C14PreSplit`) with `ϑ₃/8` (BCG02's slim value error `< ϑ₃/4`, B:8887–8889); every other
request unchanged. -/
def C14StagedRequestsSTG.withBdryCaps_BSTG (R : C14StagedRequestsSTG) (ϑ₃ : ℝ) (hϑ₃ : 0 < ϑ₃) :
    C14StagedRequestsSTG :=
  { R with
    w := fun p => min (R.w p) (boundaryVolumeCap / 2)
    w_pos := fun p => lt_min (R.w_pos p) (half_pos boundaryVolumeCap_pos)
    vs := fun p => min (R.vs p) (ϑ₃ / 8)
    vs_pos := fun p => lt_min (R.vs_pos p) (by positivity) }

/-- A prefix meeting the capped record meets the record, with `w ≤ ω₃/8` and `vs ≤ ϑ₃/8`. -/
theorem C14StagedRequestsSTG.meets_of_withBdryCaps_BSTG {R : C14StagedRequestsSTG} {ϑ₃ : ℝ}
    {hϑ₃ : 0 < ϑ₃} {P : C14PreFinal} (h : (R.withBdryCaps_BSTG ϑ₃ hϑ₃).toC14.Meets P) :
    R.toC14.Meets P ∧ P.w ≤ boundaryVolumeCap / 2 ∧ P.vs ≤ ϑ₃ / 8 :=
  ⟨⟨h.γ_le, h.γc_le, h.βc_le, h.β₂_le, h.Δ_ge, h.σc_le, h.ε_le, h.μ_le, h.τ_le, h.s_le, h.b'_le,
    h.s'_le, h.Λ_le, h.w_le.trans (min_le_left _ _), h.b_le, h.σs_le,
    h.vs_le.trans (min_le_left _ _), h.ζ_le, h.β₁_le, h.cap_le, h.T_ge, h.e_le⟩,
    h.w_le.trans (min_le_right _ _), h.vs_le.trans (min_le_right _ _)⟩

/-! ### The boundary request record -/

/-- **The boundary staged requests** (lane BSTG; review 53 §6.2): the interior requests as an STG
record (each read at its STG prefix; `β₂`'s before `βc`), and the boundary requests read AFTER the
joint output `V` (the prefix `P` contains `β₁`): BR24's cusp splitting quality `βd` and norm error
`εN` (upper), the physical scale `r∂` (upper; it reads `βd, εN`) and the cusp test / Taylor length
`H` (lower). -/
structure C14BdryStagedRequestsBSTG where
  toSTG : C14StagedRequestsSTG
  βd : C14PreFinal → ℝ → ℝ
  εN : C14PreFinal → ℝ → ℝ
  rd : C14PreFinal → ℝ → ℝ → ℝ → ℝ
  H : C14PreFinal → ℝ → ℝ → ℝ → ℝ
  βd_pos : ∀ P V, 0 < βd P V
  εN_pos : ∀ P V, 0 < εN P V
  rd_pos : ∀ P V a e, 0 < rd P V a e

/-- The trivial boundary requests. -/
def C14BdryStagedRequestsBSTG.trivial : C14BdryStagedRequestsBSTG where
  toSTG := C14StagedRequestsSTG.trivial
  βd _ _ := 1
  εN _ _ := 1
  rd _ _ _ _ := 1
  H _ _ _ _ := 0
  βd_pos _ _ := one_pos
  εN_pos _ _ := one_pos
  rd_pos _ _ _ _ := one_pos

/-- **The common boundary requests of two records**: the STG `inf` of the interior requests, the
minimum of every upper boundary request and the maximum of the lower one. -/
def C14BdryStagedRequestsBSTG.inf (R₁ R₂ : C14BdryStagedRequestsBSTG) :
    C14BdryStagedRequestsBSTG where
  toSTG := R₁.toSTG.inf R₂.toSTG
  βd P V := min (R₁.βd P V) (R₂.βd P V)
  εN P V := min (R₁.εN P V) (R₂.εN P V)
  rd P V a e := min (R₁.rd P V a e) (R₂.rd P V a e)
  H P V a e := max (R₁.H P V a e) (R₂.H P V a e)
  βd_pos P V := lt_min (R₁.βd_pos P V) (R₂.βd_pos P V)
  εN_pos P V := lt_min (R₁.εN_pos P V) (R₂.εN_pos P V)
  rd_pos P V a e := lt_min (R₁.rd_pos P V a e) (R₂.rd_pos P V a e)

/-! ### The boundary values read after `V` -/

/-- The cusp splitting quality: `min(Rq.βd, β₁/2)` (BR24: below `β₁`). -/
def bdryβd_BSTG (Rq : C14BdryStagedRequestsBSTG) (P : C14PreFinal) (V : ℝ) : ℝ :=
  min (Rq.βd P V) (P.β 1 / 2)

/-- The cusp norm error: the request itself. -/
def bdryεN_BSTG (Rq : C14BdryStagedRequestsBSTG) (P : C14PreFinal) (V : ℝ) : ℝ :=
  Rq.εN P V

/-- The cusp test / Taylor length `H∂ = max(1, Rq.H)`. -/
def bdryH_BSTG (Rq : C14BdryStagedRequestsBSTG) (P : C14PreFinal) (V : ℝ) : ℝ :=
  max 1 (Rq.H P V (bdryβd_BSTG Rq P V) (bdryεN_BSTG Rq P V))

/-- The physical scale `r∂ = min(Rq.rd, 1/(200 H∂))`. -/
def bdryRd_BSTG (Rq : C14BdryStagedRequestsBSTG) (P : C14PreFinal) (V : ℝ) : ℝ :=
  min (Rq.rd P V (bdryβd_BSTG Rq P V) (bdryεN_BSTG Rq P V)) (1 / (200 * bdryH_BSTG Rq P V))

theorem bdryβd_pos_BSTG (Rq : C14BdryStagedRequestsBSTG) (P : C14PreFinal) (V : ℝ) :
    0 < bdryβd_BSTG Rq P V :=
  lt_min (Rq.βd_pos P V) (half_pos P.β₁_pos)

theorem bdryβd_lt_BSTG (Rq : C14BdryStagedRequestsBSTG) (P : C14PreFinal) (V : ℝ) :
    bdryβd_BSTG Rq P V < P.β 1 :=
  (min_le_right _ _).trans_lt (half_lt_self P.β₁_pos)

theorem bdryεN_pos_BSTG (Rq : C14BdryStagedRequestsBSTG) (P : C14PreFinal) (V : ℝ) :
    0 < bdryεN_BSTG Rq P V :=
  Rq.εN_pos P V

theorem one_le_bdryH_BSTG (Rq : C14BdryStagedRequestsBSTG) (P : C14PreFinal) (V : ℝ) :
    1 ≤ bdryH_BSTG Rq P V :=
  le_max_left _ _

theorem bdryRd_pos_BSTG (Rq : C14BdryStagedRequestsBSTG) (P : C14PreFinal) (V : ℝ) :
    0 < bdryRd_BSTG Rq P V := by
  have hH : 0 < bdryH_BSTG Rq P V := one_pos.trans_le (one_le_bdryH_BSTG Rq P V)
  exact lt_min (Rq.rd_pos _ _ _ _) (by positivity)

/-- BRegPhysical's entry `r∂ < 1/(100H∂)`: `100 H∂ r∂ < 1`. -/
theorem bdryH_mul_bdryRd_lt_BSTG (Rq : C14BdryStagedRequestsBSTG) (P : C14PreFinal) (V : ℝ) :
    100 * bdryH_BSTG Rq P V * bdryRd_BSTG Rq P V < 1 := by
  have hH : 0 < bdryH_BSTG Rq P V := one_pos.trans_le (one_le_bdryH_BSTG Rq P V)
  have h1 : bdryRd_BSTG Rq P V ≤ 1 / (200 * bdryH_BSTG Rq P V) := min_le_right _ _
  have h2 : 100 * bdryH_BSTG Rq P V * (1 / (200 * bdryH_BSTG Rq P V)) = 1 / 2 := by
    field_simp
    ring
  calc 100 * bdryH_BSTG Rq P V * bdryRd_BSTG Rq P V
      ≤ 100 * bdryH_BSTG Rq P V * (1 / (200 * bdryH_BSTG Rq P V)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 / 2 := h2
    _ < 1 := by norm_num

/-! ### The certificate premise on one tail -/

/-- **The certificate premise holds on a tail** for every fixed positive bound `X`:
`1000 δ_{n+1}² < X` for all late `n` (BBR03's ratios tend to zero). -/
theorem eventually_bdry_ratio_sq_lt_BSTG {δ₀ X : ℝ} (hδ₀ : 0 < δ₀) (hX : 0 < X) :
    ∀ᶠ n : ℕ in atTop, 1000 * boundaryCounterexampleRatio δ₀ (n + 1) ^ 2 < X := by
  have hc : 0 < min 1 (X / 2000) := lt_min one_pos (by positivity)
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine (hnR.eventually_ge_atTop (1 / (16 * min 1 (X / 2000)))).mono fun n hn => ?_
  have hn' : 1 / (16 * min 1 (X / 2000)) ≤ ((n + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hle := boundaryCounterexampleRatio_le_of_BDRY5 δ₀ hc (Nat.le_add_left 1 n)
    (one_le_sixteen_mul_of_ge_BDRY5 hc hn')
  have h0 := (boundaryCounterexampleRatio_pos hδ₀ (Nat.le_add_left 1 n)).le
  have h1 : min 1 (X / 2000) ≤ 1 := min_le_left _ _
  have h2 : min 1 (X / 2000) ≤ X / 2000 := min_le_right _ _
  have h3 : boundaryCounterexampleRatio δ₀ (n + 1) * boundaryCounterexampleRatio δ₀ (n + 1) ≤
      min 1 (X / 2000) * 1 := mul_le_mul hle (hle.trans h1) h0 hc.le
  rw [pow_two]
  linarith

/-- **The certificate premise is monotone in the radius**: if it holds at `r ≥ 0`, it holds at
every `r' ≥ r` (so the premise at `r∂` gives every conditional certificate at radii `≥ r∂`). -/
theorem bdry_premise_mono_BSTG {δn w' r r' : ℝ} (hw' : 0 ≤ w') (hr : 0 ≤ r) (hrr : r ≤ r')
    (h : 1000 * δn ^ 2 < w' * min (1 / 2) (r / 4) ^ 2) :
    1000 * δn ^ 2 < w' * min (1 / 2) (r' / 4) ^ 2 := by
  have h0 : 0 ≤ min (1 / 2 : ℝ) (r / 4) := le_min (by norm_num) (by linarith)
  have hm : min (1 / 2 : ℝ) (r / 4) ≤ min (1 / 2) (r' / 4) := min_le_min le_rfl (by linarith)
  have hsq : min (1 / 2 : ℝ) (r / 4) ^ 2 ≤ min (1 / 2) (r' / 4) ^ 2 := pow_le_pow_left₀ h0 hm 2
  exact h.trans_le (mul_le_mul_of_nonneg_left hsq hw')

/-! ### ONE staged boundary assignment -/

/-- **ONE staged boundary assignment on T3B_IDX2's prefix order** (lane BSTG; review 53 §6.2 / §8,
the boundary staged adapter): there is `δStar > 0` such that for the early tolerances `t`, every
boundary tolerance `ϑ₃ > 0` and every boundary request record `Rq` there is ONE admissible prefix
`P` (every parameter of the boundary producer before the sequence, with the producer's threshold
outputs) meeting `Rq`'s interior requests (each at the STG prefix before its stage), with
`3βc ≤ β 2`, `w < ω₃/4` (at the `w` stage) and `vs < ϑ₃/4` (at the `vs` stage), such that for every
boundary sequence at BBR03's ratios `δ_{n+1}` (`δ₀ ≤ δStar`), with the outputs `V ≥ T`, `δ < δ'`,
`Lmax := c14Lmax` (above `400V` and `Rq`'s `Lmax` request), the cusp requests read after `V`
(`βd ≤ Rq.βd`, `βd < β₁`, `εN = Rq.εN`) and the physical data (`H∂ ≥ Rq.H`, `r∂ ≤ Rq.rd`,
`100 H∂ r∂ < 1`), every late member satisfies T3B_IDX2's per-member conclusion
`BoundaryPacketsOutBFR_BQ` at exactly these parameters (BCP04.a at the member's index `n + 1`),
together with the certificate premise at `r∂` on the SAME tail. -/
theorem exists_bdry_staged_assignment_BSTG (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ δStar : ℝ, 0 < δStar ∧ ∀ (t : C14Tol) (ϑ₃ : ℝ), 0 < ϑ₃ → ∀ Rq : C14BdryStagedRequestsBSTG,
    ∃ P : C14PreFinal, P.toC14Tol = t ∧ Rq.toSTG.toC14.Meets P ∧ 3 * P.βc ≤ P.β 2 ∧
      P.w < boundaryVolumeCap ∧ P.vs < ϑ₃ / 4 ∧
      ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∃ V : ℝ, P.T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < P.δ' ∧
        400 * V < c14Lmax Rq.toSTG.toC14 P V ∧ Rq.toSTG.Lmax P V ≤ c14Lmax Rq.toSTG.toC14 P V ∧
        bdryβd_BSTG Rq P V ≤ Rq.βd P V ∧ bdryβd_BSTG Rq P V < P.β 1 ∧
        Rq.H P V (bdryβd_BSTG Rq P V) (bdryεN_BSTG Rq P V) ≤ bdryH_BSTG Rq P V ∧
        bdryRd_BSTG Rq P V ≤ Rq.rd P V (bdryβd_BSTG Rq P V) (bdryεN_BSTG Rq P V) ∧
        100 * bdryH_BSTG Rq P V * bdryRd_BSTG Rq P V < 1 ∧
        ∀ᶠ n in atTop,
          BoundaryPacketsOutBFR_BQ (W n) (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)
            ((n + 1 : ℕ) : ℝ) P.Λ P.w P.β P.Δ P.σs P.σc P.μ P.b P.s P.b' P.s' P.ε P.γc P.βc
            (c14Lmax Rq.toSTG.toC14 P V) P.τ P.γ δ P.εr P.e P.T V P.vs P.ζ P.Λz
            (bdryβd_BSTG Rq P V) (bdryεN_BSTG Rq P V) ∧
          1000 * boundaryCounterexampleRatio δ₀ (n + 1) ^ 2 <
            P.w / (2 * (1 + 2 * P.Λ⁻¹) ^ 3) * min (1 / 2) (bdryRd_BSTG Rq P V / 4) ^ 2 := by
  obtain ⟨δStar, hδStar, a₂, ha₂, h0⟩ := lc88_boundary_packets_BFR_out_BQ_IDX4 K hK A hA
  refine ⟨δStar, hδStar, fun t ϑ₃ hϑ₃ Rq => ?_⟩
  obtain ⟨p1, rfl, rfl, h1γ, h⟩ :=
    c14_stage_circ_FAM2b t ha₂ ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).γ_pos t) h0
  obtain ⟨p2, rfl, h2βc, h2γc, h⟩ := c14_stage_collar_STG p1
    (fun g => min ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).βc g.toC14PreCirc)
      (c14β₂Value_STG (Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃) g / 3))
    (fun g => lt_min ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).βc_pos _)
      (div_pos (c14β₂Value_pos_STG _ g) zero_lt_three))
    ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).γc_pos p1) h
  have h2 : p2.βc ≤ min p2.β₀ (min ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).β₂ p2.toGc_STG)
      (min (1 / 10000000) (p2.γT / 20))) / 3 :=
    h2βc.trans (min_le_right _ _)
  obtain ⟨p3, rfl, h3β₂, h3v, h⟩ :=
    c14_stage_excl_STG p2 ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).β₂_pos p2.toGc_STG) h
  have h3βc : 3 * p3.βc ≤ p3.β₂ := by
    rw [h3v]
    linarith
  obtain ⟨p4, rfl, h4Δ, h⟩ :=
    c14_stage_scale_FAM2b p3 ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).Δ p3) h
  obtain ⟨p5, rfl, h5σc, h5ε, h5μ, h5τ, h5s, h5b', h5s', h⟩ := c14_stage_edge_FAM2b p4
    ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).σc_pos p4) ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).ε_pos p4)
    ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).μ_pos p4) ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).τ_pos p4)
    ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).s_pos p4) ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).b'_pos p4)
    ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).s'_pos p4) h
  obtain ⟨p6, rfl, h6Λ, h⟩ :=
    c14_stage_lip_FAM2b p5 ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).Λ_pos p5) h
  obtain ⟨p7, rfl, h7w, h⟩ :=
    c14_stage_vol_FAM2b p6 ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).w_pos p6) h
  obtain ⟨p8, rfl, h8b, h⟩ :=
    c14_stage_split_FAM2b p7 ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).b_pos p7) h
  obtain ⟨p9, rfl, h9σs, h9vs, h⟩ := c14_stage_slim_FAM2b p8
    ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).σs_pos p8) ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).vs_pos p8)
    h
  obtain ⟨p10, rfl, h10ζ, h10β, h⟩ := c14_stage_beta_FAM2b p9
    ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).ζ_pos p9) ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).β₁_pos p9)
    h
  obtain ⟨p11, rfl, h11cap, h⟩ :=
    c14_stage_zero_FAM2b p10 ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).cap_pos p10) h
  obtain ⟨P, rfl, h12T, h12e, h⟩ := c14_stage_final_FAM2b p11
    ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).T p11) ((Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).e_pos p11) h
  have hM : (Rq.toSTG.withBdryCaps_BSTG ϑ₃ hϑ₃).toC14.Meets P :=
    ⟨h1γ, h2γc, h2βc.trans (min_le_left _ _), h3β₂, h4Δ, h5σc, h5ε, h5μ, h5τ, h5s, h5b', h5s',
      h6Λ, h7w, h8b, h9σs, h9vs, h10ζ, h10β, h11cap, h12T, h12e⟩
  obtain ⟨hMR, hw2, hvs8⟩ := C14StagedRequestsSTG.meets_of_withBdryCaps_BSTG hM
  have hcap := boundaryVolumeCap_pos
  refine ⟨P, rfl, hMR, by rw [P.β_two]; exact h3βc, by linarith, by linarith, ?_⟩
  intro δ₀ hδ₀ hδ₀S W _ g B hcoll hder
  obtain ⟨V, hTV, δ, hδ, hδδ', hV⟩ := h δ₀ hδ₀ hδ₀S W g B hcoll hder
  have hw' : 0 < P.w / (2 * (1 + 2 * P.Λ⁻¹) ^ 3) := by
    have := P.w_pos
    have := P.Λ_pos
    positivity
  have hr := bdryRd_pos_BSTG Rq P V
  have hX : 0 < P.w / (2 * (1 + 2 * P.Λ⁻¹) ^ 3) * min (1 / 2) (bdryRd_BSTG Rq P V / 4) ^ 2 := by
    have : 0 < min (1 / 2 : ℝ) (bdryRd_BSTG Rq P V / 4) := lt_min (by norm_num) (by positivity)
    positivity
  refine ⟨V, hTV, δ, hδ, hδδ', c14Lmax_gt Rq.toSTG.toC14 P V, c14Lmax_ge Rq.toSTG.toC14 P V,
    min_le_left _ _, bdryβd_lt_BSTG Rq P V, le_max_right _ _, min_le_left _ _,
    bdryH_mul_bdryRd_lt_BSTG Rq P V, ?_⟩
  exact (hV _ (c14Lmax_pos Rq.toSTG.toC14 P V) _ _ (bdryβd_pos_BSTG Rq P V)
    (bdryεN_pos_BSTG Rq P V)).and (eventually_bdry_ratio_sq_lt_BSTG hδ₀ hX)

end DifferentialGeometry.Geometry.Collapse
