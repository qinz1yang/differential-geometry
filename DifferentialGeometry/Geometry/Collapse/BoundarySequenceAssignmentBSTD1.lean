import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterOverBSTD1
import DifferentialGeometry.Geometry.Collapse.BoundaryEarlyStagedBSTD1

/-!
# ONE per-sequence boundary assignment (lane BSTG-D1, task 61 D61-11 D3)

Dispositions of task 61, D61-11 (draft §7.2):

`exists_boundarySequenceAssignment (early) (S) : ∃ V, ∃ R : BoundaryRegisterOver early V, ∃ n₀,
  ∀ n ≥ n₀, Nonempty (BoundaryMemberOutput S n R)`,

with `R.early = early` fixed by the type and the order
`early ≺ S ≺ V, δ_local ≺ L_max ≺ β_∂, ε_N ≺ r_∂ ≺ n₀`.

* `BoundaryMemberOutput_BSTD1 S n R`: the present tail of one member — T3B-BFRZ's per-member
  conclusion (`BoundaryPacketsOutBFRZ_BSTD1`: packet, scale and certificates, completion, ONE
  `F : LocalPacketsOnBFRZ … oM` for every orientation, product OR separation) at the member ratio
  `δ_n = boundaryCounterexampleRatio δ₀ (n+1)` (packet, collapse, derivative and the `δ_n²`
  premise), BCP04.a at the member's index `n + 1` (the accepted IDX4 form), exactly the early
  choice's parameters and the register's `δ_local, L_max, β_∂, ε_N` — together with the
  certificate premise `1000 δ_n² < w'·min(1/2, r_∂/4)²` at the register's `r_∂` (so every
  conditional certificate of the member holds at every radius `≥ r_∂`, `bdry_premise_mono_BSTG`).
  It grows with the augmented chain (draft §7.5); BBR02 only binds, BBR03 takes ONE tail member.
* `BoundaryMemberOutput_BSTD1.premise_cusp_BSTD1`: the premise at `r_∂` gives BCUSP-1's B5 premise
  at the register's physical cusp scale.
* `boundarySequenceAssignment_of_register_BSTD1`: on every standing sequence the producer's outputs
  `V ≥ T` and `δ < δ'` are such that EVERY register over `(early, V)` with `δ_local = δ` has a tail.
* `exists_boundarySequenceAssignment_req_BSTD1`: the same with the register of lane BSTG G1/G3's
  values meeting any late request record.
* `exists_boundarySequenceAssignment_BSTD1`: the D61-11 statement.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter

namespace DifferentialGeometry.Geometry.Collapse

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **The output of one member of the boundary sequence assignment** (D61-11 D3): T3B-BFRZ's
per-member conclusion at the member ratio `δ_{n+1}`, the BCP04.a index `n + 1`, the early choice's
parameters and the register's `δ_local, L_max, β_∂, ε_N`, and the certificate premise at the
register's `r_∂`. -/
def BoundaryMemberOutput_BSTD1 {Θ : BoundaryProducerThresholds_BSTD1} {K : ℕ} {A : ℝ → ℝ}
    {E : BoundaryEarlyOver_BSTD1 Θ} {V : ℝ} (S : BoundaryStandingSequence_BSTD1 K A Θ.δStar)
    (n : ℕ) (R : BoundaryRegisterOver_BSTD1 E V) : Prop :=
  BoundaryPacketsOutBFRZ_BSTD1 (S.W n) (S.g n) K A (boundaryCounterexampleRatio S.δ₀ (n + 1))
      (S.B n) ((n + 1 : ℕ) : ℝ) E.Λ E.w E.β E.Δ E.σs E.σc E.μ E.b E.s E.b' E.s' E.ε E.γc E.βc
      R.Lmax E.τ E.γ R.δlocal E.εr E.e E.T V E.vs E.ζ E.Λz R.βd R.εN ∧
    1000 * boundaryCounterexampleRatio S.δ₀ (n + 1) ^ 2 <
      E.w / (2 * (1 + 2 * E.Λ⁻¹) ^ 3) * min (1 / 2) (R.rd / 4) ^ 2

/-- **The member's premise feeds B5 at the register's physical cusp scale**: the certificate premise
at `r_∂` gives the premise of lane BCUSP-1's B5 (physical and first-exit certificates) at
`cuspPhysicalScale_BCUSP1 β_∂ (10⁶Δ) H_∂ ϑ c₃` (`r_∂` lies below it; `bdry_premise_mono_BSTG`). -/
theorem BoundaryMemberOutput_BSTD1.premise_cusp_BSTD1 {Θ : BoundaryProducerThresholds_BSTD1}
    {K : ℕ} {A : ℝ → ℝ} {E : BoundaryEarlyOver_BSTD1 Θ} {V : ℝ}
    {S : BoundaryStandingSequence_BSTD1 K A Θ.δStar} {n : ℕ} {R : BoundaryRegisterOver_BSTD1 E V}
    (h : BoundaryMemberOutput_BSTD1 S n R) :
    1000 * boundaryCounterexampleRatio S.δ₀ (n + 1) ^ 2 < E.w / (2 * (1 + 2 * E.Λ⁻¹) ^ 3) *
      min (1 / 2) (cuspPhysicalScale_BCUSP1 R.βd (10 ^ 6 * E.Δ) R.Hd E.ϑmin E.c₃ / 4) ^ 2 := by
  have hw' : 0 ≤ E.w / (2 * (1 + 2 * E.Λ⁻¹) ^ 3) := by
    have := E.w_pos
    have := E.Λ_pos
    positivity
  exact bdry_premise_mono_BSTG hw' R.rd_pos.le R.rd_le_cusp h.2

/-- **Every register at the producer's cone error has a tail** (D61-11 D3, strong form): for every
early choice `E` and every standing sequence `S` (with `δ₀ ≤ δStar`), the producer's finite zero
scale `V ≥ T` and cone error `0 < δ < δ'(E)` are such that EVERY register `R` over `(E, V)` with
`δ_local = δ` has a tail of members carrying `BoundaryMemberOutput_BSTD1 S n R`. -/
theorem boundarySequenceAssignment_of_register_BSTD1 {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w}
    (E : BoundaryEarlyChoices_BSTD1 K hK A hA)
    (S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar) :
    ∃ V : ℝ, E.T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < E.δ' ∧
      ∀ R : BoundaryRegisterOver_BSTD1 E V, R.δlocal = δ →
        ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Nonempty (BoundaryMemberOutput_BSTD1 S n R) := by
  obtain ⟨V, hTV, δ, hδ, hδδ', hev⟩ := bdry_early_continuation_BSTD1 E S
  refine ⟨V, hTV, δ, hδ, hδδ', fun R hR => ?_⟩
  subst hR
  have hw' : 0 < E.w / (2 * (1 + 2 * E.Λ⁻¹) ^ 3) := by
    have := E.w_pos
    have := E.Λ_pos
    positivity
  have hX : 0 < E.w / (2 * (1 + 2 * E.Λ⁻¹) ^ 3) * min (1 / 2) (R.rd / 4) ^ 2 := by
    have : 0 < min (1 / 2 : ℝ) (R.rd / 4) := lt_min (by norm_num) (by linarith [R.rd_pos])
    positivity
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp ((hev R.Lmax R.Lmax_pos R.βd R.εN R.βd_pos
    R.εN_pos).and (eventually_bdry_ratio_sq_lt_BSTG S.δ₀_pos hX))
  exact ⟨n₀, fun n hn => ⟨hn₀ n hn⟩⟩

/-- **ONE per-sequence boundary assignment meeting the late requests** (D61-11 D2 + D3): for every
early choice, every standing sequence and every late request record `Rq`, the producer's `V ≥ T`,
then the register of lane BSTG G1/G3's values (`δ_local` the producer's cone error, `L_max ≥ Rq`,
`β_∂ ≤ Rq`, `ε_N = Rq`, `H_∂ ≥ Rq`, `r_∂ ≤ Rq`, each read in the D61-11 order), then `n₀`. -/
theorem exists_boundarySequenceAssignment_req_BSTD1 {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w}
    (E : BoundaryEarlyChoices_BSTD1 K hK A hA)
    (S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar)
    (Rq : BoundaryLateRequests_BSTD1) :
    ∃ V : ℝ, E.T ≤ V ∧ ∃ R : BoundaryRegisterOver_BSTD1 E V,
      Rq.Lmax V R.δlocal ≤ R.Lmax ∧ R.βd ≤ Rq.βd V R.δlocal R.Lmax ∧
      R.εN = Rq.εN V R.δlocal R.Lmax ∧ Rq.H V R.δlocal R.Lmax R.βd R.εN ≤ R.Hd ∧
      R.rd ≤ Rq.rd V R.δlocal R.Lmax R.βd R.εN R.Hd ∧
      ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Nonempty (BoundaryMemberOutput_BSTD1 S n R) := by
  obtain ⟨V, hTV, δ, hδ, hδδ', hR⟩ := boundarySequenceAssignment_of_register_BSTD1 E S
  obtain ⟨R, hRδ, h1, h2, h3, h4, h5⟩ := exists_boundaryRegisterOver_BSTD1 E V δ hδ hδδ' Rq
  subst hRδ
  exact ⟨V, hTV, R, h1, h2, h3, h4, h5, hR R rfl⟩

/-- **ONE per-sequence boundary assignment** (task 61, D61-11): for every early choice `E` (an
input, over the exported producer thresholds) and every standing sequence `S` of BBR03 with
`δ₀ ≤ δStar`, there are the zero scale `V`, a boundary register `R` over `(E, V)` (`R.early = E` by
type; `δ_local ≺ L_max ≺ β_∂, ε_N ≺ r_∂`) and `n₀` such that every member `n ≥ n₀` has its output
(T3B-BFRZ's per-member conclusion at `δ_{n+1}`, index `n + 1`, and the premise at `r_∂`). -/
theorem exists_boundarySequenceAssignment_BSTD1 {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w}
    (E : BoundaryEarlyChoices_BSTD1 K hK A hA)
    (S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar) :
    ∃ V : ℝ, ∃ R : BoundaryRegisterOver_BSTD1 E V, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      Nonempty (BoundaryMemberOutput_BSTD1 S n R) := by
  obtain ⟨V, -, R, -, -, -, -, -, hR⟩ :=
    exists_boundarySequenceAssignment_req_BSTD1 E S BoundaryLateRequests_BSTD1.trivial
  exact ⟨V, R, hR⟩

end DifferentialGeometry.Geometry.Collapse
