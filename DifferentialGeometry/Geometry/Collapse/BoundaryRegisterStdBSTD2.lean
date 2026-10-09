import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterExtBSTD2

/-!
# The enhanced chain's uniform register block `std` at the extended register (lane BSTD2, G1b)

Text `TargetsBoundary-A-v3.lean.txt` (lane BAUG-Dc, D69-5 / D69-12): the enhanced boundary chain
`BoundaryGaf02ChainE` stores ONE uniform register block `std` (closed `Gaf02Chain.std`); A2-mk v3
takes it as its premise block. Its new entries `σs, σc, γc, εr ∈ [0, 1]` (lane B-DFB's derivative
bound) hold on EVERY early choice of lane BSTG-D1 (`σs ≤ 1/100`, `σc < 1`, `γc < 1/100`,
`εr < 1/4`); the whole block holds at the extended register.

* `BoundaryEarlyOver_BSTD1.icc_BSTD2`: `σs, σc, γc, εr ∈ [0, 1]`.
* `BoundaryRegisterOverX_BSTD2.std_block_BSTD2`: A2-mk v3's uniform block, verbatim and in order.
* consumer `exists_boundarySequenceAssignmentX_std_BSTD2`: ONE assignment whose register carries the
  block (A2-mk v3's premises discharged once for the whole tail).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter

namespace DifferentialGeometry.Geometry.Collapse

/-- **`σs, σc, γc, εr ∈ [0, 1]` on every early choice** (B-DFB's derivative bound; closed
`Gaf02Chain.std`). -/
theorem BoundaryEarlyOver_BSTD1.icc_BSTD2 {Θ : BoundaryProducerThresholds_BSTD1}
    (E : BoundaryEarlyOver_BSTD1 Θ) :
    E.σs ∈ Icc (0 : ℝ) 1 ∧ E.σc ∈ Icc (0 : ℝ) 1 ∧ E.γc ∈ Icc (0 : ℝ) 1 ∧
      E.εr ∈ Icc (0 : ℝ) 1 := by
  have h1 := E.σs_le
  have h2 := E.γc_lt
  have h3 := E.εr_pos
  have h4 : E.εr < 1 / 4 := Θ.ER_lt _
  exact ⟨⟨E.σs_pos.le, by linarith⟩, ⟨E.σc_pos.le, E.σc_lt.le⟩, ⟨E.γc_pos.le, by linarith⟩,
    ⟨h3.le, by linarith⟩⟩

/-- **A2-mk v3's uniform register block** (`BoundaryGaf02ChainE.std`, verbatim and in order) at the
extended register: BAUG-A's nine, `1 ≤ Δ`, the unified Λ–Δ clause, the CHI buffer / `e` / `T`
lines and `σs, σc, γc, εr ∈ [0, 1]`. -/
theorem BoundaryRegisterOverX_BSTD2.std_block_BSTD2 {Θ : BoundaryProducerThresholds_BSTD1}
    {χ : BoundaryChainThresholds_BSTD2} {E : BoundaryEarlyOverX_BSTD2 Θ χ} {V : ℝ}
    (R : BoundaryRegisterOverX_BSTD2 E V) :
    0 ≤ E.Λ ∧ 0 < E.Δ ∧ E.μ ≤ 1 / 100 ∧ E.τ ≤ 1 / 100 ∧ 100 * E.Δ * E.Λ ≤ 1 / 100 ∧ 0 ≤ V ∧
      0 < E.β 1 ∧ 0 < E.b ∧ E.e ≤ 1 / 10 ∧ 1 ≤ E.Δ ∧ 1000000 * E.Δ * E.Λ < 1 / 100000 ∧
      4 * (10 + 2 * (2000000 * E.Δ) + E.Δ / 3) ≤ R.Lmax ∧ E.e < 1 / 40 ∧
      1600 * (1000000 * E.Δ) ≤ E.T ∧
      E.σs ∈ Icc (0 : ℝ) 1 ∧ E.σc ∈ Icc (0 : ℝ) 1 ∧ E.γc ∈ Icc (0 : ℝ) 1 ∧
      E.εr ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := R.register_block_BSTD2
  obtain ⟨i1, i2, i3, i4⟩ := E.toBoundaryEarlyOver_BSTD1.icc_BSTD2
  exact ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, R.Lmax_ge_buf, E.e_lt, E.T_ge_Δ, i1, i2, i3,
    i4⟩

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **Consumer: ONE assignment with the enhanced chain's uniform block** — for every extended early
choice and every standing sequence, `V`, an extended register (whose numbers satisfy A2-mk v3's
uniform block, ONE block for the whole tail) and `n₀` with the extended member output. -/
theorem exists_boundarySequenceAssignmentX_std_BSTD2 {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w}
    {χ : BoundaryChainThresholds_BSTD2} (E : BoundaryEarlyChoicesX_BSTD2 K hK A hA χ)
    (S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar) :
    ∃ V : ℝ, ∃ R : BoundaryRegisterOverX_BSTD2 E V,
      (0 ≤ E.Λ ∧ 0 < E.Δ ∧ E.μ ≤ 1 / 100 ∧ E.τ ≤ 1 / 100 ∧ 100 * E.Δ * E.Λ ≤ 1 / 100 ∧ 0 ≤ V ∧
        0 < E.β 1 ∧ 0 < E.b ∧ E.e ≤ 1 / 10 ∧ 1 ≤ E.Δ ∧ 1000000 * E.Δ * E.Λ < 1 / 100000 ∧
        4 * (10 + 2 * (2000000 * E.Δ) + E.Δ / 3) ≤ R.Lmax ∧ E.e < 1 / 40 ∧
        1600 * (1000000 * E.Δ) ≤ E.T ∧
        E.σs ∈ Icc (0 : ℝ) 1 ∧ E.σc ∈ Icc (0 : ℝ) 1 ∧ E.γc ∈ Icc (0 : ℝ) 1 ∧
        E.εr ∈ Icc (0 : ℝ) 1) ∧
      ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Nonempty (BoundaryMemberOutputX_BSTD2 S n R) := by
  obtain ⟨V, R, n₀, hR⟩ := exists_boundarySequenceAssignmentX_BSTD2 E S
  exact ⟨V, R, R.std_block_BSTD2, n₀, hR⟩

end DifferentialGeometry.Geometry.Collapse
