import DifferentialGeometry.Geometry.Collapse.BoundaryPacketsOutBASeqBSTD2
import DifferentialGeometry.Geometry.Collapse.BoundaryEarlyThresholdsBSTD1

/-!
# The joint (BA) producer's thresholds as top-level definitions (lane BSTD2, G2-pre)

Lane BSTG-D1 exported the thresholds of T3B-BFRZ (`exists_bdryThresholds_BSTD1`); its member output
has no (BA) certificates. The (BA) certificates of a `BoundarySupply` come only from the joint
producer `lc88_boundary_packets_BFRZ_BA_BIND`, which fixes the (BA) error `θ` and `ν` FIRST and
outputs, besides T3B-BFRZ's thresholds, `σC, ηC` (before `δStar`) and `σE, ηE, σS, ηS` (after
`β₂ Δ`). Here its thresholds are exported by the same `choose` / `dite` pattern, with `θ, ν` as
parameters of the export (like `K, A`):

* `BoundaryProducerThresholdsBA_BSTD2 extends BoundaryProducerThresholds_BSTD1`: + `σC ηC` and the
  functions `SE HE SS HS` of the parameters `(γ βc γc β₂ Δ)`.
* `BoundaryEarlyOverBA_BSTD2 Θ θ ν` extends
  `BoundaryEarlyOver_BSTD1 Θ.toBoundaryProducerThresholds_BSTD1`:
  + exactly the joint producer's extra conditions, each on its node (`γ ≤ θ²/10⁷`; `3β₂ ≤ σC`,
  `β₂ ≤ θ²/10⁷`; `μΔ ≤ θ/4`, `σc ≤ θ²/10⁷`; `3b ≤ σE`, `b(2(421Δ+1)) ≤ 1`, `b ≤ θ²/10⁷`; `vs ≤ θ/4`,
  `σs ≤ θ²/10⁷`; `3ν ≤ β 3`, `2β₁ ≤ ηC, ηE, ηS`, `10⁶Δβ₁³ < 1`, `3β₁ ≤ σS`,
  `β₁(2(1950002Δ+1)) ≤ 1`, `β₁ ≤ θ²/10⁷`). No field states a continuation.
* `exists_bdryThresholdsBA_of_BSTD2`: for `0 < θ < 1`, `0 < ν < 10⁻⁶` there are thresholds such
  that EVERY early choice over them and EVERY standing sequence with `δ₀ ≤ δStar` have the joint
  producer's continuation at the member's index `n + 1` (`V ≥ T`, `δ < δ'`, then for every
  `L_max ≥ σC⁻¹, σE⁻¹, σS⁻¹` and `β_∂ > 0`, `0 < ε_N ≤ θ²/(4·10⁷)` the joint per-member conclusion
  on a tail).
* `exists_bdryThresholdsBA_BSTD2`: the same with `(θ, ν)` free (the range conditions moved after
  the thresholds; outside the range the record is lane BSTG-D1's with unit extras), so that
  `bdryThresholdsBA_BSTD2 K hK A hA θ ν` is a total Skolem function of `(K, A, θ, ν)` (the shape
  of text v3 §H's stand-in); `BoundaryEarlyChoicesBA_BSTD2`, `bdry_early_continuationBA_BSTD2`
  (the range conditions as arguments).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter

namespace DifferentialGeometry.Geometry.Collapse

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **The joint (BA) producer's threshold outputs as functions**: T3B-BFRZ-shaped thresholds of the
joint chain, `σC, ηC` (constants of `θ, ν`) and `σE, ηE, σS, ηS` as functions of
`(γ βc γc β₂ Δ)`, all positive. -/
structure BoundaryProducerThresholdsBA_BSTD2 extends BoundaryProducerThresholds_BSTD1 where
  σC : ℝ
  ηC : ℝ
  SE : BdryParamsScale_BSTD1 → ℝ
  HE : BdryParamsScale_BSTD1 → ℝ
  SS : BdryParamsScale_BSTD1 → ℝ
  HS : BdryParamsScale_BSTD1 → ℝ
  σC_pos : 0 < σC
  ηC_pos : 0 < ηC
  SE_pos : ∀ p, 0 < SE p
  HE_pos : ∀ p, 0 < HE p
  SS_pos : ∀ p, 0 < SS p
  HS_pos : ∀ p, 0 < HS p

/-- **An early choice over the joint thresholds** at the (BA) error `θ` and `ν`: an early choice
of lane BSTG-D1 over the T3B-shaped part, with exactly the joint producer's extra conditions, each
read against the thresholds at the parameters before it. -/
structure BoundaryEarlyOverBA_BSTD2 (Θ : BoundaryProducerThresholdsBA_BSTD2) (θ ν : ℝ) extends
    BoundaryEarlyOver_BSTD1 Θ.toBoundaryProducerThresholds_BSTD1 where
  γ_le_θ : γ ≤ θ ^ 2 / 10000000
  three_β₂_le_σC : 3 * β₂ ≤ Θ.σC
  β₂_le_θ : β₂ ≤ θ ^ 2 / 10000000
  μΔ_le_θ : μ * Δ ≤ θ / 4
  σc_le_θ : σc ≤ θ ^ 2 / 10000000
  three_b_le_σE : 3 * b ≤ Θ.SE toBdryParamsScale_BSTD1
  b_mul_le : b * (2 * (421 * Δ + 1)) ≤ 1
  b_le_θ : b ≤ θ ^ 2 / 10000000
  vs_le_θ : vs ≤ θ / 4
  σs_le_θ : σs ≤ θ ^ 2 / 10000000
  three_ν_le : 3 * ν ≤ β 3
  two_β₁_le_ηC : 2 * β 1 ≤ Θ.ηC
  two_β₁_le_ηE : 2 * β 1 ≤ Θ.HE toBdryParamsScale_BSTD1
  two_β₁_le_ηS : 2 * β 1 ≤ Θ.HS toBdryParamsScale_BSTD1
  Δβ₁_lt : 1000000 * Δ * β 1 ^ 3 < 1
  three_β₁_le_σS : 3 * β 1 ≤ Θ.SS toBdryParamsScale_BSTD1
  β₁_mul_le : β 1 * (2 * (1950002 * Δ + 1)) ≤ 1
  β₁_le_θ : β 1 ≤ θ ^ 2 / 10000000

/-- **The joint (BA) producer's thresholds, exported** (the `choose` / `dite` pattern of
`exists_bdryThresholds_BSTD1`): for every early choice `E` over them and every standing sequence `S`
with `δ₀ ≤ δStar`, `V ≥ T`, `δ < δ'`, and for every `L_max ≥ σC⁻¹, σE⁻¹, σS⁻¹`, `β_∂ > 0` and
`0 < ε_N ≤ θ²/(4·10⁷)` every late member carries the joint per-member conclusion at the ratio
`δ_{n+1}`, the index `n + 1`, the error `θ` and exactly `E`'s parameters. -/
theorem exists_bdryThresholdsBA_of_BSTD2 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) {θ ν : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1 / 1000000) :
    ∃ Θ : BoundaryProducerThresholdsBA_BSTD2, ∀ (E : BoundaryEarlyOverBA_BSTD2 Θ θ ν)
      (S : BoundaryStandingSequence_BSTD1 K A Θ.δStar),
      ∃ V : ℝ, E.T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < E.δ' ∧ ∀ Lmax : ℝ, 0 < Lmax → Θ.σC⁻¹ ≤ Lmax →
      (Θ.SE E.toBdryParamsScale_BSTD1)⁻¹ ≤ Lmax → (Θ.SS E.toBdryParamsScale_BSTD1)⁻¹ ≤ Lmax →
      ∀ βd εN : ℝ, 0 < βd → 0 < εN → εN ≤ θ ^ 2 / 40000000 → ∀ᶠ n in atTop,
        BoundaryPacketsOutBA_BSTD2 (S.W n) (S.g n) K A (boundaryCounterexampleRatio S.δ₀ (n + 1))
          (S.B n) ((n + 1 : ℕ) : ℝ) E.Λ E.w E.β E.Δ E.σs E.σc E.μ E.b E.s E.b' E.s' E.ε E.γc E.βc
          Lmax E.τ E.γ δ E.εr E.e E.T V E.vs E.ζ E.Λz βd εN θ := by
  classical
  obtain ⟨σC, hσC, ηC, hηC, δStar, hδStar, a₂, ha₂, hP⟩ :=
    lc88_boundary_packets_BA_out_succ_BSTD2 K hK A hA hθ hθ1 hν hν1
  -- `β₀ (γ)`
  let C1 : ℝ → Prop := fun γ => 0 < γ ∧ γ < 1 / 10 ∧ γ ≤ θ ^ 2 / 10000000
  have hP1 : ∀ (γ : ℝ) (hc : C1 γ), _ := fun γ hc => hP γ hc.1 hc.2.1 hc.2.2
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
  -- `σE ηE σS ηS τ₀ bc₀ (… β₂ Δ)`
  let C3 : BdryParamsScale_BSTD1 → Prop := fun p =>
    C2 p.toBdryParamsCollar_BSTD1 ∧ (0 < p.β₂ ∧ p.β₂ ≤ B0 p.γ ∧ p.β₂ < 1 / 100 ∧
      100 / p.β₂ < p.Δ ∧ D0 p.toBdryParamsCollar_BSTD1 ≤ p.Δ) ∧
    (3 * p.β₂ ≤ σC ∧ p.β₂ ≤ θ ^ 2 / 10000000)
  have hP3 : ∀ (p : BdryParamsScale_BSTD1) (hc : C3 p), _ := fun p hc =>
    hP p.toBdryParamsCollar_BSTD1 hc.1 p.β₂ p.Δ hc.2.1.1
      ((hc.2.1.2.1).trans_eq (dite_eq_left hc.1.1)) hc.2.1.2.2.1 hc.2.1.2.2.2.1
      ((dite_eq_left hc.1).symm.trans_le hc.2.1.2.2.2.2) hc.2.2.1 hc.2.2.2
  choose σE hσE ηE hηE σS hσS ηS hηS τ₀ hτ₀ bc₀ hbc₀ hP using hP3
  let SE : BdryParamsScale_BSTD1 → ℝ := fun p => if hc : C3 p then σE p hc else 1
  let HE : BdryParamsScale_BSTD1 → ℝ := fun p => if hc : C3 p then ηE p hc else 1
  let SS : BdryParamsScale_BSTD1 → ℝ := fun p => if hc : C3 p then σS p hc else 1
  let HS : BdryParamsScale_BSTD1 → ℝ := fun p => if hc : C3 p then ηS p hc else 1
  let T0 : BdryParamsScale_BSTD1 → ℝ := fun p => if hc : C3 p then τ₀ p hc else 1
  let BC : BdryParamsScale_BSTD1 → ℝ := fun p => if hc : C3 p then bc₀ p hc else 1
  -- `a₀, b₁ (… σc ε μ τ s b' s')`
  let C4 : BdryParamsEdge_BSTD1 → Prop := fun p =>
    C3 p.toBdryParamsScale_BSTD1 ∧
    (0 < p.σc ∧ p.σc ≤ S0 p.toBdryParamsCollar_BSTD1 ∧ p.σc < 1 ∧ 0 < p.ε ∧ p.ε < 1 / 100 ∧
      0 < p.μ ∧ p.μ ≤ 1 / 1000000 ∧ 0 < p.τ ∧ p.τ ≤ T0 p.toBdryParamsScale_BSTD1 ∧
      140 * Real.sqrt p.τ < p.ε ^ 2 / 20 ∧ p.ε ≤ 1 / 10 ^ 8 ∧ p.μ ≤ 1 / 10 ^ 8) ∧
    (p.μ * p.Δ ≤ θ / 4 ∧ p.σc ≤ θ ^ 2 / 10000000) ∧
    (0 < p.s ∧ p.s < 1 / 100 ∧ p.s < p.b' / 100000 ∧ p.s < p.s' / 100000 ∧
      p.b' < 1 / (1000000 * p.Δ) ∧ p.s' < 1 / (1000000 * p.Δ) ∧
      p.b' < p.τ * p.Δ / 1000000000 ∧ p.s' < p.τ * p.Δ / 1000000000)
  have hP4 : ∀ (p : BdryParamsEdge_BSTD1) (hc : C4 p), _ := fun p hc =>
    hP p.toBdryParamsScale_BSTD1 hc.1 p.σc p.ε p.μ p.τ hc.2.1.1
      ((hc.2.1.2.1).trans_eq (dite_eq_left hc.1.1)) hc.2.1.2.2.1 hc.2.1.2.2.2.1
      hc.2.1.2.2.2.2.1 hc.2.1.2.2.2.2.2.1 hc.2.1.2.2.2.2.2.2.1 hc.2.1.2.2.2.2.2.2.2.1
      ((hc.2.1.2.2.2.2.2.2.2.2.1).trans_eq (dite_eq_left hc.1))
      hc.2.1.2.2.2.2.2.2.2.2.2.1 hc.2.1.2.2.2.2.2.2.2.2.2.2.1 hc.2.1.2.2.2.2.2.2.2.2.2.2.2
      hc.2.2.1.1 hc.2.2.1.2
      p.s p.b' p.s' hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1
      hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2
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
    (3 * p.b ≤ SE p.toBdryParamsScale_BSTD1 ∧ p.b * (2 * (421 * p.Δ + 1)) ≤ 1 ∧
      p.b ≤ θ ^ 2 / 10000000) ∧
    (0 < p.σs ∧ p.σs ≤ 1 / 100 ∧ 0 < p.vs) ∧ (p.vs ≤ θ / 4 ∧ p.σs ≤ θ ^ 2 / 10000000)
  have hP7 : ∀ (p : BdryParamsSlim_BSTD1) (hc : C7 p), _ := fun p hc =>
    hP p.toBdryParamsVol_BSTD1 hc.1 p.b hc.2.1.1 hc.2.1.2.1
      ((hc.2.1.2.2.1).trans_eq (dite_eq_left hc.1.1.1.1))
      ((hc.2.1.2.2.2.1).trans_eq (dite_eq_left hc.1.1.1)) hc.2.1.2.2.2.2.1
      ((hc.2.1.2.2.2.2.2).trans_eq (dite_eq_left hc.1))
      ((hc.2.2.1.1).trans_eq (dite_eq_left hc.1.1.1.1)) hc.2.2.1.2.1 hc.2.2.1.2.2
      p.σs p.vs hc.2.2.2.1.1 hc.2.2.2.1.2.1 hc.2.2.2.1.2.2 hc.2.2.2.2.1 hc.2.2.2.2.2
  choose b₀ hb₀ hP using hP7
  let BZ : BdryParamsSlim_BSTD1 → ℝ := fun p => if hc : C7 p then b₀ p hc else 1
  -- `εr, δ', Λz (… β ζ cap)`
  let C8 : BdryParamsZero_BSTD1 → Prop := fun p =>
    C7 p.toBdryParamsSlim_BSTD1 ∧
    (p.β 2 = p.β₂ ∧ 0 < p.β 1 ∧ p.β 1 < BZ p.toBdryParamsSlim_BSTD1 ∧ p.β 1 < 1 ∧
      p.β 3 ≤ threeSplittingExclusionThreshold.{0, 0}) ∧
    (3 * ν ≤ p.β 3 ∧ 2 * p.β 1 ≤ ηC ∧ 2 * p.β 1 ≤ HE p.toBdryParamsScale_BSTD1 ∧
      2 * p.β 1 ≤ HS p.toBdryParamsScale_BSTD1 ∧ 1000000 * p.Δ * p.β 1 ^ 3 < 1 ∧
      3 * p.β 1 ≤ SS p.toBdryParamsScale_BSTD1 ∧ p.β 1 * (2 * (1950002 * p.Δ + 1)) ≤ 1 ∧
      p.β 1 ≤ θ ^ 2 / 10000000) ∧
    (p.β 1 < p.ζ ∧ p.ζ < 1 ∧ 0 < p.cap)
  have hP8 : ∀ (p : BdryParamsZero_BSTD1) (hc : C8 p), _ := fun p hc =>
    hP p.toBdryParamsSlim_BSTD1 hc.1 p.β hc.2.1.1 hc.2.1.2.1
      ((hc.2.1.2.2.1).trans_eq (dite_eq_left hc.1)) hc.2.1.2.2.2.1 hc.2.1.2.2.2.2
      hc.2.2.1.1 hc.2.2.1.2.1
      ((hc.2.2.1.2.2.1).trans_eq (dite_eq_left hc.1.1.1.1.1))
      ((hc.2.2.1.2.2.2.1).trans_eq (dite_eq_left hc.1.1.1.1.1)) hc.2.2.1.2.2.2.2.1
      ((hc.2.2.1.2.2.2.2.2.1).trans_eq (dite_eq_left hc.1.1.1.1.1))
      hc.2.2.1.2.2.2.2.2.2.1 hc.2.2.1.2.2.2.2.2.2.2
      p.ζ p.cap hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2
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
  refine ⟨⟨⟨δStar, a₂, B0, S0, D0, T0, BC, A0, B1, W0, BD, BZ, ER, DP, LZ, hδStar, ha₂,
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
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (hΛ' p) one_pos⟩, σC, ηC, SE, HE, SS, HS, hσC, hηC,
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (hσE p) one_pos,
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (hηE p) one_pos,
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (hσS p) one_pos,
    fun p => dite_mem_BSTD1 (fun x => 0 < x) (hηS p) one_pos⟩, fun E S => ?_⟩
  -- the producer's conditions at `E`, stage by stage
  have hc1 : C1 E.γ := ⟨E.γ_pos, E.γ_lt, E.γ_le_θ⟩
  have hc2 : C2 E.toBdryParamsCollar_BSTD1 := ⟨hc1, E.βc_pos, E.βc_lt, E.γc_pos, E.γc_lt⟩
  have hc3 : C3 E.toBdryParamsScale_BSTD1 :=
    ⟨hc2, ⟨E.β₂_pos, E.β₂_le, E.β₂_lt, E.Δ_gt, E.Δ_ge⟩, E.three_β₂_le_σC, E.β₂_le_θ⟩
  have hc4 : C4 E.toBdryParamsEdge_BSTD1 :=
    ⟨hc3, ⟨E.σc_pos, E.σc_le, E.σc_lt, E.ε_pos, E.ε_lt, E.μ_pos, E.μ_le, E.τ_pos, E.τ_le,
      E.τ_sqrt, E.ε_le8, E.μ_le8⟩, ⟨E.μΔ_le_θ, E.σc_le_θ⟩,
      ⟨E.s_pos, E.s_lt, E.s_lt_b', E.s_lt_s', E.b'_lt, E.s'_lt, E.b'_lt_τ, E.s'_lt_τ⟩⟩
  have hc5 : C5 E.toBdryParamsLip_BSTD1 :=
    ⟨hc4, ⟨E.σ_pos, E.σ_le_a₂, E.σ_le_thr, E.σ_le_a₀⟩,
      ⟨E.Λ_pos, E.Λ_c1, E.Λ_c2, E.Λ_c3, E.budget, E.Λ_c5, E.Λ_c6⟩⟩
  have hc6 : C6 E.toBdryParamsVol_BSTD1 := ⟨hc5, E.w_pos, E.w_lt, E.w_lt_pi⟩
  have hc7 : C7 E.toBdryParamsSlim_BSTD1 :=
    ⟨hc6, ⟨E.b_pos, E.b_lt_s, E.b_lt_bc₀, E.b_lt_b₁, E.b_inv, E.b_lt_bd₀⟩,
      ⟨E.three_b_le_σE, E.b_mul_le, E.b_le_θ⟩, ⟨E.σs_pos, E.σs_le, E.vs_pos⟩,
      ⟨E.vs_le_θ, E.σs_le_θ⟩⟩
  have hc8 : C8 E.toBdryParamsZero_BSTD1 :=
    ⟨hc7, ⟨E.β_two, E.β₁_pos, E.β₁_lt_b₀, E.β₁_lt, E.β_three⟩,
      ⟨E.three_ν_le, E.two_β₁_le_ηC, E.two_β₁_le_ηE, E.two_β₁_le_ηS, E.Δβ₁_lt,
        E.three_β₁_le_σS, E.β₁_mul_le, E.β₁_le_θ⟩, ⟨E.β₁_lt_ζ, E.ζ_lt, E.cap_pos⟩⟩
  have eLZ : LZ E.toBdryParamsZero_BSTD1 = Λ' E.toBdryParamsZero_BSTD1 hc8 := dite_eq_left hc8
  have hT : 20 * Λ' E.toBdryParamsZero_BSTD1 hc8 ≤ E.T := by
    rw [← eLZ]
    exact E.T_ge
  obtain ⟨V, hTV, δ, hδ, hδδ', hev⟩ := hP E.toBdryParamsZero_BSTD1 hc8 E.T E.T_pos hT E.e E.e_pos
    E.e_lt S.δ₀ S.δ₀_pos S.δ₀_le S.W S.g S.B S.coll S.der
  have eDP : E.δ' = δ' E.toBdryParamsZero_BSTD1 hc8 := dite_eq_left hc8
  have eER : E.εr = εr E.toBdryParamsZero_BSTD1 hc8 := dite_eq_left hc8
  have eΛz : E.Λz = Λ' E.toBdryParamsZero_BSTD1 hc8 := dite_eq_left hc8
  have eSE : SE E.toBdryParamsScale_BSTD1 = σE E.toBdryParamsScale_BSTD1 hc3 := dite_eq_left hc3
  have eSS : SS E.toBdryParamsScale_BSTD1 = σS E.toBdryParamsScale_BSTD1 hc3 := dite_eq_left hc3
  refine ⟨V, hTV, δ, hδ, hδδ'.trans_eq eDP.symm,
    fun Lmax hLmax o1 o2 o3 βd εN hβd hεN hεNθ => ?_⟩
  rw [eER, eΛz]
  exact hev Lmax hLmax o1 (eSE ▸ o2) (eSS ▸ o3) βd εN hβd hεN hεNθ

/-- **The joint (BA) thresholds for every `(θ, ν)`**: the range conditions `0 < θ < 1`,
`0 < ν < 10⁻⁶` are read AFTER the record (outside the range the record is lane BSTG-D1's
`bdryThresholds_BSTD1` with unit extras, and the continuation is vacuous). -/
theorem exists_bdryThresholdsBA_BSTD2 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) (θ ν : ℝ) :
    ∃ Θ : BoundaryProducerThresholdsBA_BSTD2, 0 < θ → θ < 1 → 0 < ν → ν < 1 / 1000000 →
      ∀ (E : BoundaryEarlyOverBA_BSTD2 Θ θ ν) (S : BoundaryStandingSequence_BSTD1 K A Θ.δStar),
      ∃ V : ℝ, E.T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < E.δ' ∧ ∀ Lmax : ℝ, 0 < Lmax → Θ.σC⁻¹ ≤ Lmax →
      (Θ.SE E.toBdryParamsScale_BSTD1)⁻¹ ≤ Lmax → (Θ.SS E.toBdryParamsScale_BSTD1)⁻¹ ≤ Lmax →
      ∀ βd εN : ℝ, 0 < βd → 0 < εN → εN ≤ θ ^ 2 / 40000000 → ∀ᶠ n in atTop,
        BoundaryPacketsOutBA_BSTD2 (S.W n) (S.g n) K A (boundaryCounterexampleRatio S.δ₀ (n + 1))
          (S.B n) ((n + 1 : ℕ) : ℝ) E.Λ E.w E.β E.Δ E.σs E.σc E.μ E.b E.s E.b' E.s' E.ε E.γc E.βc
          Lmax E.τ E.γ δ E.εr E.e E.T V E.vs E.ζ E.Λz βd εN θ := by
  by_cases h : 0 < θ ∧ θ < 1 ∧ 0 < ν ∧ ν < 1 / 1000000
  · obtain ⟨Θ, hΘ⟩ := exists_bdryThresholdsBA_of_BSTD2 K hK A hA h.1 h.2.1 h.2.2.1 h.2.2.2
    exact ⟨Θ, fun _ _ _ _ => hΘ⟩
  · refine ⟨⟨bdryThresholds_BSTD1 K hK A hA, 1, 1, fun _ => 1, fun _ => 1, fun _ => 1,
      fun _ => 1, one_pos, one_pos, fun _ => one_pos, fun _ => one_pos, fun _ => one_pos,
      fun _ => one_pos⟩, fun hθ hθ1 hν hν1 => absurd ⟨hθ, hθ1, hν, hν1⟩ h⟩

/-- **The exported joint (BA) thresholds** (top-level Skolem data at `(K, A, θ, ν)`, total in
`(θ, ν)`). -/
def bdryThresholdsBA_BSTD2 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) (θ ν : ℝ) :
    BoundaryProducerThresholdsBA_BSTD2 :=
  Classical.choose (exists_bdryThresholdsBA_BSTD2 K hK A hA θ ν)

/-- **The early choices of the joint (BA) assignment**: the early choices over the exported joint
thresholds at `(K, A, θ, ν)`. -/
abbrev BoundaryEarlyChoicesBA_BSTD2 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) (θ ν : ℝ) : Type :=
  BoundaryEarlyOverBA_BSTD2 (bdryThresholdsBA_BSTD2 K hK A hA θ ν) θ ν

/-- **Every legal early choice has the joint producer's continuation** (`early` an input; the range
conditions of `(θ, ν)` as arguments). -/
theorem bdry_early_continuationBA_BSTD2 {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {θ ν : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1 / 1000000)
    (E : BoundaryEarlyChoicesBA_BSTD2 K hK A hA θ ν)
    (S : BoundaryStandingSequence_BSTD1 K A (bdryThresholdsBA_BSTD2 K hK A hA θ ν).δStar) :
    ∃ V : ℝ, E.T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < E.δ' ∧ ∀ Lmax : ℝ, 0 < Lmax →
      (bdryThresholdsBA_BSTD2 K hK A hA θ ν).σC⁻¹ ≤ Lmax →
      ((bdryThresholdsBA_BSTD2 K hK A hA θ ν).SE E.toBdryParamsScale_BSTD1)⁻¹ ≤ Lmax →
      ((bdryThresholdsBA_BSTD2 K hK A hA θ ν).SS E.toBdryParamsScale_BSTD1)⁻¹ ≤ Lmax →
      ∀ βd εN : ℝ, 0 < βd → 0 < εN → εN ≤ θ ^ 2 / 40000000 → ∀ᶠ n in atTop,
        BoundaryPacketsOutBA_BSTD2 (S.W n) (S.g n) K A (boundaryCounterexampleRatio S.δ₀ (n + 1))
          (S.B n) ((n + 1 : ℕ) : ℝ) E.Λ E.w E.β E.Δ E.σs E.σc E.μ E.b E.s E.b' E.s' E.ε E.γc E.βc
          Lmax E.τ E.γ δ E.εr E.e E.T V E.vs E.ζ E.Λz βd εN θ :=
  Classical.choose_spec (exists_bdryThresholdsBA_BSTD2 K hK A hA θ ν) hθ hθ1 hν hν1 E S

end DifferentialGeometry.Geometry.Collapse
