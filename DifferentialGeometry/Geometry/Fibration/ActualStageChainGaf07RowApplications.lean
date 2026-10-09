import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07Row
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsEZ

/-!
# Consumers of GAF07's row on the final closed family

Blueprint `master207B.tex`, GAF07 (B:6049–6165); the row is `Gaf02ChainEJA.gaf07_row_GAFD`. Each
consumer states, as its conclusion, the row's statement instantiated at the chain in question
(`type_of% (Gaf02ChainEJA.gaf07_row_GAFD …)`; no named `Prop`).

* `gaf07_row_C14Z_GAFD`: for a packet `P_Z` of the FINAL family `LocalChartPacketsC14Z` and a chain
  with (JA) on its `LocalChartPacketsC14` projection (review 71 D71-3), with the family's OWN
  orientation `oM`; the numerical inputs (TCP01 range `β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10`; `K ≥ 5`) stay as
  hypotheses on the packet constants.
* `exists_closedChainEZRowsSource_tcp01_GAFD` (helper): register V4's rows' source with the
  register's TCP01 numerics `β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10`.
* `eventually_gaf07_rowsSourceZ_GAFD` (tail form, (JA)): on every closed standing sequence, at the
  strategy of register V4 (`register_yields_chainEJAZ_RGC`), every register has, on a tail of
  members, a nonempty model on which for every base point the ONE rows' source `S` satisfies the
  WHOLE GAF07 row; the numerical inputs are DISCHARGED there (stated as existentials over their
  proofs): `β₂ ≤ 10⁻⁷` and `γ + β₂ < 1/10` from the register's TCP01 numerics
  (`0 < γ < 1/100`, `β₂ ≤ γ/2`, `β₂ ≤ 10⁻⁷`), `5 ≤ K` from `10 ≤ K`, and `oM` is the model's
  orientation `M.orientation_RGC` (the one stored in `P_Z`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **GAF07 on the final closed family** (D71-3): for every packet `P_Z` of
`LocalChartPacketsC14Z` (orientation parameter `oM`) with the TCP01 range and `K ≥ 5`, and every
chain with (JA) on its `LocalChartPacketsC14` projection, the whole GAF07 row holds. -/
theorem gaf07_row_C14Z_GAFD {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    (PZ : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}
    (C : Gaf02ChainEJA PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K) :
    type_of% (Gaf02ChainEJA.gaf07_row_GAFD C hβ hd hK oM) :=
  by exact C.gaf07_row_GAFD hβ hd hK oM

/-- **Register V4's rows' source together with its TCP01 numerics** (helper of the tail form): at
register V4's strategy, every register has `β₂ ≤ 10⁻⁷` and `γ + β₂ < 1/10` (from `0 < γ < 1/100`,
`β₂ ≤ γ/2`, `β₂ ≤ 10⁻⁷`) and, on its tail, nonempty models carrying a rows' source at every base
point (`exists_closedChainEZRowsSource_RGC`'s construction). -/
theorem exists_closedChainEZRowsSource_tcp01_GAFD (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T,
        (R.β 2 ≤ 1 / 10000000 ∧ R.later.circle.γ + R.β 2 < 1 / 10) ∧
        ∃ εr δ Λz : ℝ, ∀ m, R.later.tail ≤ m →
          ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧ ∀ x₀ : M.X,
            ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ := by
  obtain ⟨T, hv, hTU, -, -, -, hR⟩ := register_yields_chainEJAZ_RGC K hK A hA Wseq gseq hf hg
  refine ⟨T, hTU, hv, fun R => ?_⟩
  obtain ⟨⟨-, -, -, -, ⟨-, hγ1, hβγ, hβ7⟩, -⟩, εr, -, Λz, δc, -, -, ht⟩ := hR R
  refine ⟨⟨by norm_num at hβ7 ⊢; exact hβ7, by linarith⟩, εr, δc, Λz, fun m hm => ?_⟩
  obtain ⟨M, F, -, -, -, -, -, -, hchain⟩ := ht m hm
  have : ConnectedSpace (Wseq m).Carrier := (hf m).connected
  refine ⟨M, ⟨M.ψ.symm (Classical.arbitrary (Wseq m).Carrier)⟩, fun x₀ => ?_⟩
  obtain ⟨C, hC, -⟩ := hchain x₀
  exact ⟨⟨F, C⟩, hC⟩

/-- **GAF07 on the rows' source of every register, on a tail** ((JA), final family C14Z, numerical
inputs discharged): at register V4's strategy, every register has `ε_r, δ, Λ_z` such that for all
large members `m` there is a nonempty model on which, for every base point `x₀`, the rows' source
`S` with `S.chain.x₀ = x₀` satisfies the whole GAF07 row, its TCP01 range and `K ≥ 5` holding. -/
theorem eventually_gaf07_rowsSourceZ_GAFD (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, ∀ᶠ m in atTop,
        ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧ ∀ x₀ : M.X,
          ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            ∃ (hβ : R.β 2 ≤ 1 / 10000000) (hd : R.later.circle.γ + R.β 2 < 1 / 10) (h5 : 5 ≤ K),
              type_of% (Gaf02ChainEJA.gaf07_row_GAFD S.chain hβ hd h5 M.orientation_RGC) := by
  have key := exists_closedChainEZRowsSource_tcp01_GAFD K hK A hA Wseq gseq hf hg
  have h5 : 5 ≤ K := by omega
  refine key.imp fun T hT => ⟨hT.1, hT.2.1, fun R => ?_⟩
  exact (hT.2.2 R).2.imp fun εr h => h.imp fun δ h => h.imp fun Λz ht =>
    eventually_atTop.mpr ⟨R.later.tail, fun m hm => (ht m hm).imp fun M hM =>
      ⟨hM.1, fun x₀ => (hM.2 x₀).imp fun S hS =>
        ⟨hS, (hT.2.2 R).1.1, (hT.2.2 R).1.2, h5,
          by exact S.chain.gaf07_row_GAFD (hT.2.2 R).1.1 (hT.2.2 R).1.2 h5 M.orientation_RGC⟩⟩⟩

end DifferentialGeometry.Geometry.Collapse
