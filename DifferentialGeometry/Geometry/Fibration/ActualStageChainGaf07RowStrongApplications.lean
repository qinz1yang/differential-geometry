import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07RowStrong
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07RowApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07RowDihedral

/-!
# Consumers of GAF07's STRONG row on the final closed family

Blueprint `master207B.tex`, GAF07 (B:6049–6165); the row is `Gaf02ChainEJA.gaf07_row_strong_GAFD`.
Each consumer states, as its conclusion, the strong row instantiated at the chain in question
(`type_of% (Gaf02ChainEJA.gaf07_row_strong_GAFD …)`; no named `Prop`).

* `gaf07_row_strong_C14Z_GAFD`: packet `P_Z` of `LocalChartPacketsC14Z` kept (D71-3), its own `oM`.
* `eventually_gaf07_rowsSourceZ_strong_GAFD` (tail form at register V4's strategy; the numerical
  inputs discharged as in `eventually_gaf07_rowsSourceZ_GAFD`).
* `exists_gaf07_row_strong_dihedralTiny_GAFD`: all premises at once on the `K = 5` dihedral
  fixture; its stage families are EMPTY, so the stage clauses are vacuous there (D71-7 / D70-8).
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

/-- **GAF07's strong row on the final closed family** (D71-3; TCP01 range, `K ≥ 5`, the family's
own orientation). -/
theorem gaf07_row_strong_C14Z_GAFD {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    (PZ : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}
    (C : Gaf02ChainEJA PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K) :
    type_of% (Gaf02ChainEJA.gaf07_row_strong_GAFD C hβ hd hK oM) :=
  by exact C.gaf07_row_strong_GAFD hβ hd hK oM

/-- **GAF07's strong row on the rows' source of every register, on a tail** ((JA), final family
C14Z; the TCP01 range and `K ≥ 5` from the register, `oM` the model's orientation). -/
theorem eventually_gaf07_rowsSourceZ_strong_GAFD (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
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
              type_of% (Gaf02ChainEJA.gaf07_row_strong_GAFD S.chain hβ hd h5
                M.orientation_RGC) := by
  have key := exists_closedChainEZRowsSource_tcp01_GAFD K hK A hA Wseq gseq hf hg
  have h5 : 5 ≤ K := by omega
  refine key.imp fun T hT => ⟨hT.1, hT.2.1, fun R => ?_⟩
  exact (hT.2.2 R).2.imp fun εr h => h.imp fun δ h => h.imp fun Λz ht =>
    eventually_atTop.mpr ⟨R.later.tail, fun m hm => (ht m hm).imp fun M hM =>
      ⟨hM.1, fun x₀ => (hM.2 x₀).imp fun S hS =>
        ⟨hS, (hT.2.2 R).1.1, (hT.2.2 R).1.2, h5,
          by
            exact S.chain.gaf07_row_strong_GAFD (hT.2.2 R).1.1 (hT.2.2 R).1.2 h5
              M.orientation_RGC⟩⟩⟩

section Dihedral

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- **All premises of GAF07's strong row at once** on the `K = 5` dihedral final-family fixture
(stage families EMPTY, stated: the stage clauses are vacuous there, D71-7 / D70-8). -/
theorem exists_gaf07_row_strong_dihedralTiny_GAFD (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).circle.centres = ∅ ∧
        (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).edge.centres = ∅ ∧
        (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).slim.centres = ∅ ∧
        ∃ (hβ : dihedralTinyRowBeta_CHI β₂ 2 ≤ 1 / 10000000)
          (hd : (0 : ℝ) + dihedralTinyRowBeta_CHI β₂ 2 < 1 / 10) (h5 : 5 ≤ 5),
          type_of% (Gaf02ChainEJA.gaf07_row_strong_GAFD C hβ hd h5
            dihedralTinyOrientation_CHI) := by
  exact (exists_gaf02ChainEJA_rowsZ5_dihedralTiny_GAFD Kj).imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun C hC => ⟨rfl, rfl, rfl, (dihedralTinyRowBeta_two_CHI _).trans_le hC.2.1,
      by rw [zero_add, dihedralTinyRowBeta_two_CHI]; linarith [hC.2.1], le_rfl,
      by
        exact C.gaf07_row_strong_GAFD ((dihedralTinyRowBeta_two_CHI _).trans_le hC.2.1)
          (by rw [zero_add, dihedralTinyRowBeta_two_CHI]; linarith [hC.2.1]) le_rfl
          dihedralTinyOrientation_CHI⟩

end Dihedral

end DifferentialGeometry.Geometry.Collapse
