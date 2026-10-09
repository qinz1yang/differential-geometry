import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdp02RowEDP23
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeBaseExactApplicationsEDP23

/-!
# Consumers of EDP02's row on the final closed family

Blueprint `master207B.tex`, EDP02 (B:6748–6835); the row is `Gaf02ChainE.edp02_row_EDP23`
(group G2 of lane S-EDP02-03). Each consumer states, as its conclusion, the row instantiated at
the chain in question (`type_of% (Gaf02ChainE.edp02_row_EDP23 …)`; it elaborates to the full
conjunction of the row — no named `Prop`).

* `edp02_row_C14Z_EDP23`: for a chain on the `LocalChartPacketsC14` projection of a packet of the
  FINAL family `LocalChartPacketsC14Z` (D71-3).
* `eventually_edp02_row_rowsSourceZ_EDP23` (tail form): on every closed standing sequence, at the
  strategy of `exists_closedChainEZRowsSource_RGC`, every register has, on a tail of members
  (`∀ᶠ m in atTop`), a nonempty model on which, for every base point, the closed rows' source `S`
  satisfies the whole row (`Δ ≥ 2` read off `Δ > 10⁶` of the register).
* `exists_edp02_row_dihedralTiny_EDP23`: ALL premises hold at once on the dihedral final-family
  fixture (`Δ = 1200`). KNOWN ACCEPTANCE GAP (D71-7 / D70-8): the fixture's circle, edge and slim
  families are EMPTY, so `W₂ = ∅`, `B₂ = X₂ = ∅` and every clause of the row is vacuously true
  there (the clause about the final fibre is an implication with a false premise).
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

/-- **EDP02's row on the final closed family** (D71-3): for every packet of
`LocalChartPacketsC14Z` and every enhanced chain on its `LocalChartPacketsC14` projection. -/
theorem edp02_row_C14Z_EDP23 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    (PZ : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (Ĉ : Gaf02ChainE PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hΔ : 2 ≤ Δ) : type_of% (Ĉ.edp02_row_EDP23 hΔ) :=
  Ĉ.edp02_row_EDP23 hΔ

/-- **EDP02's row at the closed rows' source of every register, on a tail** (final family C14Z):
at the strategy of `exists_closedChainEZRowsSource_RGC`, every register has `ε_r, δ, Λ_z` such that
for all large members `m` there is a nonempty model on which, for every base point `x₀`, the rows'
source `S` with `S.chain.x₀ = x₀` satisfies the whole EDP02 row. -/
theorem eventually_edp02_row_rowsSourceZ_EDP23 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
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
            type_of% (S.chain.toGaf02ChainE.edp02_row_EDP23 R.two_le_Δ_EDP23) := by
  have key := exists_closedChainEZRowsSource_RGC K hK A hA Wseq gseq hf hg
  obtain ⟨T, hTU, hv, h1, h2, hR⟩ := key
  refine ⟨T, hTU, hv, fun R => ?_⟩
  exact (hR R).imp fun εr h => h.imp fun δ h => h.imp fun Λz ht =>
    eventually_atTop.mpr ⟨R.later.tail, fun m hm => (ht m hm).imp fun M hM =>
      ⟨hM.1, fun x₀ => (hM.2 x₀).imp fun S hS =>
        ⟨hS, by exact S.chain.toGaf02ChainE.edp02_row_EDP23 R.two_le_Δ_EDP23⟩⟩⟩

section Dihedral

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- **All premises of EDP02's row hold at once** on the dihedral final-family fixture
(`Δ = 1200`): a chain with (JA) exists there and the row holds for it. The fixture's circle, edge
and slim families are EMPTY (stated), so the clauses are vacuous on it — the known acceptance gap
(D71-7, D70-8). -/
theorem exists_edp02_row_dihedralTiny_EDP23 (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZ_CHI β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      (dihedralRowZ_CHI β₂ γc Lmax σs ζ h).circle.centres = ∅ ∧
        (dihedralRowZ_CHI β₂ γc Lmax σs ζ h).edge.centres = ∅ ∧
        (dihedralRowZ_CHI β₂ γc Lmax σs ζ h).slim.centres = ∅ ∧
        type_of% (C.toGaf02ChainE.edp02_row_EDP23 (by norm_num : (2 : ℝ) ≤ 1200)) := by
  exact (exists_gaf02ChainEJA_rowsZ_dihedralTiny_CHI Kj).imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun C _ => ⟨rfl, rfl, rfl,
      C.toGaf02ChainE.edp02_row_EDP23 (by norm_num : (2 : ℝ) ≤ 1200)⟩

end Dihedral

end DifferentialGeometry.Geometry.Collapse
