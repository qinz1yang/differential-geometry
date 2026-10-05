import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf06Row
import DifferentialGeometry.Geometry.Fibration.ActualStageChainRowsInhabitant
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsEZ

/-!
# Consumers of GAF06's row on the final closed family

Blueprint `master207B.tex`, GAF06 (B:6008–6047); the row is `Gaf02ChainEJA.gaf06_row_GAFD`. Each
consumer below states, as its conclusion, the row's statement instantiated at the chain in question
(written `type_of% (Gaf02ChainEJA.gaf06_row_GAFD …)`; it elaborates to the full conjunction of the
row — no named `Prop`).

* `gaf06_row_C14Z_GAFD`: for a chain with (JA) on the `LocalChartPacketsC14` projection of a packet
  `P_Z` of the FINAL family `LocalChartPacketsC14Z` (review 71 D71-3: the packet is kept, forgotten
  to `C14`, and the chain is built on it).
* `eventually_gaf06_rowsSourceZ_GAFD` (tail form, (JA)): on every closed standing sequence, at the
  strategy of `exists_closedChainEZRowsSource_RGC` (lane C14-REG-CHAINb), every register has, on a
  tail of members (`∀ᶠ m in atTop`), a nonempty model on which, for every base point, the ONE rows'
  source `S` (the C14Z instance `P_Z` and the chain with (JA) on `P_Z.toLocalChartPacketsC14`)
  satisfies GAF06.
* `exists_gaf06_row_dihedralTiny_GAFD`: ALL premises hold at once — a `Gaf02ChainEJA` exists on the
  dihedral final-family fixture (`exists_gaf02ChainEJA_rowsZ_dihedralTiny_CHI`) and GAF06 holds on
  it. KNOWN ACCEPTANCE GAP: the fixture's three stage families (circle, edge, slim) are EMPTY, so
  every stage clause of the row is vacuously true there (D71-7 / D70-8: no fixture with a nonempty
  stage family exists yet).
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

/-- **GAF06 on the final closed family** (D71-3): for every packet `P_Z` of
`LocalChartPacketsC14Z` and every chain with (JA) on its `LocalChartPacketsC14` projection, the
whole GAF06 row holds. -/
theorem gaf06_row_C14Z_GAFD {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    (PZ : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}
    (C : Gaf02ChainEJA PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj) :
    type_of% (Gaf02ChainEJA.gaf06_row_GAFD C) :=
  C.gaf06_row_GAFD

/-- **GAF06 on the rows' source of every register, on a tail** ((JA), final family C14Z): at the
strategy of `exists_closedChainEZRowsSource_RGC`, every register has `ε_r, δ, Λ_z` such that for
all large members `m` there is a nonempty model on which, for every base point `x₀`, the rows'
source `S` with `S.chain.x₀ = x₀` satisfies the whole GAF06 row. -/
theorem eventually_gaf06_rowsSourceZ_GAFD (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
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
            type_of% (Gaf02ChainEJA.gaf06_row_GAFD S.chain) := by
  have key := exists_closedChainEZRowsSource_RGC K hK A hA Wseq gseq hf hg
  obtain ⟨T, hTU, hv, h1, h2, hR⟩ := key
  refine ⟨T, hTU, hv, fun R => ?_⟩
  exact (hR R).imp fun εr h => h.imp fun δ h => h.imp fun Λz ht =>
    eventually_atTop.mpr ⟨R.later.tail, fun m hm => (ht m hm).imp fun M hM =>
      ⟨hM.1, fun x₀ => (hM.2 x₀).imp fun S hS =>
        ⟨hS, by exact S.chain.gaf06_row_GAFD⟩⟩⟩

section Dihedral

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- **All premises of GAF06 hold at once** on the dihedral final-family fixture: a chain with (JA)
exists there (`exists_gaf02ChainEJA_rowsZ_dihedralTiny_CHI`) and the row holds for it. The fixture's
circle, edge and slim families are EMPTY (stated), so the stage clauses are vacuous on it — the
known acceptance gap (D71-7, D70-8). -/
theorem exists_gaf06_row_dihedralTiny_GAFD (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZ_CHI β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      (dihedralRowZ_CHI β₂ γc Lmax σs ζ h).circle.centres = ∅ ∧
        (dihedralRowZ_CHI β₂ γc Lmax σs ζ h).edge.centres = ∅ ∧
        (dihedralRowZ_CHI β₂ γc Lmax σs ζ h).slim.centres = ∅ ∧
        type_of% (Gaf02ChainEJA.gaf06_row_GAFD C) := by
  exact (exists_gaf02ChainEJA_rowsZ_dihedralTiny_CHI Kj).imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun C _ => ⟨rfl, rfl, rfl, by exact C.gaf06_row_GAFD⟩

end Dihedral

end DifferentialGeometry.Geometry.Collapse
