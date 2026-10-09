import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4WholeSupportCount
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4Rows

/-!
# `early.N` and the whole support-list counts on every instance of the record (lane C14-COUNTb)

Instance-level supply of the register slot `early.N` (review 57 §4.1 row "N", §6.3; PR01,
B:10078–10086) for the closed validity on register V4: the whole-list counts of
`wholeSupportCounts_of_below_CNT` on every `ClosedFamilyInstanceV4` / `ClosedFamilyInstanceC14DV4`
at every register of a strategy below the 11-row strategy, and the inhabited record together with
the counts.

* `wholeSupportCounts_of_below_rows_CNTb`: the same conclusion for strategies below
  `rowsStrategyV4` (the strategy of `exists_partialClosedThresholdValidityV4Rows_VAL6` and of the
  staged record).
* `ClosedFamilyInstanceV4.wholeSupportCounts_CNTb`,
  `ClosedFamilyInstanceC14DV4.wholeSupportCounts_CNTb`:
  on one instance of the final family at `R` (`LocalChartPacketsC14` resp. `LocalChartPacketsC14D`).
* `PartialClosedThresholdValidityV4.wholeSupportCounts_CNTb` (**the FC39-V4C(b) entry point**): the
  validity record's `N_ge` gives, on every instance at every register below the 11-row strategy,
  `N_TCP + 1 ≤ N`, TCP01's three lists `≤ N_TCP`, the zero list `≤ 1`, all four `≤ N`, EGP02's and
  SGP01's whole lists `≤ N_TCP` and LPA06's pointwise count `≤ N_TCP`.
* Consumer `exists_partialClosedThresholdValidityV4Rows_wholeCounts_CNTb`: at `earlyDataSharedV4 K`
  on every closed standing sequence, one strategy `T` at which the record
  `PartialClosedThresholdValidityV4Rows` holds AND, on every instance at every register, TCP01's
  whole lists with the zero slot number at most `N`.
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

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- Every strategy below the rows strategy is below the 11-row strategy. -/
theorem ClosedStrategyBelowV4.below_partialRows_CNTb {D : ClosedEarlyData}
    {T : ClosedThresholdsV4 D} (hTU : ClosedStrategyBelowV4 T (rowsStrategyV4 D)) :
    ClosedStrategyBelowV4 T (partialRowsStrategyV4 D) :=
  hTU.trans_VAL6 ((ClosedThresholdsV4.inf_below_left_VAL6 _ _).trans_VAL6
    (ClosedThresholdsV4.inf_below_right_VAL6 _ _))

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14I_CNTb {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14I_CNTb {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14I_CNTb {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- `wholeSupportCounts_of_below_CNT` for strategies below the rows strategy. -/
theorem wholeSupportCounts_of_below_rows_CNTb {D : ClosedEarlyData} (hN : gafMultiplicity ≤ D.N)
    {T : ClosedThresholdsV4 D} (hTU : ClosedStrategyBelowV4 T (rowsStrategyV4 D))
    (R : ClosedRegisterV4 D T) {K : ℕ} {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {δ εr Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ R.later.scale.Λ R.β R.later.excl.Δ
      R.later.err.co.qs K R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc R.later.circle.βc
      R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀ R.later.split.T₀
      R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz) :
    tcp01SupportBound + 1 ≤ D.N ∧
    (∀ i : X,
      (tcp01CircleList P.toLocalChartFamily i).ncard +
          (tcp01EdgeList P.toLocalChartFamily i).ncard +
          (tcp01SlimList P.toLocalChartFamily i).ncard ≤ tcp01SupportBound ∧
        (zeroMeetingList P.zero i 10).ncard ≤ 1 ∧
        (tcp01CircleList P.toLocalChartFamily i).ncard +
            (tcp01EdgeList P.toLocalChartFamily i).ncard +
            (tcp01SlimList P.toLocalChartFamily i).ncard +
            (zeroMeetingList P.zero i 10).ncard ≤ D.N) ∧
    (∀ i : X, (egpEdgeList P.toLocalChartFamily i).ncard +
        (egpSlimList P.toLocalChartFamily i).ncard ≤ tcp01SupportBound) ∧
    (∀ i : X, (sgpSlimList P.slim i).ncard ≤ tcp01SupportBound) ∧
    (∀ x : X, (P.circle.centres ∩ {j | x ∈ tsupport (P.circle.cutoff j)}).ncard +
        (P.slim.centres ∩ {j | x ∈ tsupport (P.slim.cutoff j)}).ncard +
        (P.edge.centres ∩ {j | x ∈ tsupport (P.edge.cutoff j)}).ncard ≤ tcp01SupportBound) :=
  wholeSupportCounts_of_below_CNT hN hTU.below_partialRows_CNTb R P

/-- **The whole support-list counts on one instance of the final family at `R`**
(`ClosedFamilyInstanceV4`, family `LocalChartPacketsC14` at the register's values). -/
theorem ClosedFamilyInstanceV4.wholeSupportCounts_CNTb {K : ℕ} {D : ClosedEarlyData}
    (hN : gafMultiplicity ≤ D.N) {T : ClosedThresholdsV4 D}
    (hTU : ClosedStrategyBelowV4 T (partialRowsStrategyV4 D)) {R : ClosedRegisterV4 D T}
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g}
    {δ εr Λz : ℝ} (F : ClosedFamilyInstanceV4 K R M δ εr Λz) :
    tcp01SupportBound + 1 ≤ D.N ∧
    (∀ i : M.X,
      (tcp01CircleList F.family.toLocalChartFamily i).ncard +
          (tcp01EdgeList F.family.toLocalChartFamily i).ncard +
          (tcp01SlimList F.family.toLocalChartFamily i).ncard ≤ tcp01SupportBound ∧
        (zeroMeetingList F.family.zero i 10).ncard ≤ 1 ∧
        (tcp01CircleList F.family.toLocalChartFamily i).ncard +
            (tcp01EdgeList F.family.toLocalChartFamily i).ncard +
            (tcp01SlimList F.family.toLocalChartFamily i).ncard +
            (zeroMeetingList F.family.zero i 10).ncard ≤ D.N) ∧
    (∀ i : M.X, (egpEdgeList F.family.toLocalChartFamily i).ncard +
        (egpSlimList F.family.toLocalChartFamily i).ncard ≤ tcp01SupportBound) ∧
    (∀ i : M.X, (sgpSlimList F.family.slim i).ncard ≤ tcp01SupportBound) ∧
    (∀ x : M.X, (F.family.circle.centres ∩ {j | x ∈ tsupport (F.family.circle.cutoff j)}).ncard +
        (F.family.slim.centres ∩ {j | x ∈ tsupport (F.family.slim.cutoff j)}).ncard +
        (F.family.edge.centres ∩ {j | x ∈ tsupport (F.family.edge.cutoff j)}).ncard ≤
          tcp01SupportBound) :=
  wholeSupportCounts_of_below_CNT hN hTU R F.family

/-- **The whole support-list counts on one complete instance** (`ClosedFamilyInstanceC14DV4`, final
family `LocalChartPacketsC14D`, counted on its projection `toLocalChartPacketsC14`). -/
theorem ClosedFamilyInstanceC14DV4.wholeSupportCounts_CNTb {K : ℕ} {D : ClosedEarlyData}
    (hN : gafMultiplicity ≤ D.N) {T : ClosedThresholdsV4 D}
    (hTU : ClosedStrategyBelowV4 T (partialRowsStrategyV4 D)) {R : ClosedRegisterV4 D T}
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g}
    {δ εr Λz : ℝ} (F : ClosedFamilyInstanceC14DV4 K R M δ εr Λz) :
    tcp01SupportBound + 1 ≤ D.N ∧
    (∀ i : M.X,
      (tcp01CircleList F.family.toLocalChartFamily i).ncard +
          (tcp01EdgeList F.family.toLocalChartFamily i).ncard +
          (tcp01SlimList F.family.toLocalChartFamily i).ncard ≤ tcp01SupportBound ∧
        (zeroMeetingList F.family.zero i 10).ncard ≤ 1 ∧
        (tcp01CircleList F.family.toLocalChartFamily i).ncard +
            (tcp01EdgeList F.family.toLocalChartFamily i).ncard +
            (tcp01SlimList F.family.toLocalChartFamily i).ncard +
            (zeroMeetingList F.family.zero i 10).ncard ≤ D.N) ∧
    (∀ i : M.X, (egpEdgeList F.family.toLocalChartFamily i).ncard +
        (egpSlimList F.family.toLocalChartFamily i).ncard ≤ tcp01SupportBound) ∧
    (∀ i : M.X, (sgpSlimList F.family.slim i).ncard ≤ tcp01SupportBound) ∧
    (∀ x : M.X, (F.family.circle.centres ∩ {j | x ∈ tsupport (F.family.circle.cutoff j)}).ncard +
        (F.family.slim.centres ∩ {j | x ∈ tsupport (F.family.slim.cutoff j)}).ncard +
        (F.family.edge.centres ∩ {j | x ∈ tsupport (F.family.edge.cutoff j)}).ncard ≤
          tcp01SupportBound) :=
  F.toC14_VAL6.wholeSupportCounts_CNTb hN hTU

/-- **The FC39-V4C(b) entry point for `early.N`**: the validity record's `N_ge` makes `N` dominate
the whole support-list counts on every instance of the final family at every register of a
strategy below the 11-row strategy (`N_TCP + 1 ≤ N`; TCP01's three lists `≤ N_TCP`, the zero list
`≤ 1`, all four `≤ N`; EGP02's and SGP01's whole lists and LPA06's pointwise count `≤ N_TCP`). -/
theorem PartialClosedThresholdValidityV4.wholeSupportCounts_CNTb {K : ℕ} {A : ℝ → ℝ}
    {Wseq : ℕ → CompactCarrier.{u}}
    {gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier} {D : ClosedEarlyData}
    {T : ClosedThresholdsV4 D} (hv : PartialClosedThresholdValidityV4 K A Wseq gseq D T)
    (hTU : ClosedStrategyBelowV4 T (partialRowsStrategyV4 D)) {R : ClosedRegisterV4 D T}
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g}
    {δ εr Λz : ℝ} (F : ClosedFamilyInstanceV4 K R M δ εr Λz) :
    tcp01SupportBound + 1 ≤ D.N ∧
    (∀ i : M.X,
      (tcp01CircleList F.family.toLocalChartFamily i).ncard +
          (tcp01EdgeList F.family.toLocalChartFamily i).ncard +
          (tcp01SlimList F.family.toLocalChartFamily i).ncard ≤ tcp01SupportBound ∧
        (zeroMeetingList F.family.zero i 10).ncard ≤ 1 ∧
        (tcp01CircleList F.family.toLocalChartFamily i).ncard +
            (tcp01EdgeList F.family.toLocalChartFamily i).ncard +
            (tcp01SlimList F.family.toLocalChartFamily i).ncard +
            (zeroMeetingList F.family.zero i 10).ncard ≤ D.N) ∧
    (∀ i : M.X, (egpEdgeList F.family.toLocalChartFamily i).ncard +
        (egpSlimList F.family.toLocalChartFamily i).ncard ≤ tcp01SupportBound) ∧
    (∀ i : M.X, (sgpSlimList F.family.slim i).ncard ≤ tcp01SupportBound) ∧
    (∀ x : M.X, (F.family.circle.centres ∩ {j | x ∈ tsupport (F.family.circle.cutoff j)}).ncard +
        (F.family.slim.centres ∩ {j | x ∈ tsupport (F.family.slim.cutoff j)}).ncard +
        (F.family.edge.centres ∩ {j | x ∈ tsupport (F.family.edge.cutoff j)}).ncard ≤
          tcp01SupportBound) :=
  F.wholeSupportCounts_CNTb hv.N_ge hTU

/-- **Consumer: the inhabited record with `early.N` dominating the whole lists.** At the early data
`earlyDataSharedV4 K`, on every closed standing sequence, one strategy `T` at which the record
`PartialClosedThresholdValidityV4Rows` holds and, on every instance of the final family at every
register, TCP01's whole lists `J₂, J_e, J_s` with the zero slot number at most `N`. -/
theorem exists_partialClosedThresholdValidityV4Rows_wholeCounts_CNTb (K : ℕ) (hK : 10 ≤ K)
    (A : ℝ → ℝ) (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      ∀ (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) (δ εr Λz : ℝ) (m : ℕ)
        (M : ClosedModel (Wseq m) (gseq m)) (F : ClosedFamilyInstanceV4 K R M δ εr Λz) (i : M.X),
        (tcp01CircleList F.family.toLocalChartFamily i).ncard +
            (tcp01EdgeList F.family.toLocalChartFamily i).ncard +
            (tcp01SlimList F.family.toLocalChartFamily i).ncard +
            (zeroMeetingList F.family.zero i 10).ncard ≤ (earlyDataSharedV4 K).N := by
  obtain ⟨hN, hP, hPs, hPz, hL₀, hΞ, hΞr, hC⟩ := earlyDataSharedV4_fields_VAL6 K
  obtain ⟨T, hTU, hH, hlc, hfam, hsc, hrows⟩ :=
    exists_closed_realization_rows_VAL6 K hK A hA Wseq gseq hf hg hC
  refine ⟨T, ⟨⟨hN, hP, hPs, hPz, hL₀, hΞ, hΞr, hlc, hTU.I₁_eq, fun m p => ?_, fun _ => hfam⟩,
    hC, hsc, fun R δ εr Λz hεr hΛz m M F => hrows R δ εr Λz hεr hΛz m M F⟩,
    fun R δ εr Λz m M F i =>
      ((F.wholeSupportCounts_CNTb hN hTU.below_VAL6.below_partialRows_CNTb).2.1 i).2.2⟩
  rw [hH m]
  exact closed_standing_clauses_VAL K A Wseq gseq hg m p

end DifferentialGeometry.Geometry.Collapse
