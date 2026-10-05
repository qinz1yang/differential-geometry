import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4RowsStrategy
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4Provenance
import DifferentialGeometry.Geometry.Fibration.ActualWholeSupportCount

/-!
# The register slot `early.N` dominates the whole support-list counts (lane C14-COUNT)

Review 57 §4.1 (row "N": `N_ge` binds `gafMultiplicity`; after the whole-list count is supplied it
must be shown that `N` dominates it) and §6.3; blueprint PBR01 PR01–PR03 (B:10078–10086): "Let `N`
dominate LPA06, SGP01, EGP02 and TCP01's WHOLE support-list counts … Thus `N` precedes `Δ`."

* `early_N_dominates_tcp01_CNT`: `gafMultiplicity ≤ N` (the register field `N_ge`) gives
  `N_TCP + 1 ≤ N` (`tcp01SupportBound_add_one_CNT`: `gafMultiplicity = N_TCP + 1`, the `+1` being
  TCP01's zero slot).
* `PartialClosedThresholdValidityV4.tcp01SupportBound_lt_N_CNT`: the same, read off the validity
  record.
* `earlyDataSharedV4_N_eq_CNT`: the shared early data of register V4 has `N = N_TCP + 1`.
* `lmax_of_below_CNT`: at every register of a strategy below the 11-row strategy, the curvature
  buffer radius of the packing, `4(10 + 4·10⁶Δ + Δ/3)`, is below the register's `Lmax`.
* `wholeSupportCounts_of_below_CNT` (**the entry point for FC39-V4C**): at every register `R` of a
  strategy below `partialRowsStrategyV4 D` with `gafMultiplicity ≤ D.N`, and every final family `P`
  at `R`'s values: `N_TCP + 1 ≤ D.N`; at every point `i` TCP01's three lists number at most `N_TCP`,
  at most one zero support meets `B(i, 10ρ(i))`, and all four together at most `D.N`; EGP02's and
  SGP01's whole lists and LPA06's pointwise count are at most `N_TCP`.
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

/-- **The early `N` dominates `N_TCP` with the zero slot**: `gafMultiplicity ≤ N` gives
`N_TCP + 1 ≤ N`. -/
theorem early_N_dominates_tcp01_CNT {N : ℕ} (hN : gafMultiplicity ≤ N) :
    tcp01SupportBound + 1 ≤ N := by
  rw [tcp01SupportBound_add_one_CNT]
  exact hN

/-- The validity record's `N_ge` makes `D.N` dominate `N_TCP` and the zero slot. -/
theorem PartialClosedThresholdValidityV4.tcp01SupportBound_lt_N_CNT {K : ℕ} {A : ℝ → ℝ}
    {Wseq : ℕ → CompactCarrier.{u}}
    {gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier} {D : ClosedEarlyData}
    {T : ClosedThresholdsV4 D} (hv : PartialClosedThresholdValidityV4 K A Wseq gseq D T) :
    tcp01SupportBound + 1 ≤ D.N :=
  early_N_dominates_tcp01_CNT hv.N_ge

/-- The shared early data of register V4 has `N = N_TCP + 1`. -/
theorem earlyDataSharedV4_N_eq_CNT (K : ℕ) : (earlyDataSharedV4 K).N = tcp01SupportBound + 1 :=
  tcp01SupportBound_add_one_CNT.symm

/-- At every register of a strategy below the 11-row strategy, the packing's buffer radius
`4(10 + 4·10⁶Δ + Δ/3)` is below `Lmax`. -/
theorem lmax_of_below_CNT {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
    (hTU : ClosedStrategyBelowV4 T (partialRowsStrategyV4 D)) (R : ClosedRegisterV4 D T) :
    4 * (10 + 2 * (2000000 * R.later.excl.Δ) + R.later.excl.Δ / 3) < R.later.Lmax := by
  have hLU := (hTU.LmaxLow_ge _ _ _ _ _ _).trans_lt ((le_max_right _ _).trans_lt R.later.Lmax_gt)
  simp only [partialRowsStrategyV4, max_lt_iff] at hLU
  exact hLU.1

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14R_CNT {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14R_CNT {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14R_CNT {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **The register slot `early.N` and the whole support-list counts** (PR01, B:10078–10086; review
57 §4.1 "N" and §6.3): at every register `R` of a strategy below the 11-row strategy, with the
validity field `gafMultiplicity ≤ D.N`, and every final family `P` at `R`'s values,
1. `N_TCP + 1 ≤ D.N`;
2. at every point `i`, TCP01's lists `J₂(i), J_e(i), J_s(i)` (closed supports meeting
   `B(i, 10ρ(i))`) number at most `N_TCP`, at most one zero support meets `B(i, 10ρ(i))`, and all
   of them together number at most `D.N`;
3. at every point `i`, EGP02's whole lists at `B(i, 20Δρ(i))` number at most `N_TCP`;
4. at every point `i`, SGP01's whole list at `B(i, .95·10⁶Δρ(i))` numbers at most `N_TCP`;
5. at every point `x`, LPA06's pointwise circle + slim + edge count is at most `N_TCP`. -/
theorem wholeSupportCounts_of_below_CNT {D : ClosedEarlyData} (hN : gafMultiplicity ≤ D.N)
    {T : ClosedThresholdsV4 D} (hTU : ClosedStrategyBelowV4 T (partialRowsStrategyV4 D))
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
        (P.edge.centres ∩ {j | x ∈ tsupport (P.edge.cutoff j)}).ncard ≤ tcp01SupportBound) := by
  have hΔ1 : 1 ≤ R.later.excl.Δ :=
    ((by norm_num : (1 : ℝ) < 100).trans R.later.hundred_lt_Δ_VAL6).le
  have hΛ0 : 0 ≤ R.later.scale.Λ := R.later.Λ_pos.le
  have hLΛ : 1000000 * R.later.excl.Δ * R.later.scale.Λ < 1 / 100000 := by
    have h := R.later.regScale_L
    unfold closedLongLength at h
    linarith
  have hT1600 : 1600 * (1000000 * R.later.excl.Δ) ≤ R.later.split.T₀ := by
    have h := (le_max_left _ _).trans R.later.T₀_ge
    unfold closedLongLength at h
    linarith
  have he40 : R.later.err.co.e₀ < 1 / 40 := R.later.e₀_lt_VAL6
  have hL := (lmax_of_below_CNT hTU R).le
  have hNT := early_N_dominates_tcp01_CNT hN
  refine ⟨hNT, fun i => ?_, fun i => ?_, fun i => ?_, fun x => ?_⟩
  · obtain ⟨h3, hz⟩ := tcp01_support_count_C14 P hΛ0 hΔ1 hLΛ hL he40 hT1600 i
    exact ⟨h3, hz, by omega⟩
  · exact P.toLocalChartFamilyQ.egp02_whole_count_CNT hΛ0 hΔ1 hLΛ hL i
  · exact P.toLocalChartFamilyQ.sgp01_whole_count_CNT hΛ0 hΔ1 hLΛ hL i
  · exact P.toLocalChartFamilyQ.lpa06_pointwise_le_CNT hΛ0 hΔ1 hLΛ hL x

end DifferentialGeometry.Geometry.Collapse
