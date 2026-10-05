import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMap
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedInterior

/-!
# The `…On` global block map is BAUG-A's interior formula (lane B-PORT-A, G1)

Hand-written companion of the generated `BoundaryPortGlobalBlockMap.lean`:

* on the enriched boundary base family `L : LocalPacketsOnB` the ported names are BAUG-A's
  weak-edge names (`cgpHeight_eq_edgeBHeight_BAUGP`, `cgpEdgeSum_eq_edgeBSum_BAUGP`,
  `cgpEdgeMarker_eq_edgeBMarker_BAUGP`, `cgpEdgeDomain_eq_edgeBDomain_BAUGP`), and the
  CGP01 smoothness / row hold WITHOUT the margin input: the edge zero-extension margin is BAUG-A's
  FC18 (ii) for `edgeB` (`contMDiff_cgpGlobalMap_family_BAUGP`, `cgp01_row_family_BAUGP`);
* on a stored supply `S : BoundarySupplyCore`: the interior tags ARE the ported tags
  (`intTag_eq_cgpTag_BAUGP`, with the scale / `E'` tags), and **BAUG-A's interior map is the
  ported global block map of the SAME active family** (`interiorMapOn_eq_cgpGlobalMap_BAUGP`):
  `S.interiorMapOn_BAUGA = cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero`;
* consumers: `contMDiff_interiorMapOn_BAUGP` (the interior formula is smooth on `W°`) and
  `interiorMapOn_scale_BAUGP` (its scale block is `ρ`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint
open DifferentialGeometry.Analysis DifferentialGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
    U₁ U₂ Ue₁ Ue₂)

/-- The ported `E'` height is BAUG-A's `t_B = edgeB.smoothing / ρ`. -/
theorem cgpHeight_eq_edgeBHeight_BAUGP : cgpHeight_BAUGP L = L.edgeBHeight_BAUGA :=
  rfl

/-- The ported edge sum is BAUG-A's `Σ_{I_e^B} ζ_i^B`. -/
theorem cgpEdgeSum_eq_edgeBSum_BAUGP : cgpEdgeSum_BAUGP L = L.edgeBSum_BAUGA :=
  rfl

/-- The ported `E'` marker is BAUG-A's `z_{E'}`. -/
theorem cgpEdgeMarker_eq_edgeBMarker_BAUGP : cgpEdgeMarker_BAUGP L = L.edgeBMarker_BAUGA :=
  rfl

/-- The ported collar domain is BAUG-A's `edgeB` collar domain. -/
theorem cgpEdgeDomain_eq_edgeBDomain_BAUGP : cgpEdgeDomain_BAUGP L = L.edgeBDomain_BAUGA :=
  rfl

/-- **CGP01 smoothness on the boundary family, margin-free**: the edge zero-extension margin is
FC18 (ii) for `edgeB` (`LocalPacketsOnB.tsupport_edgeB_cutoff_subset_BAUGA`). -/
theorem contMDiff_cgpGlobalMap_family_BAUGP
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (he : e ≤ 1 / 8) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) ∞
      (cgpGlobalMap_BAUGP L Z) :=
  contMDiff_cgpGlobalMap_BAUGP L Z hΔ he fun _ hj =>
    (L.tsupport_edgeB_cutoff_subset_BAUGA hΛ hΔ hμ hτ hΔΛ hj).2.2

/-- **CGP01 on the boundary family, margin-free** (`cgp01_row_BAUGP` with FC18 (ii) for
`edgeB`). -/
theorem cgp01_row_family_BAUGP
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (he : e ≤ 1 / 8) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) ∞
        (cgpGlobalMap_BAUGP L Z) ∧
      (∀ p, (cgpGlobalMap_BAUGP L Z p (cgpScaleTag_BAUGP L Z)).snd = ρ p) ∧
      (∀ p, ‖(cgpGlobalMap_BAUGP L Z p (cgpEdgeTag_BAUGP L Z)).fst‖ =
          ρ p * cgpHeight_BAUGP L p * cgpEdgeMarker_BAUGP L p ∧
        (cgpGlobalMap_BAUGP L Z p (cgpEdgeTag_BAUGP L Z)).snd = ρ p * cgpEdgeMarker_BAUGP L p) ∧
      (∀ p, 0 ≤ cgpHeight_BAUGP L p) ∧
      (∀ p, cgpEdgeMarker_BAUGP L p = cgpEdgeH (cgpHeight_BAUGP L p / Δ) *
        cfsRamp lc87EdgeTransition (1 / 2) 1
          (∑ j : L.edgeB.finite_centres.toFinset, L.edgeB.cutoff_BAUGA j p)) ∧
      (∀ u, cgpEdgeH u ∈ Icc (0 : ℝ) 1) ∧
      (∀ u, 3 / 10 ≤ u → cgpEdgeH u = 1 - cfsRamp lc87EdgeTransition 8 9 u) ∧
      (∀ (j : L.edgeB.finite_centres.toFinset) p,
        (cgpGlobalMap_BAUGP L Z p (cgpEdgeBlockTag_BAUGP L Z j)).fst =
            (ρ j * L.edgeB.cutoff_BAUGA j p) • planeAxis (L.edgeB.coord_BAUGA j p) ∧
          (cgpGlobalMap_BAUGP L Z p (cgpEdgeBlockTag_BAUGP L Z j)).snd =
            ρ j * L.edgeB.cutoff_BAUGA j p) ∧
      (∀ j p, L.edgeB.cutoff_BAUGA j p ∈ Icc (0 : ℝ) 1) ∧
      (∀ j p, p ∉ ball j (100 * Δ * ρ j) → L.edgeB.cutoff_BAUGA j p = 0) ∧
      (∀ j ∈ L.edgeB.centres, ∀ p ∈ ball j (100 * Δ * ρ j), |L.edgeB.coord_BAUGA j p| < 8 * Δ →
        L.edgeB.cutoff_BAUGA j p = 1 - cfsRamp lc87EdgeTransition 8 9 (cgpHeight_BAUGP L p / Δ)) :=
  cgp01_row_BAUGP L Z hΔ he fun _ hj =>
    (L.tsupport_edgeB_cutoff_subset_BAUGA hΛ hΔ hμ hτ hΔΛ hj).2.2

end Generic

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

namespace BoundarySupplyCore

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    W g δn n B oM)

/-- **The interior tags are the ported tags** of the stored active family. -/
theorem intTag_eq_cgpTag_BAUGP :
    S.IntTag_BAUGA =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       letI := S.family.instMetricN
       letI := S.family.instChartedN
       letI := S.family.instMetricC
       CGPTag_BAUGP S.family.toLocalPacketsOnB S.family.zero) :=
  rfl

/-- The scale tag of the interior map is the ported scale tag. -/
theorem scaleTag_eq_cgpScaleTag_BAUGP :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    S.scaleTag_BAUGA = cgpScaleTag_BAUGP S.family.toLocalPacketsOnB S.family.zero :=
  rfl

/-- The `E'` tag of the interior map is the ported `E'` tag. -/
theorem edgeTag_eq_cgpEdgeTag_BAUGP :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    S.edgeTag_BAUGA = cgpEdgeTag_BAUGP S.family.toLocalPacketsOnB S.family.zero :=
  rfl

/-- **BAUG-A's interior formula is the ported CGP01 global block map of the SAME active family**:
`F_int = cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero` on `W°` (same tags, radii,
cutoffs; the circle coordinate of BAUG-A is the chart coordinate at every centre). -/
theorem interiorMapOn_eq_cgpGlobalMap_BAUGP :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    S.interiorMapOn_BAUGA = cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hcoord : S.intCoord_BAUGA =
      cgpCoord_BAUGP S.family.toLocalPacketsOnB S.family.zero := by
    funext t
    rcases t with j | j | j | i | bb
    · have hj := (Set.Finite.mem_toFinset _).mp j.2
      change S.family.circle.coord_BAUGA j.1 = _
      unfold CircleFamilyOn.coord_BAUGA
      rw [dite_eq_left hj]
      rfl
    · rfl
    · rfl
    · rfl
    · cases bb <;> rfl
  have hrad : S.intRadius_BAUGA = cgpRadius_BAUGP S.family.toLocalPacketsOnB S.family.zero := by
    funext t
    rcases t with j | j | j | i | bb
    · rfl
    · rfl
    · rfl
    · rfl
    · cases bb <;> rfl
  have hcut : S.intCutoff_BAUGA = cgpCutoff_BAUGP S.family.toLocalPacketsOnB S.family.zero := by
    funext t
    rcases t with j | j | j | i | bb
    · rfl
    · rfl
    · rfl
    · rfl
    · cases bb <;> rfl
  funext x
  change blockMap S.intRadius_BAUGA S.intCutoff_BAUGA S.intCoord_BAUGA x =
    blockMap (cgpRadius_BAUGP S.family.toLocalPacketsOnB S.family.zero)
      (cgpCutoff_BAUGP S.family.toLocalPacketsOnB S.family.zero)
      (cgpCoord_BAUGP S.family.toLocalPacketsOnB S.family.zero) x
  rw [hrad, hcut, hcoord]

/-- **Consumer: the interior formula is smooth on `W°`** (the ported CGP01 smoothness through the
bridge; the edge margin is FC18 (ii) for `edgeB`). -/
theorem contMDiff_interiorMapOn_BAUGP (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (he : e ≤ 1 / 8) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)) ∞
      S.interiorMapOn_BAUGA := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  rw [S.interiorMapOn_eq_cgpGlobalMap_BAUGP]
  exact contMDiff_cgpGlobalMap_family_BAUGP S.family.toLocalPacketsOnB S.family.zero hΛ hΔ hμ hτ
    hΔΛ he

/-- **Consumer: the scale block of the interior formula is `ρ`** (`cgpGlobalMap_scale_BAUGP`
through the bridge). -/
theorem interiorMapOn_scale_BAUGP (x : W.pieceInterior ⊤) :
    (S.interiorMapOn_BAUGA x S.scaleTag_BAUGA).snd = S.rho x := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  rw [S.interiorMapOn_eq_cgpGlobalMap_BAUGP]
  exact cgpGlobalMap_scale_BAUGP S.family.toLocalPacketsOnB S.family.zero x

end BoundarySupplyCore

end DifferentialGeometry.Geometry.Collapse
