import DifferentialGeometry.Geometry.Fibration.ActualEdgeSupportLink
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment

/-!
# Boundary port (lane B-PORT-A): ActualEdgeSupportLink (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualEdgeSupportLink.lean` by
`build-logs/scratch/B-PORT-A/gen_circle.py` (engine `portlib2.py`); do
not edit by hand, re-run the script. Closed family → boundary family (`LocalPacketsOnB` /
`LocalPacketsOnBF`, complete σ-compact carrier, regional `…On` families, ACTIVE edge `edgeB`); every
ported declaration `x` ↦ `x_BAUGP` (namespaced `T.m` ↦ `TOn.m_BAUGP`). Substitution table and
failure points: `build-logs/resume/state-B-PORT-A.md`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Link

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}
  {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc : ℝ}
  {Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **FC18 (ii) with the composite `Q` as input** (the form discharged by LC87's packet (iv)). -/
theorem fc18_edge_support_of_link_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂) (hΛ : 0 ≤ Λ)
    {j : X} (hj : j ∈ L.edgeB.centres) {τ : ℝ} (hΔ : 0 < Δ) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hμ : μ ≤ 1 / 10) (Q : X → WithLp 2 (ℝ × ℝ))
    (hQ0 : Q j = 0) (hQnn : ∀ x, 0 ≤ (Q x).snd)
    (hQdist : ∀ x y, (ρ j)⁻¹ * dist x j < 200 * Δ → (ρ j)⁻¹ * dist y j < 200 * Δ →
      |dist (Q x) (Q y) - (ρ j)⁻¹ * dist x y| ≤ τ * Δ)
    (hQlow : ∀ z ∈ closure {y : X | @isEdgePoint.{0, 0} X
        (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'},
      (ρ j)⁻¹ * dist z j < 120 * Δ → (Q z).snd < Δ / 10)
    (hlink : ∀ x, (ρ j)⁻¹ * dist x j < 100 * Δ → |L.edgeB.coord_BAUGA j x - (Q x).fst| ≤ Δ / 100) :
    tsupport (L.edgeB.cutoff_BAUGA j) ⊆ closedBall j (14 * Δ * ρ j) ∧
      closedBall j (14 * Δ * ρ j) ⊆ ball j (20 * Δ * ρ j) ∧
      tsupport (L.edgeB.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j) := by
  have hrj := hρ j
  have hpE := L.edgeB.mem_closure_weakEdge_BDRY5 hj
  have hpt : ∀ x, L.edgeB.cutoff_BAUGA j x ≠ 0 → dist x j ≤ 14 * Δ * ρ j := by
    intro x hx
    obtain ⟨-, hball, hcoord, hheight⟩ := L.edgeB.mem_of_cutoff_ne_zero_BAUGA hΔ hx
    have hrx := hρ x
    have hdxj : dist x j < 100 * Δ * ρ j := by
      rw [inv_mul_lt_iff₀ hrj] at hball
      linarith
    have hρx : ρ x ≤ 101 / 100 * ρ j := by
      have hlip := L.lipschitz_scale.dist_le_mul x j
      rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at hlip
      have h1 : Λ * dist x j ≤ Λ * (100 * Δ * ρ j) := mul_le_mul_of_nonneg_left hdxj.le hΛ
      have h2 : Λ * (100 * Δ * ρ j) ≤ 1 / 100 * ρ j := by nlinarith
      linarith [(abs_le.mp hlip).2]
    have hval := L.edgeB.smoothing_value j hj x
    have hFx : L.edgeB.smoothing x < 9 * Δ * ρ x := by
      rwa [div_lt_iff₀ hrx] at hheight
    have hinf : infDist x (closure {y : X | @isEdgePoint.{0, 0} X
        (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}) < 46 * Δ / 5 * ρ j := by
      have h9 : 9 * Δ * ρ x ≤ 9 * Δ * (101 / 100 * ρ j) :=
        mul_le_mul_of_nonneg_left hρx (by positivity)
      have hμ' : μ * (Δ * ρ j) ≤ 1 / 10 * (Δ * ρ j) :=
        mul_le_mul_of_nonneg_right hμ (by positivity)
      have := mul_pos hΔ hrj
      linarith [(abs_lt.mp hval).1]
    obtain ⟨z, hz, hxz⟩ := (infDist_lt_iff ⟨j, hpE⟩).mp hinf
    have hk := @fc18_edge_support_kernel X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ
        j))).toPseudoMetricSpace
      Q (L.edgeB.coord_BAUGA j) (closure {y : X | @isEdgePoint.{0, 0} X
        (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}) j Δ (τ * Δ) hΔ
      (by nlinarith) hQ0 hQnn (fun x hx y hy => hQdist x y hx hy)
      (fun z hz => hQlow z hz.1 hz.2) (fun x hx => hlink x hx) x hball hcoord
      ⟨z, hz, (show (ρ j)⁻¹ * dist x z < 46 * Δ / 5 by
        rw [inv_mul_lt_iff₀ hrj]; linarith)⟩
    have hk' : (ρ j)⁻¹ * dist x j < 14 * Δ := hk
    rw [inv_mul_lt_iff₀ hrj] at hk'
    linarith
  have hS : tsupport (L.edgeB.cutoff_BAUGA j) ⊆ closedBall j (14 * Δ * ρ j) :=
    closure_minimal (fun x hx => mem_closedBall.mpr (hpt x hx)) isClosed_closedBall
  have hpos := mul_pos hΔ hrj
  have hB : closedBall j (14 * Δ * ρ j) ⊆ ball j (20 * Δ * ρ j) :=
    closedBall_subset_ball (by nlinarith)
  refine ⟨hS, hB, hS.trans (hB.trans (ball_subset_ball (by nlinarith)))⟩

end Link

section FamilyE

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}
  {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc Lmax τ : ℝ}
  {γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **FC18 (ii)** on the actual edge family of `LocalChartFamilyE` (no link hypothesis: LC87's
`exists_edge_link`). -/
theorem fc18_edge_rowE_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) {j : X} (hj : j ∈ L.edgeB.centres) :
    tsupport (L.edgeB.cutoff_BAUGA j) ⊆ closedBall j (14 * Δ * ρ j) ∧
      closedBall j (14 * Δ * ρ j) ⊆ ball j (20 * Δ * ρ j) ∧
      tsupport (L.edgeB.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j) := by
  obtain ⟨Q, h0, hnn, hdist, hlow, hlink⟩ := L.exists_edgeB_link_BAUGA hΔ hμ (by linarith) hj
  exact fc18_edge_support_of_link_BAUGP L hΛ hj hΔ hτ hΔΛ (by linarith) Q h0 hnn
    hdist hlow hlink

/-- **The edge zero-extension margin** (CGP01's `hmargin`) on `LocalChartFamilyE`. -/
theorem edge_margin_rowE_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) :
    ∀ j ∈ L.edgeB.centres, tsupport (L.edgeB.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j) := fun _ hj =>
  (fc18_edge_rowE_BAUGP L hΛ hΔ hμ hτ hΔΛ hj).2.2

/-- **FC12, edge half** on `LocalChartFamilyE`: every test ball `B(p, Rρ(p))` meeting an actual
edge support has comparable scale and lies in `B(j, (14Δ + 4R)ρ(j)) ⊆ B(j, 100Δρ(j))` with margin
`(86Δ − 4R)ρ(j)`. -/
theorem fc12_edge_rowE_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) {j : X} (hj : j ∈ L.edgeB.centres) {p : X} {R : ℝ}
    (hR : 0 < R) (hbudget : Λ * max R (14 * Δ) ≤ 1 / 4) (hgap : 4 * R < 100 * Δ - 14 * Δ)
    (hmeet : (tsupport (L.edgeB.cutoff_BAUGA j) ∩ ball p (R * ρ p)).Nonempty) :
    ρ j / ρ p ∈ Icc (1 / 2) 2 ∧ dist j p ≤ (R + 2 * (14 * Δ)) * ρ p ∧
      ball p (R * ρ p) ⊆ ball j ((14 * Δ + 4 * R) * ρ j) ∧
      ball j ((14 * Δ + 4 * R) * ρ j) ⊆ ball j (100 * Δ * ρ j) ∧
      ∀ x ∈ ball p (R * ρ p), (ball j (100 * Δ * ρ j))ᶜ.Nonempty →
        (100 * Δ - 14 * Δ - 4 * R) * ρ j ≤ infDist x (ball j (100 * Δ * ρ j))ᶜ := by
  have hS := (fc18_edge_rowE_BAUGP L hΛ hΔ hμ hτ hΔΛ hj).1
  have hS' : tsupport (L.edgeB.cutoff_BAUGA j) ⊆ closedBall j ((14 * Δ) * ρ j) := by
    rw [show (14 * Δ) * ρ j = 14 * Δ * ρ j by ring]
    exact hS
  exact DifferentialGeometry.Geometry.Fibration.finite_packet_support_scale_buffer
    L.lipschitz_scale (hρ p) (hρ j) hR (by linarith) (by rwa [Real.coe_toNNReal _ hΛ]) hgap hS'
    (by rw [show 100 * Δ * ρ j = (100 * Δ) * ρ j by ring]) hmeet

end FamilyE

section CGP01E

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **CGP01 on `LocalChartFamilyE` + the zero family, unconditional**: the SAME map
`cgpGlobalMap_BAUGP L Z` is smooth (the margin comes from packet (iv)). -/
theorem cgp01_rowE_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (he : e ≤ 1 / 8) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) ∞
      (cgpGlobalMap_BAUGP L Z) :=
  contMDiff_cgpGlobalMap_BAUGP L Z hΔ he (edge_margin_rowE_BAUGP L hΛ hΔ hμ hτ hΔΛ)

end CGP01E


end DifferentialGeometry.Geometry.Collapse
