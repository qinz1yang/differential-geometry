import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeBufferOWF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeRimBlocks
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison

/-!
# O-WF G6a: the edge buffer and the original zero disk on `W°` (supply level)

`LocalPacketsOnB.edgeB_buffer_OWF` and `LocalPacketsOnBF.edgeB_smoothDisk_OWF` read on the stored
family of a boundary supply `S` (carrier `W°` with the completed metric `ĝ`, proper by Hopf–Rinow),
in the supply's notation: `η_j = S.edgeEta_BIF j`, `t = S.edgeHeightRaw`,
`H₀ = S.edgeH0_OWF = Δψ(t/Δ)`, the original source
`Y_j = S.edgeSource_OWF j = {q ∈ B(j, 100Δρ_j) : |η_j| < 5Δ, t < 5Δ}`.

* `isProper_interior_OWF`: `(W°, d_ĝ)` is proper.
* `edge_buffer_OWF` (EDP03 on `W°`) and `edge_zeroDisk_OWF` (the original zero disk).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- `(W°, d_ĝ)` is a proper metric space (Hopf–Rinow for the complete `ĝ`). -/
theorem isProper_interior_OWF :
    letI := inducedMetricSpace S.completion.metric
    ProperSpace (W.pieceInterior ⊤) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  exact inducedMetricSpace_properSpace_of_riemannianMetricComplete
    ((riemannianMetricComplete_iff_completeSpace
      (inducedMetricSpace_hmetric S.completion.metric)).mpr S.completion.complete)

/-- EDP03's original height `H₀ = Δψ(t/Δ)` of the revised edge family on `W°`. -/
def edgeH0_OWF : W.pieceInterior ⊤ → ℝ :=
  edgeRowHeight Δ S.edgeSmoothing_BAUGD (fun x => S.rho x.val)

/-- The original edge source `Y_j = {q ∈ B(j, 100Δρ_j) : |η_j| < 5Δ, t < 5Δ}` on `W°`. -/
def edgeSource_OWF (j : S.EdgeIdx_BAUGD) : Set (W.pieceInterior ⊤) :=
  letI := inducedMetricSpace S.completion.metric
  {q | dist q j.1 < 100 * Δ * S.rho j.1 ∧ |S.edgeEta_BIF j.1 q| < 5 * Δ ∧
    S.edgeHeightRaw q < 5 * Δ}

theorem edgeEta_fun_eq_OWF (j : S.EdgeIdx_BAUGD) :
    S.edgeEta_BIF j.1 =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       S.family.edgeB.coord_BAUGA j.1) :=
  funext fun q => S.edgeEta_eq_coord_BAUGP2 j q

theorem mem_edgeB_centres_OWF (j : S.EdgeIdx_BAUGD) :
    (letI := inducedMetricSpace S.completion.metric
     letI := S.completion.complete
     j.1 ∈ S.family.edgeB.centres) :=
  (Set.Finite.mem_toFinset _).mp j.2

/-- The original edge source is open. -/
theorem isOpen_edgeSource_OWF (j : S.EdgeIdx_BAUGD) : IsOpen (S.edgeSource_OWF j) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have h := S.family.toLocalPacketsOnBF.toLocalPacketsOnB.isOpen_edgeBSource_OWF
    (S.mem_edgeB_centres_OWF j)
  have he : S.edgeSource_OWF j = {p | p ∈ ball j.1 (100 * Δ * S.rho j.1) ∧
      |S.family.edgeB.coord_BAUGA j.1 p| < 5 * Δ ∧
      S.family.edgeB.smoothing p / S.rho p.val < 5 * Δ} := by
    ext q
    simp only [edgeSource_OWF, mem_ofPred_eq, mem_ball, S.edgeEta_eq_coord_BAUGP2 j q]
    rfl
  rw [he]
  exact h

/-- **EDP03 on `W°`** (see the module docstring): the enclosure `Y_j ⊆ B(j, 8Δρ_j)`, smoothness
of `η_j` and `H₀` on `Y_j`, the unit vector of `ρ_j⁻²ĝ` with `dη_j > .99`, and the compact
buffer `Q_j ⊆ Y_j` with `{|η_j| < 4.2Δ, t < 4.2Δ}` in its interior. Register premises:
`μ, τ ≤ 10⁻⁸`, `100ΔΛ ≤ 10⁻⁸`, `σc ≤ 10⁻³`, `b · 1000Δ ≤ 1`, `1 ≤ Δ`. -/
theorem edge_buffer_OWF (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1)
    (j : S.EdgeIdx_BAUGD) :
    (letI := inducedMetricSpace S.completion.metric
     S.edgeSource_OWF j ⊆ ball j.1 (8 * Δ * S.rho j.1)) ∧
    ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (S.edgeEta_BIF j.1) (S.edgeSource_OWF j) ∧
    ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ S.edgeH0_OWF (S.edgeSource_OWF j) ∧
    (∀ q ∈ S.edgeSource_OWF j, ∃ w : TangentSpace (𝓡 3) q,
      S.completion.metric.inner q w w = S.rho j.1 ^ 2 ∧
      99 / 100 < mvfderiv (𝓡 3) (S.edgeEta_BIF j.1) q w) ∧
    ∃ Q : Set (W.pieceInterior ⊤), IsCompact Q ∧ Q ⊆ S.edgeSource_OWF j ∧
      (letI := inducedMetricSpace S.completion.metric
       {q | dist q j.1 < 100 * Δ * S.rho j.1 ∧ |S.edgeEta_BIF j.1 q| < 21 / 5 * Δ ∧
        S.edgeHeightRaw q < 21 / 5 * Δ} ⊆ interior Q) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ : ProperSpace (W.pieceInterior ⊤) := S.isProper_interior_OWF
  have h := S.family.toLocalPacketsOnBF.toLocalPacketsOnB.edgeB_buffer_OWF hΔ hμ hτ hlam hσc hb
    (S.mem_edgeB_centres_OWF j)
  have he : S.edgeSource_OWF j = {p | p ∈ ball j.1 (100 * Δ * S.rho j.1) ∧
      |S.family.edgeB.coord_BAUGA j.1 p| < 5 * Δ ∧
      S.family.edgeB.smoothing p / S.rho p.val < 5 * Δ} := by
    ext q
    simp only [edgeSource_OWF, mem_ofPred_eq, mem_ball, S.edgeEta_eq_coord_BAUGP2 j q]
    rfl
  have hη := S.edgeEta_fun_eq_OWF j
  obtain ⟨h8, hηs, hHs, hdη, Q, hQ, hQY, hQi⟩ := h
  refine ⟨?_, ?_, ?_, ?_, Q, hQ, ?_, ?_⟩
  · rw [he]; exact h8
  · rw [he, hη]; exact hηs
  · rw [he]; exact hHs
  · intro q hq
    rw [he] at hq
    obtain ⟨w, hw, hlt⟩ := hdη q hq
    exact ⟨w, hw, by rw [hη]; exact hlt⟩
  · rw [he]; exact hQY
  · intro q hq
    refine hQi ⟨mem_ball.mpr hq.1, ?_, hq.2.2⟩
    rw [← S.edgeEta_eq_coord_BAUGP2 j q]
    exact hq.2.1

/-- **The original zero disk on `W°`**: `{q ∈ B(j, 100Δρ_j) : η_j = 0, H₀ ≤ 4Δ}` is the range of
a smooth embedding of `ClosedCell 2`, boundary circle onto `{H₀ = 4Δ}`. -/
theorem edge_zeroDisk_OWF (hΔ : 0 < Δ) (j : S.EdgeIdx_BAUGD) :
    ∃ φ : ClosedCell 2 → W.pieceInterior ⊤, IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ φ ∧
      range φ = (letI := inducedMetricSpace S.completion.metric
        {q | dist q j.1 < 100 * Δ * S.rho j.1 ∧ S.edgeEta_BIF j.1 q = 0 ∧
          S.edgeH0_OWF q ≤ 4 * Δ}) ∧
      range (φ ∘ cellBoundaryInclusion 2) = (letI := inducedMetricSpace S.completion.metric
        {q | dist q j.1 < 100 * Δ * S.rho j.1 ∧ S.edgeEta_BIF j.1 q = 0 ∧
          S.edgeH0_OWF q = 4 * Δ}) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨φ, hφ, hr, hb⟩ := S.family.toLocalPacketsOnBF.edgeB_smoothDisk_OWF hΔ
    (S.mem_edgeB_centres_OWF j)
  refine ⟨φ, hφ, ?_, ?_⟩
  · rw [hr]
    ext q
    simp only [mem_ofPred_eq, mem_ball, S.edgeEta_eq_coord_BAUGP2 j q]
    rfl
  · rw [hb]
    ext q
    simp only [mem_ofPred_eq, mem_ball, S.edgeEta_eq_coord_BAUGP2 j q]
    rfl

end BoundarySupplyCore

end DifferentialGeometry.Geometry.Collapse
