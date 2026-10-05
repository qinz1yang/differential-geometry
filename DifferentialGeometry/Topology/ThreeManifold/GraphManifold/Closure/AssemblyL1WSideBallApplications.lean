import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideBall

/-!
# Consumers of the ball step T3′ (lane ASM-L1b, group G2)

* `compress_nonpos_iff`, `neckCompress_mem_range_iff`: the compressed neck keeps the ball side
  `{τ ≤ 0}` of the neck;
* `PieceEmbedding.exists_ballReparam_eq_neckCompress`: T3′ in the form the cycle normal form uses —
  the reparametrized ball agrees, on the cap region `b`, with the COMPRESSED neck
  `neckCompress (N b)` read through the cap chart.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASML1bU : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

theorem compress_nonpos_iff {l a : ℝ} (hl : 0 < l) (ha : 0 ≤ a) {τ : ℝ} :
    compress l ha τ ≤ 0 ↔ τ ≤ 0 := by
  constructor
  · intro h
    by_contra hτ
    rw [compress_of_nonneg hl ha (le_of_lt (not_le.mp hτ))] at h
    exact hτ h
  · exact compress_nonpos hl ha

/-- The compressed neck has the same ball side. -/
theorem neckCompress_mem_range_iff {W : CompactCarrier.{u}} {B : PieceEmbedding W}
    {N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞}
    (hside : ∀ {q}, q ∈ N.source → (N q ∈ range B.map ↔ q.2 ≤ 0)) {l a : ℝ} (hl : 0 < l)
    (ha : 0 ≤ a) {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ (neckCompress N hl ha).source) :
    neckCompress N hl ha q ∈ range B.map ↔ q.2 ≤ 0 := by
  rw [neckCompress_apply, hside ((mem_neckCompress_source hl).mp hq)]
  exact compress_nonpos_iff hl ha

/-- **T3′, compressed-neck form.** -/
theorem PieceEmbedding.exists_ballReparam_eq_neckCompress {W : CompactCarrier.{u}}
    (B : PieceEmbedding W) (e : B.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) {ε : ℝ} (hε : 0 < ε)
    (hε' : ε ≤ 1 / 8)
    (N : Bool → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    (hsrc : ∀ b, closedNeckDomain ε ⊆ (N b).source)
    (hdisj : Disjoint (N false).target (N true).target)
    (hside : ∀ b {q}, q ∈ (N b).source → (N b q ∈ range B.map ↔ q.2 ≤ 0))
    (hsign : ∀ x₀ x₁, B.map (e.symm x₀) = N false 0 → B.map (e.symm x₁) = N true 0 →
      ballNeckDetAmb B e x₀ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (N false) 0) *
      ballNeckDetAmb B e x₁ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (N true) 0) < 0) :
    ∃ l a : ℝ, ∃ (hl : 0 < l) (ha : 0 ≤ a), ∃ β : ClosedCell 3 → W.Carrier,
      ContMDiff (𝓡∂ 3) W.model ∞ β ∧ (∀ x, Bijective (mfderiv (𝓡∂ 3) W.model β x)) ∧
      Injective β ∧ range β = range B.map ∧
      ∀ b x, x ∈ neckCapRegion ε b →
        β x = neckCompress (N b) hl ha (capMap b (x : EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨l, a, hl, ha, -, β, hβ, hβd, hβi, hβr, hβc⟩ :=
    B.exists_ballReparam_eq_necks e hε hε' N hsrc hdisj hside hsign
  exact ⟨l, a, hl, ha, β, hβ, hβd, hβi, hβr, fun b x hx => by
    rw [neckCompress_apply]
    exact hβc b x hx⟩

end GC.GraphManifold.Assembly
