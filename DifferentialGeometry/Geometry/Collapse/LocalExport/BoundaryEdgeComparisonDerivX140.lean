import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeBValueBEC
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightEdgeDifferential
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeAffineComparison

/-!
# EGP04 (EC), derivative clause on the final boundary family (X140)

The edgeB pair kernel and its one-sign EGP03 consumer are already proved in
BoundaryPortEdgeAffineComparison. This module exposes the derivative projection at the
LocalPacketsOnBFRZ W-level. The separate value clause remains in BoundaryEdgeBValueBEC.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Pair

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X]
  [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
  {Δ σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ}
  {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- Derivative-only projection of the established EGP04 edgeB pair kernel. -/
theorem egp04_edgeB_deriv_pair_X140
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
      Lmax τ γ δ εr e
      T V vs U₁ U₂ Ue₁ Ue₂)
    {θ E a : ℝ} (hΔ : 1 ≤ Δ) (hθ : 0 < θ) (hθ1 : θ < 1) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμ1 : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hbθ : b ≤ θ ^ 2 / 10 ^ 8) (hbL : b ≤ 1 / (1000 * (1000000 * Δ)))
    (hE : E ≤ θ ^ 2 / 10 ^ 8) (hσc : σc ≤ θ ^ 2 / 10 ^ 8) (hμ : μ * Δ < θ / 100)
    {i j : X} (hi : i ∈ L.edgeB.centres) (hj : j ∈ egpEdgeList_BAUGP L i)
    (ha : a = 1 ∨ a = -1)
    (hER : ∀ x ∈ ball i (600 * Δ * ρ i),
      |ρ j / ρ i * egpRaw_BAUGP L.edgeB j x - a * egpRaw_BAUGP L.edgeB i x -
        ρ j / ρ i * egpRaw_BAUGP L.edgeB j i| < E) :
    ∀ x ∈ ball i (20 * Δ * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
        |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA j) x w -
          a * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA i) x w| < θ := by
  intro x hx w hw
  exact (egp04_edge_pair_KC2_BAUGP L hΔ hθ hθ1 hΛ hLΛ hμ1 hτ hbθ hbL hE hσc hμ
    hi hj ha hER x hx).2 w hw

end Pair

/-- EGP04 derivative region tier. Numeric thresholds precede the actual final family. -/
theorem egp04_edgeB_derivative_region_X140 {Δ β₂ θ : ℝ} (hΔ : 1 ≤ Δ)
    (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ {X : Type} [_mX : MetricSpace X] [ChartedSpace E3 X]
        [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X]
        {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
        {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
        {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
        {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
        {U₁ U₂ Ue₁ Ue₂ : Set X} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
        (F : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
          Lmax τ γ δ
          εr e T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM),
        let L := F.toLocalPacketsOnBFR.toLocalPacketsOnBF.toLocalPacketsOnB
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
        σc ≤ θ ^ 2 / 10 ^ 8 → μ * Δ < θ / 100 →
        ∀ i, i ∈ L.edgeB.centres → ∀ j, j ∈ egpEdgeList_BAUGP L i →
          ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (20 * Δ * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
                |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA j) x w -
                  a * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA i) x w| < θ := by
  obtain ⟨Lc, η₀, hLc, hη₀, hrow⟩ :=
    egp04_edge_BAUGP hΔ hβ₂ hβ₂1 hθ hθ1
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X mX instC instM hXc instS g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM F
  dsimp only
  intro hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ i hi j hj
  let L := F.toLocalPacketsOnBFR.toLocalPacketsOnBF.toLocalPacketsOnB
  obtain ⟨a, ha, hEC⟩ := hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ
    γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂ L hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ
    i hi j hj
  exact ⟨a, ha, fun x hx w hw => (hEC x hx).2 w hw⟩

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- W-level adapter using the induced metric on the interior carrier. -/
theorem egp04_edgeB_derivative_BFRZ_X140 {Δ β₂ θ : ℝ} (hΔ : 1 ≤ Δ)
    (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (ρ : W.pieceInterior ⊤ → ℝ) (hρ : ∀ p, 0 < ρ p)
        {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
        {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
        (U₂ Ue₁ Ue₂ : Set (W.pieceInterior ⊤))
        (oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3)
        (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)),
        letI := inducedMetricSpace ĝ
        ∀ (_ : CompleteSpace (W.pieceInterior ⊤))
          (F : LocalPacketsOnBFRZ (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
            (fun x => ρ x) (fun x => hρ x) Λ β Δ σs K σc μ b s b' s' ε γc βc
            Lmax τ γ δ εr e
            T V vs ζ Λz
            {x | ENNReal.ofReal 10 < distanceToBoundary W g x} U₂ Ue₁ Ue₂ oM),
          let L := F.toLocalPacketsOnBFR.toLocalPacketsOnBF.toLocalPacketsOnB
          b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
          1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
          σc ≤ θ ^ 2 / 10 ^ 8 → μ * Δ < θ / 100 →
          ∀ i, i ∈ L.edgeB.centres → ∀ j, j ∈ egpEdgeList_BAUGP L i →
            ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
              ∀ x ∈ ball i (20 * Δ * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) x,
                (ρ i)⁻¹ ^ 2 * ĝ.inner x w w = 1 →
                  |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA j) x w -
                    a * mvfderiv 𝓘(ℝ, E3) (L.edgeB.coord_BAUGA i) x w| < θ := by
  obtain ⟨Lc, η₀, hLc, hη₀, hregion⟩ :=
    egp04_edgeB_derivative_region_X140 hΔ hβ₂ hβ₂1 hθ hθ1
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro W hconn g ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    U₂ Ue₁ Ue₂ oM ĝ hMc F
  let hSigma : SigmaCompactSpace (W.pieceInterior ⊤) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen W.model (W.pieceInterior ⊤).isOpen)
  exact @hregion (W.pieceInterior ⊤) (inducedMetricSpace ĝ)
    (interiorCharted_BDRY1 W) (interiorManifold_BDRY1 W) hMc hSigma
    ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x) (fun x => hρ x) Λ β σs K σc μ b s
    b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    {x | ENNReal.ofReal 10 < distanceToBoundary W g x} U₂ Ue₁ Ue₂ oM F

end DifferentialGeometry.Geometry.Collapse
