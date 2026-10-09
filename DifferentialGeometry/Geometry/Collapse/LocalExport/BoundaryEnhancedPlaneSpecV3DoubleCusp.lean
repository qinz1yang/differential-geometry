import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEnhancedPlaneSpecV3
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySupplyDoubleCuspInst

/-!
# `BoundaryEnhancedPlaneSpecV3` on the double-cusp supply (lane BAUG-C, G2V3)

New module (V3 copy of the accepted `BoundaryEnhancedPlaneSpecDoubleCusp`, AGZ, which stays unchanged;
lead decision (B): spec V3 with `radius_mcb` / `preimage_comparable` instead of `scale_kept`).

Non-vacuous use of the boundary enhanced-plane spec (the brief's inhabitant requirement for a new
interface structure): on the double-cusp standing sequence of BAUG-A G4
(`lc88_boundarySupply_doubleCusp_BAUGA`, members `T² × [0, 240]` with two boundary components, no
counterfactual hypothesis), on one tail EVERY member carries a `BoundarySupply` `S` together with a
parameter slot and the circle / revised-edge / slim stage tables of the stored rows of `S.ba_spec`
(`S.circleRow_BIF`, `S.edgeRow_BIF`, `S.slimRow_BIF`), each with `BoundaryEnhancedPlaneSpecV3` at the
given qualities `Γ`, radius factors `sg` and normal errors `eg` (`exists_boundaryEnhancedPlaneSpecV3_stored_BAUGC`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **The enhanced-plane spec on the double-cusp supply** (non-vacuous use): with BAUG-A G4's
prefix verbatim (one `A`, then the producer's prefix), for every `0 < δ₀ ≤ δStar` the double-cusp
sequence has, on one tail, at every member an orientation `oM`, a `BoundarySupply` `S` and the three
stored-row stage tables with `BoundaryEnhancedPlaneSpecV3` at `(Γ st, sg st, eg st)`. -/
theorem doubleCusp_boundaryEnhancedPlaneSpecV3_BAUGC
    (K : ℕ) (hK : 10 ≤ K) (Γ sg eg : Fin 3 → ℝ) {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν)
    (hν1 : ν < 1 / 1000000) :
    ∃ A : ℝ → ℝ, (∀ w, 0 < A w) ∧
    ∃ σC : ℝ, 0 < σC ∧ ∃ ηC : ℝ, 0 < ηC ∧
    ∃ δStar : ℝ, 0 < δStar ∧
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → γ ≤ θ ^ 2 / 10000000 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      3 * β₂ ≤ σC → β₂ ≤ θ ^ 2 / 10000000 → ∃ σE : ℝ, 0 < σE ∧ ∃ ηE : ℝ, 0 < ηE ∧
      ∃ σS : ℝ, 0 < σS ∧ ∃ ηS : ℝ, 0 < ηS ∧
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 → μ ≤ 1 / 10 ^ 8 →
        μ * Δ ≤ θ / 4 → σc ≤ θ ^ 2 / 10000000 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 → ∃ bd₀ : ℝ, 0 < bd₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → b < bd₀ → 3 * b ≤ σE →
        b * (2 * (421 * Δ + 1)) ≤ 1 → b ≤ θ ^ 2 / 10000000 →
      ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs → vs ≤ θ / 4 → σs ≤ θ ^ 2 / 10000000 →
      ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
        3 * ν ≤ β 3 → 2 * β 1 ≤ ηC → 2 * β 1 ≤ ηE → 2 * β 1 ≤ ηS →
        1000000 * Δ * β 1 ^ 3 < 1 → 3 * β 1 ≤ σS → β 1 * (2 * (1950002 * Δ + 1)) ≤ 1 →
        β 1 ≤ θ ^ 2 / 10000000 →
      ∀ ζ cap : ℝ, β 1 < ζ → ζ < 1 → 0 < cap →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ ≤ δStar →
      ∃ (W : ℕ → CompactCarrier.{0}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, (B n).count = 2) ∧
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) ∧
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) ∧
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ Lmax : ℝ, 0 < Lmax → σC⁻¹ ≤ Lmax →
      σE⁻¹ ≤ Lmax → σS⁻¹ ≤ Lmax → ∀ βd εN : ℝ, 0 < βd → 0 < εN → εN ≤ θ ^ 2 / 40000000 →
      ∀ᶠ n in atTop,
        ∃ oM : ManifoldOrientation 𝓘(ℝ, E3) ((W n).pieceInterior ⊤) 3,
        ∃ S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
            vs ζ Λ' θ (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) n (B n) oM,
          (∃ (Φ : BoundaryInteriorSlots_BIF S)
            (R : BoundaryStageReferences_BIF Φ 0 (EuclideanSpace ℝ (Fin 2)) S.circleEta_BIF
              S.circleRow_BIF), BoundaryEnhancedPlaneSpecV3 R (Γ 0) (sg 0) (eg 0)) ∧
          (∃ (Φ : BoundaryInteriorSlots_BIF S)
            (R : BoundaryStageReferences_BIF Φ 1 ℝ S.edgeEta_BIF S.edgeRow_BIF),
              BoundaryEnhancedPlaneSpecV3 R (Γ 1) (sg 1) (eg 1)) ∧
          ∃ (Φ : BoundaryInteriorSlots_BIF S)
            (R : BoundaryStageReferences_BIF Φ 2 ℝ S.slimEta_BIF S.slimRow_BIF),
              BoundaryEnhancedPlaneSpecV3 R (Γ 2) (sg 2) (eg 2) := by
  obtain ⟨A, hApos, σC, hσC, ηC, hηC, δStar, hδStar, a₂, ha₂, h1⟩ :=
    lc88_boundarySupply_doubleCusp_BAUGA K hK hθ hθ1 hν hν1
  refine ⟨A, hApos, σC, hσC, ηC, hηC, δStar, hδStar, a₂, ha₂, fun γ c1 c2 c3 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h2⟩ := h1 γ c1 c2 c3
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc d1 d2 d3 d4 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h3⟩ := h2 βc γc d1 d2 d3 d4
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ f1 f2 f3 f4 f5 f6 f7 => ?_⟩
  obtain ⟨σE, hσE, ηE, hηE, σS, hσS, ηS, hηS, τ₀, hτ₀, bc₀, hbc₀, h4⟩ :=
    h3 β₂ Δ f1 f2 f3 f4 f5 f6 f7
  refine ⟨σE, hσE, ηE, hηE, σS, hσS, ηS, hηS, τ₀, hτ₀, bc₀, hbc₀,
    fun σc ε μ τ k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 s b' s' l1 l2 l3 l4 l5 l6 l7 l8 =>
      ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h5⟩ :=
    h4 σc ε μ τ k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 s b' s' l1 l2 l3 l4 l5 l6 l7 l8
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ m1 m2 m3 m4 Λ n1 n2 n3 n4 n5 n6 n7 => ?_⟩
  obtain ⟨w₀, hw₀, h6⟩ := h5 σ m1 m2 m3 m4 Λ n1 n2 n3 n4 n5 n6 n7
  refine ⟨w₀, hw₀, fun w o1 o2 o3 => ?_⟩
  obtain ⟨bd₀, hbd₀, h7⟩ := h6 w o1 o2 o3
  refine ⟨bd₀, hbd₀, fun b p1 p2 p3 p4 p5 p6 p7 p8 p9 σs vs q1 q2 q3 q4 q5 => ?_⟩
  obtain ⟨b₀, hb₀, h8⟩ := h7 b p1 p2 p3 p4 p5 p6 p7 p8 p9 σs vs q1 q2 q3 q4 q5
  refine ⟨b₀, hb₀, fun β r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 ζ cap u1 u2 u3 => ?_⟩
  obtain ⟨εr, δ', Λ', v1, v2, v3, v4, v5, h9⟩ :=
    h8 β r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 ζ cap u1 u2 u3
  refine ⟨εr, δ', Λ', v1, v2, v3, v4, v5, fun T x1 x2 e x3 x4 δ₀ x5 x6 => ?_⟩
  obtain ⟨W, hW, g, B, hc, hvol, hder, V, hV, δ, hδ, hδ', h10⟩ := h9 T x1 x2 e x3 x4 δ₀ x5 x6
  refine ⟨W, hW, g, B, hc, hvol, hder, V, hV, δ, hδ, hδ', fun Lmax y1 y2 y3 y4 βd εN z1 z2 z3 =>
    ?_⟩
  refine (h10 Lmax y1 y2 y3 y4 βd εN z1 z2 z3).mono fun n hn => ?_
  obtain ⟨oM, ⟨S⟩⟩ := hn
  exact ⟨oM, S, exists_boundaryEnhancedPlaneSpecV3_stored_BAUGC S Γ sg eg⟩

end DifferentialGeometry.Geometry.Collapse
