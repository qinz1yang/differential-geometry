import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJA
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07

/-!
# GAF06 and GAF07's interface on `Gaf02ChainEJA`, without numerical hypotheses

Blueprint `master207B.tex`, GAF06 (B:6008–6047) and GAF07 (B:6049–6165); GAF01's (JA)
(B:5705–5711). The chain-object theorems `Gaf02Chain.gaf06_G47`, `Gaf02Chain.gaf07_*_G47` read
GAF01's `c₃ = c 2 < 1/1000` as a numerical hypothesis on the chain's own parameter. On
`C : Gaf02ChainEJA` this inequality is the field `C.c_two_lt` of the same numeric choice, so the
rows hold with no hypothesis beyond the object:

* `Gaf02ChainEJA.gaf06_GAFC`: GAF06 at every point `H_τ p = (1 − τ)𝓔⁰ p + τE p` of the segment.
* `Gaf02ChainEJA.gaf07_circle_interface_GAFC`, `Gaf02ChainEJA.gaf07_slim_interface_GAFC`: GAF07's
  interface for every base set `W` (first inclusion up to `W`, `X_j ⊂ U_j`, properness).
* Consumers on the final family `LocalChartPacketsC14Z` (chain on its `LocalChartPacketsC14`
  projection): `gaf06_final_family_EJA_GAFC`, `gaf07_final_family_interface_EJA_GAFC`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- **GAF06 on the chain with (JA)** (B:6008): for EVERY retained index `i`, every `ℓ ≥ 1`, every
`p` and `τ ∈ [0, 1]`, (RP) at `H_τ p = (1 − τ)𝓔⁰ p + τ E p` forces a positive original cutoff, `p`
in the chart domain and `|η_i(p)| < 4.01ℓ`. No numerical hypothesis: `c₃ < 1/1000` is
`C.c_two_lt`. -/
theorem gaf06_GAFC (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) {ℓ : ℝ} (hℓ : 1 ≤ ℓ)
    (i : CGPMarkerIndex P.toLocalChartFamily) :
    ∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
      9 / 10 * ρ (cgpMarkerCentre P.toLocalChartFamily i) <
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p)‖ ≤
        4 * ℓ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero i)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • C.toChain.E p) →
      0 < cgpMarkerCutoff P.toLocalChartFamily i p ∧
        p ∈ ball (cgpMarkerCentre P.toLocalChartFamily i)
          (cgpMarkerDomain P.toLocalChartFamily i * ρ (cgpMarkerCentre P.toLocalChartFamily i)) ∧
        ‖cgpCoord P.toLocalChartFamily P.zero (cgpMarkerTag P.toLocalChartFamily P.zero i) p‖ <
          401 / 100 * ℓ :=
  C.toChain.gaf06_G47 C.c_two_lt hℓ i

/-- **GAF07's interface, circle stage, on the chain with (JA)**, for EVERY base set `W`: the
`3.5`-slab lies in `X₁` up to `π₁E p ∈ W`, `X₁ ⊂ U₁` (cutoff one, `‖η_i‖ < 4.01`), and
`π₁E : X₁ → B₁` is proper (`B₁ = W ∩ R₁`, `X₁ = (π₁E)⁻¹(B₁)`). -/
theorem gaf07_circle_interface_GAFC (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (W : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) :
    (∀ p, (∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
        p ∈ ball i.1 (200 * ρ i.1) ∧ ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ ≤ 7 / 2) →
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈ W →
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
        W ∩ gaf07CircleRatio_G47 P.toLocalChartPackets) ∧
    (∀ p, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
        W ∩ gaf07CircleRatio_G47 P.toLocalChartPackets →
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset, p ∈ ball i.1 (200 * ρ i.1) ∧
        ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 401 / 100 ∧
        P.circle.cutoff i.1 p = 1) ∧
    IsProperMap ((W ∩ gaf07CircleRatio_G47 P.toLocalChartPackets).restrictPreimage
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p))) :=
  C.toChain.gaf07_circle_interface_G47 C.c_two_lt W

/-- **GAF07's interface, slim stage, on the chain with (JA)**, for EVERY base set `W`: the
`3.5·10⁵Δ`-slab lies in `X₃` up to `π₃E p ∈ W`, `X₃ ⊂ U₃` (cutoff one, `|η_i| < 4.01·10⁵Δ`), and
`π₃E : X₃ → B₃` is proper. -/
theorem gaf07_slim_interface_GAFC (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (W : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) :
    (∀ p, (∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
        p ∈ ball i.1 (1000000 * Δ * ρ i.1) ∧
        |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
          7 / 2 * (10 ^ 5 * Δ)) →
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) ∈ W →
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) ∈
        W ∩ gaf07SlimRatio_G47 P.toLocalChartPackets) ∧
    (∀ p, (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) ∈
        W ∩ gaf07SlimRatio_G47 P.toLocalChartPackets →
      ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
        p ∈ ball i.1 (1000000 * Δ * ρ i.1) ∧
        |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| <
          401 / 100 * (10 ^ 5 * Δ) ∧
        P.slim.cutoff i.1 p = 1) ∧
    IsProperMap ((W ∩ gaf07SlimRatio_G47 P.toLocalChartPackets).restrictPreimage
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p))) :=
  C.toChain.gaf07_slim_interface_G47 C.c_two_lt W

end Gaf02ChainEJA

/-- **Consumer: GAF06 for a chain with (JA) on the final family** `LocalChartPacketsC14Z` (chain
on its `LocalChartPacketsC14` projection), at the end point `τ = 1` (`H₁ = E`): (RP) at `E p` for a
circle / slim index makes the original cutoff one, for an edge index gives the tangential bound. -/
theorem gaf06_final_family_EJA_GAFC {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (p : X) :
    (∀ j : P.circle.finite_centres.toFinset,
      9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inl j) (C.toChain.E p) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl j)
          (C.toChain.E p)‖ ≤
        4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl j)
          (C.toChain.E p) →
      P.circle.cutoff j.1 p = 1) ∧
    (∀ j : P.slim.finite_centres.toFinset,
      9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inl j)) (C.toChain.E p) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl j))
          (C.toChain.E p)‖ ≤
        4 * (10 ^ 5 * Δ) * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inl j)) (C.toChain.E p) →
      P.slim.cutoff j.1 p = 1) ∧
    ∀ j : P.edge.finite_centres.toFinset,
      9 / 10 * ρ j.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl j))) (C.toChain.E p) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl j))) (C.toChain.E p)‖ ≤
        4 * Δ * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl j))) (C.toChain.E p) →
      |P.edge.coord j.1 p| < 401 / 100 * Δ :=
  gaf06_final_family_G47 C.toChain C.c_two_lt p

/-- **Consumer: GAF07's interface for a chain with (JA) on the final family**
`LocalChartPacketsC14Z`, for EVERY pair of base sets `W₁, W₃` (BASES' embedded bases): the whole
preimages `X₁`, `X₃` lie in the original threshold-5 domains with cutoff one and contain the
`3.5`-slabs over `W_j`. -/
theorem gaf07_final_family_interface_EJA_GAFC {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (W₁ W₃ : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) :
    (∀ p, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
        W₁ ∩ gaf07CircleRatio_G47 P.toLocalChartPackets →
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
        ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 5 ∧ P.circle.cutoff i.1 p = 1) ∧
    (∀ p, (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) ∈
        W₃ ∩ gaf07SlimRatio_G47 P.toLocalChartPackets →
      ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
        |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 5 * (10 ^ 5 * Δ) ∧
        P.slim.cutoff i.1 p = 1) ∧
    (∀ (i : P.toLocalChartFamily.circle.finite_centres.toFinset) p,
      p ∈ ball i.1 (200 * ρ i.1) → ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ ≤ 7 / 2 →
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈ W₁ →
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
        W₁ ∩ gaf07CircleRatio_G47 P.toLocalChartPackets) ∧
    ∀ (i : P.toLocalChartFamily.slim.finite_centres.toFinset) p,
      p ∈ ball i.1 (1000000 * Δ * ρ i.1) →
      |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ 7 / 2 * (10 ^ 5 * Δ) →
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) ∈ W₃ →
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) ∈
        W₃ ∩ gaf07SlimRatio_G47 P.toLocalChartPackets :=
  gaf07_final_family_interface_G47 C.toChain C.c_two_lt W₁ W₃

end DifferentialGeometry.Geometry.Collapse
