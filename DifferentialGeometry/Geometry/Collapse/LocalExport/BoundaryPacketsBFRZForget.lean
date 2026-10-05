import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRZ

/-!
# The forgetful projection of the complete final boundary family (lane BFAM-ZD)

Dispositions of task 61 (D61-2): the family field of the boundary `BoundarySupply` is the final
family `LocalPacketsOnBFRZ`; its forgetful projection to `LocalPacketsOnBFR` is a DEFINITION (not
only the anonymous `extends` projection), so that rows stated on `LocalPacketsOnBFR` read the
SAME packet.

* `LocalPacketsOnBFRZ.forgetBFR_BFZD`: the forgetful projection (`= toLocalPacketsOnBFR`);
* `LocalPacketsOnBFRZ.forgetBFR_BFZD_eq`, `…_zero`, `…_edgeB`, `…_edge`: it is the `extends`
  projection, and keeps the zero family, the revised edge family and the old edge family.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **The forgetful projection** of the complete final boundary family to `LocalPacketsOnBFR`
(D61-2): the same packet without the two final fields. -/
def LocalPacketsOnBFRZ.forgetBFR_BFZD
    (P : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) :
    LocalPacketsOnBFR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
      Λz U₁ U₂ Ue₁ Ue₂ :=
  P.toLocalPacketsOnBFR

/-- The forgetful projection is the `extends` projection. -/
theorem LocalPacketsOnBFRZ.forgetBFR_BFZD_eq
    (P : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) :
    P.forgetBFR_BFZD = P.toLocalPacketsOnBFR :=
  rfl

/-- The forgetful projection keeps the zero family. -/
theorem LocalPacketsOnBFRZ.forgetBFR_BFZD_zero
    (P : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) :
    P.forgetBFR_BFZD.zero = P.zero :=
  rfl

/-- The forgetful projection keeps the revised (active) edge family. -/
theorem LocalPacketsOnBFRZ.forgetBFR_BFZD_edgeB
    (P : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) :
    P.forgetBFR_BFZD.edgeB = P.edgeB :=
  rfl

/-- The forgetful projection keeps the inherited edge family. -/
theorem LocalPacketsOnBFRZ.forgetBFR_BFZD_edge
    (P : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) :
    P.forgetBFR_BFZD.edge = P.edge :=
  rfl

end DifferentialGeometry.Geometry.Collapse
