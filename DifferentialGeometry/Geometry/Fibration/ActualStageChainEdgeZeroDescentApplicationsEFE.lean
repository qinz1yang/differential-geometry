import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeZeroDescentEFE

/-!
# Consumer of EDP05's zero-face descent (G4a): the final closed family

Lane S-EDP-FDC2, group G4. On the final closed family `LocalChartPacketsC14Z`, for a chain with
(JA) (`Gaf02ChainEJA`, whose `toGaf02ChainE` carries the zero-domain facts), a closed slim base set
and a zero-face point `q` with `f₃ q` outside it, `edge_zero_face_M2_local_EFE` describes
`M₂ = M₁ ∖ int_{M₁} M^slim` over a neighbourhood of `π₂E q` by the descended zero ratio, and
`edge_zero_fibre_subset_M2_EFE` puts the whole `π₂E`-fibre inside `∂Z_k ∩ M₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02ChainEJA

/-- **EDP05's zero-face descent on the final closed family**: the descended defining identity of
the actual `M₂` along a zero face, over a neighbourhood of the whole `π₂E`-fibre, and the face
saturation of the fibre. -/
theorem edge_zero_face_M2_local_C14Z_EFE {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    (PZ : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}
    (C : Gaf02ChainEJA PZ.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2)
    (Kb : Set (BlockSpace (fun _ : CGPTag PZ.toLocalChartFamily PZ.zero =>
      EuclideanSpace ℝ (Fin 2))))
    (hKc : IsClosed Kb) (k : PZ.zero.finite_centres.toFinset) {q : X}
    (hq : q ∈ frontier (zspDomain_ZSP35 PZ.toLocalChartFamily PZ.zero k C.E))
    (hK : C.slimMap_ZSP35 q ∉ Kb) :
    type_of% (C.toGaf02ChainE.edge_zero_face_M2_local_EFE hεr hKc k hq hK) ∧
      ∀ y : X, (gafStageQ PZ.toLocalChartFamily PZ.zero 1).starProjection (C.toChain.E y) =
        (gafStageQ PZ.toLocalChartFamily PZ.zero 1).starProjection (C.toChain.E q) →
      y ∈ frontier (zspDomain_ZSP35 PZ.toLocalChartFamily PZ.zero k C.E) ∧
        y ∈ C.cutM2_R74 Kb :=
  ⟨C.toGaf02ChainE.edge_zero_face_M2_local_EFE hεr hKc k hq hK,
    fun _ hy => C.toGaf02ChainE.edge_zero_fibre_subset_M2_EFE hεr Kb k hq hK hy⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
