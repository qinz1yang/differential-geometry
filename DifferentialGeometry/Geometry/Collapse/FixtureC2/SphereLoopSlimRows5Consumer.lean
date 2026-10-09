import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopSgp5C2

/-!
# Consumer of `loopSlimRows5_FXC2` and `loopSlimRows5_sgp_FXC2` (S-FIXTURE-C2d, G8 file 4)

`loopSlimRows5_consumer_FXC2` is the statement of `loopSlimRows_FXC2` (SGP04 and SGP06 on the
closed packet, chain at every base point with an active stage-2 slot, zero family empty, register
facts), now obtained from the register with exposed thresholds `loopSlimRows5_FXC2` and the
generic-on-packet consumer `loopSlimRows5_sgp_FXC2`, which itself delivers SGP04, SGP05 and SGP06
on `C14of PZ`. It shows that the new register contains the earlier one and that
`loopSlimRows5_sgp_FXC2` applies to every closed packet the register produces.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bundle Manifold Filter GC.MetricGeometry
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete
attribute [local instance] loopMS3_FXC2
attribute [local instance] nezero_finrank_euclideanThree_LC87
attribute [local instance] instMetricNC14_FXC2 instChartedNC14_FXC2 instMetricCC14_FXC2

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "C14of" PZ => LocalChartPacketsC14D.toLocalChartPacketsC14
  (LocalChartPacketsC14Z.toLocalChartPacketsC14D PZ)

/-- **The counted slim rows on the C2 chain, from the register with exposed thresholds.** -/
theorem loopSlimRows5_consumer_FXC2 :
    ∃ (Kj : ℕ) (Ξ : Fin 3 → ℝ → ℝ) (Γ S eg c cw : Fin 3 → ℝ) (cadj : ℝ) (R : ℝ) (hR : 0 < R)
      (ℓ : LoopLen_FXC2) (β : ℕ → ℝ) (Δ σs vs : ℝ) (K : ℕ)
      (Lam σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ) (Γ₆ sg eg₄ eg₆ : ℝ),
      (β 2 ≤ 1 / 10000000 ∧ γ + β 2 < 1 / 10 ∧ 5 ≤ K ∧ εr < 1 / 2) ∧
      Nonempty (ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3) ∧
      ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3,
        ∃ PZ : LocalChartPacketsC14Z (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
          (fun _ => R) (fun _ => hR) Lam β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
          Λz oM,
        Sgp04OutV2 (C14of PZ).toLocalChartPacketsRVZ eg₄ ∧ Sgp06OutV2 (C14of PZ) Γ₆ sg eg₆ ∧
        PZ.zero.centres = ∅ ∧
        (∃ j ∈ PZ.slim.centres, j ∈ gafStageCore PZ.toLocalChartFamily PZ.zero 2) ∧
        ∀ x₀ : LoopC_FXC2 ℓ,
          ∃ C : Gaf02ChainEJA (C14of PZ) Kj (fun j => Ξ j (Γ j)) Γ S eg c cw cadj,
          C.x₀ = x₀ ∧ ∃ j ∈ PZ.slim.centres, ∃ O, C.toChain.slot 2 = Gaf02StageSlot.active O := by
  have h0 := loopSlimRows5_FXC2
  obtain ⟨β₂, θ', Lc', η', Γ₆, sg, eg₆, hθ', hLc', hη', hS, h1⟩ := h0
  obtain ⟨Ξ, Γ, S, eg, c, cw, R, hR, ℓ, β, σs, vs, γc, Lmax, ζ, hreg, hfacts, hor, hZ⟩ := h1
  obtain ⟨hβ2, hη, hL, hσs, hσ, hv, hζ, hζ1, hζ2⟩ := hfacts
  refine ⟨5, Ξ, Γ, S, eg, c, cw, 1, R, hR, ℓ, β, 1200, σs, vs, 5, 0, 0, 0, 0, 0, 0, 0, 0, γc, 0,
    Lmax, 0, 0, 0, 0, 0, 1600 * (1000000 * 1200), 0, ζ, 0, Γ₆, sg, 1 / 200, eg₆,
    ⟨hreg.1, hreg.2, le_rfl, by norm_num⟩, hor, fun oM => ?_⟩
  have h2 := hZ oM
  obtain ⟨PZ, hz0, hcore, hchain⟩ := h2
  have hsgp := loopSlimRows5_sgp_FXC2 hS hθ' hβ2 hη hL hσs hσ hv hζ hζ1 hζ2 PZ (C14of PZ) rfl
  exact ⟨PZ, hsgp.1, hsgp.2.1, hz0, hcore, hchain⟩

end DifferentialGeometry.Geometry.Collapse
