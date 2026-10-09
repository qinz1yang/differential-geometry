import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopSlimPieces
import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopChainRows5

/-!
# ZSP04's full row on the C2 chain with a non-empty `K₃` (S-FIXTURE-C2d, G9 file 2)

`loopChain_slimPieces_FXC2`: on ANY chain over the closed C2 family `PZ` (all packet parameters
free) with an actual slim centre `j` and empty zero family, the admissible pair `K₃, D₃` of
ZSP04 carries the whole full row with its arc / loop bundle clauses
(`Gaf02ChainEJA.slim_pieces_nonempty_FXC2`, quoted by `type_of%`) and is non-empty.

`loopSlimPieces_FXC2`: at the register of `loopSlimRows5_FXC2` (Δ = 1200, K = 5, εr = 0), for every
orientation parameter, the closed family has a chain at every base point whose slim centre `j`
lies in the slim piece `M^slim = f₃⁻¹(D₃)` of an admissible pair `K₃, D₃`, with the image of `j`
in `K₃` and at least one arc or loop in `D₃`: the first non-vacuous run of `zsp04_full_row_ZSP35`
(the dihedral fixture is an empty-truth test).
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bundle Manifold Filter GC.MetricGeometry
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete
attribute [local instance] loopMS3_FXC2
attribute [local instance] nezero_finrank_euclideanThree_LC87
attribute [local instance] instMetricNC14_FXC2 instChartedNC14_FXC2 instMetricCC14_FXC2
attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "C14of" PZ => LocalChartPacketsC14D.toLocalChartPacketsC14
  (LocalChartPacketsC14Z.toLocalChartPacketsC14D PZ)

/-- **ZSP04's full row with a non-empty `K₃` on any chain over the closed C2 family.** -/
theorem loopChain_slimPieces_FXC2 {ℓ : LoopLen_FXC2} {R : ℝ} {hR : 0 < R} {Lam : ℝ}
    {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {oM : ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3}
    (PZ : LocalChartPacketsC14Z (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
      (fun _ => R) (fun _ => hR) Lam β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      oM)
    {Kj : ℕ} {Ξ' Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}
    (C : Gaf02ChainEJA (C14of PZ) Kj Ξ' Γ S eg c cw cadj) (hεr : εr < 1 / 2) (hK : 5 ≤ K)
    (hΔ : 0 < Δ) {j : LoopC_FXC2 ℓ} (hj : j ∈ PZ.slim.centres) (h0 : PZ.zero.centres = ∅) :
    type_of% (C.slim_pieces_nonempty_FXC2 (P := PZ) hεr hK hΔ hj h0) :=
  C.slim_pieces_nonempty_FXC2 (P := PZ) hεr hK hΔ hj h0

/-- **The counted ZSP04 full row on the C2 chain, `K₃` non-empty.** See the module docstring. -/
theorem loopSlimPieces_FXC2 :
    ∃ (Ξ : Fin 3 → ℝ → ℝ) (Γ S eg c cw : Fin 3 → ℝ) (R : ℝ) (hR : 0 < R)
      (ℓ : LoopLen_FXC2) (β : ℕ → ℝ) (σs vs γc Lmax ζ : ℝ),
      ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3,
        ∃ PZ : LocalChartPacketsC14Z (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ)
          (loopMS3_hmetric_FXC2 ℓ) (fun _ => R) (fun _ => hR) 0 β 1200 σs 5 0 0 0 0 0 0 0 γc 0
          Lmax 0 0 0 0 0 (1600 * (1000000 * 1200)) 0 vs ζ 0 oM,
        PZ.zero.centres = ∅ ∧
        ∀ x₀ : LoopC_FXC2 ℓ,
          ∃ C : Gaf02ChainEJA (C14of PZ) 5 (fun j => Ξ j (Γ j)) Γ S eg c cw 1,
          C.x₀ = x₀ ∧ ∃ j ∈ PZ.slim.centres,
            ∃ (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35),
              D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧ j ∈ C.slimPiece_ZSP35 K₃.carrier ∧
              C.slimMap_ZSP35 j ∈ K₃.carrier ∧ 0 < D₃.m + D₃.l := by
  have h0 := loopSlimRows5_FXC2
  obtain ⟨β₂, θ', Lc', η', Γ₆, sg, eg₆, -, -, -, -, h1⟩ := h0
  obtain ⟨Ξ, Γ, S, eg, c, cw, R, hR, ℓ, β, σs, vs, γc, Lmax, ζ, -, -, -, hZ⟩ := h1
  refine ⟨Ξ, Γ, S, eg, c, cw, R, hR, ℓ, β, σs, vs, γc, Lmax, ζ, fun oM => ?_⟩
  have hz := hZ oM
  obtain ⟨PZ, hz0, -, hchain⟩ := hz
  refine ⟨PZ, hz0, fun x₀ => ?_⟩
  have hc := hchain x₀
  obtain ⟨C, hCx, j, hj, -⟩ := hc
  have hpc := C.slim_pieces_nonempty_FXC2 (P := PZ) (by norm_num) le_rfl (by norm_num) hj hz0
  obtain ⟨K₃, D₃, hD, -, -, -, -, -, hjP, hjK, hlt⟩ := hpc
  exact ⟨C, hCx, j, hj, K₃, D₃, hD, hjP, hjK, hlt⟩

end DifferentialGeometry.Geometry.Collapse
