import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusRegisterChain
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc30
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf0405
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf05Circle
import DifferentialGeometry.Geometry.Fibration.ActualStageChainBases

/-!
# What a non-empty first stage records at an actual circle centre (O-FIXTURE-C1, G8 file 1)

Review 75 D75-6: a non-empty stage test records `j ∈ P.centres`, a point of that centre's actual
plateau, a point of `U_j⁵`, and the bindings to the actual cloud, the native output, the BASES patch
and the final map — not `.active O` alone. For a VARIABLE packet `P` and ANY chain with (JA) on it
(rows are stated on variable packets; the fixture enters afterwards), at a circle centre `j` whose
own coordinate vanishes there (`η_j(j) = 0`), `Gaf02ChainEJA.circle_centre_records_OFC` gives:

* the plateau: `ψ_j(j) = 1`, and `j ∈ B(j, 200ρ_j)` with `|η_j(j)| < 5` (`j ∈ U_j⁵`);
* the cloud: `y₀ = π_{E⁰}(j)` lies in the stage-0 cloud `S₁`, and the stage-0 slot is ACTIVE;
* the native output (GAF04, first stage): the circle marker of the stage-0 map at `y₀` is `ρ_j`;
* the final map (GAF05, circle): the circle markers of `g₁(j)` and of `E(j)` are `ρ_j`;
* FC30: the marker-locality source cutoff is `1` at `G(j)` (the global map at `j`);
* BASES: the bases object of the chain on its own rough data (`Gaf02ChainE.bases_BAS`) and, on the
  circle patch of `j`, the marker identity `μ_j = ρ_j` (GAF05).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- **The records of the first stage at an actual circle centre** (D75-6; see the module header). -/
theorem circle_centre_records_OFC (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) (hS : 0 < S 0)
    {j : X} (hj : j ∈ P.circle.centres) (h0 : cgpCircleCoord P.toLocalChartFamily j hj j = 0) :
    P.circle.cutoff j j = 1 ∧ j ∈ ball j (200 * ρ j) ∧
    ‖cgpCoord P.toLocalChartFamily P.zero (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩) j‖ < 5 ∧
    cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) j ∈
      gafCloud P.toLocalChartFamily P.zero 0 ∧
    (∃ O, C.toChain.slot 0 = Gaf02StageSlot.active O) ∧
    blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩))
        ((C.toChain.slot 0).map (cgpProjMap P.toLocalChartFamily P.zero
          (gafStageTags P.toLocalChartFamily P.zero 0) j)) = ρ j ∧
    gafCircleMarker P.toLocalChartPackets ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩
        (C.toChain.g₁ j) = ρ j ∧
    gafCircleMarker P.toLocalChartPackets ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩
        (C.toChain.E j) = ρ j ∧
    markerLocalitySourceCutoff lc87EdgeTransition (fun i => ρ i.1)
        (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets)
        (cgpGlobalMap P.toLocalChartFamily P.zero j) = 1 ∧
    Nonempty (Gaf02Bases C.toChain C.rough) ∧
    ∀ w ∈ C.toChain.circlePatch_BAS ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩,
      gafCircleMarker P.toLocalChartPackets ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ w = ρ j := by
  have hρj := hρ j
  have hball : j ∈ ball j (200 * ρ j) := mem_ball_self (by positivity)
  have hη : ‖cgpCoord P.toLocalChartFamily P.zero
      (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩) j‖ = 0 := by
    change ‖cgpCircleCoord P.toLocalChartFamily j hj j‖ = 0
    rw [h0, norm_zero]
  have hcore := gafCloud_zero_nonempty_FXC1 P.toLocalChartFamily P.zero hj (by
    rw [h0, norm_zero]
    norm_num)
  have hy : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) j ∈
      gafCloud P.toLocalChartFamily P.zero 0 := ⟨j, hcore.1, rfl⟩
  obtain ⟨-, h04⟩ := C.toGaf02ChainE.gaf04_first_G47
    ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ hball (by
      change ‖cgpCircleCoord P.toLocalChartFamily j hj j‖ ≤ 7
      rw [h0, norm_zero]
      norm_num)
  have h05 := C.toGaf02ChainE.gaf05_circle_GAFC ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩
  obtain ⟨hg1, hE⟩ := h05.2.2.2 j hball (by rw [hη]; norm_num)
  obtain ⟨-, -, h30, -⟩ := (C.toChain.fc30_row_chain_G47).1
  refine ⟨P.circle.plateau j hj j (mem_ball_self (by positivity)), hball, by rw [hη]; norm_num,
    hy, slot_zero_active_FXC1 C.toChain hj, h04 _ (mem_ball_self (by
      have := hρ (C.toChain.sel 0 (cgpProjMap P.toLocalChartFamily P.zero
        (gafStageTags P.toLocalChartFamily P.zero 0) j))
      positivity)), hg1, hE,
    h30 j ⟨⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩, hball, by rw [hη]; norm_num⟩,
    ⟨C.toGaf02ChainE.bases_BAS⟩, h05.1⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
