import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusRegisterRows
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf07Circle

/-!
# The BASES circle patch of an actual centre is NON-EMPTY (O-FIXTURE-C1, G9 file 1)

D75-6 asks for the binding of a non-empty stage to the actual BASES patch, not a statement that
holds vacuously. For a VARIABLE packet and ANY chain (`Gaf02ChainE`), at every circle centre `i`,
GAF05's chart `ρ_i⁻¹ u_i : W₁ ∩ {v_i > .9ρ_i, ‖u_i‖ < 5.5ρ_i} → B(0, 11/2)` is a bijection, so its
CENTRE `0` has a preimage `w`: `w` lies in the final base `W₁`, `u_i(w) = 0`, `v_i(w) = ρ_i`, `w` is
the image `Θ₁(w')` of a point `w'` of the circle patch `V_i⁰` (`finalBase_inter_circle_BAS`), and
`w` is the `Q₁`-projection of the final map at a point `p` of the manifold (GAF07, onto)
(`Gaf02ChainE.circle_patch_centre_OFC`). On the register chain over the flat torus this holds at the
origin centre `j₀` (`torRegChain_patch_OFC`): the circle patch of `j₀` is non-empty, so the BASES
clauses quantified over it in G8 have content.
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

section Patch

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **The centre of the circle patch** (see the module header). -/
theorem Gaf02ChainE.circle_patch_centre_OFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    ∃ w ∈ C.toChain.finalBase_BAS 0, gafCircleVector P.toLocalChartPackets i w = 0 ∧
      gafCircleMarker P.toLocalChartPackets i w = ρ i.1 ∧
      (∃ w' ∈ C.toChain.circlePatch_BAS i, C.toChain.Θ_BAS 0 w' = w) ∧
      ∃ p : X, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) = w := by
  have h05 := C.gaf05_circle_GAFC i
  have h0 : (0 : ℝ²) ∈ ball (0 : ℝ²) (11 / 2 * 1) := mem_ball_self (by norm_num)
  obtain ⟨w, hw, hw0⟩ := h05.2.2.1.surjOn h0
  have hρi := hρ i.1
  have hu : gafCircleVector P.toLocalChartPackets i w = 0 := by
    have h := hw0
    rw [smul_apply] at h
    exact (smul_eq_zero.mp h).resolve_left (inv_ne_zero hρi.ne')
  have hmem : w ∈ C.toChain.Θ_BAS 0 '' C.toChain.circlePatch_BAS i := by
    rw [← C.toChain.finalBase_inter_circle_BAS i]
    exact hw
  obtain ⟨w', hw', hΘ⟩ := hmem
  exact ⟨w, hw.1, hu, h05.2.1 w hw, ⟨w', hw', hΘ⟩, C.gaf07_circle_onto_GAFC w hw.1⟩

end Patch

attribute [local instance] torMS_FXC1

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  (R : ClosedRegisterV4 (earlyDataSharedV4 K) T)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hlc : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0}) {Kf : ℕ} {δ εr Λz : ℝ}
  (C : Gaf02ChainEJA (torRegPackets_OFC R hT hlc Kf δ εr Λz) K
    (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig R.stage.e R.stage.c
    (stageCwAt_V4C R.stage) (registerCadj_RGC K))

/-- **The circle patch of the origin centre of the register torus is non-empty** (its centre `w`:
`u_{j₀}(w) = 0`, `v_{j₀}(w) = 1`, `w = Θ₁(w')` with `w'` in the patch, `w = Q₁ E(p)`). -/
theorem torRegChain_patch_OFC :
    type_of% (C.toGaf02ChainE.circle_patch_centre_OFC ⟨torRegOrigin_OFC R,
      (Set.Finite.mem_toFinset _).mpr (torRegPackets_origin_mem_OFC R hT hlc)⟩) :=
  C.toGaf02ChainE.circle_patch_centre_OFC _

end DifferentialGeometry.Geometry.Collapse
