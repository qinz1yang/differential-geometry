import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf0405
import DifferentialGeometry.Geometry.Fibration.ActualStageChainChartCircleApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainLater

/-!
# GAF05's first paragraph on `Gaf02ChainE`, circle charts: exact markers on the bases

Blueprint `master207B.tex`, GAF05 (`prop:fibration-exact-interior-markers`, B:5971–6006): "Every
marked stage patch `V_i⁰` of CGP07 satisfies `v_i = R_i` identically. Its later image `V_i ⊂ W_j`
has the same property and `a = u_i/R_i = u_i/v_i : V_i → B(0, 5.5ℓ_i)` is a diffeomorphism."
Circle charts (`j = 1`, `ℓ_i = 1`), on ONE chain on the enhanced planes `C : Gaf02ChainE`
(lane C14-GAF8b) with its OWN rough data `C.rough`; the bases are BASES' (lane C14-BASES):
`V_i⁰ = C.toChain.circlePatch_BAS i` (CGP07, `Gaf02Chain.cgp07_circle_BAS`), `W₁ =
C.toChain.finalBase_BAS 0 = Θ₁(V₁⁰)` (CGP08), `V_i = W₁ ∩ {v_i > .9R_i, ‖u_i‖ < 5.5R_i} = Θ₁(V_i⁰)`
(`Gaf02Chain.finalBase_inter_circle_BAS`).

Route (blueprint's, with BASES' exits): every patch point is `f₁(p)` for an ORIGINAL threshold-6
plateau point `p` (CGP07 exhaustion), whose stage image has marker exactly `R_i` (GAF05's plateau
clause, `Gaf02Chain.gaf05_first_plateau_G47` with the FM certificate `C.planes₀`); `Θ₁` keeps the
whole circle block (`Gaf02Chain.theta_retains_circle_BAS`) and is smooth at every stage image
(`Gaf02Chain.contDiffAt_theta_BAS`), so `Θ₁ ∘ φ` is a smooth inverse chart of the later patch.

* `Gaf02ChainE.gaf05_circlePatch_marker_GAFC`: `v_i ≡ R_i` on `V_i⁰`.
* `Gaf02ChainE.gaf05_circlePatch_chart_GAFC`: `u_i/v_i = u_i/R_i` on `V_i⁰`; `R_i⁻¹u_i : V_i⁰ →
  B(0, 5.5)` bijective with a smooth inverse chart.
* `Gaf02ChainE.gaf05_circleBase_marker_GAFC`: `v_i ≡ R_i` on the later image `V_i ⊂ W₁`.
* `Gaf02ChainE.gaf05_circleBase_chart_GAFC`: `u_i/v_i = u_i/R_i` on `V_i`; `R_i⁻¹u_i : V_i →
  B(0, 5.5)` bijective with the smooth inverse chart `Θ₁ ∘ φ`.
* Consumer `Gaf02ChainE.gaf05_circle_GAFC`: GAF05 for the circle charts — both patch clauses and
  the plateau clause (stage image and final image) — at every circle index.
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainE

/-- The stage-one map is `g₁` (`Q₁ = H`). -/
theorem stageMap_zero_eq_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (p : X) :
    C.toChain.stageMap_BAS 0 p = C.toChain.g₁ p := by
  change (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.g₁ p) = _
  exact gafStageQ_zero_starProjection_BAS P.toLocalChartPackets _

/-- **GAF05, circle patches** (B:5971–5973): `v_i ≡ R_i` on CGP07's marked stage patch `V_i⁰`. -/
theorem gaf05_circlePatch_marker_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    ∀ w ∈ C.toChain.circlePatch_BAS i, gafCircleMarker P.toLocalChartPackets i w = ρ i.1 := by
  intro w hw
  obtain ⟨p, ⟨hp, hη⟩, hpw⟩ := (C.toChain.cgp07_circle_BAS C.rough i).2.1 w hw
  rw [← hpw, C.stageMap_zero_eq_GAFC]
  exact (C.toChain.gaf05_first_plateau_G47 C.planes₀ C.x₀ C.sel_eq.1 C.plane_eq.1
    (C.rough.sigma_le 0).le i hp hη).2.2.1

/-- **GAF05, circle patch chart** (B:5974–5977): on `V_i⁰`, `u_i/v_i = u_i/R_i`, and
`R_i⁻¹u_i : V_i⁰ → B(0, 5.5)` is a bijection with a smooth inverse chart `φ` (CGP07). -/
theorem gaf05_circlePatch_chart_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    (∀ w ∈ C.toChain.circlePatch_BAS i,
      (gafCircleMarker P.toLocalChartPackets i w)⁻¹ • gafCircleVector P.toLocalChartPackets i w =
        ((ρ i.1)⁻¹ • gafCircleVector P.toLocalChartPackets i) w) ∧
    BijOn ((ρ i.1)⁻¹ • gafCircleVector P.toLocalChartPackets i) (C.toChain.circlePatch_BAS i)
      (ball 0 (11 / 2 * 1)) ∧
    ∃ φ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * 1)) ∧
      InvOn φ ((ρ i.1)⁻¹ • gafCircleVector P.toLocalChartPackets i) (C.toChain.circlePatch_BAS i)
        (ball 0 (11 / 2 * 1)) ∧
      MapsTo φ (ball 0 (11 / 2 * 1)) (C.toChain.circlePatch_BAS i) := by
  obtain ⟨hbij, -, φ, hφ, hinv, hmaps, -⟩ := C.toChain.cgp07_circle_BAS C.rough i
  refine ⟨fun w hw => ?_, hbij, φ, hφ, hinv, hmaps⟩
  rw [C.gaf05_circlePatch_marker_GAFC i w hw, smul_apply]

/-- **GAF05, later circle image** (B:5974–5975): `v_i ≡ R_i` on `V_i = W₁ ∩ {v_i > .9R_i,
‖u_i‖ < 5.5R_i} = Θ₁(V_i⁰)` (CGP08 keeps the whole circle block). -/
theorem gaf05_circleBase_marker_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    ∀ w ∈ C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets i)
        (gafCircleMarker P.toLocalChartPackets i) (ρ i.1) 1,
      gafCircleMarker P.toLocalChartPackets i w = ρ i.1 := by
  intro w hw
  rw [C.toChain.finalBase_inter_circle_BAS i] at hw
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  rw [(C.toChain.theta_retains_circle_BAS i w₀).2]
  exact C.gaf05_circlePatch_marker_GAFC i w₀ hw₀

/-- **GAF05, later circle chart** (B:5975–5977): on `V_i = W₁ ∩ {v_i > .9R_i, ‖u_i‖ < 5.5R_i}`,
`u_i/v_i = u_i/R_i`, and `R_i⁻¹u_i : V_i → B(0, 5.5)` is a bijection with the smooth inverse chart
`Θ₁ ∘ φ` landing in `V_i`. -/
theorem gaf05_circleBase_chart_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    (∀ w ∈ C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE
        (gafCircleVector P.toLocalChartPackets i) (gafCircleMarker P.toLocalChartPackets i)
          (ρ i.1) 1,
      (gafCircleMarker P.toLocalChartPackets i w)⁻¹ • gafCircleVector P.toLocalChartPackets i w =
        ((ρ i.1)⁻¹ • gafCircleVector P.toLocalChartPackets i) w) ∧
    BijOn ((ρ i.1)⁻¹ • gafCircleVector P.toLocalChartPackets i)
      (C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets i)
        (gafCircleMarker P.toLocalChartPackets i) (ρ i.1) 1) (ball 0 (11 / 2 * 1)) ∧
    ∃ ψ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      ContDiffOn ℝ ∞ ψ (ball 0 (11 / 2 * 1)) ∧
      InvOn ψ ((ρ i.1)⁻¹ • gafCircleVector P.toLocalChartPackets i)
        (C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets i)
          (gafCircleMarker P.toLocalChartPackets i) (ρ i.1) 1) (ball 0 (11 / 2 * 1)) ∧
      MapsTo ψ (ball 0 (11 / 2 * 1)) (C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE
        (gafCircleVector P.toLocalChartPackets i) (gafCircleMarker P.toLocalChartPackets i)
          (ρ i.1) 1) := by
  obtain ⟨hbij, hwit, φ, hφ, hinv, hmaps, -⟩ := C.toChain.cgp07_circle_BAS C.rough i
  rw [C.toChain.finalBase_inter_circle_BAS i]
  have hret : ∀ w, ((ρ i.1)⁻¹ • ⇑(gafCircleVector P.toLocalChartPackets i))
      (C.toChain.Θ_BAS 0 w) = ((ρ i.1)⁻¹ • ⇑(gafCircleVector P.toLocalChartPackets i)) w :=
    fun w => by simp only [Pi.smul_apply, (C.toChain.theta_retains_circle_BAS i w).1]
  have hretC : ∀ w, ((ρ i.1)⁻¹ • gafCircleVector P.toLocalChartPackets i)
      (C.toChain.Θ_BAS 0 w) = ((ρ i.1)⁻¹ • gafCircleVector P.toLocalChartPackets i) w :=
    fun w => by
      simp only [FunLike.coe_smul, Pi.smul_apply,
        (C.toChain.theta_retains_circle_BAS i w).1]
  refine ⟨fun w hw => ?_, ⟨?_, ?_, ?_⟩, C.toChain.Θ_BAS 0 ∘ φ, ?_, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨w₀, hw₀, rfl⟩ := hw
    have hm := C.gaf05_circlePatch_marker_GAFC i w₀ hw₀
    simp only [smul_apply, (C.toChain.theta_retains_circle_BAS i w₀).1,
      (C.toChain.theta_retains_circle_BAS i w₀).2, hm]
  · rintro _ ⟨w₀, hw₀, rfl⟩
    rw [hretC]
    exact hbij.mapsTo hw₀
  · rintro _ ⟨w₀, hw₀, rfl⟩ _ ⟨w₁, hw₁, rfl⟩ h
    rw [hretC, hretC] at h
    rw [hbij.injOn hw₀ hw₁ h]
  · intro a ha
    obtain ⟨w₀, hw₀, rfl⟩ := hbij.surjOn ha
    exact ⟨C.toChain.Θ_BAS 0 w₀, ⟨w₀, hw₀, rfl⟩, hretC w₀⟩
  · intro a ha
    obtain ⟨p, -, hp⟩ := hwit (φ a) (hmaps ha)
    have hΘ := C.toChain.contDiffAt_theta_BAS 0 p
    rw [hp] at hΘ
    exact hΘ.comp_contDiffWithinAt a (hφ a ha)
  · rintro _ ⟨w₀, hw₀, rfl⟩
    change C.toChain.Θ_BAS 0 (φ (((ρ i.1)⁻¹ • ⇑(gafCircleVector P.toLocalChartPackets i))
      (C.toChain.Θ_BAS 0 w₀))) = C.toChain.Θ_BAS 0 w₀
    rw [hret, hinv.1 hw₀]
  · intro a ha
    change ((ρ i.1)⁻¹ • ⇑(gafCircleVector P.toLocalChartPackets i)) (C.toChain.Θ_BAS 0 (φ a)) = a
    rw [hret]
    exact hinv.2 ha
  · intro a ha
    exact ⟨φ a, hmaps ha, rfl⟩

/-- **Consumer: GAF05 for the circle charts of a chain on the enhanced planes** (B:5971–6006):
for every circle index `i`, `v_i ≡ R_i` on `V_i⁰` and on its later image `V_i ⊂ W₁`, where
`R_i⁻¹u_i = u_i/v_i` is a bijection onto `B(0, 5.5)` with a smooth inverse chart; and on the
original threshold-6 plateau the stage image `g₁ p` and the final image `E p` have marker exactly
`R_i`. -/
theorem gaf05_circle_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    (∀ w ∈ C.toChain.circlePatch_BAS i, gafCircleMarker P.toLocalChartPackets i w = ρ i.1) ∧
    (∀ w ∈ C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE
        (gafCircleVector P.toLocalChartPackets i) (gafCircleMarker P.toLocalChartPackets i)
          (ρ i.1) 1,
      gafCircleMarker P.toLocalChartPackets i w = ρ i.1) ∧
    BijOn ((ρ i.1)⁻¹ • gafCircleVector P.toLocalChartPackets i)
      (C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets i)
        (gafCircleMarker P.toLocalChartPackets i) (ρ i.1) 1) (ball 0 (11 / 2 * 1)) ∧
    ∀ p, p ∈ ball i.1 (200 * ρ i.1) → ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 6 →
      gafCircleMarker P.toLocalChartPackets i (C.toChain.g₁ p) = ρ i.1 ∧
        gafCircleMarker P.toLocalChartPackets i (C.toChain.E p) = ρ i.1 := by
  refine ⟨C.gaf05_circlePatch_marker_GAFC i, C.gaf05_circleBase_marker_GAFC i,
    (C.gaf05_circleBase_chart_GAFC i).2.1, fun p hp hη => ?_⟩
  obtain ⟨-, -, h1, h2⟩ := C.toChain.gaf05_first_plateau_G47 C.planes₀ C.x₀ C.sel_eq.1
    C.plane_eq.1 (C.rough.sigma_le 0).le i hp hη
  exact ⟨h1, h2⟩

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
