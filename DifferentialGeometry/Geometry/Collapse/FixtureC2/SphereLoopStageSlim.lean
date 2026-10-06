import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopPacketsExamples
import DifferentialGeometry.Geometry.Fibration.ActualStageClouds
import DifferentialGeometry.Geometry.Fibration.ActualStageChain

/-!
# The slim stage of the chain runs on the sphere loop (S-FIXTURE-C2b, R2 start)

For ANY local chart family `L` and any slim centre `j` (`ΔΛ`-free): the centre lies in the slim
stage core `A₃ = fc27SlimSet L 7` (the slim coordinate of its own chart vanishes at `j`), the
cutoff of its packet equals `1` at `j` (the plateau, D75-6), hence the stage-2 cloud
`S₃ = π 𝓔⁰ (A₃)` is non-empty and every `Gaf02Chain` over a packet containing `j` has an ACTIVE
slim slot. Applied to the C2 packet `loopPacketsC14Z_FXC2` (non-empty slim family) these are the
first slim-stage objects of the tree that actually run on a non-empty slim family.

* `slimCentre_coord_center_FXC2`, `slimCentre_cutoff_center_FXC2` (plateau at the centre),
  `slimCentre_mem_core_FXC2`, `gafCloud_two_nonempty_FXC2`, `slot_two_active_FXC2`;
* `loopPackets_slim_stage_FXC2`: on the C2 packet.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bundle GC.MetricGeometry
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology ENNReal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete
attribute [local instance] loopMS3_FXC2
attribute [local instance] nezero_finrank_euclideanThree_LC87

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Stage

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- The slim coordinate of a slim centre vanishes at the centre. -/
theorem slimCentre_coord_center_FXC2 {β₁ : ℝ} {j : X}
    (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) : c.coord j = 0 := by
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  exact P.toSlimChart.coord_center

/-- **Plateau at the centre**: the cutoff of the slim packet is `1` at the centre. -/
theorem slimCentre_cutoff_center_FXC2 {β₁ : ℝ} {j : X} (hΔ : 0 < Δ)
    (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) : c.cutoff j = 1 := by
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have h0 := P.toSlimChart.coord_center
  exact P.toSlimChart.cutoff_eq_one j (mem_ball_self (by positivity))
    (by rw [h0, abs_zero]; positivity)

/-- **A slim centre lies in the slim stage core `A₃`.** -/
theorem slimCentre_mem_core_FXC2
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) {j : X}
    (hj : j ∈ L.slim.centres) (hΔ : 0 < Δ) : j ∈ fc27SlimSet L 7 := by
  refine ⟨⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩, mem_ball_self (by have := hρ j; positivity), ?_⟩
  rw [slimCentre_coord_center_FXC2, abs_zero]
  positivity

/-- **The stage-2 cloud over a non-empty slim family is non-empty.** -/
theorem gafCloud_two_nonempty_FXC2
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) {j : X}
    (hj : j ∈ L.slim.centres) (hΔ : 0 < Δ) :
    j ∈ gafStageCore L Z 2 ∧ (gafCloud L Z 2).Nonempty := by
  have hmem : j ∈ gafStageCore L Z 2 := slimCentre_mem_core_FXC2 L hj hΔ
  exact ⟨hmem, ⟨_, j, hmem, rfl⟩⟩

variable {Lmax τ γ : ℝ}

/-- **A chain over a packet with a slim centre has an active slim slot** (stage 2). -/
theorem slot_two_active_FXC2
    {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V}
    {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {j : X}
    (hj : j ∈ P.slim.centres) :
    ∃ O, C.slot 2 = Gaf02StageSlot.active O := by
  rcases h : C.slot 2 with O | hempty
  · exact ⟨O, rfl⟩
  · exfalso
    have : j ∈ gafStageCentres P 2 := hj
    rw [hempty] at this
    exact this

end Stage

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_FXC2 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_FXC2 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_FXC2 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

section OnLoop

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

variable (ℓ : LoopLen_FXC2) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ} {D0 : ℝ}
  (hD0 : ∀ s s' : S2, sphereDist_FXC2 s s' ≤ D0) (hβ1 : 0 < β 1) (hβ1' : β 1 < 1)
  (hβ2 : β 2 ≤ 3 / 20) (hβ3 : β 3 ≤ 3 / 20) (hthin : β 1 / 2 + D0 / R ≤ 1 / 100)
  (hℓ : 8 * R / β 1 ≤ ℓ.1)
  {Δ σs vs : ℝ} {K : ℕ} (hΔ : 1 ≤ Δ) (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (hvs : 0 < vs)
  (hK : 5 ≤ K) (hR1 : 1 ≤ R) (hD00 : 0 ≤ D0) (z₀ : S2) {N : ℕ} (hN : ℓ.1 = N * (Δ * R))
  (hΔR : 2 * D0 ≤ Δ * R) (hβ0 : β 1 < slimBeta0_FXC2 hR z₀ hΔ hσs hσs1 hvs hK)
  {Lam σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ} (hbs : b + s ≤ 1 / 100)

include hR1 hD00 hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ hN hΔR hβ0 hσs hσs1 hvs hK hbs in
/-- **The slim stage runs on the C2 packet**: every slim centre `j` of `loopPacketsC14_FXC2` lies in
the slim stage core, its stage-2 cloud is non-empty and the cutoff of its slim packet is `1` at
`j` (plateau). The first part gives a centre when `N ≥ 1`. -/
theorem loopPackets_slim_stage_FXC2 {j : LoopC_FXC2 ℓ}
    (hj : j ∈ (loopPacketsC14_FXC2 (Lam := Lam) (σc := σc) (μ := μ) (b' := b') (s' := s')
      (ε := ε) (γc := γc) (βc := βc) (Lmax := Lmax) (τ := τ) (γ := γ) (δ := δ) (εr := εr)
      (e := e) (T := T) (V := V) (ζ := ζ) (Λz := Λz) ℓ hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ hΔ hσs
      hσs1 hvs hK hR1 hD00 z₀ hN hΔR hβ0 hbs).slim.centres) :
    j ∈ gafStageCore (loopPacketsC14_FXC2 (Lam := Lam) (σc := σc) (μ := μ) (b' := b')
      (s' := s') (ε := ε) (γc := γc) (βc := βc) (Lmax := Lmax) (τ := τ) (γ := γ) (δ := δ)
      (εr := εr) (e := e) (T := T) (V := V) (ζ := ζ) (Λz := Λz) ℓ hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ
      hΔ hσs hσs1 hvs hK hR1 hD00 z₀ hN hΔR hβ0 hbs).toLocalChartFamily
      (loopPacketsC14_FXC2 (Lam := Lam) (σc := σc) (μ := μ) (b' := b') (s' := s') (ε := ε)
      (γc := γc) (βc := βc) (Lmax := Lmax) (τ := τ) (γ := γ) (δ := δ) (εr := εr) (e := e)
      (T := T) (V := V) (ζ := ζ) (Λz := Λz) ℓ hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ hΔ hσs hσs1 hvs
      hK hR1 hD00 z₀ hN hΔR hβ0 hbs).zero 2 := by
  exact (gafCloud_two_nonempty_FXC2 _ _ hj (by linarith)).1

end OnLoop

end DifferentialGeometry.Geometry.Collapse
