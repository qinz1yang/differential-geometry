import DifferentialGeometry.Geometry.Fibration.ActualStageCoreKernel

/-!
# GAF02 CORE exports: kept coordinates, the scale exit and the empty-family identity stages

Blueprint `master207B.tex`, GAF02 (B:5797) and review 55 / draft 59 §3.4–3.5. For
`Ψ = adjustmentMap Q (π_Q ∘ a) ψ` (ADJ):

* `adjustmentMap_sub_mem_GAF8`: `Ψ z − z ∈ Q`, hence `proj_{Q^⊥} Ψ z = proj_{Q^⊥} z`;
  `adjustmentMap_eq_id_of_cutoff_GAF8`: a vanishing cutoff gives `Ψ = id`;
  `adjustmentMap_starProjection_eq_id_GAF8`: the smoothing `π_Q ∘ id` gives `Ψ = id` (inactive
  slot).
* `gafStage_adjust_kept_GAF8`: on the actual stage targets, every block whose tag is not a stage tag
  is kept by the stage adjustment; `gafStage_kept_tags_GAF8`: the scale, `E'` and circle blocks are
  not stage tags of stages two and three, and the edge blocks are not stage tags of stage three.
* `gafScale_exit_GAF8`: if a stage-one output `g₁` has `‖g₁ − 𝓔⁰‖ < c₀ρ` with `c₀ ≤ 1` and
  later stages keep the scale block, then `s = ℓ_ρ(E) = ℓ_ρ(g₁)`, `|s − ρ| < c₀ρ` and `s > 0`.
* `gafStageOne_scale_blend_GAF8`: the exact first-stage scale formula
  `ℓ_ρ(g₁) = (1 − χ)ρ + χ z_ρ`, `χ = ψ₁ ∘ 𝓔⁰`, `z_ρ = ℓ_ρ(a₀ ∘ 𝓔⁰)` (SCALE-EXIT).
* `gafStage_cutoff_empty_GAF8`: the actual cutoffs `ψ₁, ψ₂, ψ₃` vanish identically when the circle,
  edge, resp. slim family is empty (sum over an empty index set), so the stage is the identity.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_GAF8x
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF8x
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF8x
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

section Generic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- (ADJ) with the smoothing `π_Q ∘ a`: the adjustment moves only inside `Q`. -/
theorem adjustmentMap_sub_mem_GAF8 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] (a : H → H)
    (ψ : H → ℝ) (z : H) :
    adjustmentMap Q (fun y => Q.starProjection (a y)) ψ z - z ∈ Q := by
  rw [adjustmentMap_apply, add_sub_cancel_left]
  exact Q.smul_mem _ (Q.sub_mem (Submodule.starProjection_apply_mem _ _)
    (Submodule.starProjection_apply_mem _ _))

/-- A vanishing cutoff makes the adjustment the identity. -/
theorem adjustmentMap_eq_id_of_cutoff_GAF8 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    (P : H → H) {ψ : H → ℝ} (hψ : ∀ z, ψ z = 0) : adjustmentMap Q P ψ = id := by
  funext z
  rw [adjustmentMap_apply, hψ z, zero_smul, add_zero, id]

/-- The smoothing `π_Q ∘ id` makes the adjustment the identity (the inactive stage). -/
theorem adjustmentMap_starProjection_eq_id_GAF8 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    (ψ : H → ℝ) : adjustmentMap Q (fun y => Q.starProjection y) ψ = id := by
  funext z
  rw [adjustmentMap_apply, Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem Q z), sub_self, smul_zero, add_zero, id]

end Generic

section Actual

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a}
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

open Classical in
/-- A vector of the stage target `Q_st` has zero blocks off the stage tags. -/
theorem gafStageQ_apply_eq_zero_GAF8 {st : Fin 3}
    {y : BlockSpace (fun _ : CGPTag L Z => ℝ²)} (hy : y ∈ gafStageQ L Z st)
    {t : CGPTag L Z} (ht : t ∉ gafStageTags L Z st) : y t = 0 := by
  obtain ⟨w, rfl⟩ := hy
  change blockRestrict (gafStageTags L Z st) w t = 0
  rw [blockRestrict_apply]
  simp [ht]

/-- **Kept coordinates**: the stage adjustment keeps every block off the stage tags. -/
theorem gafStage_adjust_kept_GAF8 (st : Fin 3)
    (a : BlockSpace (fun _ : CGPTag L Z => ℝ²) → BlockSpace (fun _ : CGPTag L Z => ℝ²))
    (ψ : BlockSpace (fun _ : CGPTag L Z => ℝ²) → ℝ) (z : BlockSpace (fun _ : CGPTag L Z => ℝ²))
    {t : CGPTag L Z} (ht : t ∉ gafStageTags L Z st) :
    adjustmentMap (gafStageQ L Z st) (fun y => (gafStageQ L Z st).starProjection (a y)) ψ z t =
      z t := by
  have h := gafStageQ_apply_eq_zero_GAF8 L Z (adjustmentMap_sub_mem_GAF8 _ a ψ z) ht
  rwa [PiLp.sub_apply, sub_eq_zero] at h

/-- The tags kept by the later stages: the scale and `E'` blocks and the circle blocks are not
stage tags of stages two (`Q₂`) and three (`Q₃`); the edge blocks are not stage tags of stage three;
`Q₃`'s tags are `Q₂`'s tags. -/
theorem gafStage_kept_tags_GAF8 :
    cgpScaleTag L Z ∉ gafStageTags L Z 1 ∧ cgpScaleTag L Z ∉ gafStageTags L Z 2 ∧
    cgpEdgeTag L Z ∉ gafStageTags L Z 1 ∧ cgpEdgeTag L Z ∉ gafStageTags L Z 2 ∧
    (∀ j : L.circle.finite_centres.toFinset, (.inl j : CGPTag L Z) ∉ gafStageTags L Z 1 ∧
      (.inl j : CGPTag L Z) ∉ gafStageTags L Z 2) ∧
    (∀ j : L.edge.finite_centres.toFinset,
      (.inr (.inr (.inl j)) : CGPTag L Z) ∉ gafStageTags L Z 2) ∧
    ∀ t, t ∉ gafStageTags L Z 1 → t ∉ gafStageTags L Z 2 := by
  have h2 : ∀ t, t ∈ gafStageTags L Z 1 ↔ cgpInQ2 L Z t = true := fun t => by
    change t ∈ cgpQ2Tags L Z ↔ _
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  have h3 : ∀ t, t ∈ gafStageTags L Z 2 ↔ cgpInQ3 L Z t = true := fun t => by
    change t ∈ cgpQ3Tags L Z ↔ _
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun j => ⟨fun h => ?_, fun h => ?_⟩,
    fun j h => ?_, fun t ht h => ht ?_⟩
  · exact absurd ((h2 _).mp h) (by simp [cgpInQ2])
  · exact absurd ((h3 _).mp h) (by simp [cgpInQ3])
  · exact absurd ((h2 _).mp h) (by simp [cgpInQ2])
  · exact absurd ((h3 _).mp h) (by simp [cgpInQ3])
  · exact absurd ((h2 _).mp h) (by simp [cgpInQ2])
  · exact absurd ((h3 _).mp h) (by simp [cgpInQ3])
  · exact absurd ((h3 _).mp h) (by simp [cgpInQ3])
  · rw [h2]
    have h' := (h3 _).mp h
    rcases t with t | t | t | t | t <;> simp_all [cgpInQ2, cgpInQ3]

/-- **The scale exit.** If `‖g₁ − 𝓔⁰‖ < c₀ρ`, `c₀ ≤ 1` and `E` keeps the scale block of `g₁`, then
`s = ℓ_ρ(E) = ℓ_ρ(g₁)`, `|s − ρ| < c₀ρ` and `s > 0`. -/
theorem gafScale_exit_GAF8 {c₀ : ℝ} (hc₀ : c₀ ≤ 1)
    (g₁ E : X → BlockSpace (fun _ : CGPTag L Z => ℝ²))
    (hg₁ : ∀ p, ‖g₁ p - cgpGlobalMap L Z p‖ < c₀ * ρ p)
    (hkeep : ∀ p, E p (cgpScaleTag L Z) = g₁ p (cgpScaleTag L Z)) (p : X) :
    gafScaleMarker L Z (E p) = gafScaleMarker L Z (g₁ p) ∧
      |gafScaleMarker L Z (E p) - ρ p| < c₀ * ρ p ∧ 0 < gafScaleMarker L Z (E p) := by
  have hEq : gafScaleMarker L Z (E p) = gafScaleMarker L Z (g₁ p) := by
    change (E p (cgpScaleTag L Z)).snd = (g₁ p (cgpScaleTag L Z)).snd
    rw [hkeep p]
  have hF : gafScaleMarker L Z (cgpGlobalMap L Z p) = ρ p := cgpGlobalMap_scale L Z p
  have hlin : |gafScaleMarker L Z (g₁ p) - ρ p| < c₀ * ρ p := by
    have hsub : gafScaleMarker L Z (g₁ p) - ρ p =
        gafScaleMarker L Z (g₁ p - cgpGlobalMap L Z p) := by rw [map_sub, hF]
    rw [hsub]
    refine lt_of_le_of_lt ?_ (hg₁ p)
    have h1 := (gafScaleMarker L Z).le_opNorm (g₁ p - cgpGlobalMap L Z p)
    have h2 : ‖gafScaleMarker L Z‖ ≤ 1 := norm_blockMarkerCLM_le _
    rw [Real.norm_eq_abs] at h1
    nlinarith [norm_nonneg (g₁ p - cgpGlobalMap L Z p)]
  refine ⟨hEq, hEq ▸ hlin, ?_⟩
  rw [hEq]
  have := (abs_lt.mp hlin).1
  nlinarith [hρ p]

open Classical in
/-- **SCALE-EXIT, first stage.** For `g₁ = Ψ₁ ∘ 𝓔⁰` with `Ψ₁ = adjustmentMap Q₁ (π_{Q₁} ∘ a₀) ψ`
(`Q₁ = H`): `ℓ_ρ(g₁ p) = (1 − χ(p))ρ(p) + χ(p) z_ρ(p)` with `χ = ψ ∘ 𝓔⁰`, `z_ρ = ℓ_ρ ∘ a₀ ∘ 𝓔⁰`. -/
theorem gafStageOne_scale_blend_GAF8
    (a : BlockSpace (fun _ : CGPTag L Z => ℝ²) → BlockSpace (fun _ : CGPTag L Z => ℝ²))
    (ψ : BlockSpace (fun _ : CGPTag L Z => ℝ²) → ℝ) (p : X) :
    gafScaleMarker L Z (adjustmentMap (gafStageQ L Z 0)
        (fun y => (gafStageQ L Z 0).starProjection (a y)) ψ (cgpGlobalMap L Z p)) =
      (1 - ψ (cgpGlobalMap L Z p)) * ρ p +
        ψ (cgpGlobalMap L Z p) * gafScaleMarker L Z (a (cgpGlobalMap L Z p)) := by
  have hid : ∀ y, (gafStageQ L Z 0).starProjection y = y := fun y => by
    rw [gafStageQ_starProjection]
    change blockRestrict Finset.univ y = y
    rw [blockRestrict_univ]
    rfl
  rw [adjustmentMap_apply, hid, hid, map_add, map_smul, map_sub, smul_eq_mul]
  have hF : gafScaleMarker L Z (cgpGlobalMap L Z p) = ρ p := cgpGlobalMap_scale L Z p
  rw [hF]
  ring

end Actual

/-- **Empty-family identity stages.** The actual cutoffs vanish identically on an empty family:
`ψ₁ ≡ 0` if there are no circle centres, `ψ₂ ≡ 0` if there are no edge centres, `ψ₃ ≡ 0` if there
are no slim centres; hence the corresponding stage adjustment is the identity for every
smoothing. -/
theorem gafStage_cutoff_empty_GAF8
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V) :
    (P.circle.centres = ∅ → ∀ z,
      markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P) z = 0) ∧
    (P.edge.centres = ∅ → ∀ z, gafStageTwoCutoff P.toLocalChartFamily P.zero z = 0) ∧
    (P.slim.centres = ∅ → ∀ z, gafStageThreeCutoff P.toLocalChartFamily P.zero z = 0) := by
  refine ⟨fun h z => ?_, fun h z => ?_, fun h z => ?_⟩
  · have : IsEmpty P.circle.finite_centres.toFinset :=
      ⟨fun j => by simpa [h] using (Set.Finite.mem_toFinset _).mp j.2⟩
    rw [markerLocalitySourceCutoff, Finset.univ_eq_empty, Finset.sum_empty]
    exact cfsRamp_eq_zero (fun t ht => lc87EdgeTransition_eq_zero ht) (by norm_num) (by norm_num)
  · have : IsEmpty P.edge.finite_centres.toFinset :=
      ⟨fun j => by simpa [h] using (Set.Finite.mem_toFinset _).mp j.2⟩
    rw [gafStageTwoCutoff, cfsBufferedEdgeCutoff, Finset.univ_eq_empty, Finset.sum_empty]
    exact cfsRamp_eq_zero (fun t ht => lc87EdgeTransition_eq_zero ht) (by norm_num) (by norm_num)
  · have : IsEmpty P.slim.finite_centres.toFinset :=
      ⟨fun j => by simpa [h] using (Set.Finite.mem_toFinset _).mp j.2⟩
    rw [gafStageThreeCutoff, cfsUniformAxisCutoff, Finset.univ_eq_empty, Finset.sum_empty]
    exact cfsRamp_eq_zero (fun t ht => lc87EdgeTransition_eq_zero ht) (by norm_num) (by norm_num)

/-- **Consumer of the GAF02 CORE kernel: the scale exit on the chain.** On the kernel's data, the
final map `E` keeps the scale block of `g₁`, so `s = ℓ_ρ(E) = ℓ_ρ(g₁)`, `|s − ρ| < c₀ρ`, `s > 0`,
and `ℓ_ρ(g₁) = (1 − χ)ρ + χ z_ρ` with `χ = ψ₁ ∘ 𝓔⁰`, `z_ρ = ℓ_ρ ∘ a₀ ∘ 𝓔⁰`. -/
theorem gaf02_core_scale_exit_GAF8
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    (sel₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₀ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (sel₀ x) = x)
    {Ξ₀ sg₀ eg₀ : ℝ} (hsg₀ : 0 < sg₀) (hΞ₀ : 0 < Ξ₀) (hmo₀ : 128 * Ξ₀⁻¹ * sg₀ ≤ 1 / 5)
    (heg₀ : 0 ≤ eg₀)
    (plane₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hplaneQ₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      plane₀ x ≤ gafStageQ P.toLocalChartFamily P.zero 0)
    (hpp₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane₀ x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (hrank₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x → ∀ v,
        ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
            ((plane₀ x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpGlobalMap P.toLocalChartFamily P.zero) q) v :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))‖ ≤
          eg₀ * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v))
    (a₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm₀ : ContDiffOn ℝ ∞ a₀ (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ball x (sg₀ * ρ (sel₀ x))))
    (hab₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg₀ * ρ (sel₀ x)),
      ‖a₀ z - (x + (plane₀ x).starProjection (z - x))‖ ≤ Ξ₀ * (sg₀ * ρ (sel₀ x)) ∧
      DifferentiableAt ℝ a₀ z ∧ ‖fderiv ℝ a₀ z - (plane₀ x).starProjection‖ ≤ Ξ₀ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 0,
          (closedBall i (80 * Ξ₀⁻¹ * (sg₀ * ρ (sel₀ i))) ∩
            ball x (8 * Ξ₀⁻¹ * (sg₀ * ρ (sel₀ x)))).Nonempty →
          Kk.starProjection i = c ∧ plane₀ i ≤ Kkᗮ) →
        Kk.starProjection (a₀ z) = c)
    (sel₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₁ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
        (sel₁ x) = x)
    {Ξ₁ sg₁ eg₁ : ℝ} (hsg₁ : 0 < sg₁) (hΞ₁ : 0 < Ξ₁) (hmo₁ : 128 * Ξ₁⁻¹ * sg₁ ≤ 1 / 5)
    (heg₁ : 0 ≤ eg₁)
    (plane₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hplaneQ₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
      plane₁ x ≤ gafStageQ P.toLocalChartFamily P.zero 1)
    (hpp₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane₁ x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (hrank₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∃ i ∈ P.edge.centres,
      ∀ q : X,
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
        ∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
          ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
            (plane₁ x).starProjection
              ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg₁)
    (a₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm₁ : ContDiffOn ℝ ∞ a₁ (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
      ball x (sg₁ * ρ (sel₁ x))))
    (hab₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ z ∈ ball x (sg₁ * ρ (sel₁ x)),
      ‖a₁ z - (x + (plane₁ x).starProjection (z - x))‖ ≤ Ξ₁ * (sg₁ * ρ (sel₁ x)) ∧
      DifferentiableAt ℝ a₁ z ∧ ‖fderiv ℝ a₁ z - (plane₁ x).starProjection‖ ≤ Ξ₁ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 1,
          (closedBall i (80 * Ξ₁⁻¹ * (sg₁ * ρ (sel₁ i))) ∩
            ball x (8 * Ξ₁⁻¹ * (sg₁ * ρ (sel₁ x)))).Nonempty →
          Kk.starProjection i = c ∧ plane₁ i ≤ Kkᗮ) →
        Kk.starProjection (a₁ z) = c)
    (sel₂ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₂ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2)
        (sel₂ x) = x)
    {Ξ₂ sg₂ eg₂ : ℝ} (hsg₂ : 0 < sg₂) (hΞ₂ : 0 < Ξ₂) (hmo₂ : 128 * Ξ₂⁻¹ * sg₂ ≤ 1 / 5)
    (heg₂ : 0 ≤ eg₂)
    (plane₂ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hplaneQ₂ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      plane₂ x ≤ gafStageQ P.toLocalChartFamily P.zero 2)
    (hpp₂ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane₂ x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (hrank₂ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
      ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q = x →
        ∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) q v -
            ((plane₂ x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero))
                q) v : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))‖ ≤
          eg₂ * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v))
    (a₂ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hsm₂ : ContDiffOn ℝ ∞ a₂ (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      ball x (sg₂ * ρ (sel₂ x))))
    (hab₂ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ z ∈ ball x (sg₂ * ρ (sel₂ x)),
      ‖a₂ z - (x + (plane₂ x).starProjection (z - x))‖ ≤ Ξ₂ * (sg₂ * ρ (sel₂ x)) ∧
      DifferentiableAt ℝ a₂ z ∧ ‖fderiv ℝ a₂ z - (plane₂ x).starProjection‖ ≤ Ξ₂ ∧
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 2,
          (closedBall i (80 * Ξ₂⁻¹ * (sg₂ * ρ (sel₂ i))) ∩
            ball x (8 * Ξ₂⁻¹ * (sg₂ * ρ (sel₂ x)))).Nonempty →
          Kk.starProjection i = c ∧ plane₂ i ≤ Kkᗮ) →
        Kk.starProjection (a₂ z) = c)
    {c₀ : ℝ} (hv₁ : 5 / 3 * Ξ₀ * sg₀ < c₀) (hc₀ : c₀ ≤ 1 / 512)
    (hd₁ : (5 / 3 * Ξ₀ * sg₀ * gafCutoffConstant * gafDerivativeBound +
        Ξ₀ * gafDerivativeBound + eg₀) < c₀)
    (hc₀κ : c₀ ≤ 4 * gafKappa / 5) (hc₀s : c₀ ≤ 3 * sg₁ / 10) {c₁ : ℝ}
    (hv₂ : (c₀ + (5 / 3 * Ξ₁ * sg₁ + (1 + Ξ₁) * c₀)) < c₁) (hc₁ : c₁ ≤ 1 / 512)
    (hd₂ : ((5 / 3 * Ξ₁ * sg₁ + (1 + Ξ₁) * c₀) * gafCutoffConstant * (gafDerivativeBound + c₀) +
        Ξ₁ * (gafDerivativeBound + c₀) + eg₁ + 2 * c₀) < c₁)
    (hc₁κ : c₁ ≤ 4 * gafKappa / 5) (hc₁s : c₁ ≤ 3 * sg₂ / 10) {c₂ : ℝ}
    (hv₃ : (c₁ + (5 / 3 * Ξ₂ * sg₂ + (1 + Ξ₂) * c₁)) < c₂) (hc₂ : c₂ ≤ 1 / 512)
    (hd₃ : ((5 / 3 * Ξ₂ * sg₂ + (1 + Ξ₂) * c₁) * gafCutoffConstant * (gafDerivativeBound + c₁) +
        Ξ₂ * (gafDerivativeBound + c₁) + eg₂ + 2 * c₁) < c₂) (p : X) :
    gafScaleMarker P.toLocalChartFamily P.zero
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
          (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
          (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
            (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
            (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
            (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
              (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
              (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
                (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) p) =
      gafScaleMarker P.toLocalChartFamily P.zero
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p) ∧
    |gafScaleMarker P.toLocalChartFamily P.zero
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
          (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
          (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
            (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
            (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
            (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
              (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
              (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
                (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) p) - ρ p| <
      c₀ * ρ p ∧
    0 < gafScaleMarker P.toLocalChartFamily P.zero
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
          (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
          (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
            (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
            (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
            (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
              (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
              (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
                (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) p) ∧
    gafScaleMarker P.toLocalChartFamily P.zero
        ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p) =
      (1 - (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P))
          (cgpGlobalMap P.toLocalChartFamily P.zero p)) * ρ p +
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P))
          (cgpGlobalMap P.toLocalChartFamily P.zero p) *
          gafScaleMarker P.toLocalChartFamily P.zero
            (a₀ (cgpGlobalMap P.toLocalChartFamily P.zero p)) := by
  have k := gaf02_core_kernel_GAF8 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    sel₀ hsel₀ hsg₀ hΞ₀ hmo₀ heg₀ plane₀ hplaneQ₀ hpp₀ hrank₀ a₀ hsm₀ hab₀
    sel₁ hsel₁ hsg₁ hΞ₁ hmo₁ heg₁ plane₁ hplaneQ₁ hpp₁ hrank₁ a₁ hsm₁ hab₁
    sel₂ hsel₂ hsg₂ hΞ₂ hmo₂ heg₂ plane₂ hplaneQ₂ hpp₂ hrank₂ a₂ hsm₂ hab₂
    hv₁ hc₀ hd₁ hc₀κ hc₀s hv₂ hc₁ hd₂ hc₁κ hc₁s hv₃ hc₂ hd₃
  have ht := gafStage_kept_tags_GAF8 P.toLocalChartFamily P.zero
  have hkeep : ∀ q, ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
            (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (a₂ y))
            (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘
            (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1)
              (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (a₁ y))
              (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘
              (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
                (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
                (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
                  (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero))) q)
        (cgpScaleTag P.toLocalChartFamily P.zero) =
      ((adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0)
            (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (a₀ y))
            (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
              (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) q)
        (cgpScaleTag P.toLocalChartFamily P.zero) := fun q =>
    (gafStage_adjust_kept_GAF8 _ _ 2 _ _ _ ht.2.1).trans
      (gafStage_adjust_kept_GAF8 _ _ 1 _ _ _ ht.1)
  have hex := gafScale_exit_GAF8 P.toLocalChartFamily P.zero (hc₀.trans (by norm_num)) _ _
    k.2.2.2.1 hkeep p
  exact ⟨hex.1, hex.2.1, hex.2.2, gafStageOne_scale_blend_GAF8 _ _ _ _ p⟩

end DifferentialGeometry.Geometry.Collapse
