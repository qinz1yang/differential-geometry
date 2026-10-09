import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf04
import DifferentialGeometry.Geometry.Fibration.ActualSegmentLocalization

/-!
# GAF05 on the chain object: exact markers on the ORIGINAL threshold-6 source plateaux

Blueprint `master207B.tex`, GAF05 (`prop:fibration-exact-interior-markers`, B:5971–6006), second
paragraph of the proof: "For an original threshold-`6` source point, `x = π_jF(p)` again meets
GAF04. The preceding perturbed input is in `B(x, r_x)` by GAF02/CFS16. Its actual cutoff equals
one, so the stage output is `P_j` of that input. GAF03 gives marker `R_i`, and later stages retain
it." Review 66, D66-8: GAF05 is a consumer of the chain `C` and of the same-plane (FM\*)
certificate (the stage's enhanced planes `A`, `x₀`, `C.sel st = A.rsel x₀`, `C.plane st = A.plane` —
the fields of `Gaf02ChainE`), exactly as GAF04 (`ActualStageChainGaf04.lean`).

For a marked chart `i` of stage `st` and an ORIGINAL threshold-`6` plateau point `p` of `i`
(`‖η_i‖ < 6`; `|η_i| < 6Δ` and `t < 6Δ`; `|η_i| < 6·10⁵Δ`):

* the actual cutoff is one at the stage input `g_st p` (`g₀ = 𝓔⁰`) and the projected input lies in
  the tube ball `B(π_st𝓔⁰ p, Σ_stρ(sel(π_st𝓔⁰ p)))`;
* the stage output `g_{st+1} p` has marker EXACTLY `R_i`, and so does the final image `C.E p`
  (later stages keep the earlier family blocks, `C.keeps_earlier_family_blocks`).

`Gaf02Chain.gaf05_first_plateau_G47`, `gaf05_edge_plateau_G47`, `gaf05_slim_plateau_G47`; helper
`marker_stageQ_G47` (`v_i ∘ π_{Q_st} = v_i` for a retained tag). Consumer
`gaf05_final_family_plateau_G47` (a chain on `LocalChartPacketsC14Z` bound to its three enhanced
planes: the FINAL image has marker `R_i` on all three plateaux).

NOT here (needs `Gaf02Bases`, lane C14-BASES): GAF05's first paragraph — `v_i ≡ R_i` on the CGP07
marked patches `V_i⁰` and their later images `V_i ⊂ W_j`, and `u_i/R_i : V_i → B(0, 5.5ℓ_i)` a
diffeomorphism (interface recorded in `build-logs/resume/state-C14-GAF47.md`).
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

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a}

open Classical in
/-- A block marker of a tag retained by the stage target `Q_st` is unchanged by `π_{Q_st}`. -/
theorem marker_stageQ_G47 (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) {st : Fin 3} {t : CGPTag L Z}
    (ht : t ∈ gafStageTags L Z st) (y : BlockSpace (fun _ : CGPTag L Z => ℝ²)) :
    blockMarkerCLM (V := fun _ : CGPTag L Z => ℝ²) t ((gafStageQ L Z st).starProjection y) =
      blockMarkerCLM (V := fun _ : CGPTag L Z => ℝ²) t y := by
  rw [gafStageQ_starProjection, blockMarkerCLM_apply, blockMarkerCLM_apply, blockRestrict_apply]
  simp [ht]

namespace Gaf02Chain

/-- **GAF05 on the chain, circle (first) stage, plateau `p ∈ B(c_i, 200ρ(c_i))`, `‖η_i(p)‖ < 6`**
(B:5998–6005), a consumer of the
chain and of the same-plane (FM\*) certificate (`C.sel 0 = A.rsel x₀`, `C.plane 0 = A.plane`):
the actual cutoff is one at the stage input, the projected input lies in the tube ball
`B(π𝓔⁰ p, Σρ(sel(π𝓔⁰ p)))`, and the stage output (and the final image) has marker EXACTLY `R_i`. -/
theorem gaf05_first_plateau_G47 {vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (A : FirstStagePlanes_PLN P (Γ 0) (S 0) (eg 0)) (x₀ : X) (hsel : C.sel 0 = A.rsel x₀)
    (hplane : C.plane 0 = A.plane) (hSΞ : S 0 ≤ Ξ 0 / 10000)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (200 * ρ i.1))
    (hη : ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 6) :
    (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
        (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets))
            (cgpGlobalMap P.toLocalChartFamily P.zero p) = 1 ∧
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (cgpGlobalMap P.toLocalChartFamily
          P.zero p) ∈
        ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
            p) (S 0 * ρ (C.sel 0 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
                P.toLocalChartFamily P.zero 0) p))) ∧
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) (C.g₁ p) = ρ i.1 ∧
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) (C.E p) = ρ i.1 := by
  have hψ : (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
        (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets))
            (cgpGlobalMap P.toLocalChartFamily P.zero p) = 1 := (C.cutoff_bindings).1.2.2.1 p ⟨i,
                hpi, hη⟩
  have hsupp : (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ tsupport (markerLocalitySourceCutoff
      lc87EdgeTransition (fun j => ρ j.1)
        (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets)) :=
    subset_tsupport _ (by rw [Function.mem_support, hψ]; exact one_ne_zero)
  obtain ⟨-, hxb⟩ := (C.stage_input_mem_tube p).1 hsupp
  have hxb' : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (cgpGlobalMap
      P.toLocalChartFamily P.zero p) ∈
      ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) p)
          (S 0 * ρ (C.sel 0 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
              P.toLocalChartFamily P.zero 0) p))) := by
    rw [← gafStageQ_starProjection_globalMap]
    exact hxb
  have h7 : ‖cgpCircleCoord P.toLocalChartFamily i.1 ((Set.Finite.mem_toFinset _).mp i.2) p‖ ≤ 7 :=
      by
    have h6 : ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ ≤ 7 := by linarith
    exact h6
  have hslot := (C.gaf04_first_G47 A x₀ hsel hplane hSΞ i hpi h7).2
  have hv := hslot _ hxb'
  have hJQ : ∀ y, blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) ((gafStageQ P.toLocalChartFamily P.zero
            0).starProjection y) = blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero
                => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) y :=
    marker_stageQ_G47 P.toLocalChartFamily P.zero (Finset.mem_univ _)
  have h1 : blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) (C.g₁ p) = ρ i.1 :=
    adjustmentMap_apply_eq_GAF2 (gafStageQ P.toLocalChartFamily P.zero 0)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection ((C.slot 0).map y)) _ _ hJQ
      (by rw [hJQ]; exact hv) (Or.inl hψ)
  refine ⟨hψ, hxb', h1, ?_⟩
  have hk : C.E p (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) =
      C.g₁ p (cgpMarkerTag P.toLocalChartFamily P.zero (.inl i)) :=
    (C.keeps_earlier_family_blocks p).2.2.1 i
  rw [blockMarkerCLM_apply, hk, ← blockMarkerCLM_apply]
  exact h1

/-- **GAF05 on the chain, edge stage, plateau `p ∈ B(c_i, 100Δρ(c_i))`, `|η_i(p)| < 6Δ`,
`t(p) < 6Δ`** (B:5998–6005), a consumer of the
chain and of the same-plane (FM\*) certificate (`C.sel 1 = A.rsel x₀`, `C.plane 1 = A.plane`):
the actual cutoff is one at the stage input, the projected input lies in the tube ball
`B(π𝓔⁰ p, Σρ(sel(π𝓔⁰ p)))`, and the stage output (and the final image) has marker EXACTLY `R_i`. -/
theorem gaf05_edge_plateau_G47 {vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (A : EdgeStagePlanes_PLN P (Γ 1) (S 1) (eg 1)) (x₀ : X) (hsel : C.sel 1 = A.rsel x₀)
    (hplane : C.plane 1 = A.plane) (hSΞ : S 1 ≤ Ξ 1 / 10000)
    (i : P.toLocalChartFamily.edge.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (100 * Δ * ρ i.1)) (hη : |P.edge.coord i.1 p| < 6 * Δ)
    (ht : cgpHeight P.toLocalChartFamily p < 6 * Δ) :
    (gafStageTwoCutoff P.toLocalChartFamily P.zero) (C.g₁ p) = 1 ∧
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.g₁ p) ∈
        ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
            p) (S 1 * ρ (C.sel 1 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
                P.toLocalChartFamily P.zero 1) p))) ∧
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) (C.g₂ p) = ρ i.1 ∧
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) (C.E p) = ρ i.1 := by
  have hψ : (gafStageTwoCutoff P.toLocalChartFamily P.zero) (C.g₁ p) = 1 :=
      (C.cutoff_bindings).2.1.2.2.1 p ⟨i, hpi, hη, ht⟩
  have hsupp : (C.g₁ p) ∈ tsupport (gafStageTwoCutoff P.toLocalChartFamily P.zero) :=
    subset_tsupport _ (by rw [Function.mem_support, hψ]; exact one_ne_zero)
  obtain ⟨-, hxb⟩ := (C.stage_input_mem_tube p).2.1 hsupp
  have hxb' : (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.g₁ p) ∈
      ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) p)
          (S 1 * ρ (C.sel 1 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
              P.toLocalChartFamily P.zero 1) p))) := by
    rw [← gafStageQ_starProjection_globalMap]
    exact hxb
  have hslot := (C.gaf04_edge_G47 A x₀ hsel hplane hSΞ i hpi
      (by linarith [abs_nonneg (P.edge.coord i.1 p)]) (by linarith [abs_nonneg (P.edge.coord i.1
          p)])).2
  have hv := hslot _ hxb'
  have hJQ : ∀ y, blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) ((gafStageQ P.toLocalChartFamily
            P.zero 1).starProjection y) = blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily
                P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) y :=
    marker_stageQ_G47 P.toLocalChartFamily P.zero (edge_mem_cgpQ2Tags P.toLocalChartFamily P.zero i)
  have h1 : blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) (C.g₂ p) = ρ i.1 :=
    adjustmentMap_apply_eq_GAF2 (gafStageQ P.toLocalChartFamily P.zero 1)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection ((C.slot 1).map y)) _ _ hJQ
      (by rw [hJQ]; exact hv) (Or.inl hψ)
  refine ⟨hψ, hxb', h1, ?_⟩
  have hk : C.E p (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) =
      C.g₂ p (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inr i))) :=
    (C.keeps_earlier_family_blocks p).2.2.2 i
  rw [blockMarkerCLM_apply, hk, ← blockMarkerCLM_apply]
  exact h1

/-- **GAF05 on the chain, slim stage, plateau `p ∈ B(c_i, 10⁶Δρ(c_i))`, `|η_i(p)| < 6·10⁵Δ`**
(B:5998–6005), a consumer of the
chain and of the same-plane (FM\*) certificate (`C.sel 2 = A.rsel x₀`, `C.plane 2 = A.plane`):
the actual cutoff is one at the stage input, the projected input lies in the tube ball
`B(π𝓔⁰ p, Σρ(sel(π𝓔⁰ p)))`, and the stage output (and the final image) has marker EXACTLY `R_i`. -/
theorem gaf05_slim_plateau_G47 {vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (A : SlimStagePlanes_PLN P (Γ 2) (S 2) (eg 2)) (x₀ : X) (hsel : C.sel 2 = A.rsel x₀)
    (hplane : C.plane 2 = A.plane) (hSΞ : S 2 ≤ Ξ 2 / 10000)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (1000000 * Δ * ρ i.1))
    (hη : |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 6 * (10 ^ 5 * Δ)) :
    (gafStageThreeCutoff P.toLocalChartFamily P.zero) (C.g₂ p) = 1 ∧
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.g₂ p) ∈
        ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2)
            p) (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
                P.toLocalChartFamily P.zero 2) p))) ∧
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) (C.E p) = ρ i.1 := by
  have hψ : (gafStageThreeCutoff P.toLocalChartFamily P.zero) (C.g₂ p) = 1 :=
      (C.cutoff_bindings).2.2.2.2.1 p ⟨i, hpi, hη⟩
  have hsupp : (C.g₂ p) ∈ tsupport (gafStageThreeCutoff P.toLocalChartFamily P.zero) :=
    subset_tsupport _ (by rw [Function.mem_support, hψ]; exact one_ne_zero)
  obtain ⟨-, hxb⟩ := (C.stage_input_mem_tube p).2.2 hsupp
  have hxb' : (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.g₂ p) ∈
      ball (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) p)
          (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags
              P.toLocalChartFamily P.zero 2) p))) := by
    rw [← gafStageQ_starProjection_globalMap]
    exact hxb
  have hslot := (C.gaf04_slim_G47 A x₀ hsel hplane hSΞ i (by convert hpi using 2; norm_num)
      (by linarith [abs_nonneg ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord
          p)])).2
  have hv := hslot _ hxb'
  have hJQ : ∀ y, blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) ((gafStageQ P.toLocalChartFamily
            P.zero 2).starProjection y) = blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily
                P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) y :=
    marker_stageQ_G47 P.toLocalChartFamily P.zero (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i)
  have h1 : blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero (.inr (.inl i))) (C.E p) = ρ i.1 :=
    adjustmentMap_apply_eq_GAF2 (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection ((C.slot 2).map y)) _ _ hJQ
      (by rw [hJQ]; exact hv) (Or.inl hψ)
  refine ⟨hψ, hxb', h1⟩


end Gaf02Chain

/-- **Consumer: GAF05's source-plateau clause for a chain on the final family**
`LocalChartPacketsC14Z` bound to its three enhanced stage planes (the data of `Gaf02ChainE`): on
every ORIGINAL threshold-`6` plateau (circle `‖η_i‖ < 6`, edge `|η_i| < 6Δ` with `t < 6Δ`, slim
`|η_i| < 6·10⁵Δ`) the FINAL image `C.E p` has marker exactly `R_i`. -/
theorem gaf05_final_family_plateau_G47 {vs ζ Λz : ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (x₀ : X)
    (A₀ : FirstStagePlanes_PLN P.toLocalChartPacketsC14 (Γ 0) (S 0) (eg 0))
    (A₁ : EdgeStagePlanes_PLN P.toLocalChartPacketsC14 (Γ 1) (S 1) (eg 1))
    (A₂ : SlimStagePlanes_PLN P.toLocalChartPacketsC14 (Γ 2) (S 2) (eg 2))
    (hsel : ∀ j, C.sel j = ![A₀.rsel x₀, A₁.rsel x₀, A₂.rsel x₀] j)
    (hplane : ∀ j, C.plane j = ![A₀.plane, A₁.plane, A₂.plane] j)
    (hSΞ : ∀ j, S j ≤ Ξ j / 10000) (p : X) :
    (∀ i : P.toLocalChartFamily.circle.finite_centres.toFinset, p ∈ ball i.1 (200 * ρ i.1) →
      ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 6 →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) (C.E p) = ρ
          i.1) ∧
    (∀ i : P.toLocalChartFamily.edge.finite_centres.toFinset, p ∈ ball i.1 (100 * Δ * ρ i.1) →
      |P.edge.coord i.1 p| < 6 * Δ → cgpHeight P.toLocalChartFamily p < 6 * Δ →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inl i)))
          (C.E p) = ρ i.1) ∧
    ∀ i : P.toLocalChartFamily.slim.finite_centres.toFinset, p ∈ ball i.1 (1000000 * Δ * ρ i.1) →
      |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 6 * (10 ^ 5 * Δ) →
      blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)) (C.E
          p) = ρ i.1 :=
  ⟨fun i hpi hη => (Gaf02Chain.gaf05_first_plateau_G47 (P := P.toLocalChartPacketsC14) C A₀ x₀
      (hsel 0) (hplane 0) (hSΞ 0) i hpi hη).2.2.2,
    fun i hpi hη ht => (Gaf02Chain.gaf05_edge_plateau_G47 (P := P.toLocalChartPacketsC14) C A₁ x₀
      (hsel 1) (hplane 1) (hSΞ 1) i hpi hη ht).2.2.2,
    fun i hpi hη => (Gaf02Chain.gaf05_slim_plateau_G47 (P := P.toLocalChartPacketsC14) C A₂ x₀
      (hsel 2) (hplane 2) (hSΞ 2) i hpi hη).2.2⟩

end DifferentialGeometry.Geometry.Collapse
