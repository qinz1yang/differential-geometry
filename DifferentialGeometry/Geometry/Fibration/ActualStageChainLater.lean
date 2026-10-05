import DifferentialGeometry.Geometry.Fibration.ActualStageChainPatches
import DifferentialGeometry.Geometry.Metric.UniformCutoffConsumer

/-!
# GAF02 BASES, sixth step (algebra): the later transports `Θ_j` of the chain

Blueprint `master207B.tex`, CGP08 (B:4259–4316); external draft 59 §4 "第六步" (D59-5); review 66
§5.3 (D66-7: the descent of the ACTUAL third-stage cutoff through the `gafStageTags` inclusions, not
only `Q₃ ⊆ Q₂`; an image-neighbourhood smoothness exit `ContDiffAt Ψ₃ (g₂ p)` from native-tube
smoothness + closed-support localization + off-support identity). Indexed by ONE chain `C`.

* Tag facts: `gafStageQ_two_le_one_BAS` (`Q₃ ≤ Q₂` from `cgpQ3Tags ⊆ cgpQ2Tags`),
  `starProjection_apply_of_mem_tags_BAS`, `apply_eq_zero_of_mem_stageQ_BAS`.
* **`third_stage_factors_through_Q2`**: `gafStageThreeCutoff_starProjection_BAS` (`ψ₃ ∘ π₂ = ψ₃`:
  the slim blocks are `Q₂`-coordinates), `Gaf02Chain.Ψ₃₂_BAS` (the draft's
  `Ψ₃₂ = adjustmentMap Q₃ (π₃ ∘ a₂) (ψ₃ ∘ π₂)`), `Gaf02Chain.Ψ₃₂_eq_Ψ₃_BAS`,
  `Gaf02Chain.third_stage_factors_through_Q2_BAS`: `π₂ E = Ψ₃₂ ∘ f₂` at EVERY point (never
  `π₂ g₂ = π₂ E`).
* `Gaf02Chain.Θ_BAS st` (`Θ₁ = Ψ₃ ∘ Ψ₂`, `Θ₂ = Ψ₃₂`, `Θ₃ = id`), `Gaf02Chain.final_factor_BAS`
  (`π_st E = Θ_st ∘ f_st` everywhere), block retention `Gaf02Chain.theta_retains_circle_BAS`,
  `Gaf02Chain.theta_retains_edge_BAS`.
* Image-neighbourhood smoothness: `contDiffAt_adjust_of_tube_BAS` (kernel),
  `Gaf02Chain.contDiffAt_Ψ₂_BAS` (`Ψ₂` at `g₁ p`), `Gaf02Chain.contDiffAt_Ψ₃_BAS` (`Ψ₃` at `g₂ p`),
  `Gaf02Chain.contDiffAt_theta_BAS` (`Θ_st` at `f_st p`, every `p`).
* Bases: `Gaf02Chain.markedBase_BAS st` (`V_st⁰ = ⋃_j V_j⁰`), `Gaf02Chain.finalBase_BAS st`
  (`W_st = Θ_st(V_st⁰)`), patch identification `Gaf02Chain.finalBase_inter_circle_BAS`,
  `Gaf02Chain.finalBase_inter_edge_BAS` (`W ∩ {marked j} = Θ(V_j⁰)`).
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

/-- **Smoothness of an adjustment at a point** (CFS18 without a global extension): if `ψ` is smooth
at `z` and, when `z ∈ tsupport ψ`, the smoothing map is smooth at `π_Q z`, then
`adjustmentMap Q (π_Q ∘ a) ψ` is smooth at `z` (off the closed support it is the identity nearby). -/
theorem contDiffAt_adjust_of_tube_BAS {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] (a : H → H)
    (ψ : H → ℝ) {z : H} (hψ : ContDiffAt ℝ ∞ ψ z)
    (ha : z ∈ tsupport ψ → ContDiffAt ℝ ∞ a (Q.starProjection z)) :
    ContDiffAt ℝ ∞ (adjustmentMap Q (fun y => Q.starProjection (a y)) ψ) z := by
  by_cases hz : z ∈ tsupport ψ
  · have hπ : ContDiffAt ℝ ∞ (fun y => Q.starProjection y) z :=
      Q.starProjection.contDiff.contDiffAt
    have hπa : ContDiffAt ℝ ∞ (fun y => Q.starProjection (a (Q.starProjection y))) z :=
      Q.starProjection.contDiff.contDiffAt.comp z ((ha hz).comp z hπ)
    exact contDiffAt_id.add (hψ.smul (hπa.sub hπ))
  · exact contDiffAt_id.congr_of_eventuallyEq (adjustmentMap_eventuallyEq_id_GAF5 Q _ hz)

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

section Tags

variable (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
  T V)

/-- `π_st` keeps the blocks of its tags. -/
theorem starProjection_apply_of_mem_tags_BAS {st : Fin 3} {t : CGPTag P.toLocalChartFamily P.zero}
    (ht : t ∈ gafStageTags P.toLocalChartFamily P.zero st)
    (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
    (gafStageQ P.toLocalChartFamily P.zero st).starProjection z t = z t := by
  classical
  rw [gafStageQ_starProjection]
  simp only [blockRestrict_apply, ht, ↓reduceIte]

/-- A vector of `Q_st` vanishes on the blocks of the other tags. -/
theorem apply_eq_zero_of_mem_stageQ_BAS {st : Fin 3} {t : CGPTag P.toLocalChartFamily P.zero}
    (ht : t ∉ gafStageTags P.toLocalChartFamily P.zero st)
    {q : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hq : q ∈ gafStageQ P.toLocalChartFamily P.zero st) : q t = 0 := by
  classical
  have h := Submodule.starProjection_eq_self_iff.mpr hq
  rw [gafStageQ_starProjection] at h
  rw [← h]
  simp only [blockRestrict_apply, ht, ↓reduceIte]

/-- `Q₃ ≤ Q₂` from the actual tag inclusion `cgpQ3Tags ⊆ cgpQ2Tags`. -/
theorem gafStageQ_two_le_one_BAS :
    gafStageQ P.toLocalChartFamily P.zero 2 ≤ gafStageQ P.toLocalChartFamily P.zero 1 := by
  classical
  intro q hq
  rw [← Submodule.starProjection_eq_self_iff]
  refine PiLp.ext fun t => ?_
  by_cases ht : t ∈ gafStageTags P.toLocalChartFamily P.zero 1
  · exact starProjection_apply_of_mem_tags_BAS P ht q
  · have ht3 : t ∉ gafStageTags P.toLocalChartFamily P.zero 2 := by
      intro h3
      apply ht
      change t ∈ cgpQ2Tags P.toLocalChartFamily P.zero
      change t ∈ cgpQ3Tags P.toLocalChartFamily P.zero at h3
      rw [cgpQ3Tags, Finset.mem_filter] at h3
      rw [cgpQ2Tags, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases t with t | t | t | t | t <;> simp_all [cgpInQ2, cgpInQ3]
    rw [apply_eq_zero_of_mem_stageQ_BAS P ht3 hq]
    rw [gafStageQ_starProjection]
    simp only [blockRestrict_apply, ht, ↓reduceIte]

/-- **The actual third-stage cutoff descends to `Q₂`** (`third_stage_factors_through_Q2`): the slim
vectors and markers are `Q₂`-coordinates (`cgpQ2Tags` contains every slim tag), so
`ψ₃(π₂ z) = ψ₃(z)`. -/
theorem gafStageThreeCutoff_starProjection_BAS
    (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
    gafStageThreeCutoff P.toLocalChartFamily P.zero
        ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection z) =
      gafStageThreeCutoff P.toLocalChartFamily P.zero z := by
  have hslim : ∀ j : P.toLocalChartFamily.slim.finite_centres.toFinset,
      (.inr (.inl j) : CGPTag P.toLocalChartFamily P.zero) ∈
        gafStageTags P.toLocalChartFamily P.zero 1 := fun j =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have h := cfsUniformAxisCutoff_comp_of_factor lc87EdgeTransition (10 ^ 5 * Δ)
    (fun j : P.toLocalChartFamily.slim.finite_centres.toFinset => ρ j.1)
    (gafSlimVector P.toLocalChartFamily P.zero) (gafSlimMarker P.toLocalChartFamily P.zero)
    (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
    (fun j z => by
      rw [gafSlimVector, blockVectorCLM_apply, blockVectorCLM_apply,
        starProjection_apply_of_mem_tags_BAS P (hslim j)])
    (fun j z => by
      rw [gafSlimMarker, blockMarkerCLM_apply, blockMarkerCLM_apply,
        starProjection_apply_of_mem_tags_BAS P (hslim j)])
  exact congrFun h z

end Tags

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The draft's `Ψ₃₂ = adjustmentMap Q₃ (π₃ ∘ a₂) (ψ₃ ∘ π₂)` (the third adjustment through `Q₂`). -/
def Ψ₃₂_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) :=
  adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2)
    (fun y => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection ((C.slot 2).map y))
    (gafStageThreeCutoff P.toLocalChartFamily P.zero ∘
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection)

/-- `Ψ₃₂ = Ψ₃` (the actual cutoff is `π₂`-invariant). -/
theorem Ψ₃₂_eq_Ψ₃_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) : C.Ψ₃₂_BAS = C.Ψ₃ := by
  have h : gafStageThreeCutoff P.toLocalChartFamily P.zero ∘
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection =
      gafStageThreeCutoff P.toLocalChartFamily P.zero :=
    funext fun z => gafStageThreeCutoff_starProjection_BAS P z
  rw [Ψ₃₂_BAS, h]
  rfl

/-- **`third_stage_factors_through_Q2`** (draft 59 §4 sixth step, D66-7): `ψ₃ ∘ π₂ = ψ₃` and
`π₂ E = Ψ₃₂ ∘ f₂` at EVERY point (`f₂ = π₂ g₂`; never `π₂ g₂ = π₂ E`). -/
theorem third_stage_factors_through_Q2_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (∀ z, gafStageThreeCutoff P.toLocalChartFamily P.zero
        ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection z) =
      gafStageThreeCutoff P.toLocalChartFamily P.zero z) ∧
    ∀ p, (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E p) =
      C.Ψ₃₂_BAS (C.stageMap_BAS 1 p) := by
  refine ⟨gafStageThreeCutoff_starProjection_BAS P, fun p => ?_⟩
  rw [C.Ψ₃₂_eq_Ψ₃_BAS]
  exact stage_two_final_factor_BPRE (gafStageQ P.toLocalChartFamily P.zero 1)
    (gafStageQ P.toLocalChartFamily P.zero 2) (gafStageQ_two_le_one_BAS P)
    (fun z => Submodule.starProjection_apply_mem _ _) (gafStageThreeCutoff_starProjection_BAS P)
    C.g₂ p

/-- The later transports `Θ₁ = Ψ₃ ∘ Ψ₂`, `Θ₂ = Ψ₃₂`, `Θ₃ = id`. -/
def Θ_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) :
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) :=
  ![C.Ψ₃ ∘ C.Ψ₂, C.Ψ₃₂_BAS, id] st

/-- **The final factorization** `π_st E = Θ_st ∘ f_st` at every point. -/
theorem final_factor_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) (p : X) :
    (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) =
      C.Θ_BAS st (C.stageMap_BAS st p) := by
  fin_cases st
  · change (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p) =
      C.Ψ₃ (C.Ψ₂ ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.g₁ p)))
    rw [gafStageQ_zero_starProjection_BAS, gafStageQ_zero_starProjection_BAS]
    rfl
  · exact C.third_stage_factors_through_Q2_BAS.2 p
  · rfl

/-- **`Θ₁` keeps every circle block** (circle tags are not `Q₂`-tags). -/
theorem theta_retains_circle_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.toLocalChartFamily.circle.finite_centres.toFinset)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
    gafCircleVector P j (C.Θ_BAS 0 w) = gafCircleVector P j w ∧
      gafCircleMarker P j (C.Θ_BAS 0 w) = gafCircleMarker P j w := by
  have hnot : (.inl j : CGPTag P.toLocalChartFamily P.zero) ∉
      gafStageTags P.toLocalChartFamily P.zero 1 := by
    intro h
    change (.inl j : CGPTag P.toLocalChartFamily P.zero) ∈ cgpQ2Tags P.toLocalChartFamily P.zero at h
    rw [cgpQ2Tags, Finset.mem_filter] at h
    exact absurd h.2 (by simp [cgpInQ2])
  have hb : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (bb : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] F),
      (∀ y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        y (.inl j) = 0 → bb y = 0) →
      bb (C.Θ_BAS 0 w) = bb w := by
    intro F _ _ bb hbb
    exact theta_one_retains_block_BPRE (gafStageQ P.toLocalChartFamily P.zero 1)
      (gafStageQ P.toLocalChartFamily P.zero 2) (gafStageQ_two_le_one_BAS P)
      (fun z => Submodule.starProjection_apply_mem _ _)
      (fun z => Submodule.starProjection_apply_mem _ _) _ _ bb
      (fun q hq => hbb q (apply_eq_zero_of_mem_stageQ_BAS P hnot hq)) w
  refine ⟨hb (gafCircleVector P j) fun y hy => ?_, hb (gafCircleMarker P j) fun y hy => ?_⟩
  · rw [gafCircleVector, blockVectorCLM_apply, hy]
    rfl
  · rw [gafCircleMarker, blockMarkerCLM_apply, hy]
    rfl

/-- **`Θ₂` keeps every edge block** (edge tags are not `Q₃`-tags). -/
theorem theta_retains_edge_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
    gafEdgeVector P.toLocalChartFamily P.zero j (C.Θ_BAS 1 w) =
        gafEdgeVector P.toLocalChartFamily P.zero j w ∧
      gafEdgeMarker P.toLocalChartFamily P.zero j (C.Θ_BAS 1 w) =
        gafEdgeMarker P.toLocalChartFamily P.zero j w := by
  have hnot : (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero) ∉
      gafStageTags P.toLocalChartFamily P.zero 2 := by
    intro h
    change (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero) ∈
      cgpQ3Tags P.toLocalChartFamily P.zero at h
    rw [cgpQ3Tags, Finset.mem_filter] at h
    exact absurd h.2 (by simp [cgpInQ3])
  have hb : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (bb : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] F),
      (∀ y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        y (.inr (.inr (.inl j))) = 0 → bb y = 0) →
      bb (C.Θ_BAS 1 w) = bb w := by
    intro F _ _ bb hbb
    change bb (C.Ψ₃₂_BAS w) = bb w
    exact adjustmentMap_retains_block_BPRE (gafStageQ P.toLocalChartFamily P.zero 2)
      (fun z => Submodule.starProjection_apply_mem _ _) _ bb
      (fun q hq => hbb q (apply_eq_zero_of_mem_stageQ_BAS P hnot hq)) w
  refine ⟨hb (gafEdgeVector P.toLocalChartFamily P.zero j) fun y hy => ?_,
    hb (gafEdgeMarker P.toLocalChartFamily P.zero j) fun y hy => ?_⟩
  · rw [gafEdgeVector, blockVectorCLM_apply, hy]
    rfl
  · rw [gafEdgeMarker, blockMarkerCLM_apply, hy]
    rfl

/-- The slot's smoothing map is smooth at every point of the open domain `Ω_st`. -/
theorem slot_contDiffAt_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3)
    {x y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero st) (hy : y ∈ ball x (S st * ρ (C.sel st x))) :
    ContDiffAt ℝ ∞ (C.slot st).map y := by
  have hopen : IsOpen (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st,
      ball x (S st * ρ (C.sel st x))) := isOpen_biUnion fun _ _ => isOpen_ball
  have hmem : y ∈ ⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st, ball x (S st * ρ (C.sel st x)) :=
    mem_iUnion₂.mpr ⟨x, hx, hy⟩
  exact ((C.slot st).smooth y hmem).contDiffAt (hopen.mem_nhds hmem)

/-- **Image-neighbourhood smoothness of `Ψ₂` at `g₁ p`** (CFS18: the scale is positive at `g₁ p`,
the closed support localizes to the native tube, off it `Ψ₂ = id` nearby). -/
theorem contDiffAt_Ψ₂_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (p : X) :
    ContDiffAt ℝ ∞ C.Ψ₂ (C.g₁ p) := by
  have cb := C.cutoff_bindings
  have hscale : 0 < gafScaleMarker P.toLocalChartFamily P.zero (C.g₁ p) := by
    have h := (cb.2.1.2.2.2.2 p 1 (by norm_num)).1
    simpa using h
  have hopen : IsOpen {z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) |
      0 < gafScaleMarker P.toLocalChartFamily P.zero z} :=
    isOpen_lt continuous_const (gafScaleMarker P.toLocalChartFamily P.zero).continuous
  have hψ : ContDiffAt ℝ ∞ (gafStageTwoCutoff P.toLocalChartFamily P.zero) (C.g₁ p) :=
    (cb.2.1.1 _ hscale).contDiffAt (hopen.mem_nhds hscale)
  refine contDiffAt_adjust_of_tube_BAS _ _ _ hψ fun hz => ?_
  obtain ⟨hx, hy⟩ := (C.stage_input_mem_tube p).2.1 hz
  exact C.slot_contDiffAt_BAS 1 hx hy

/-- **Image-neighbourhood smoothness of `Ψ₃` at `g₂ p`** (D66-7: native-tube smoothness on the
closed support, identity off it; `ψ₃` is smooth). -/
theorem contDiffAt_Ψ₃_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (p : X) :
    ContDiffAt ℝ ∞ C.Ψ₃ (C.g₂ p) := by
  have cb := C.cutoff_bindings
  refine contDiffAt_adjust_of_tube_BAS _ _ _ cb.2.2.1.contDiffAt fun hz => ?_
  obtain ⟨hx, hy⟩ := (C.stage_input_mem_tube p).2.2 hz
  exact C.slot_contDiffAt_BAS 2 hx hy

/-- **The later transports are smooth at the stage images**: `Θ_st` is smooth at `f_st p` for
every `p` (`Θ₁` at `g₁ p`, `Θ₂ = Ψ₃₂` at `π₂ g₂ p` by the `π₂`-invariance, `Θ₃ = id`). -/
theorem contDiffAt_theta_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) (p : X) :
    ContDiffAt ℝ ∞ (C.Θ_BAS st) (C.stageMap_BAS st p) := by
  fin_cases st
  · change ContDiffAt ℝ ∞ (C.Ψ₃ ∘ C.Ψ₂)
      ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.g₁ p))
    rw [gafStageQ_zero_starProjection_BAS]
    exact (C.contDiffAt_Ψ₃_BAS p).comp (C.g₁ p) (C.contDiffAt_Ψ₂_BAS p)
  · change ContDiffAt ℝ ∞ C.Ψ₃₂_BAS
      ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.g₂ p))
    rw [C.Ψ₃₂_eq_Ψ₃_BAS]
    exact contDiffAt_adjustmentMap_starProjection_BPRE (gafStageQ P.toLocalChartFamily P.zero 1)
      (gafStageQ P.toLocalChartFamily P.zero 2) (gafStageQ_two_le_one_BAS P) _
      (gafStageThreeCutoff_starProjection_BAS P) (C.contDiffAt_Ψ₃_BAS p)
  · exact contDiffAt_id

/-- The marked stage bases `V_st⁰ = ⋃_j V_j⁰` (circle, edge, slim patches of the chain). -/
def markedBase_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  ![⋃ j, C.circlePatch_BAS j, ⋃ j, C.edgePatch_BAS j, ⋃ j, C.slimPatch_BAS j] st

/-- The final bases `W_st = Θ_st(V_st⁰)`. -/
def finalBase_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  C.Θ_BAS st '' C.markedBase_BAS st

/-- **Patch identification, circle stage**: `W₁ ∩ {v_j > .9R_j, ‖u_j‖ < 5.5R_j} = Θ₁(V_j⁰)`. -/
theorem finalBase_inter_circle_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    C.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P j) (gafCircleMarker P j) (ρ j.1) 1 =
      C.Θ_BAS 0 '' C.circlePatch_BAS j :=
  theta_image_inter_marked_BPRE (C.slot 0).zeroSet (gafCircleVector P) (gafCircleMarker P)
    (fun k => ρ k.1) (fun _ => 1) (C.Θ_BAS 0)
    (fun k w _ => C.theta_retains_circle_BAS k w) j

/-- **Patch identification, edge stage**: `W₂ ∩ {v_j > .9R_j, |u_j| < 5.5ΔR_j} = Θ₂(V_j⁰)`. -/
theorem finalBase_inter_edge_BAS (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) :
    C.finalBase_BAS 1 ∩ markedCondition_BPRE (axisCoordCLM_BAS.comp (gafEdgeVector
        P.toLocalChartFamily P.zero j)) (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ =
      C.Θ_BAS 1 '' C.edgePatch_BAS j :=
  theta_image_inter_marked_BPRE (C.slot 1).zeroSet
    (fun k => axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero k))
    (gafEdgeMarker P.toLocalChartFamily P.zero) (fun k => ρ k.1) (fun _ => Δ) (C.Θ_BAS 1)
    (fun k w _ => ⟨by rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        (C.theta_retains_edge_BAS k w).1], (C.theta_retains_edge_BAS k w).2⟩) j

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
