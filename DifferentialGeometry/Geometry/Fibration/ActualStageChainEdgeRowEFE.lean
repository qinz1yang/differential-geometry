import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRankTwoEFE
import DifferentialGeometry.Topology.Ehresmann.ArcEndDefiningFunctionZSP35

/-!
# FDC02 / EDP05: the whole edge row on the actual chain (faces, properness), group G9

Lane S-EDP-FDC4, group G9 (second part). Blueprint `master207B.tex`, EDP05 (B:7040–7090) and
FDC02 (B:7246–7283). Generic in `M₂ : Set X` (chain-level statements about the descended defining
function of `M₂`; the final-family assembly is in `ActualStageChainEdgeRowApplicationsEFE`).

* `edgeBlockProj_EFE`, `edgeValB_EFE`: `π₂E : X → block space` and the inclusion `B₂ → block space`;
* `edge_proper_EFE` (`EdgeBundle.proper`): the preimage of a compact subset of `B₂` below `4Δ` is
  compact;
* `eq_zero_of_mem_frontier_of_descended_EFE`: on `∂M₂` the descended defining function vanishes;
* `edge_regular_face_EFE`: along a regular descended defining function `F = hh ∘ π₂E` the base
  point is a limit of points of `B₂ ∖ C₂` and the whole fibre lies in the closure of `X ∖ M₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **Generic: the descended defining function vanishes on the frontier.** -/
theorem eq_zero_of_mem_frontier_of_descended_EFE {Y B : Type*} [TopologicalSpace Y]
    [TopologicalSpace B] {pr : Y → B} (hpr : Continuous pr) {M₂ : Set Y} {N : Set B}
    (hN : IsOpen N) {hh : B → ℝ} (hhc : ContinuousOn hh N)
    (hdef : ∀ y, pr y ∈ N → (y ∈ M₂ ↔ 0 ≤ hh (pr y))) {y : Y} (hy : y ∈ frontier M₂)
    (hyM : y ∈ M₂) (hyN : pr y ∈ N) : hh (pr y) = 0 := by
  refine le_antisymm ?_ ((hdef y hyN).mp hyM)
  by_contra hpos
  push Not at hpos
  have hO : IsOpen (pr ⁻¹' (N ∩ hh ⁻¹' Ioi 0)) :=
    (hhc.isOpen_inter_preimage hN isOpen_Ioi).preimage hpr
  have hsub : pr ⁻¹' (N ∩ hh ⁻¹' Ioi 0) ⊆ M₂ := fun z hz => (hdef z hz.1).mpr (le_of_lt hz.2)
  exact hy.2 (mem_interior.mpr ⟨_, hsub, hO, ⟨hyN, hpos⟩⟩)

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainE

variable {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- `π₂E : X → block space`. -/
def edgeBlockProj_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) :
    X → BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) := fun y =>
  (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E y)

/-- The inclusion `B₂ → block space`. -/
def edgeValB_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) :
    Ĉ.edgeBaseOpens_EFE → BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) :=
  fun cc => ((cc : Ĉ.toChain.finalBase_BAS 1) :
    BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))

/-- `ι ∘ f₂ = π₂E` on the edge source. -/
theorem edgeValB_edgeProj_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (z : Ĉ.edgeSource_EFE) :
    Ĉ.edgeValB_EFE (Ĉ.edgeProj_EFE z) = Ĉ.edgeBlockProj_EFE z.1 := rfl

theorem continuous_edgeBlockProj_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) :
    Continuous Ĉ.edgeBlockProj_EFE :=
  (gafStageQ L.toLocalChartFamily L.zero 1).starProjection.continuous.comp
    Ĉ.toChain.stage_smooth.2.2.continuous

theorem contMDiff_edgeBlockProj_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)) ∞
      Ĉ.edgeBlockProj_EFE := A.proj.final_smooth 1

theorem contMDiff_edgeValB_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain) :
    let _ := A.edgeChartedSpace1
    ContMDiff (𝓡 1) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)) ∞
      Ĉ.edgeValB_EFE := by
  intro _
  exact (A.edge_isManifold1.2.1).comp (contMDiff_subtype_val (I := 𝓡 1))

/-- **`EdgeBundle.proper` of the actual chain**: the part below `4Δ` of the preimage of a compact
subset of `B₂` is compact. -/
theorem edge_proper_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ2 : 2 ≤ Δ)
    (A : SmoothStageBasesOn74 Ĉ.toChain) (Kc : Set Ĉ.edgeBaseOpens_EFE) (hKc : IsCompact Kc) :
    let _ := A.edgeChartedSpace1
    IsCompact (Subtype.val '' {x : Ĉ.edgeSource_EFE | Ĉ.edgeProj_EFE x ∈ Kc ∧
      Ĉ.edgeHeight_EFE x ≤ 4 * Δ}) := by
  intro _
  have hcomp : IsCompact (Ĉ.edgeValB_EFE '' Kc) :=
    hKc.image (Ĉ.contMDiff_edgeValB_EFE A).continuous
  have h := Ĉ.toChain.edgeSublevel_preimage_isCompact_EFE (Δ := Δ) hcomp
  convert h using 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    exact ⟨⟨_, hx1, rfl⟩, hx2⟩
  · rintro ⟨⟨cc, hcc, hcy⟩, hy2⟩
    have hR : Ĉ.edgeBlockProj_EFE y ∈ edgeRatio_R74 L := by
      have h1 : Ĉ.edgeBlockProj_EFE y = Ĉ.edgeValB_EFE cc := hcy.symm
      rw [h1]
      exact cc.2
    have hys : y ∈ Ĉ.edgeSource_EFE := Ĉ.mem_edgeSource_EFE hΔ2 hR hy2
    refine ⟨⟨y, hys⟩, ⟨?_, hy2⟩, rfl⟩
    have : Ĉ.edgeProj_EFE ⟨y, hys⟩ = cc := by
      apply Subtype.ext
      apply Subtype.ext
      exact hcy.symm
    rw [this]
    exact hcc

/-- **The descended defining function on the base**: `bb = hh ∘ ι` is smooth over `{ι ∈ N}`, and
`F = bb ∘ f₂` on the edge source, so `dF = dbb ∘ df₂` there. -/
theorem edge_descended_mfderiv_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain)
    {N : Set (BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))} (hN : IsOpen N)
    {hh : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) → ℝ}
    (hhN : ContDiffOn ℝ ∞ hh N) {F : X → ℝ}
    (hFeq : ∀ y, F y = hh (Ĉ.edgeBlockProj_EFE y)) (z : Ĉ.edgeSource_EFE)
    (hz : Ĉ.edgeBlockProj_EFE z.1 ∈ N) :
    let _ := A.edgeChartedSpace1
    ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun cc => hh (Ĉ.edgeValB_EFE cc)) (Ĉ.edgeProj_EFE z) ∧
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F z.1 =
        (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun cc => hh (Ĉ.edgeValB_EFE cc)) (Ĉ.edgeProj_EFE z)).comp
          (mfderiv 𝓘(ℝ, E3) (𝓡 1) Ĉ.edgeProj_EFE z) := by
  intro _
  have hval := Ĉ.contMDiff_edgeValB_EFE A
  have hproj := Ĉ.edgeProj_contMDiff_EFE A
  have hblock := Ĉ.contMDiff_edgeBlockProj_EFE A
  have hFsm : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ F z.1 := by
    have : F = fun y => hh (Ĉ.edgeBlockProj_EFE y) := funext hFeq
    rw [this]
    exact ((hhN.contDiffAt (hN.mem_nhds hz)).contMDiffAt).comp z.1 (hblock z.1)
  have hbsm : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun cc => hh (Ĉ.edgeValB_EFE cc))
      (Ĉ.edgeProj_EFE z) :=
    ((hhN.contDiffAt (hN.mem_nhds hz)).contMDiffAt).comp (Ĉ.edgeProj_EFE z)
      (hval (Ĉ.edgeProj_EFE z))
  refine ⟨hbsm, ?_⟩
  have h1 : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun w : Ĉ.edgeSource_EFE => F w.1) z =
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F z.1 :=
    mfderiv_comp_subtype_val_R74 Ĉ.edgeSource_EFE (fun _ => rfl) z
      (hFsm.mdifferentiableAt (by simp))
  have h2 : (fun w : Ĉ.edgeSource_EFE => F w.1) =
      (fun cc => hh (Ĉ.edgeValB_EFE cc)) ∘ Ĉ.edgeProj_EFE := funext fun w => hFeq w.1
  rw [← h1, h2]
  exact mfderiv_comp z (hbsm.mdifferentiableAt (by simp)) ((hproj z).mdifferentiableAt (by simp))

/-- **Regular zeros are limits of negative values** (generic, boundaryless model). -/
theorem mem_closure_neg_of_mfderiv_ne_zero_EFE {EX HX : Type*} [NormedAddCommGroup EX]
    [NormedSpace ℝ EX] [TopologicalSpace HX] {I : ModelWithCorners ℝ EX HX} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace HX M] {f : M → ℝ} {x : M}
    (hf : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) (h0 : f x = 0) : x ∈ closure {y | f y < 0} := by
  have hne : mfderiv I 𝓘(ℝ, ℝ) (-f) x ≠ 0 := by
    rw [mfderiv_neg]
    exact neg_ne_zero.mpr hf
  have h := mem_closure_pos_of_mfderiv_ne_zero_ZSP35 (I := I) hne
  refine closure_mono (fun y hy => ?_) h
  change (-f) x < (-f) y at hy
  change f y < 0
  have : -f x < -f y := hy
  linarith

/-- **A regular descended defining function, base part** (EDP05, B:7061–7084): `F = hh ∘ π₂E`,
`z ∈ M₂ ↔ hh(π₂E z) ≥ 0` over `{π₂E ∈ N}`, `F` regular at `x₁` with `hh(π₂E x₁) = 0`. Then the
descended differential at `f₂ x₁` is nonzero and `f₂ x₁` is a limit of points of `B₂` outside
`C₂ = f₂(M₂ ∩ {T ≤ 4Δ})`. -/
theorem edge_regular_face_base_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain) (M₂ : Set X)
    {N : Set (BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))} (hN : IsOpen N)
    {hh : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) → ℝ}
    (hhN : ContDiffOn ℝ ∞ hh N)
    (hdef : ∀ y : X, Ĉ.edgeBlockProj_EFE y ∈ N → (y ∈ M₂ ↔ 0 ≤ hh (Ĉ.edgeBlockProj_EFE y)))
    {F : X → ℝ} (hFeq : ∀ y, F y = hh (Ĉ.edgeBlockProj_EFE y))
    (x₁ : Ĉ.edgeSource_EFE) (hx₁N : Ĉ.edgeBlockProj_EFE x₁.1 ∈ N)
    (hFne : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F x₁.1 ≠ 0)
    (hzero : hh (Ĉ.edgeBlockProj_EFE x₁.1) = 0) :
    let _ := A.edgeChartedSpace1
    mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun cc => hh (Ĉ.edgeValB_EFE cc)) (Ĉ.edgeProj_EFE x₁) ≠ 0 ∧
      Ĉ.edgeProj_EFE x₁ ∈ closure ((Ĉ.edgeProj_EFE '' {x : Ĉ.edgeSource_EFE |
        (x : X) ∈ M₂ ∧ Ĉ.edgeHeight_EFE x ≤ 4 * Δ})ᶜ) := by
  intro _
  obtain ⟨hbsm, hFcomp⟩ := Ĉ.edge_descended_mfderiv_EFE A hN hhN hFeq x₁ hx₁N
  have hdb : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun cc => hh (Ĉ.edgeValB_EFE cc)) (Ĉ.edgeProj_EFE x₁) ≠ 0 := by
    intro h0
    apply hFne
    rw [hFcomp, h0, ContinuousLinearMap.zero_comp]
    rfl
  refine ⟨hdb, ?_⟩
  have hval := Ĉ.contMDiff_edgeValB_EFE A
  have hcl := mem_closure_neg_of_mfderiv_ne_zero_EFE (I := 𝓡 1) hdb (by
    rw [Ĉ.edgeValB_edgeProj_EFE x₁]
    exact hzero)
  have hO : IsOpen (Ĉ.edgeValB_EFE ⁻¹' N) := hN.preimage hval.continuous
  refine closure_mono ?_ (hO.closure_inter ⟨hcl, hx₁N⟩)
  rintro cc ⟨hcc, hccN⟩ ⟨w, ⟨hwM, -⟩, hw⟩
  have hwN : Ĉ.edgeBlockProj_EFE w.1 ∈ N := by
    rw [← Ĉ.edgeValB_edgeProj_EFE w, hw]
    exact hccN
  have h1 := (hdef w.1 hwN).mp hwM
  have h2 : hh (Ĉ.edgeValB_EFE cc) < 0 := hcc
  rw [← hw, Ĉ.edgeValB_edgeProj_EFE w] at h2
  linarith

/-- **A regular descended defining function, fibre part**: with the data of the base part (and the
nonzero descended differential), every point of the edge source over `f₂ x₁` is a limit of points
outside `M₂`. -/
theorem edge_regular_face_fibre_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain) (M₂ : Set X)
    {N : Set (BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))} (hN : IsOpen N)
    {hh : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) → ℝ}
    (hhN : ContDiffOn ℝ ∞ hh N)
    (hdef : ∀ y : X, Ĉ.edgeBlockProj_EFE y ∈ N → (y ∈ M₂ ↔ 0 ≤ hh (Ĉ.edgeBlockProj_EFE y)))
    {F : X → ℝ} (hFeq : ∀ y, F y = hh (Ĉ.edgeBlockProj_EFE y))
    (x₁ : Ĉ.edgeSource_EFE) (hx₁N : Ĉ.edgeBlockProj_EFE x₁.1 ∈ N)
    (hzero : hh (Ĉ.edgeBlockProj_EFE x₁.1) = 0) :
    let _ := A.edgeChartedSpace1
    mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun cc => hh (Ĉ.edgeValB_EFE cc)) (Ĉ.edgeProj_EFE x₁) ≠ 0 →
      ∀ z : Ĉ.edgeSource_EFE, Ĉ.edgeProj_EFE z = Ĉ.edgeProj_EFE x₁ → z.1 ∈ closure (M₂ᶜ) := by
  intro _ hdb z hz
  have hblk : Ĉ.edgeBlockProj_EFE z.1 = Ĉ.edgeBlockProj_EFE x₁.1 := by
    rw [← Ĉ.edgeValB_edgeProj_EFE z, ← Ĉ.edgeValB_edgeProj_EFE x₁, hz]
  have hzN : Ĉ.edgeBlockProj_EFE z.1 ∈ N := by
    rw [hblk]
    exact hx₁N
  have hzF : F z.1 = 0 := by
    rw [hFeq, hblk]
    exact hzero
  obtain ⟨-, hFcomp⟩ := Ĉ.edge_descended_mfderiv_EFE A hN hhN hFeq z hzN
  have hdb' : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun cc => hh (Ĉ.edgeValB_EFE cc)) (Ĉ.edgeProj_EFE z) ≠ 0 := by
    rw [hz]
    exact hdb
  have hFne' : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F z.1 ≠ 0 := by
    rw [hFcomp]
    intro hc0
    apply hdb'
    ext w
    obtain ⟨v, hv⟩ := Ĉ.edge_proj_submersion_EFE A z w
    have h1 : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun cc => hh (Ĉ.edgeValB_EFE cc)) (Ĉ.edgeProj_EFE z)
        (mfderiv 𝓘(ℝ, E3) (𝓡 1) Ĉ.edgeProj_EFE z v) = 0 := congrArg (fun Lm => Lm v) hc0
    rw [hv] at h1
    exact h1
  have hcl := mem_closure_neg_of_mfderiv_ne_zero_EFE (I := 𝓘(ℝ, E3)) hFne' hzF
  have hO : IsOpen (Ĉ.edgeBlockProj_EFE ⁻¹' N) := hN.preimage Ĉ.continuous_edgeBlockProj_EFE
  refine closure_mono ?_ (hO.closure_inter ⟨hcl, hzN⟩)
  rintro y ⟨hy1, hyN⟩ hyM
  have h1 := (hdef y hyN).mp hyM
  rw [← hFeq y] at h1
  have h2 : F y < 0 := hy1
  linarith

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
