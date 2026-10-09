import DifferentialGeometry.Geometry.Fibration.ActualStageChainCircleBundleTrivEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSmoothBases
import DifferentialGeometry.Topology.Manifold.LinearChartAtlasEFE

/-!
# FDC03's circle bundle over the ABSTRACT base `B₁ ⊆ W₁`: the data of `CircleBundle`

Lane S-EDP-FDC2, group G6 (FDC03 circle bundle, draft 74 D74-13; successor of S-EDP-FDC's
partial G6). `ActualStageChainCircleBundleTrivEFE` trivializes `g_i = κ_i ∘ π₁E` over the ball of
the base CHART; here the base is the abstract smooth surface `W₁` (the manifold structure
`A.circleChartedSpace` of the smooth stage bases `A : SmoothStageBasesOn74 C.toChain`, D74-2) and
the statements are those of the rows' `CircleBundle` structure (`FC39P0Base.lean`): domain,
projection, submersion, local trivializations preserving the projection, compact `cbase`.

For a chain `C : Gaf02ChainEJA P …` (closed route; the CompactCarrier identification is the
assembler's):

* `C.circleDomain_EFE : Opens X` — the open set `⋃_i {p ∈ Y_i | ‖g_i p‖ < 4}`; it is the WHOLE
  preimage `(π₁E)⁻¹(B₁)` (`circleDomain_eq_EFE`), where `B₁ = circleBase_BAS = W₁ ∩ R₁`;
* `C.circleBaseOpens_EFE : Opens W₁` — the open set `{w ∈ W₁ | w ∈ R₁}` (`B₁` as the rows' `Base`);
* `C.circleProj_EFE : circleDomain → circleBaseOpens` — `p ↦ π₁E p` (`circleProjC_EFE`: as a
  continuous map).

Statements: `circleProj_contMDiff_EFE` (smooth for the abstract structure, through
`contMDiff_of_val_EFE`), `circleProj_mfderiv_surjective_EFE` (submersion at every point: the chart
`κ_i` of `W₁` is a smooth chart, `surjective_mfderiv_of_chart_EFE`, and `g_i` is a submersion on
`Y_i`), `circleProj_isProper_EFE`, `circleProj_surjective_EFE`, `circleProj_fibre_EFE` (the fibre
of `circleProj_EFE` over `c` is exactly the WHOLE fibre `(π₁E)⁻¹(c)` of GAF07),
`circleProj_connected_EFE`, `circleProj_circle_EFE` (the whole fibre is a smooth embedded circle),
`circleProj_cbase_compact_EFE` (`π₁E(M₃)` compact for closed `M₃ ⊆ domain`), and the local
trivializations `circleProj_trivial_EFE` (over a neighbourhood `Q` of every `c` of `W₁ ∩ R₁`, a
diffeomorphism `proj⁻¹(Q) ≃ₘ Q × Circle` in the models `𝓘(ℝ, E3)` and `(𝓡 2).prod (𝓡 1)` with first
coordinate `proj`: `CircleBundle.trivialization` / `projection_trivialization`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace SmoothStageBasesOn74

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw}
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- A map into `W₁` is smooth (for the manifold structure of the abstract base) as soon as its
composite with the inclusion `W₁ → BlockSpace` is. -/
theorem circle_contMDiff_of_val_EFE (A : SmoothStageBasesOn74 C) (F : M → C.finalBase_BAS 0)
    (hF : ContMDiff I
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (fun z => (F z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))) :
    let _ := A.circleChartedSpace
    ContMDiff I 𝓘(ℝ, ℝ²) ∞ F :=
  contMDiff_of_val_EFE _ _ _ _ _ _ _ _ _ _ F hF

/-- **Surjective differential into the abstract base through the chart `κ_j`**. -/
theorem circle_surjective_mfderiv_EFE (A : SmoothStageBasesOn74 C) (F : M → C.finalBase_BAS 0)
    (x : M) (j : P.toLocalChartFamily.circle.finite_centres.toFinset)
    (hx : (F x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∈
      markedCondition_BPRE (gafCircleVector P.toLocalChartPackets j)
        (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1)
    (hFs : let _ := A.circleChartedSpace
      ContMDiffAt I 𝓘(ℝ, ℝ²) ∞ F x)
    (hsur : Surjective (mfderiv I 𝓘(ℝ, ℝ²) (fun z =>
      ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
        (F z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) x)) :
    let _ := A.circleChartedSpace
    Surjective (mfderiv I 𝓘(ℝ, ℝ²) F x) :=
  surjective_mfderiv_of_chart_EFE _ _ _ _ _ _ _ _ _ _ F x j hx hFs hsur

end SmoothStageBasesOn74

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- **The open source of the circle bundle**: `⋃_i {p ∈ Y_i | ‖g_i(p)‖ < 4}`, the whole preimage of
`B₁` (`circleDomain_eq_EFE`). -/
def circleDomain_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) : TopologicalSpace.Opens X :=
  ⟨⋃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
    {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
      ‖C.toChain.gaf07CircleCoord_GAFC i p‖ < 4},
    isOpen_iUnion fun i => C.toChain.isOpen_gaf07CircleChartSource_GAFD i⟩

/-- **The rows' circle base `W₁ ∩ R₁`** as an open subset of the abstract base `W₁`. -/
def circleBaseOpens_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    TopologicalSpace.Opens (C.toChain.finalBase_BAS 0) :=
  ⟨Subtype.val ⁻¹' gaf07CircleRatio_G47 P.toLocalChartPackets,
    (isOpen_gaf07CircleRatio_GAFC P.toLocalChartPackets).preimage continuous_subtype_val⟩

theorem circleDomain_mem_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) {p : X}
    (hp : p ∈ C.circleDomain_EFE) :
    (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
        C.toChain.finalBase_BAS 0 ∧
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
        gaf07CircleRatio_G47 P.toLocalChartPackets := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  have h := (Set.ext_iff.mp (C.toGaf02ChainE.gaf07_circle_piece_preimage_GAFD C.c_two_lt i) p).mpr
    hi
  exact ⟨h.1, mem_iUnion.mpr ⟨i, h.2⟩⟩

theorem mem_circleDomain_of_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) {p : X}
    (hW : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
      C.toChain.finalBase_BAS 0)
    (hR : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
      gaf07CircleRatio_G47 P.toLocalChartPackets) : p ∈ C.circleDomain_EFE := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hR
  exact mem_iUnion.mpr ⟨i, (Set.ext_iff.mp
    (C.toGaf02ChainE.gaf07_circle_piece_preimage_GAFD C.c_two_lt i) p).mp ⟨hW, hi⟩⟩

/-- **The projection of the circle bundle**: `p ↦ π₁E(p) ∈ W₁ ∩ R₁`. -/
def circleProj_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    C.circleDomain_EFE → C.circleBaseOpens_EFE := fun x =>
  ⟨⟨(gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E x.1),
      (C.circleDomain_mem_EFE x.2).1⟩, (C.circleDomain_mem_EFE x.2).2⟩

theorem circleProj_val_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) (x : C.circleDomain_EFE) :
    (((C.circleProj_EFE x : C.circleBaseOpens_EFE) : C.toChain.finalBase_BAS 0) :
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) =
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E x.1) :=
  rfl

/-- The domain is the whole preimage of `B₁ = circleBase_BAS`. -/
theorem circleDomain_eq_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) :
    (C.circleDomain_EFE : Set X) =
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) ⁻¹'
        C.toChain.circleBase_BAS := by
  obtain ⟨⟨hB1, -⟩, -⟩ := C.gaf07_circle_row_GAFD hβ hd
  rw [hB1]
  exact Set.ext fun p =>
    ⟨fun h => C.circleDomain_mem_EFE h, fun h => C.mem_circleDomain_of_EFE h.1 h.2⟩

/-- The open base is `B₁ = circleBase_BAS` as a set of `W₁`. -/
theorem circleBaseOpens_eq_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) :
    (C.circleBaseOpens_EFE : Set (C.toChain.finalBase_BAS 0)) =
      (Subtype.val : C.toChain.finalBase_BAS 0 →
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ⁻¹'
        C.toChain.circleBase_BAS := by
  obtain ⟨⟨hB1, -⟩, -⟩ := C.gaf07_circle_row_GAFD hβ hd
  rw [hB1]
  exact Set.ext fun w => ⟨fun h => ⟨w.2, h⟩, fun h => h.2⟩

/-- The composite `x ↦ π₁E x ∈ W₁` is smooth for the abstract structure of `W₁`. -/
theorem circleProjW_contMDiff_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain) :
    let _ := A.circleChartedSpace
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (fun z : C.circleDomain_EFE =>
      ((C.circleProj_EFE z : C.circleBaseOpens_EFE) : C.toChain.finalBase_BAS 0)) := by
  intro _
  have hFval : ContMDiff 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (fun z : C.circleDomain_EFE => (((C.circleProj_EFE z : C.circleBaseOpens_EFE) :
        C.toChain.finalBase_BAS 0) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) :=
    (A.proj.final_smooth 0).comp (contMDiff_subtype_val (I := 𝓘(ℝ, E3)))
  exact A.circle_contMDiff_of_val_EFE _ hFval

/-- **`proj` is smooth** for the abstract structure of `W₁` (`CircleBundle.proj_smooth`). -/
theorem circleProj_contMDiff_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain) :
    let _ := A.circleChartedSpace
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ C.circleProj_EFE := by
  intro _
  exact (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff C.circleBaseOpens_EFE
    C.circleProj_EFE).mp (C.circleProjW_contMDiff_EFE A)

/-- **`proj` is a submersion at every point** (`CircleBundle.proj_submersion`): the chart `κ_i`
of `W₁` is a smooth chart and `g_i = κ_i ∘ π₁E` is a submersion on `Y_i` (GAF07 (6)). -/
theorem circleProj_mfderiv_surjective_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain) (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) :
    let _ := A.circleChartedSpace
    ∀ x, Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) C.circleProj_EFE x) := by
  intro _ x
  have hFs := C.circleProjW_contMDiff_EFE A
  have hx : x.1 ∈ ⋃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
        ‖C.toChain.gaf07CircleCoord_GAFC i p‖ < 4} := x.2
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  have hxY : x.1 ∈ gaf07CircleY_GAFC P.toLocalChartPackets i := hi.1
  have hsubF : Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun z : C.circleDomain_EFE =>
      ((C.circleProj_EFE z : C.circleBaseOpens_EFE) : C.toChain.finalBase_BAS 0)) x) := by
    refine A.circle_surjective_mfderiv_EFE _ x i ?_ (hFs.contMDiffAt) ?_
    · exact (C.toGaf02ChainE.final_mem_circleBase_GAFC i hxY).2
    · have h1 := C.toChain.gaf07_circle_submersion_of_mem_GAFD C.c_two_lt hβ hd i hxY
      have h2 := DifferentialGeometry.mfderiv_restrict_open (I := 𝓘(ℝ, E3)) (J := 𝓘(ℝ, ℝ²))
        (C.toChain.gaf07CircleCoord_GAFC i) C.circleDomain_EFE x
      exact h2.symm ▸ h1
  have h := DifferentialGeometry.Topology.mfderiv_subtypeVal_comp (I := 𝓘(ℝ, E3))
    (J := 𝓘(ℝ, ℝ²)) C.circleBaseOpens_EFE C.circleProj_EFE x
  rw [← h]
  exact hsubF

theorem circleProj_continuous_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    Continuous C.circleProj_EFE := by
  have hπc : Continuous (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
      (C.toChain.E p)) :=
    (gafStageQ P.toLocalChartFamily P.zero 0).starProjection.continuous.comp
      C.toChain.stage_smooth.2.2.continuous
  exact Topology.IsInducing.subtypeVal.continuous_iff.mpr
    (Topology.IsInducing.subtypeVal.continuous_iff.mpr (hπc.comp continuous_subtype_val))

/-- **`proj` is proper** (`CircleBundle`: proper smooth circle bundle): the preimage of a compact
set is a closed subset of the compact `X`, contained in the domain. -/
theorem circleProj_isProper_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    IsProperMap C.circleProj_EFE := by
  have hπc : Continuous (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
      (C.toChain.E p)) :=
    (gafStageQ P.toLocalChartFamily P.zero 0).starProjection.continuous.comp
      C.toChain.stage_smooth.2.2.continuous
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨C.circleProj_continuous_EFE, fun Kc hKc => ?_⟩
  have hK' : IsCompact ((fun v : C.circleBaseOpens_EFE => ((v : C.toChain.finalBase_BAS 0) :
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) '' Kc) :=
    hKc.image (continuous_subtype_val.comp continuous_subtype_val)
  have hcl : IsCompact ((fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
      (C.toChain.E p)) ⁻¹' ((fun v : C.circleBaseOpens_EFE => ((v : C.toChain.finalBase_BAS 0) :
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) '' Kc)) :=
    (hK'.isClosed.preimage hπc).isCompact
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  convert hcl using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨C.circleProj_EFE y, hy, rfl⟩
  · rintro ⟨v, hv, hvx⟩
    have hvx' : ((v : C.toChain.finalBase_BAS 0) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) =
        (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E x) := hvx
    have hxD : x ∈ C.circleDomain_EFE :=
      C.mem_circleDomain_of_EFE (hvx' ▸ v.1.2) (hvx' ▸ v.2)
    refine ⟨⟨x, hxD⟩, ?_, rfl⟩
    have hpv : C.circleProj_EFE ⟨x, hxD⟩ = v := Subtype.ext (Subtype.ext hvx.symm)
    change C.circleProj_EFE ⟨x, hxD⟩ ∈ Kc
    rw [hpv]
    exact hv

/-- **`proj` is onto `W₁ ∩ R₁`** (GAF07 (5)). -/
theorem circleProj_surjective_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    Surjective C.circleProj_EFE := fun cc => by
  obtain ⟨p, hp⟩ := C.toGaf02ChainE.gaf07_circle_onto_GAFC (cc : C.toChain.finalBase_BAS 0) cc.1.2
  have hD : p ∈ C.circleDomain_EFE := C.mem_circleDomain_of_EFE (hp ▸ cc.1.2) (hp ▸ cc.2)
  exact ⟨⟨p, hD⟩, Subtype.ext (Subtype.ext hp)⟩

/-- **The fibres of `proj` are the WHOLE fibres of `π₁E`** (the SAME whole circles of GAF07; the
saturation `E⁻¹(C₁) = proj⁻¹(C₁)`). -/
theorem circleProj_fibre_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (cc : C.circleBaseOpens_EFE) :
    Subtype.val '' {x : C.circleDomain_EFE | C.circleProj_EFE x = cc} =
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) ⁻¹'
        {((cc : C.toChain.finalBase_BAS 0) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact congrArg (fun v : C.circleBaseOpens_EFE => ((v : C.toChain.finalBase_BAS 0) :
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) hx
  · intro hp
    have hp' : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) =
        ((cc : C.toChain.finalBase_BAS 0) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) := hp
    have hpD : p ∈ C.circleDomain_EFE := C.mem_circleDomain_of_EFE (hp' ▸ cc.1.2) (hp' ▸ cc.2)
    exact ⟨⟨p, hpD⟩, Subtype.ext (Subtype.ext hp'), rfl⟩

theorem circleProj_connected_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (cc : C.circleBaseOpens_EFE) :
    IsConnected {x : C.circleDomain_EFE | C.circleProj_EFE x = cc} := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := C.gaf07_circle_row_GAFD hβ hd
  obtain ⟨i, hi⟩ := mem_iUnion.mp cc.2
  obtain ⟨-, -, -, hcon, -⟩ := h7 cc.1.1 cc.1.2 i hi.1 hi.2
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := C.circleProj_surjective_EFE cc
    exact ⟨x, hx⟩
  · exact (Topology.IsInducing.subtypeVal.isPreconnected_image).mp
      ((C.circleProj_fibre_EFE cc) ▸ hcon.isPreconnected)

/-- **The whole fibre of `proj` is a smooth embedded circle** in `X`. -/
theorem circleProj_circle_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (cc : C.circleBaseOpens_EFE) :
    ∃ f : Circle → X, IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E3) ∞ f ∧
      range f = Subtype.val '' {x : C.circleDomain_EFE | C.circleProj_EFE x = cc} := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := C.gaf07_circle_row_GAFD hβ hd
  obtain ⟨i, hi⟩ := mem_iUnion.mp cc.2
  obtain ⟨-, -, -, -, ⟨f, hf, hrf⟩, -⟩ := h7 cc.1.1 cc.1.2 i hi.1 hi.2
  exact ⟨f, hf, by rw [C.circleProj_fibre_EFE cc]; exact hrf⟩

/-- **`cbase` is compact** (`CircleBundle.cbase_compact`): the image `π₁E(M₃)` of a closed set
`M₃ ⊆ domain` (the actual remainder is closed in the compact `X`). -/
theorem circleProj_cbase_compact_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) {M₃ : Set X}
    (hM : IsClosed M₃) (hMD : M₃ ⊆ C.circleDomain_EFE) :
    IsCompact (C.circleProj_EFE '' (Subtype.val ⁻¹' M₃)) := by
  refine IsCompact.image ?_ C.circleProj_continuous_EFE
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have h : (Subtype.val : C.circleDomain_EFE → X) '' (Subtype.val ⁻¹' M₃) = M₃ := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      exact ⟨⟨p, hMD hp⟩, hp, rfl⟩
  rw [h]
  exact hM.isCompact

/-- The projection as a continuous map (the form `CircleBundle.proj : C(domain, Base)`). -/
def circleProjC_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    C(↥C.circleDomain_EFE, ↥C.circleBaseOpens_EFE) :=
  ⟨C.circleProj_EFE, C.circleProj_continuous_EFE⟩

/-- **The local trivializations preserving the projection** (`CircleBundle.trivialization`,
`projection_trivialization`): over a neighbourhood `Q` of every point of `W₁ ∩ R₁` (open in the
abstract base), a diffeomorphism `proj⁻¹(Q) ≃ₘ Q × Circle` (models `𝓘(ℝ, E3)` and
`(𝓡 2).prod (𝓡 1)`) whose first coordinate is `proj`. -/
theorem circleProj_trivial_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain) (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) :
    let _ := A.circleChartedSpace
    ∀ cc : ↥C.circleBaseOpens_EFE, ∃ Q : TopologicalSpace.Opens ↥C.circleBaseOpens_EFE, cc ∈ Q ∧
      ∃ Ψ : Diffeomorph 𝓘(ℝ, E3) ((𝓡 2).prod (𝓡 1))
        ↥(TopologicalSpace.Opens.comap C.circleProjC_EFE Q) (↥Q × Circle) ∞,
        ∀ x, (Ψ x).1.1 = C.circleProj_EFE x.1 := by
  intro _ cc
  let _ : IsManifold 𝓘(ℝ, ℝ²) ∞ (C.toChain.finalBase_BAS 0) := A.circle_isManifold.1
  have hdim : Module.finrank ℝ E3 = Module.finrank ℝ ℝ² + 1 := by
    simp only [finrank_euclideanSpace_fin]
  have : LocallyCompactSpace C.circleDomain_EFE :=
    ChartedSpace.locallyCompactSpace E3 C.circleDomain_EFE
  have h1 : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ C.circleProj_EFE := C.circleProj_contMDiff_EFE A
  have h2 : ∀ x, Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) C.circleProj_EFE x) :=
    C.circleProj_mfderiv_surjective_EFE A hβ hd
  have h3 : ∀ y, IsConnected {x | C.circleProj_EFE x = y} := C.circleProj_connected_EFE hβ hd
  have h4 : IsProperMap C.circleProj_EFE := C.circleProj_isProper_EFE
  exact exists_circle_trivialization_of_proper_submersion_EFE C.circleProj_EFE
    h1 h4 h2 hdim h3 cc

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
