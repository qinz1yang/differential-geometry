import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimM2DomainZSP35
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeZeroDescentEFE
import DifferentialGeometry.Topology.Ehresmann.ArcEndDescentEFE

/-!
# EDP05, slim faces: the descended defining identity on the edge stage

Lane S-EDP-FDC3, group G8 (EDP05, slim half; draft 74 D74-11 / D74-14 layers 1–2).
Blueprint `master207B.tex`, EDP05 (B:7040–7090): "If it meets a slim boundary, its constant `π₂E`
makes `π₃E` constant; GAF07 and ZSP04 identify the WHOLE latter fiber with that slim boundary. Thus
the entire disk lies in the same component of `∂M₂`. ... For a slim face use a local coordinate
defining its chosen endpoint in `D₃`, composed with `π_{2,3}` on the base. This latter composition
has its required domain: the whole compact edge disk lies in the open set `X₃`; properness of `f₂`
gives a base neighborhood whose whole disks stay in `X₃`."

* `slim_free_end_tube_descent_EFE`: ZSP05's tube over a free arc end of `D₃` with the defining
  function exported as `h = a ∘ f₃` (kernel `exists_arc_end_tube_descent_EFE`, `a` smooth on the
  block space);
* `edge_slim_face_descent_EFE`: for a point `x` of the whole fibre `f₃⁻¹(y)` over a free end `y`:
  (hface) the whole `π₂E`-fibre through `x` lies in `M₂ = M₁ ∖ int_{M₁} M^slim(K₃)`;
  (hdesc) an open `N ∋ π₂E x` of the block space and a smooth `hh = a ∘ π_{2,3}` with
  `z ∈ M₂ ↔ hh(π₂E z) ≥ 0` for all `z` with `π₂E z ∈ N`, and the ambient `F = h` (nonzero
  differential at `x`) with `F = hh ∘ π₂E`. The domain `N = (π₂E '' U^c)^c` is the properness
  argument, using compactness of `X`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open GC.GraphManifold GC.Endpoint
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann

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
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

section Final

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **The tube over a free arc end, inside `M₁`, with `h = a ∘ f₃`** (the kernel tube
`exists_arc_end_tube_descent_EFE` for the proper submersion `f₃`, as ZSP05's
`slim_free_end_tube_ZSP35`, with the extra open set `G ∋ y`, `G ∩ Bs ⊆ C₃`). -/
theorem slim_free_end_tube_descent_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    {y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hy : ∃ k : Fin D₃.m, y = D₃.arc k 0 ∨ y = D₃.arc k 1)
    (hyC : y ∈ Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) :
    ∃ (U : Set X) (h : X → ℝ)
      (a : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ),
      IsOpen U ∧ C.slimMap_ZSP35 ⁻¹' {y} ⊆ U ∧ U ⊆ (interior C.zeroUnion_ZSP35)ᶜ ∧
      ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ h U ∧
      (∀ x ∈ U, Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) h x)) ∧
      {x | x ∈ U ∧ h x = 0} = C.slimMap_ZSP35 ⁻¹' {y} ∧
      U ∩ C.slimMap_ZSP35 ⁻¹' D₃.carrier = {x | x ∈ U ∧ h x ≤ 0} ∧
      ContDiff ℝ ∞ a ∧ ∀ x, h x = a (C.slimMap_ZSP35 x) := by
  obtain ⟨hsat, -⟩ := C.zsp03_slim_saturated_ZSP35 hεr
  obtain ⟨-, G, hG, hyG, hGC⟩ := mem_image_interior_preimage_val_iff.mp hyC
  obtain ⟨U, h, a, hUo, hfU, hUB, -, hh, hsurj, hlev, hside, ha, hha⟩ :=
    exists_arc_end_tube_descent_EFE (P := C.slimSubmersion_EFE) D₃ hy hG hyG
  refine ⟨U, h, a, hUo, hfU, ?_, hh, hsurj, hlev, hside, ha, hha⟩
  intro x hx
  have hx' := hUB hx
  have hxB : C.slimMap_ZSP35 x ∈ C.slimBs_ZSP35 := hx'.2
  have hxC : C.slimMap_ZSP35 x ∈ C.slimC3_ZSP35 := hGC ⟨hx'.1, hx'.2⟩
  have : x ∈ C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35 ∩ C.slimMap_ZSP35 ⁻¹' C.slimC3_ZSP35 :=
    ⟨hxB, hxC⟩
  rw [← hsat] at this
  exact this.1

/-- **EDP05 along a slim face** (hface and hdesc, pointwise on whole `π₂E`-fibres): for a point `x`
of the whole fibre `f₃⁻¹(y)` over a free arc end `y ∈ int C₃` of `D₃` (`M^slim = f₃⁻¹(D₃)`):
the whole `π₂E`-fibre through `x` lies in `M₂ = M₁ ∖ int_{M₁} M^slim`; and there are an open
`N ∋ π₂E x` of the block space and a smooth `hh` with `z ∈ M₂ ↔ hh(π₂E z) ≥ 0` for all `z` with
`π₂E z ∈ N`, together with an ambient `F` of nonzero differential at `x` with `F = hh ∘ π₂E`. -/
theorem edge_slim_face_descent_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hSD : C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier)
    {y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hy : ∃ k : Fin D₃.m, y = D₃.arc k 0 ∨ y = D₃.arc k 1)
    (hyC : y ∈ Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35))
    {x : X} (hxy : C.slimMap_ZSP35 x = y) :
    (∀ z : X, (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E z) =
        (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E x) →
      z ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier) ∧
    ∃ N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen N ∧
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E x) ∈ N ∧
      ∃ hh : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ,
        ContDiff ℝ ∞ hh ∧
        (∀ z : X, (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E z) ∈ N →
          (z ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier ↔
            0 ≤ hh ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
              (C.toChain.E z)))) ∧
        ∃ F : X → ℝ, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F x ∧
          mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F x ≠ 0 ∧
          ∀ z : X, F z = hh ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (C.toChain.E z)) := by
  obtain ⟨U, h, a, hUo, hfU, hUM, hh, hsurj, hlev, hside, ha, hha⟩ :=
    C.slim_free_end_tube_descent_EFE hεr D₃ hy hyC
  have hS : C.slimPiece_ZSP35 K₃.carrier ∩ U = {x | x ∈ U ∧ h x ≤ 0} := by
    rw [hSD, inter_comm]
    exact hside
  have hM2 : C.toGaf02ChainE.cutM2_R74 K₃.carrier ∩ U = {z | z ∈ U ∧ 0 ≤ h z} :=
    free_end_M2_ZSP35 hUo hUM hh hsurj hS
  have hQ3 : ∀ w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
        ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection w) =
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection w :=
    gafStageQ_two_starProjection_one_EFE P.toLocalChartFamily P.zero
  have hsl : ∀ z : X, C.slimMap_ZSP35 z = (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
      ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E z)) :=
    fun z => (hQ3 _).symm
  have hcont2 : Continuous fun z : X =>
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E z) :=
    (gafStageQ P.toLocalChartFamily P.zero 1).starProjection.continuous.comp
      C.toChain.stage_smooth.2.2.continuous
  have hxU : x ∈ U := hfU hxy
  have hxh0 : h x = 0 := by
    have : x ∈ {z | z ∈ U ∧ h z = 0} := by
      rw [hlev]
      exact hxy
    exact this.2
  refine ⟨fun z hz => ?_, ((fun z => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
    (C.toChain.E z)) '' Uᶜ)ᶜ, (hUo.isClosed_compl.isCompact.image hcont2).isClosed.isOpen_compl,
    ?_, fun w => a ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection w),
    ha.comp (gafStageQ P.toLocalChartFamily P.zero 2).starProjection.contDiff, ?_, h, ?_, ?_, ?_⟩
  · have hzy : C.slimMap_ZSP35 z = y :=
      (hsl z).trans ((congrArg _ hz).trans ((hsl x).symm.trans hxy))
    have hzU : z ∈ {w | w ∈ U ∧ h w = 0} := by
      rw [hlev]
      exact hzy
    have : z ∈ {w | w ∈ U ∧ 0 ≤ h w} := ⟨hzU.1, hzU.2.ge⟩
    rw [← hM2] at this
    exact this.1
  · rintro ⟨z, hz, hzx⟩
    apply hz
    apply hfU
    have hzx' : (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E z) =
        (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E x) := hzx
    exact (hsl z).trans ((congrArg _ hzx').trans ((hsl x).symm.trans hxy))
  · intro z hz
    beta_reduce
    have hzU : z ∈ U := by
      by_contra hzU
      exact hz ⟨z, hzU, rfl⟩
    have hhz : h z = a ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection
        ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E z))) :=
      (hha z).trans (congrArg a (hsl z))
    constructor
    · intro hz2
      have : z ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier ∩ U := ⟨hz2, hzU⟩
      rw [hM2] at this
      rw [← hhz]
      exact this.2
    · intro hz0
      have : z ∈ {w | w ∈ U ∧ 0 ≤ h w} := ⟨hzU, hhz ▸ hz0⟩
      rw [← hM2] at this
      exact this.1
  · exact ((hh x hxU).contMDiffAt (hUo.mem_nhds hxU)).mdifferentiableAt (by decide)
  · intro h0
    obtain ⟨v, hv⟩ := hsurj x hxU (1 : ℝ)
    rw [h0, zero_apply] at hv
    have h01 : (0 : ℝ) = 1 := hv
    exact zero_ne_one h01
  · intro z
    exact (hha z).trans (congrArg a (hsl z))

end Final

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
