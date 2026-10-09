import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeBaseEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeSlimDescentEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeZeroFaceDescentEFE
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.FacePointEFE

/-!
# FDC02 / EDP05 on the actual chain: the compact edge base `C₂` and its smooth faces (E1 head)

Lane S-EDP-FDC3, group G7. Blueprint `master207B.tex`, FDC02 (B:7246–7283) and EDP05
(B:7040–7090); draft 74 D74-11 / D74-17, package E1.

On the final family, for a chain with the smooth stage bases `A` (D74-2) and ZSP04's `K₃, D₃`
(`M^slim = f₃⁻¹(D₃)`, `M₂ = M₁ ∖ int_{M₁} M^slim`): the head
`EdgeDisk.edgeCompactDomain_of_actual_faces74` of the abstract kernel is applied to the actual
objects (source `edgeSource_EFE`, projection `edgeProj_EFE`, height `edgeHeight_EFE`, level `4Δ`,
base `B₂`, `M₂`), all of whose inputs are now discharged from the actual chain:

* `hdisk`: `edgeProj_disk_EFE` (EDP04 over every point of `B₂`);
* `hface`: the face-point classification `frontier_cutM2_cases_EFE` (`∂M₂ = (∂M₁ ∖ M^slim) ∪
  (∂M^slim ∖ ∂M₁)`, ZSP05) and the whole-fibre saturation of the zero faces
  (`edge_zero_fibre_subset_M2_EFE`) and of the free slim faces (`edge_slim_face_descent_EFE`);
* `hdesc`: the face-point lemma `exists_face_point_EFE` (a frontier point of `C₂` carries a point
  of `∂M₂` on its disk), then the descended data `edge_zero_face_descent_EFE` /
  `edge_slim_face_descent_EFE` through the wrapper `edge_descent_wrap_EFE`;
* `hcpt` is the FDC02 compactness input (the consumer discharges it from
  `eventually_fdc02_M2_C14Z_EFC`-type tails).

Conclusion: `C₂` compact, `M₂ ∩ X₂ = f₂⁻¹(C₂) ∩ X₂`, and at every frontier point of `C₂` a smooth
local defining function with nonzero differential, `C₂ = {φ ≥ 0}` locally (`EdgeBundle.cbase_*`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainE

variable {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- The global height `T = A/s` on `X` (`edgeHeight_EFE` is its restriction to the edge source). -/
def edgeHeightGlobal_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) : X → ℝ := fun x =>
  EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero (Ĉ.toChain.E x)) /
    Ĉ.toChain.scale x

/-- The global height is continuous (`s > 0` everywhere). -/
theorem continuous_edgeHeightGlobal_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) :
    Continuous Ĉ.edgeHeightGlobal_EFE := by
  have hE : Continuous Ĉ.toChain.E := Ĉ.toChain.stage_smooth.2.2.continuous
  refine (((EuclideanSpace.proj (0 : Fin 2)).continuous.comp
    (gafHeightVector L.toLocalChartFamily L.zero).continuous).comp hE).div
    ((gafScaleMarker L.toLocalChartFamily L.zero).continuous.comp hE)
    fun x => (Ĉ.toChain.scale_pos x).2.ne'

/-- **The whole disk over a point `c` of `B₂` is the global set `{π₂E = c, T ≤ 4Δ}`** (ELoc). -/
theorem edgeDisk_eq_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ2 : 2 ≤ Δ)
    (cc : Ĉ.edgeBaseOpens_EFE) :
    Subtype.val '' {x : Ĉ.edgeSource_EFE | Ĉ.edgeProj_EFE x = cc ∧ Ĉ.edgeHeight_EFE x ≤ 4 * Δ} =
      {y : X | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E y) =
          (cc.1.1 : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)) ∧
        Ĉ.edgeHeightGlobal_EFE y ≤ 4 * Δ} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    exact ⟨congrArg (fun v : Ĉ.edgeBaseOpens_EFE => (v.1.1 : BlockSpace (fun _ : CGPTag
      L.toLocalChartFamily L.zero => ℝ²))) hx1, hx2⟩
  · rintro ⟨hy1, hy2⟩
    have hR : (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E y) ∈
        edgeRatio_R74 L := by
      rw [hy1]
      exact cc.2
    have hys : y ∈ Ĉ.edgeSource_EFE := Ĉ.mem_edgeSource_EFE hΔ2 hR hy2
    refine ⟨⟨y, hys⟩, ⟨Subtype.ext (Subtype.ext hy1), hy2⟩, rfl⟩

/-- **The edge piece `M₂ ∩ X₂` in the rows' form**: with D74-11's set equality (the low branch
of `V` is absorbed), `M₂ ∩ {x ∈ source | T ≤ 4Δ}` equals `M₂ ∩ (X₂ ∩ V)` in the form of FDC02's
compactness statement. -/
theorem edgePiece_eq_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ2 : 2 ≤ Δ) (M₂ : Set X) :
    M₂ ∩ Subtype.val '' {x : Ĉ.edgeSource_EFE | Ĉ.edgeHeight_EFE x ≤ 4 * Δ} =
      M₂ ∩ ({x | (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x) ∈
          Ĉ.toChain.finalBase_BAS 1 ∧
          ∃ k : L.edge.finite_centres.toFinset,
            9 / 10 * ρ k.1 < blockMarkerCLM
              (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) (.inr (.inr (.inl k)))
              ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x)) ∧
            ‖blockVectorCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
              (.inr (.inr (.inl k)))
              ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))‖ <
            4 * Δ * blockMarkerCLM (V := fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)
              (.inr (.inr (.inl k)))
              ((gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E x))} ∩
        ({p | L.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < Ĉ.toChain.scale p ∧
          EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
            (Ĉ.toChain.E p)) / Ĉ.toChain.scale p ≤ 4 * Δ})) := by
  rw [Ĉ.edgeBase_eq_heightSublevel_EFC]
  ext y
  constructor
  · rintro ⟨hyM, x, hx, rfl⟩
    refine ⟨hyM, ⟨(Ĉ.edgeSource_mem_EFE x.2).1, (Ĉ.edgeSource_mem_EFE x.2).2⟩, hx⟩
  · rintro ⟨hyM, ⟨hyW, hyR⟩, hyT⟩
    exact ⟨hyM, ⟨y, Ĉ.mem_edgeSource_EFE hΔ2 hyR hyT⟩, hyT, rfl⟩

end Gaf02ChainE

namespace Gaf02ChainEJA

section Final

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **Classification of the faces of `M₂`** (ZSP05 (RF), EDP05's two cases): a point of `∂M₂` is
either a zero-face point of `M₂`-type (`x ∈ ∂Z_k`, `f₃ x ∉ K₃`) or lies on the whole fibre `f₃⁻¹(y)`
over a free arc end `y ∈ int C₃` of `D₃`. -/
theorem frontier_cutM2_cases_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    {x : X} (hx : x ∈ frontier (C.toGaf02ChainE.cutM2_R74 K₃.carrier)) :
    (∃ k : P.zero.finite_centres.toFinset,
        x ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∧
          C.slimMap_ZSP35 x ∉ K₃.carrier) ∨
      (∃ y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        (∃ k : Fin D₃.m, y = D₃.arc k 0 ∨ y = D₃.arc k 1) ∧
          y ∈ Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) ∧
          C.slimMap_ZSP35 x = y) := by
  obtain ⟨hSD, hSeq, hSc, -, -, -, hfz, -, hfp⟩ :=
    C.slim_piece_facts_ZSP35 hεr K₃ D₃ hD hKs hKF hDreg
  have hfr := C.slim_M2_frontier_ZSP35 hεr K₃ D₃ hD hKs hDreg
  have hx' : x ∈ frontier ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
      (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier : Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) := hx
  rw [hfr] at hx'
  rcases hx' with ⟨hx1, hxp⟩ | ⟨hx2, hx3⟩
  · left
    have hxF := C.toGaf02ChainE.frontier_cutM1_subset_faces_EFE hεr hx1
    obtain ⟨k, hk⟩ := mem_iUnion.mp hxF
    refine ⟨k, hk, fun hxK => hxp ?_⟩
    rw [hSeq]
    exact ⟨C.toGaf02ChainE.frontier_zspDomain_subset_M1_EFE hεr k hk, hxK⟩
  · right
    have hx2' := hx2
    rw [hfp] at hx2'
    have hyb : C.slimMap_ZSP35 x ∈ D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) := hx2'
    have hends := hyb
    rw [D₃.relFrontier_eq] at hends
    obtain ⟨k, hk⟩ := mem_iUnion.mp hends
    rw [hdD] at hyb
    rcases hyb with hfree | hzero'
    · exact ⟨_, ⟨k, hk⟩, hfree.2, rfl⟩
    · exfalso
      apply hx3
      have hxp : x ∈ C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35 := by
        rw [hfz]
        have hyK : C.slimMap_ZSP35 x ∈ K₃.carrier := by
          obtain ⟨hyB, O, -, hyO, hOK⟩ := mem_image_interior_preimage_val_iff.mp hzero'.1
          exact hOK ⟨hyO, hyB⟩
        exact ⟨hyK, hzero'.2⟩
      obtain ⟨-, hzfr⟩ := C.slim_zero_domain_ZSP35 hεr
      exact hzfr hxp.2

end Final

end Gaf02ChainEJA

open DifferentialGeometry.Topology.Handle in
/-- The range of a continuous map from the closed disk is preconnected and nonempty. -/
theorem isPreconnected_range_closedCell_EFE {Y : Type*} [TopologicalSpace Y]
    {φ : ClosedCell 2 → Y} (hφ : Continuous φ) :
    IsPreconnected (range φ) ∧ (range φ).Nonempty := by
  have hconv : Convex ℝ ({x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1} : Set _) := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 : ℝ))
  let _ : PreconnectedSpace (ClosedCell 2) := Subtype.preconnectedSpace hconv.isPreconnected
  exact ⟨isPreconnected_range hφ, ⟨φ ⟨0, by simp⟩, mem_range_self _⟩⟩

namespace Gaf02ChainE

variable {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- **A frontier point of the edge base carries a face point**: if the whole disks over `B₂` are
the images of continuous maps from the closed disk (E0) and `M^edge = M₂ ∩ X₂` is compact (FDC02),
then for every frontier point `c₀` of `C₂ = f₂(M^edge)` the disk over `c₀` meets `∂M₂`. -/
theorem edgeBase_frontier_facePoint_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw) (hΔ2 : 2 ≤ Δ)
    {M₂ : Set X}
    (hdisk : ∀ cc : Ĉ.edgeBaseOpens_EFE, ∃ φ : ClosedCell 2 → X, Continuous φ ∧
      range φ = Subtype.val '' {x : Ĉ.edgeSource_EFE | Ĉ.edgeProj_EFE x = cc ∧
        Ĉ.edgeHeight_EFE x ≤ 4 * Δ})
    (hproj : Continuous Ĉ.edgeProj_EFE)
    (hcpt : IsCompact (M₂ ∩ Subtype.val '' {x : Ĉ.edgeSource_EFE |
      Ĉ.edgeHeight_EFE x ≤ 4 * Δ}))
    {c₀ : Ĉ.edgeBaseOpens_EFE}
    (hc₀ : c₀ ∈ frontier (Ĉ.edgeProj_EFE '' {x : Ĉ.edgeSource_EFE |
      (x : X) ∈ M₂ ∧ Ĉ.edgeHeight_EFE x ≤ 4 * Δ})) :
    ∃ x : Ĉ.edgeSource_EFE, Ĉ.edgeProj_EFE x = c₀ ∧ Ĉ.edgeHeight_EFE x ≤ 4 * Δ ∧
      (x : X) ∈ frontier M₂ := by
  have hconnne : ∀ cc : Ĉ.edgeBaseOpens_EFE,
      IsPreconnected (Subtype.val '' {x : Ĉ.edgeSource_EFE | Ĉ.edgeProj_EFE x = cc ∧
        Ĉ.edgeHeight_EFE x ≤ 4 * Δ}) ∧
      (Subtype.val '' {x : Ĉ.edgeSource_EFE | Ĉ.edgeProj_EFE x = cc ∧
        Ĉ.edgeHeight_EFE x ≤ 4 * Δ}).Nonempty := fun cc => by
    obtain ⟨φ, hφ, hr⟩ := hdisk cc
    rw [← hr]
    exact isPreconnected_range_closedCell_EFE hφ
  have hC2eq : {cc : Ĉ.edgeBaseOpens_EFE | ((Subtype.val '' {x : Ĉ.edgeSource_EFE |
        Ĉ.edgeProj_EFE x = cc ∧ Ĉ.edgeHeight_EFE x ≤ 4 * Δ}) ∩ M₂).Nonempty} =
      Ĉ.edgeProj_EFE '' {x : Ĉ.edgeSource_EFE |
        (x : X) ∈ M₂ ∧ Ĉ.edgeHeight_EFE x ≤ 4 * Δ} := by
    ext cc
    constructor
    · rintro ⟨y, ⟨x, ⟨hx1, hx2⟩, rfl⟩, hyM⟩
      exact ⟨x, ⟨hyM, hx2⟩, hx1⟩
    · rintro ⟨x, ⟨hM, hx⟩, rfl⟩
      exact ⟨x, ⟨x, ⟨rfl, hx⟩, rfl⟩, hM⟩
  have hC : IsCompact {cc : Ĉ.edgeBaseOpens_EFE | ((Subtype.val '' {x : Ĉ.edgeSource_EFE |
        Ĉ.edgeProj_EFE x = cc ∧ Ĉ.edgeHeight_EFE x ≤ 4 * Δ}) ∩ M₂).Nonempty} := by
    rw [hC2eq]
    exact EdgeDisk.isCompact_edgeBase_EFC (Ĉ.edgeSource_EFE : Set X) hproj Ĉ.edgeHeight_EFE
      (4 * Δ) M₂ hcpt
  have hcont2 : Continuous fun y : X =>
      (gafStageQ L.toLocalChartFamily L.zero 1).starProjection (Ĉ.toChain.E y) :=
    (gafStageQ L.toLocalChartFamily L.zero 1).starProjection.continuous.comp
      Ĉ.toChain.stage_smooth.2.2.continuous
  have hι : Topology.IsEmbedding (fun cc : Ĉ.edgeBaseOpens_EFE =>
      (cc.1.1 : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  rw [← hC2eq] at hc₀
  obtain ⟨y, hyD, hyF⟩ := EdgeDisk.exists_face_point_EFE hι hcont2
    Ĉ.continuous_edgeHeightGlobal_EFE (L := 4 * Δ) (M₂ := M₂)
    (fun cc => Subtype.val '' {x : Ĉ.edgeSource_EFE | Ĉ.edgeProj_EFE x = cc ∧
      Ĉ.edgeHeight_EFE x ≤ 4 * Δ})
    (fun cc => Ĉ.edgeDisk_eq_EFE hΔ2 cc) (fun cc => (hconnne cc).1) (fun cc => (hconnne cc).2)
    hC hc₀
  obtain ⟨x, ⟨hx1, hx2⟩, rfl⟩ := hyD
  exact ⟨x, hx1, hx2, hyF⟩

end Gaf02ChainE

namespace Gaf02ChainEJA

section Assembly

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **hface**: a whole edge disk meeting `∂M₂` lies in `M₂` (zero faces by ZSP03's whole fibres,
free slim faces by the slim fibre `f₃⁻¹(y)`; EDP05's saturation). -/
theorem edgeDisk_face_saturated_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (cc : C.edgeBaseOpens_EFE) :
    (Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x = cc ∧
      C.edgeHeight_EFE x ≤ 4 * Δ} ∩ frontier (C.toGaf02ChainE.cutM2_R74 K₃.carrier)).Nonempty →
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x = cc ∧
        C.edgeHeight_EFE x ≤ 4 * Δ} ⊆ C.toGaf02ChainE.cutM2_R74 K₃.carrier := by
  have hSD : C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier :=
    (C.slim_piece_facts_ZSP35 hεr K₃ D₃ hD hKs hKF hDreg).1
  rintro ⟨x, hxD, hxF⟩
  rw [C.toGaf02ChainE.edgeDisk_eq_EFE hΔ2] at hxD ⊢
  rcases C.frontier_cutM2_cases_EFE hεr K₃ D₃ hD hKs hKF hDreg hdD hxF with
    ⟨k, hk, hK⟩ | ⟨y, hy, hyC, hxy⟩
  · intro z hz
    exact (C.toGaf02ChainE.edge_zero_fibre_subset_M2_EFE hεr K₃.carrier k hk hK
      (hz.1.trans hxD.1.symm)).2
  · intro z hz
    exact (C.edge_slim_face_descent_EFE hεr K₃ D₃ hSD hy hyC hxy).1 z (hz.1.trans hxD.1.symm)

/-- **hdesc**: at every frontier point `c₀` of `C₂` (which carries a face point `x ∈ ∂M₂` on its
disk) the defining function of `M₂` descends to a smooth function on a neighbourhood of `c₀` in the
abstract base, with the ambient `F = b ∘ f₂` of nonzero differential at a point of the fibre
(zero faces by `edge_zero_face_descent_EFE`, free slim faces by `edge_slim_face_descent_EFE`,
both through `edge_descent_wrap_EFE`). -/
theorem edgeBase_descent_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain) (hεr : εr < 1 / 2)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    {c₀ : C.edgeBaseOpens_EFE}
    (hfp : ∃ x : C.edgeSource_EFE, C.edgeProj_EFE x = c₀ ∧ C.edgeHeight_EFE x ≤ 4 * Δ ∧
      (x : X) ∈ frontier (C.toGaf02ChainE.cutM2_R74 K₃.carrier)) :
    let _ := A.edgeChartedSpace1
    ∃ U : TopologicalSpace.Opens C.edgeBaseOpens_EFE, c₀ ∈ U ∧
      ∃ b : C.edgeBaseOpens_EFE → ℝ, ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U ∧
        (∀ x : C.edgeSource_EFE, C.edgeProj_EFE x ∈ U → C.edgeHeight_EFE x ≤ 4 * Δ →
          ((x : X) ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier ↔ 0 ≤ b (C.edgeProj_EFE x))) ∧
        ∃ x : C.edgeSource_EFE, C.edgeProj_EFE x = c₀ ∧ ∃ F : X → ℝ,
          MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F x ∧ mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) F x ≠ 0 ∧
          (fun z : C.edgeSource_EFE => F z) =ᶠ[nhds x] b ∘ C.edgeProj_EFE := by
  intro _
  have hSD : C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier :=
    (C.slim_piece_facts_ZSP35 hεr K₃ D₃ hD hKs hKF hDreg).1
  have hKc : IsClosed K₃.carrier := K₃.isCompact_carrier_BCF.isClosed
  obtain ⟨x, hxc, -, hxF⟩ := hfp
  rcases C.frontier_cutM2_cases_EFE hεr K₃ D₃ hD hKs hKF hDreg hdD hxF with
    ⟨k, hk, hK⟩ | ⟨y, hy, hyC, hxy⟩
  · obtain ⟨N, hNo, hxN, hh, hhN, hdef, F, hF, hFne, hFeq⟩ :=
      C.toGaf02ChainE.edge_zero_face_descent_EFE hεr hKc k hk hK
    obtain ⟨U, hxU, bb, hbb, hbdef, x', hx', F', hF', hF'ne, hF'eq⟩ :=
      C.toGaf02ChainE.edge_descent_wrap_EFE A (C.toGaf02ChainE.cutM2_R74 K₃.carrier) (4 * Δ) x
        hNo hxN hhN hdef hF hFne hFeq
    exact ⟨U, hxc ▸ hxU, bb, hbb, hbdef, x', hx'.trans hxc, F', hF', hF'ne, hF'eq⟩
  · obtain ⟨-, N, hNo, hxN, hh, hhs, hdef, F, hF, hFne, hFeq⟩ :=
      C.edge_slim_face_descent_EFE hεr K₃ D₃ hSD hy hyC hxy
    obtain ⟨U, hxU, bb, hbb, hbdef, x', hx', F', hF', hF'ne, hF'eq⟩ :=
      C.toGaf02ChainE.edge_descent_wrap_EFE A (C.toGaf02ChainE.cutM2_R74 K₃.carrier) (4 * Δ) x
        hNo hxN hhs.contDiffOn hdef hF hFne hFeq
    exact ⟨U, hxc ▸ hxU, bb, hbb, hbdef, x', hx'.trans hxc, F', hF', hF'ne, hF'eq⟩

/-- **FDC02 / EDP05 on the actual chain: the compact edge base and its smooth faces** (E1 head
`edgeCompactDomain_of_actual_faces74` applied to the actual objects; see the module docstring).
`hcpt` is FDC02's compactness of `M^edge = M₂ ∩ X₂`. -/
theorem edgeCompactDomain_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain) (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (hcpt : IsCompact (C.toGaf02ChainE.cutM2_R74 K₃.carrier ∩
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ})) :
    let _ := A.edgeChartedSpace1
    IsCompact (C.edgeProj_EFE '' {x : C.edgeSource_EFE |
        (x : X) ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier ∧ C.edgeHeight_EFE x ≤ 4 * Δ}) ∧
      C.toGaf02ChainE.cutM2_R74 K₃.carrier ∩
          Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ} =
        Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x ∈ C.edgeProj_EFE ''
          {x : C.edgeSource_EFE | (x : X) ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier ∧
            C.edgeHeight_EFE x ≤ 4 * Δ} ∧ C.edgeHeight_EFE x ≤ 4 * Δ} ∧
      ∀ c₀ ∈ frontier (C.edgeProj_EFE '' {x : C.edgeSource_EFE |
          (x : X) ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier ∧ C.edgeHeight_EFE x ≤ 4 * Δ}),
        ∃ U : TopologicalSpace.Opens C.edgeBaseOpens_EFE, c₀ ∈ U ∧
          ∃ φ : C.edgeBaseOpens_EFE → ℝ, ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c₀ = 0 ∧
            mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c₀ ≠ 0 ∧
            C.edgeProj_EFE '' {x : C.edgeSource_EFE |
              (x : X) ∈ C.toGaf02ChainE.cutM2_R74 K₃.carrier ∧ C.edgeHeight_EFE x ≤ 4 * Δ} ∩ U =
              {c | c ∈ U ∧ 0 ≤ φ c} := by
  intro _
  have hproj := C.edgeProj_contMDiff_EFE A
  have hdisk : ∀ cc : C.edgeBaseOpens_EFE, ∃ φ : ClosedCell 2 → X, Continuous φ ∧
      range φ = Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x = cc ∧
        C.edgeHeight_EFE x ≤ 4 * Δ} := fun cc => by
    obtain ⟨φ, hφ, hr⟩ := C.toGaf02ChainE.edgeProj_disk_EFE hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc
      hγc1 hβc1 cc
    exact ⟨φ, hφ.isEmbedding.continuous, hr⟩
  exact EdgeDisk.edgeCompactDomain_of_actual_faces74 (I := 𝓘(ℝ, E3)) (IB := 𝓡 1)
    C.edgeSource_EFE C.edgeProj_EFE hproj C.edgeHeight_EFE (4 * Δ)
    (C.toGaf02ChainE.cutM2_R74 K₃.carrier) hdisk
    (fun cc => C.edgeDisk_face_saturated_EFE hεr hΔ2 K₃ D₃ hD hKs hKF hDreg hdD cc) hcpt
    (fun c₀ hc₀ => C.edgeBase_descent_EFE A hεr K₃ D₃ hD hKs hKF hDreg hdD
      (C.toGaf02ChainE.edgeBase_frontier_facePoint_EFE hΔ2 hdisk hproj.continuous hcpt hc₀))

end Assembly

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
