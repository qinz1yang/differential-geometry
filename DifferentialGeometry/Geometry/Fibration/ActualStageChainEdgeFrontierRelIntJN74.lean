import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimRelIntJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerRegularJN74

/-!
# Draft 74, FDC03 at the horizontal faces: `M₃ ∩ ∂M₂ = ∂M₂ ∖ relInt_{∂M₂}(horizontal disks)`

Lane S-JUNCTIONS (by S-JUNCTIONS3), G12 (suffix `_JN74`). The field `region_boundary` of the face
facts, on the actual chain and from FDC03's relative-interior removal (review 78 D78-8: not from
rank two alone, not from a corner record that presupposes the faces). With
`H = ∂M₂ ∩ {x ∈ source | T x ≤ 4Δ}` (the horizontal disks, `edge_frontier_H_EFE`):

* `exists_frontier_point_above_JN74` (the key step): a rim point `x ∈ H` (`T x = 4Δ`) is a limit of
  points of `∂M₂` with `T > 4Δ` (the pair `(T − 4Δ, F)` is a submersion at `x`, so it reaches
  `(r, 0)`; there `dF ≠ 0` (`db ≠ 0` near the endpoint, `d f₂` onto), so the point is a limit of
  `{F < 0}`, i.e. lies in `∂M₂`);
* `mem_relInt_frontier_iff_JN74`: `x ∈ relInt_{∂M₂} H ↔ x ∈ H ∧ T x < 4Δ`;
* **`frontier_inter_cutM3_JN74`**: `∂M₂ ∩ M₃ = ∂M₂ ∖ relInt_{∂M₂} H`
  (with `mem_relInt_iff_JN74`: `int_{M₂} M^edge = M^edge ∩ {T < 4Δ}`).
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

namespace Gaf02ChainEJA

section FrontierRelInt

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **A rim point of the horizontal disks is a limit of points of `∂M₂` above the level.** -/
theorem exists_frontier_point_above_JN74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
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
    {x : X} (hxF : x ∈ frontier (edgeM2_EFE C K₃)) (hxsrc : x ∈ C.edgeSource_EFE)
    (hxT : C.edgeHeightGlobal_EFE x = 4 * Δ) {O : Set X} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ z ∈ O, z ∈ frontier (edgeM2_EFE C K₃) ∧ 4 * Δ < C.edgeHeightGlobal_EFE z ∧
      z ∈ C.edgeSource_EFE := by
  let _ := A.edgeChartedSpace1
  have := A.edge_isManifold1.1
  obtain ⟨N, hN, hxN, hh, hhN, hzero, hdef, hdb⟩ :=
    C.edge_regular_data_EFE A hεr K₃ D₃ hD hKs hKF hDreg hdD ⟨x, hxsrc⟩ hxF
  have hT' : C.edgeHeight_EFE ⟨x, hxsrc⟩ = 4 * Δ := hxT
  have hrank := C.toGaf02ChainE.edge_corner_rank_raw_EFE A hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 hN hhN
    ⟨x, hxsrc⟩ hxN hT' hdb
  have hval := C.contMDiff_edgeValB_EFE A
  let Uo : TopologicalSpace.Opens C.edgeBaseOpens_EFE :=
    ⟨C.edgeValB_EFE ⁻¹' N, hN.preimage hval.continuous⟩
  have hc₀U : C.edgeProj_EFE ⟨x, hxsrc⟩ ∈ Uo := by
    change C.edgeValB_EFE (C.edgeProj_EFE ⟨x, hxsrc⟩) ∈ N
    rw [C.edgeValB_edgeProj_EFE]
    exact hxN
  have hb₀ : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun cc => hh (C.edgeValB_EFE cc)) Uo :=
    hhN.contMDiffOn.comp hval.contMDiffOn (fun cc hcc => hcc)
  obtain ⟨U', hc₀U', hU'U, hreg'⟩ := exists_nhds_mfderiv_ne_zero_JN74 hc₀U hb₀ hdb
  have hproj := C.edgeProj_contMDiff_EFE A
  have hO₁ : IsOpen (Subtype.val '' (C.edgeProj_EFE ⁻¹' (U' : Set C.edgeBaseOpens_EFE)) :
      Set X) :=
    C.edgeSource_EFE.isOpen.isOpenMap_subtype_val _ (U'.isOpen.preimage hproj.continuous)
  have hxO₁ : x ∈ (Subtype.val '' (C.edgeProj_EFE ⁻¹' (U' : Set C.edgeBaseOpens_EFE)) : Set X) :=
    ⟨⟨x, hxsrc⟩, hc₀U', rfl⟩
  have hTg := C.contMDiff_edgeHeightGlobal_EFE
  have hF : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => hh (C.edgeBlockProj_EFE y)) x :=
    ((hhN.contDiffAt (hN.mem_nhds hxN)).contMDiffAt).comp x
      ((C.contMDiff_edgeBlockProj_EFE A) x)
  have hΨ : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ) 1
      (fun y : X => (C.edgeHeightGlobal_EFE y - 4 * Δ, hh (C.edgeBlockProj_EFE y))) x :=
    (((hTg.contMDiffAt.sub contMDiffAt_const).prodMk_space hF)).of_le (by simp)
  have hmap := map_nhds_eq_of_mfderiv_surjective_at hΨ hrank
  have hOs : O ∩ Subtype.val '' (C.edgeProj_EFE ⁻¹' (U' : Set C.edgeBaseOpens_EFE)) ∈ 𝓝 x :=
    (hO.inter hO₁).mem_nhds ⟨hxO, hxO₁⟩
  have himg : (fun y : X => (C.edgeHeightGlobal_EFE y - 4 * Δ, hh (C.edgeBlockProj_EFE y))) ''
      (O ∩ Subtype.val '' (C.edgeProj_EFE ⁻¹' (U' : Set C.edgeBaseOpens_EFE))) ∈
      𝓝 ((C.edgeHeightGlobal_EFE x - 4 * Δ, hh (C.edgeBlockProj_EFE x))) := by
    rw [← hmap]
    exact Filter.image_mem_map hOs
  have hx0 : ((C.edgeHeightGlobal_EFE x - 4 * Δ, hh (C.edgeBlockProj_EFE x))) = (0, 0) := by
    rw [hxT, hzero, sub_self]
  rw [hx0] at himg
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp himg
  have hv : ((r / 2, 0) : ℝ × ℝ) ∈ Metric.ball ((0, 0) : ℝ × ℝ) r := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero,
      abs_of_pos (half_pos hr), abs_zero]
    exact max_lt (half_lt_self hr) hr
  obtain ⟨p, ⟨hpO, p₁, hp₁U, rfl⟩, hpΨ⟩ := hball hv
  have hp1 : C.edgeHeightGlobal_EFE p₁.1 - 4 * Δ = r / 2 := congrArg Prod.fst hpΨ
  have hp2 : hh (C.edgeBlockProj_EFE p₁.1) = 0 := congrArg Prod.snd hpΨ
  have hpN : C.edgeBlockProj_EFE p₁.1 ∈ N := by
    rw [← C.edgeValB_edgeProj_EFE p₁]
    exact hU'U hp₁U
  obtain ⟨-, hFcomp⟩ := C.edge_descended_mfderiv_EFE A hN hhN
    (F := fun y => hh (C.edgeBlockProj_EFE y)) (fun _ => rfl) p₁ hpN
  have hsubm := C.edge_proj_submersion_EFE A p₁
  have hdF : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => hh (C.edgeBlockProj_EFE y)) p₁.1 ≠ 0 := by
    intro h0
    apply hreg' _ hp₁U
    rw [hFcomp] at h0
    ext w
    obtain ⟨v, rfl⟩ := hsubm w
    exact congrArg (fun L : TangentSpace 𝓘(ℝ, E3) p₁.1 →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) _ => L v) h0
  have hcl := Gaf02ChainE.mem_closure_neg_of_mfderiv_ne_zero_EFE (I := 𝓘(ℝ, E3)) hdF hp2
  have hW : IsOpen {y : X | C.edgeBlockProj_EFE y ∈ N} :=
    hN.preimage C.toGaf02ChainE.continuous_edgeBlockProj_EFE
  have hclM : p₁.1 ∈ closure ((edgeM2_EFE C K₃)ᶜ) := by
    refine closure_mono ?_ (hW.closure_inter ⟨hcl, hpN⟩)
    rintro y ⟨hy1, hy2⟩ hyM
    have h1 := (hdef y hy2).mp hyM
    exact absurd hy1 (not_lt.mpr h1)
  have hpM : p₁.1 ∈ edgeM2_EFE C K₃ := (hdef p₁.1 hpN).mpr hp2.ge
  refine ⟨p₁.1, hpO, ⟨subset_closure hpM, ?_⟩, ?_, p₁.2⟩
  · rw [interior_eq_compl_closure_compl]
    exact not_not.mpr hclM
  · linarith


/-- **The horizontal disks of the chain**: `H = ∂M₂ ∩ {x ∈ source | T x ≤ 4Δ}`
(`= f₂⁻¹(∂C₂) ∩ {T ≤ 4Δ}` by `edge_frontier_H_EFE`). -/
abbrev edgeHorizontalDisks_JN74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (K₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35) : Set X :=
  frontier (edgeM2_EFE C K₃) ∩ Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ}

/-- **`relInt_{∂M₂}(H) = H ∩ {T < 4Δ}`**. -/
theorem mem_relInt_frontier_iff_JN74
    {C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj}
    (A : SmoothStageBasesOn74 C.toChain)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    {K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35}
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
    {x : X} :
    x ∈ Subtype.val '' interior (Subtype.val ⁻¹' (C.edgeHorizontalDisks_JN74 K₃) :
      Set (frontier (edgeM2_EFE C K₃))) ↔
      x ∈ C.edgeHorizontalDisks_JN74 K₃ ∧ C.edgeHeightGlobal_EFE x < 4 * Δ := by
  constructor
  · intro hx
    obtain ⟨hxF, O, hO, hxO, hOA⟩ := (mem_image_interior_preimage_val_iff).mp hx
    have hxH : x ∈ C.edgeHorizontalDisks_JN74 K₃ := hOA ⟨hxO, hxF⟩
    obtain ⟨-, x', hx'T, hx'x⟩ := hxH
    refine ⟨⟨hxF, x', hx'T, hx'x⟩, lt_of_le_of_ne ?_ fun heq => ?_⟩
    · rw [← hx'x]
      exact hx'T
    · obtain ⟨z, hzO, hzF, hzT, hzsrc⟩ := C.exists_frontier_point_above_JN74 A hεr hΔ2 hc hϑ hε0
        hε hγc hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg hdD hxF (hx'x ▸ x'.2) heq hO hxO
      obtain ⟨-, z', hz'T, hz'z⟩ := hOA ⟨hzO, hzF⟩
      have : z' = ⟨z, hzsrc⟩ := Subtype.ext hz'z
      rw [this] at hz'T
      exact absurd hz'T (not_le.mpr hzT)
  · rintro ⟨⟨hxF, hxH⟩, hlt⟩
    refine (mem_image_interior_preimage_val_iff).mpr ⟨hxF, (C.edgeSource_EFE : Set X) ∩
      {z | C.edgeHeightGlobal_EFE z < 4 * Δ}, C.edgeSource_EFE.isOpen.inter
        (isOpen_lt C.toGaf02ChainE.continuous_edgeHeightGlobal_EFE continuous_const),
      ⟨?_, hlt⟩, ?_⟩
    · obtain ⟨x', -, rfl⟩ := hxH
      exact x'.2
    · rintro z ⟨⟨hzsrc, hzlt⟩, hzF⟩
      have hzle : C.edgeHeight_EFE ⟨z, hzsrc⟩ ≤ 4 * Δ := le_of_lt hzlt
      exact ⟨hzF, ⟨z, hzsrc⟩, hzle, rfl⟩

/-- **FDC03's `region_boundary` on the actual chain**: `∂M₂ ∩ M₃ = ∂M₂ ∖ relInt_{∂M₂}(H)`. -/
theorem frontier_inter_cutM3_JN74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
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
    :
    frontier (edgeM2_EFE C K₃) ∩ C.toGaf02ChainE.cutM3_R74 K₃.carrier =
      frontier (edgeM2_EFE C K₃) \ Subtype.val '' interior
        (Subtype.val ⁻¹' (C.edgeHorizontalDisks_JN74 K₃) : Set (frontier (edgeM2_EFE C K₃))) := by
  ext x
  constructor
  · rintro ⟨hxF, hx3⟩
    refine ⟨hxF, fun hrel => ?_⟩
    obtain ⟨⟨-, x', hx'T, hx'x⟩, hlt⟩ := (mem_relInt_frontier_iff_JN74 (C := C) A hεr hΔ2 hc hϑ
      hε0 hε hγc hγc1 hβc1 hD hKs hKF hDreg hdD).mp hrel
    have hxE : x ∈ C.toGaf02ChainE.cutEdgeSet_R74 K₃.carrier :=
      ⟨hx3.1, hx'x ▸ C.mem_edgeRegion_of_source_JN74 x'.2 hx'T⟩
    exact hx3.2 (C.mem_relInt_of_lt_JN74 hΔ2 K₃ hxE hlt)
  · rintro ⟨hxF, hxnot⟩
    have hxM2 : x ∈ edgeM2_EFE C K₃ := (C.edge_face_data_EFE hεr K₃ D₃ hD hKs hKF hDreg hdD hxF).1
    refine ⟨hxF, hxM2, fun hrel => hxnot ?_⟩
    obtain ⟨hxE, hlt⟩ := (mem_relInt_iff_JN74 (C := C) A hεr hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 hD hKs
      hKF hDreg hdD).mp hrel
    obtain ⟨hT, hsrc⟩ := C.cutEdgeSet_height_le_JN74 hΔ2 K₃ hxE
    exact (mem_relInt_frontier_iff_JN74 (C := C) A hεr hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 hD hKs hKF
      hDreg hdD).mpr ⟨⟨hxF, ⟨x, hsrc⟩, hT, rfl⟩, hlt⟩

end FrontierRelInt

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
