import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeSublevel
import DifferentialGeometry.Topology.Manifold.SubmersionOpenMap

/-!
# Draft 74, FDC03 at the rim: no point of the rim is in the relative interior of `M^edge`

Lane S-JUNCTIONS (by S-JUNCTIONS3), G8 (suffix `_JN74`). On the final-family chain
`C : Gaf02ChainEJA …` with the cut data `K₃, D₃` of the EDP05 / EDP06 lemmas:

* `not_mem_relInt_of_exists_JN74` (generic): a point of `M₂` every neighbourhood of which contains
  a point of `M₂` outside `Ed` is not in `Subtype.val '' interior (Subtype.val ⁻¹' Ed : Set M₂)`;
* `cutEdgeSet_height_le_JN74`: `M^edge ⊆ {T ≤ 4Δ}` (D74-11's set equality
  `edgeBase_eq_heightSublevel_EFC`: the low branch of `V` is absorbed);
* **`edge_rim_not_relInt_JN74`**: a rim point `x ∈ M^edge` (`T x = 4Δ`) is NOT in the relative
  interior of `M^edge` in `M₂` (blueprint FDC03 (Last), B:7341–7344: "the relative interior is
  characterized by `T < 4Δ`", the `⟹` direction at the rim). Two cases:
  `x ∈ int M₂` (the height `T` has nonzero differential at `x`, `edge_coord_height_surj_EFE`, so
  `x ∈ closure {T > 4Δ}`), and `x ∈ ∂M₂` (the pair `(T − 4Δ, F)` with the descended defining
  function of `M₂` has onto differential at `x`, EDP05 + `edge_corner_rank_raw_EFE`, hence maps
  neighbourhoods onto neighbourhoods and reaches `(r, 0)`, `r > 0`);
* `rim_mem_cutM3_JN74`: such a rim point lies in `M₃ = M₂ ∖ int_{M₂} M^edge`.

No hypothesis `x ∈ X₁` and no circle datum is needed (the descended corner chart is not used).
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

/-- **A point of `M₂` that is a limit of points of `M₂` outside `Ed` is not in the relative
interior of `Ed` in `M₂`.** -/
theorem not_mem_relInt_of_exists_JN74 {Y : Type*} [TopologicalSpace Y] {M₂ Ed : Set Y} {x : Y}
    (h : ∀ O : Set Y, IsOpen O → x ∈ O → ∃ p ∈ O, p ∈ M₂ ∧ p ∉ Ed) :
    x ∉ Subtype.val '' interior (Subtype.val ⁻¹' Ed : Set M₂) := by
  intro hx
  obtain ⟨-, O, hO, hxO, hOE⟩ := (mem_image_interior_preimage_val_iff).mp hx
  obtain ⟨p, hpO, hpM, hpE⟩ := h O hO hxO
  exact hpE (hOE ⟨hpO, hpM⟩)

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

section RimRelInt

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **The actual `X₂` as a height sublevel** (D74-11's set equality, chain form of
`edgeBase_eq_heightSublevel_EFC` with the global height). -/
theorem edgeRegion_eq_JN74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj) :
    C.toGaf02ChainE.edgeRegion_R74 = C.toGaf02ChainE.cutQ_R74 1 ⁻¹'
      (C.toChain.finalBase_BAS 1 ∩ edgeRatio_R74 P.toLocalChartPacketsC14D.toLocalChartPacketsC14) ∩
      {p | C.edgeHeightGlobal_EFE p ≤ 4 * Δ} :=
  C.toGaf02ChainE.edgeBase_eq_heightSublevel_EFC

/-- **`M^edge ⊆ {T ≤ 4Δ}` and `M^edge` lies in the edge source** (the low branch of `V` is
absorbed by `edgeRegion_eq_JN74`). -/
theorem cutEdgeSet_height_le_JN74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hΔ2 : 2 ≤ Δ) (K₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35) {p : X}
    (hp : p ∈ C.toGaf02ChainE.cutEdgeSet_R74 K₃.carrier) :
    C.edgeHeightGlobal_EFE p ≤ 4 * Δ ∧ p ∈ C.edgeSource_EFE := by
  have h2 : p ∈ C.toGaf02ChainE.edgeRegion_R74 := hp.2
  rw [C.edgeRegion_eq_JN74] at h2
  exact ⟨h2.2, C.toGaf02ChainE.mem_edgeSource_EFE hΔ2 h2.1.2 h2.2⟩

/-- **Points of the edge source at or below the level lie in the region `X₂`.** -/
theorem mem_edgeRegion_of_source_JN74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    {z : X} (hz : z ∈ C.edgeSource_EFE) (hT : C.edgeHeightGlobal_EFE z ≤ 4 * Δ) :
    z ∈ C.toGaf02ChainE.edgeRegion_R74 := by
  rw [C.edgeRegion_eq_JN74]
  exact ⟨⟨(C.edgeSource_mem_EFE hz).1, (C.edgeSource_mem_EFE hz).2⟩, hT⟩

/-- **`M^edge`-membership (the region `X₂`) is constant on the fibres of `E`.** -/
theorem mem_edgeRegion_congr_JN74
    {C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj}
    {x y : X} (h : C.toChain.E x = C.toChain.E y) :
    x ∈ C.toGaf02ChainE.edgeRegion_R74 ↔ y ∈ C.toGaf02ChainE.edgeRegion_R74 := by
  rw [C.edgeRegion_eq_JN74]
  obtain ⟨h1, h2⟩ := C.toChain.edgeRim_data_eq_of_E_eq_EFE h
  have hq : C.toGaf02ChainE.cutQ_R74 1 x = C.toGaf02ChainE.cutQ_R74 1 y := h1
  have hT : C.edgeHeightGlobal_EFE x = C.edgeHeightGlobal_EFE y := h2
  refine and_congr ?_ ?_
  · change C.toGaf02ChainE.cutQ_R74 1 x ∈ (C.toChain.finalBase_BAS 1 ∩
        edgeRatio_R74 P.toLocalChartPacketsC14D.toLocalChartPacketsC14) ↔
      C.toGaf02ChainE.cutQ_R74 1 y ∈ (C.toChain.finalBase_BAS 1 ∩
        edgeRatio_R74 P.toLocalChartPacketsC14D.toLocalChartPacketsC14)
    rw [hq]
  · change C.edgeHeightGlobal_EFE x ≤ 4 * Δ ↔ C.edgeHeightGlobal_EFE y ≤ 4 * Δ
    rw [hT]

/-- **The rim of `M^edge` is not in the relative interior of `M^edge` in `M₂`** (FDC03 (Last),
the `⟹` direction of "`int_{M₂}(M^edge) = M^edge ∩ {T < 4Δ}`" at `T = 4Δ`). -/
theorem edge_rim_not_relInt_JN74
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
    {x : X} (hxE : x ∈ C.toGaf02ChainE.cutEdgeSet_R74 K₃.carrier)
    (hxT : C.edgeHeightGlobal_EFE x = 4 * Δ) :
    x ∉ Subtype.val '' interior (Subtype.val ⁻¹' (C.toGaf02ChainE.cutEdgeSet_R74 K₃.carrier) :
      Set (C.toGaf02ChainE.cutM2_R74 K₃.carrier)) := by
  have hxM2 : x ∈ edgeM2_EFE C K₃ := hxE.1
  obtain ⟨-, hxsrc⟩ := C.cutEdgeSet_height_le_JN74 hΔ2 K₃ hxE
  have hsub : ∀ p ∈ C.toGaf02ChainE.cutEdgeSet_R74 K₃.carrier,
      C.edgeHeightGlobal_EFE p ≤ 4 * Δ := fun p hp => (C.cutEdgeSet_height_le_JN74 hΔ2 K₃ hp).1
  by_cases hint : x ∈ interior (edgeM2_EFE C K₃)
  · -- ambient interior point of `M₂`: `dT ≠ 0` at `x`
    obtain ⟨k, hk⟩ := C.toGaf02ChainE.edge_coord_height_surj_EFE hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1
      ⟨x, hxsrc⟩ hxT
    obtain ⟨v, -, hv⟩ := hk 0 1
    have hne : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) C.edgeHeightGlobal_EFE x ≠ 0 := by
      intro h0
      have h2 : mvfderiv 𝓘(ℝ, E3) C.edgeHeightGlobal_EFE x v =
          mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) C.edgeHeightGlobal_EFE x v := rfl
      rw [h2, h0] at hv
      exact zero_ne_one (α := ℝ) hv
    have hcl := mem_closure_pos_of_mfderiv_ne_zero_ZSP35 (I := 𝓘(ℝ, E3)) hne
    refine not_mem_relInt_of_exists_JN74 fun O hO hxO => ?_
    obtain ⟨p, ⟨hpO, hpI⟩, hpT⟩ := mem_closure_iff.mp hcl (O ∩ interior (edgeM2_EFE C K₃))
      (hO.inter isOpen_interior) ⟨hxO, hint⟩
    refine ⟨p, hpO, interior_subset hpI, fun hpE => ?_⟩
    have h1 := hsub p hpE
    have h2 : 4 * Δ < C.edgeHeightGlobal_EFE p := hxT ▸ hpT
    linarith
  · -- point of `∂M₂`: the pair `(T - 4Δ, F)` is a submersion at `x`
    have hfr : x ∈ frontier (edgeM2_EFE C K₃) := ⟨subset_closure hxM2, hint⟩
    let _ := A.edgeChartedSpace1
    obtain ⟨N, hN, hxN, hh, hhN, hzero, hdef, hdb⟩ :=
      C.edge_regular_data_EFE A hεr K₃ D₃ hD hKs hKF hDreg hdD ⟨x, hxsrc⟩ hfr
    have hT' : C.edgeHeight_EFE ⟨x, hxsrc⟩ = 4 * Δ := hxT
    have hrank := C.toGaf02ChainE.edge_corner_rank_raw_EFE A hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 hN hhN
      ⟨x, hxsrc⟩ hxN hT' hdb
    have hTg := C.contMDiff_edgeHeightGlobal_EFE
    have hF : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => hh (C.edgeBlockProj_EFE y)) x :=
      ((hhN.contDiffAt (hN.mem_nhds hxN)).contMDiffAt).comp x
        ((C.contMDiff_edgeBlockProj_EFE A) x)
    have hΨ : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ) 1
        (fun y : X => (C.edgeHeightGlobal_EFE y - 4 * Δ, hh (C.edgeBlockProj_EFE y))) x :=
      (((hTg.contMDiffAt.sub contMDiffAt_const).prodMk_space hF)).of_le (by simp)
    have hmap := map_nhds_eq_of_mfderiv_surjective_at hΨ hrank
    refine not_mem_relInt_of_exists_JN74 fun O hO hxO => ?_
    have hsrcN : {y : X | C.edgeBlockProj_EFE y ∈ N} ∈ 𝓝 x :=
      (hN.preimage C.toGaf02ChainE.continuous_edgeBlockProj_EFE).mem_nhds hxN
    have hOs : O ∩ {y : X | C.edgeBlockProj_EFE y ∈ N} ∈ 𝓝 x := inter_mem (hO.mem_nhds hxO) hsrcN
    have himg : (fun y : X => (C.edgeHeightGlobal_EFE y - 4 * Δ, hh (C.edgeBlockProj_EFE y))) ''
        (O ∩ {y : X | C.edgeBlockProj_EFE y ∈ N}) ∈
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
    obtain ⟨p, ⟨hpO, hpN⟩, hpΨ⟩ := hball hv
    have hp1 : C.edgeHeightGlobal_EFE p - 4 * Δ = r / 2 := congrArg Prod.fst hpΨ
    have hp2 : hh (C.edgeBlockProj_EFE p) = 0 := congrArg Prod.snd hpΨ
    refine ⟨p, hpO, (hdef p hpN).mpr hp2.ge, fun hpE => ?_⟩
    have h1 := hsub p hpE
    linarith

/-- **A rim point of `M^edge` lies in `M₃ = M₂ ∖ int_{M₂} M^edge`.** -/
theorem rim_mem_cutM3_JN74
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
    {x : X} (hxE : x ∈ C.toGaf02ChainE.cutEdgeSet_R74 K₃.carrier)
    (hxT : C.edgeHeightGlobal_EFE x = 4 * Δ) :
    x ∈ C.toGaf02ChainE.cutM3_R74 K₃.carrier :=
  ⟨hxE.1, C.edge_rim_not_relInt_JN74 A hεr hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg
    hdD hxE hxT⟩

/-- **Below the level, `M^edge` is relatively open in `M₂`**: a point of `M^edge` with `T < 4Δ`
is in `int_{M₂} M^edge` (`M^edge = M₂ ∩ X₂` and `X₂ ⊇ edgeSource ∩ {T < 4Δ}`). -/
theorem mem_relInt_of_lt_JN74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hΔ2 : 2 ≤ Δ) (K₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35) {x : X}
    (hxE : x ∈ C.toGaf02ChainE.cutEdgeSet_R74 K₃.carrier)
    (hlt : C.edgeHeightGlobal_EFE x < 4 * Δ) :
    x ∈ Subtype.val '' interior (Subtype.val ⁻¹' (C.toGaf02ChainE.cutEdgeSet_R74 K₃.carrier) :
      Set (C.toGaf02ChainE.cutM2_R74 K₃.carrier)) := by
  obtain ⟨-, hxsrc⟩ := C.cutEdgeSet_height_le_JN74 hΔ2 K₃ hxE
  refine (mem_image_interior_preimage_val_iff).mpr ⟨hxE.1, (C.edgeSource_EFE : Set X) ∩
    {z | C.edgeHeightGlobal_EFE z < 4 * Δ}, C.edgeSource_EFE.isOpen.inter
      (isOpen_lt C.toGaf02ChainE.continuous_edgeHeightGlobal_EFE continuous_const),
    ⟨hxsrc, hlt⟩, ?_⟩
  rintro z ⟨⟨hzsrc, hzlt⟩, hzM⟩
  exact ⟨hzM, C.mem_edgeRegion_of_source_JN74 hzsrc (le_of_lt hzlt)⟩

/-- **The relative interior of `M^edge` in `M₂` is `M^edge ∩ {T < 4Δ}`** (FDC03 (Last),
B:7341–7344), both directions: `⟸` is `mem_relInt_of_lt_JN74`, `⟹` is the rim lemma. -/
theorem mem_relInt_iff_JN74
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
    x ∈ Subtype.val '' interior (Subtype.val ⁻¹' (C.toGaf02ChainE.cutEdgeSet_R74 K₃.carrier) :
      Set (C.toGaf02ChainE.cutM2_R74 K₃.carrier)) ↔
      x ∈ C.toGaf02ChainE.cutEdgeSet_R74 K₃.carrier ∧ C.edgeHeightGlobal_EFE x < 4 * Δ := by
  constructor
  · intro hx
    obtain ⟨-, O, hO, hxO, hOA⟩ := (mem_image_interior_preimage_val_iff).mp hx
    have hxE : x ∈ C.toGaf02ChainE.cutEdgeSet_R74 K₃.carrier :=
      hOA ⟨hxO, ((mem_image_interior_preimage_val_iff).mp hx).1⟩
    refine ⟨hxE, lt_of_le_of_ne (C.cutEdgeSet_height_le_JN74 hΔ2 K₃ hxE).1 fun heq => ?_⟩
    exact C.edge_rim_not_relInt_JN74 A hεr hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg
      hdD hxE heq hx
  · rintro ⟨hxE, hlt⟩
    exact C.mem_relInt_of_lt_JN74 hΔ2 K₃ hxE hlt

/-- **`M₃` is saturated by the fibres of `q₀`** (the content of O-CL1's `hsat` on the chain,
EDP06 (3)): a point `y` with the same `q₀`-image as a point `x ∈ M₃ ∩ X₁` lies in `M₃`. Route:
`M₂ ∩ X₁` is saturated (`edp06_saturation_EFE`), `E` is constant on the fibre, hence so are `T`,
`q₁` and the membership in `M^edge` / the region `X₂`, so by `mem_relInt_iff_JN74` the relative
interior of `M^edge` is fibre-saturated. -/
theorem cutM3_saturated_JN74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
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
    {x y : X} (hx : x ∈ C.toGaf02ChainE.cutM3_R74 K₃.carrier) (hxX : x ∈ C.circleDomain_EFE)
    (hxy : C.toGaf02ChainE.cutQ_R74 0 y = C.toGaf02ChainE.cutQ_R74 0 x) :
    y ∈ C.toGaf02ChainE.cutM3_R74 K₃.carrier := by
  have hπ0 : ∀ w, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection w = w :=
    gafStageQ_zero_starProjection_BAS P.toLocalChartPackets
  have hE : C.toChain.E y = C.toChain.E x := by
    have h : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E y) =
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E x) := hxy
    rwa [hπ0, hπ0] at h
  have hyX : y ∈ C.circleDomain_EFE := by
    obtain ⟨h1, h2⟩ := C.circleDomain_mem_EFE hxX
    refine C.mem_circleDomain_of_EFE ?_ ?_
    · rw [hE]
      exact h1
    · rw [hE]
      exact h2
  have hyM2 : y ∈ edgeM2_EFE C K₃ :=
    C.edp06_saturation_EFE hβ hd hεr K₃ D₃ hD hKs hKF hDreg hdD ⟨x, hxX⟩ ⟨y, hyX⟩
      (Subtype.ext (Subtype.ext hxy)) hx.1
  refine ⟨hyM2, fun hyr => hx.2 ?_⟩
  obtain ⟨hyE, hyT⟩ := (mem_relInt_iff_JN74 (C := C) A hεr hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 hD hKs
    hKF hDreg hdD).mp hyr
  have hxE : x ∈ C.toGaf02ChainE.cutEdgeSet_R74 K₃.carrier :=
    ⟨hx.1, (mem_edgeRegion_congr_JN74 (C := C) hE.symm).mpr hyE.2⟩
  have hxT : C.edgeHeightGlobal_EFE x < 4 * Δ := by
    have h2 : C.edgeHeightGlobal_EFE x = C.edgeHeightGlobal_EFE y :=
      (C.toChain.edgeRim_data_eq_of_E_eq_EFE hE.symm).2
    rw [h2]
    exact hyT
  exact C.mem_relInt_of_lt_JN74 hΔ2 K₃ hxE hxT

end RimRelInt

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
