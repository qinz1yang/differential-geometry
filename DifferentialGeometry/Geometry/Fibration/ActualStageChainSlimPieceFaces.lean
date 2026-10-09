import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimPiece

/-!
# ZSP03 `∂C₃ = F₃` and ZSP04's face equalities (SF), point-set form

Lane C14-ZSP35d. Blueprint `master207B.tex`, ZSP03 (B:6494–6495: "`∂C₃` is a finite set of base
points, one for each such zero boundary") and ZSP04 (SF) (B:6544–6553), with relative interiors
and frontiers in the closed slim base `Bs` (G10) and topological frontiers in `M`.

* `Gaf02ChainEJA.zsp03_slim_boundary_eq_ZSP35`: `C₃ ∖ relint C₃ = F₃` (every face point is a
  boundary point: on the negative side of the descended `b_k` the whole fibres lie in `int Z`).
* `relInterior_inter_ZSP35` (generic): `relint (A ∩ B) = relint A ∩ relint B`.
* `Gaf02ChainEJA.zsp04_SF_ZSP35` (for every compact `K ⊆ Bs` whose relative frontier avoids
  `F₃`, in particular ZSP04's `K₃`): with `D = K ∩ C₃` and `M^slim = f⁻¹(D)`:
  `∂D = (∂K ∩ int C₃) ⊔ (int K ∩ ∂C₃)`, `∂M^slim = f⁻¹(∂D)`, `M^slim ∩ ∂Z = f⁻¹(K ∩ ∂C₃)`.

Consumer: `zsp04_SF_C14Z_ZSP35` (for the `K₃` of `zsp04_row_ZSP35`).
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

/-- **Relative interiors commute with intersections** (generic). -/
theorem relInterior_inter_ZSP35 {Y : Type*} [TopologicalSpace Y] {Bs A B : Set Y} :
    Subtype.val '' interior (Subtype.val ⁻¹' (A ∩ B) : Set Bs) =
      Subtype.val '' interior (Subtype.val ⁻¹' A : Set Bs) ∩
        Subtype.val '' interior (Subtype.val ⁻¹' B : Set Bs) := by
  ext x
  simp only [DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff, mem_inter_iff]
  constructor
  · rintro ⟨hx, O, hO, hxO, hOAB⟩
    exact ⟨⟨hx, O, hO, hxO, fun y hy => (hOAB hy).1⟩, ⟨hx, O, hO, hxO, fun y hy => (hOAB hy).2⟩⟩
  · rintro ⟨⟨hx, O, hO, hxO, hOA⟩, ⟨-, O', hO', hxO', hOB⟩⟩
    exact ⟨hx, O ∩ O', hO.inter hO', ⟨hxO, hxO'⟩,
      fun y hy => ⟨hOA ⟨hy.1.1, hy.2⟩, hOB ⟨hy.1.2, hy.2⟩⟩⟩

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **ZSP03, `j = 3`: `∂C₃` is exactly the finite face set** (B:6494–6495): `F₃ ⊆ C₃` and
`C₃ ∖ relint_{Bs} C₃ = F₃`. -/
theorem zsp03_slim_boundary_eq_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    C.slimFacePoints_ZSP35 ⊆ C.slimC3_ZSP35 ∧
      C.slimC3_ZSP35 \
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) =
        C.slimFacePoints_ZSP35 := by
  obtain ⟨hsatEq, -, -, -, hfront⟩ := C.zsp03_slim_saturated_ZSP35 hεr
  have hclk : ∀ k : P.zero.finite_centres.toFinset,
      IsClosed (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := fun k =>
    (C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).1.isClosed
  obtain ⟨hfrk, -⟩ := frontier_disjoint_iUnion_ZSP35
    (fun k : P.zero.finite_centres.toFinset => zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)
    hclk (fun k k' hkk => C.toGaf02ChainE.zsp02_disjoint_ZSP35 hεr hkk)
  have hFC : C.slimFacePoints_ZSP35 ⊆ C.slimC3_ZSP35 := by
    intro w hw
    obtain ⟨k, q, ⟨hqF, hqU⟩, rfl⟩ := mem_iUnion.mp hw
    exact ⟨q, ⟨hfrk k hqF, hqU⟩, rfl⟩
  refine ⟨hFC, Subset.antisymm hfront fun w hw => ⟨hFC hw, fun hwi => ?_⟩⟩
  obtain ⟨k, q, ⟨hqF, hqU⟩, rfl⟩ := mem_iUnion.mp hw
  have hfr := (C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).2.2.1
  have hqF' : q ∈ zspFace_ZSP35 P.toLocalChartFamily P.zero k C.E := hfr ▸ hqF
  obtain ⟨i, hY, hloc, hh, hne, h0⟩ := C.slim_face_chart_ZSP35 hεr k hqF' hqU
  obtain ⟨-, -, -, -, -, -, O, hO, hFO, hOprop, -⟩ := C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k
  obtain ⟨-, Or, hOr, hwOr, hOrC⟩ :=
    DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mp hwi
  -- the defining neighbourhood of the face
  have hfib : C.slimMap_ZSP35 ⁻¹' {C.slimMap_ZSP35 q} ⊆ O := by
    rw [C.zsp03_slim_face_fibre_ZSP35 hεr k hqF hqU, hfr]
    exact hFO
  have hGc : IsClosed (C.slimMap_ZSP35 '' Oᶜ) :=
    (hO.isClosed_compl.isCompact.image C.continuous_slimMap_ZSP35).isClosed
  have hqG : C.slimMap_ZSP35 q ∉ C.slimMap_ZSP35 '' Oᶜ := by
    rintro ⟨y, hy, hyq⟩
    exact hy (hfib hyq)
  have hdom : C.toChain.gaf07SlimCoord_GAFC i q ∈ C.slimAtlas_ZSP35.dom i := by
    refine ⟨(hloc q hY).1, ?_⟩
    change C.slimParam_ZSP35 i (C.toChain.gaf07SlimCoord_GAFC i q) ∈
      gaf07SlimRatio_G47 P.toLocalChartPacketsC14D.toLocalChartPacketsC14.toLocalChartPackets
    rw [(hloc q hY).2]
    exact hqU.2
  have hψc : ContinuousAt (C.slimParam_ZSP35 i) (C.toChain.gaf07SlimCoord_GAFC i q) :=
    (C.slimAtlas_ZSP35.continuousOn_param_BCF i).continuousAt
      ((C.slimAtlas_ZSP35.isOpen_dom i).mem_nhds hdom)
  have hT : C.slimAtlas_ZSP35.dom i ∩ C.slimParam_ZSP35 i ⁻¹' (Or ∩ (C.slimMap_ZSP35 '' Oᶜ)ᶜ) ∈
      𝓝 (C.toChain.gaf07SlimCoord_GAFC i q) := by
    refine Filter.inter_mem ((C.slimAtlas_ZSP35.isOpen_dom i).mem_nhds hdom)
      (hψc.preimage_mem_nhds ?_)
    rw [(hloc q hY).2]
    exact (hOr.inter hGc.isOpen_compl).mem_nhds ⟨hwOr, hqG⟩
  -- the negative side of the simple zero
  have hneg : ∃ t ∈ C.slimAtlas_ZSP35.dom i ∩
      C.slimParam_ZSP35 i ⁻¹' (Or ∩ (C.slimMap_ZSP35 '' Oᶜ)ᶜ),
      zspBaseFun_ZSP35 P.toLocalChartPacketsC14D.toLocalChartPacketsC14 k
        (C.slimParam_ZSP35 i t) < 0 := by
    have hh' : DifferentiableAt ℝ (fun t => -zspBaseFun_ZSP35
        P.toLocalChartPacketsC14D.toLocalChartPacketsC14 k (C.slimParam_ZSP35 i t))
        (C.toChain.gaf07SlimCoord_GAFC i q) := hh.neg
    have hne' : deriv (fun t => -zspBaseFun_ZSP35
        P.toLocalChartPacketsC14D.toLocalChartPacketsC14 k (C.slimParam_ZSP35 i t))
        (C.toChain.gaf07SlimCoord_GAFC i q) ≠ 0 := by
      rw [deriv.fun_neg]
      exact neg_ne_zero.mpr hne
    obtain ⟨t, ht, hpos⟩ := exists_pos_near_ZSP35 hh' hne' (by simp only [h0, neg_zero]) hT
    exact ⟨t, ht, by linarith⟩
  obtain ⟨t, ⟨htd, htO, htG⟩, htneg⟩ := hneg
  have htB : C.slimParam_ZSP35 i t ∈ C.slimBs_ZSP35 := C.slimAtlas_ZSP35.param_mem_BCF htd
  obtain ⟨y, ⟨hyM, hyU⟩, hyt⟩ := hOrC ⟨htO, htB⟩
  have hyO : y ∈ O := by
    by_contra hyO
    exact htG ⟨y, hyO, hyt⟩
  -- `y` lies in the open set `{r_k < 0} ∩ O ⊆ Z_k`
  have hrc : ContinuousOn (fun z => ((C.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
      (C.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) O := fun z hz =>
    ((hOprop z hz).2.1.continuousAt).continuousWithinAt
  have hry : ((C.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
      (C.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 < 0 := by
    rw [← C.baseFun_slimMap_ZSP35 k y, hyt]
    exact htneg
  have hopen := hrc.isOpen_inter_preimage hO (isOpen_Iio (a := (0 : ℝ)))
  have hyint : y ∈ interior (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := by
    rw [mem_interior]
    exact ⟨_, fun z hz => ((hOprop z hz.1).2.2).mpr (le_of_lt hz.2), hopen, hyO, hry⟩
  exact hyM (interior_mono (subset_iUnion (fun k : P.zero.finite_centres.toFinset =>
    zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) k) hyint)

/-- **ZSP04 (SF), point-set form** (B:6544–6553): for a compact `Kb ⊆ Bs` whose relative frontier
avoids the face set `F₃` (ZSP04's `K₃`), `D = Kb ∩ C₃` and `M^slim = f⁻¹(D)`:
`∂D = (∂Kb ∩ int C₃) ⊔ (int Kb ∩ ∂C₃)` (relative to `Bs`; no isolated endpoint or double boundary
constraint), `∂M^slim = f⁻¹(∂D)`, and `M^slim ∩ ∂Z = f⁻¹(Kb ∩ ∂C₃)`. -/
theorem zsp04_SF_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) {Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))}
    (hKc : IsCompact Kb) (hKB : Kb ⊆ C.slimBs_ZSP35)
    (hKF : Disjoint (Kb \ Subtype.val '' interior (Subtype.val ⁻¹' Kb : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35) :
    (Kb ∩ C.slimC3_ZSP35) \ Subtype.val '' interior
        (Subtype.val ⁻¹' (Kb ∩ C.slimC3_ZSP35) : Set C.slimBs_ZSP35) =
      ((Kb \ Subtype.val '' interior (Subtype.val ⁻¹' Kb : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' Kb : Set C.slimBs_ZSP35) ∩
          (C.slimC3_ZSP35 \
            Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35))) ∧
    Disjoint ((Kb \ Subtype.val '' interior (Subtype.val ⁻¹' Kb : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35))
      (Subtype.val '' interior (Subtype.val ⁻¹' Kb : Set C.slimBs_ZSP35) ∩
          (C.slimC3_ZSP35 \
            Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35))) ∧
    frontier (C.slimPiece_ZSP35 Kb) = C.slimMap_ZSP35 ⁻¹' ((Kb ∩ C.slimC3_ZSP35) \
      Subtype.val '' interior (Subtype.val ⁻¹' (Kb ∩ C.slimC3_ZSP35) : Set C.slimBs_ZSP35)) ∧
    C.slimPiece_ZSP35 Kb ∩ frontier C.zeroUnion_ZSP35 = C.slimMap_ZSP35 ⁻¹' (Kb ∩
      (C.slimC3_ZSP35 \
        Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35))) := by
  obtain ⟨hsatEq, hC3B, -, -, -⟩ := C.zsp03_slim_saturated_ZSP35 hεr
  obtain ⟨hFC, hbd⟩ := C.zsp03_slim_boundary_eq_ZSP35 hεr
  have hfc := C.continuous_slimMap_ZSP35
  have hUo := C.isOpen_slimSource_ZSP35
  have hclk : ∀ k : P.zero.finite_centres.toFinset,
      IsClosed (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := fun k =>
    (C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).1.isClosed
  obtain ⟨-, hfrU⟩ := frontier_disjoint_iUnion_ZSP35
    (fun k : P.zero.finite_centres.toFinset => zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)
    hclk (fun k k' hkk => C.toGaf02ChainE.zsp02_disjoint_ZSP35 hεr hkk)
  set rK := Subtype.val '' interior (Subtype.val ⁻¹' Kb : Set C.slimBs_ZSP35) with hrK
  set rC := Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) with hrC
  have hrKK : rK ⊆ Kb := fun x hx => by
    obtain ⟨hxB, O, -, hxO, hOK⟩ :=
      DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mp hx
    exact hOK ⟨hxO, hxB⟩
  have hrCC : rC ⊆ C.slimC3_ZSP35 := fun x hx => by
    obtain ⟨hxB, O, -, hxO, hOK⟩ :=
      DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mp hx
    exact hOK ⟨hxO, hxB⟩
  have hint : Subtype.val '' interior
      (Subtype.val ⁻¹' (Kb ∩ C.slimC3_ZSP35) : Set C.slimBs_ZSP35) = rK ∩ rC :=
    relInterior_inter_ZSP35
  -- (1) the boundary of `D`
  have h1 : (Kb ∩ C.slimC3_ZSP35) \ Subtype.val '' interior
      (Subtype.val ⁻¹' (Kb ∩ C.slimC3_ZSP35) : Set C.slimBs_ZSP35) =
      ((Kb \ rK) ∩ rC) ∪ (rK ∩ (C.slimC3_ZSP35 \ rC)) := by
    rw [hint]
    ext x
    constructor
    · rintro ⟨⟨hxK, hxC⟩, hxn⟩
      by_cases hxr : x ∈ rK
      · exact Or.inr ⟨hxr, hxC, fun h => hxn ⟨hxr, h⟩⟩
      · refine Or.inl ⟨⟨hxK, hxr⟩, ?_⟩
        by_contra hxc
        exact Set.disjoint_left.mp hKF ⟨hxK, hxr⟩ (hbd ▸ ⟨hxC, hxc⟩ : x ∈ C.slimFacePoints_ZSP35)
    · rintro (⟨⟨hxK, hxr⟩, hxc⟩ | ⟨hxr, hxC, hxc⟩)
      · exact ⟨⟨hxK, hrCC hxc⟩, fun h => hxr h.1⟩
      · exact ⟨⟨hrKK hxr, hxC⟩, fun h => hxc h.2⟩
  have h2 : Disjoint ((Kb \ rK) ∩ rC) (rK ∩ (C.slimC3_ZSP35 \ rC)) :=
    Set.disjoint_left.mpr fun x hx hx' => hx.1.2 hx'.1
  -- (3) the frontier of the piece
  have hSeq : C.slimPiece_ZSP35 Kb = (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' Kb := by
    ext y
    constructor
    · rintro ⟨hyK, hyC⟩
      have hy : y ∈ C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35 ∩ C.slimMap_ZSP35 ⁻¹' C.slimC3_ZSP35 :=
        ⟨hC3B hyC, hyC⟩
      rw [← hsatEq] at hy
      exact ⟨hy.1, hyK⟩
    · rintro ⟨hyM, hyK⟩
      have hy : y ∈ (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35 :=
        ⟨hyM, hKB hyK⟩
      rw [hsatEq] at hy
      exact ⟨hyK, hy.2⟩
  have hScl : IsClosed (C.slimPiece_ZSP35 Kb) := by
    rw [hSeq]
    exact isOpen_interior.isClosed_compl.inter (hKc.isClosed.preimage hfc)
  have hintS : interior (C.slimPiece_ZSP35 Kb) =
      C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35 ∩ C.slimMap_ZSP35 ⁻¹' (rK ∩ rC) := by
    ext z
    constructor
    · intro hz
      obtain ⟨O, hO, hOB⟩ := C.slim_relOpen_ZSP35 (W := interior (C.slimPiece_ZSP35 Kb))
        (fun y hy => hC3B (interior_subset hy).2) isOpen_interior
      have hzU : C.slimMap_ZSP35 z ∈ C.slimBs_ZSP35 := hC3B (interior_subset hz).2
      have hzO : C.slimMap_ZSP35 z ∈ O ∩ C.slimBs_ZSP35 := by
        rw [hOB]
        exact ⟨z, hz, rfl⟩
      refine ⟨hzU, ?_⟩
      rw [← hint]
      refine DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mpr
        ⟨hzU, O, hO, hzO.1, fun w hw => ?_⟩
      rw [hOB] at hw
      obtain ⟨y, hy, rfl⟩ := hw
      exact (interior_subset hy : y ∈ C.slimPiece_ZSP35 Kb)
    · rintro ⟨hzU, hzr⟩
      rw [← hint] at hzr
      obtain ⟨-, O, hO, hzO, hOD⟩ :=
        DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mp hzr
      rw [mem_interior]
      exact ⟨C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35 ∩ C.slimMap_ZSP35 ⁻¹' O,
        fun y hy => hOD ⟨hy.2, hy.1⟩, hUo.inter (hO.preimage hfc), hzU, hzO⟩
  have h3 : frontier (C.slimPiece_ZSP35 Kb) = C.slimMap_ZSP35 ⁻¹' ((Kb ∩ C.slimC3_ZSP35) \
      Subtype.val '' interior (Subtype.val ⁻¹' (Kb ∩ C.slimC3_ZSP35) : Set C.slimBs_ZSP35)) := by
    rw [hScl.frontier_eq, hintS, hint]
    ext z
    constructor
    · rintro ⟨hzS, hzn⟩
      exact ⟨hzS, fun h => hzn ⟨hC3B hzS.2, h⟩⟩
    · rintro ⟨hzS, hzn⟩
      exact ⟨hzS, fun h => hzn h.2⟩
  -- (4) the shared zero faces
  have h4 : C.slimPiece_ZSP35 Kb ∩ frontier C.zeroUnion_ZSP35 =
      C.slimMap_ZSP35 ⁻¹' (Kb ∩ (C.slimC3_ZSP35 \ rC)) := by
    rw [hbd]
    ext x
    constructor
    · rintro ⟨hxS, hxZ⟩
      rw [Gaf02ChainE.zeroUnion_ZSP35, hfrU] at hxZ
      obtain ⟨k, hk⟩ := mem_iUnion.mp hxZ
      exact ⟨hxS.1, mem_iUnion.mpr ⟨k, x, ⟨hk, hC3B hxS.2⟩, rfl⟩⟩
    · rintro ⟨hxK, hxF⟩
      obtain ⟨k, q, ⟨hqF, hqU⟩, hqx⟩ := mem_iUnion.mp hxF
      have hfib := C.zsp03_slim_face_fibre_ZSP35 hεr k hqF hqU
      have hxk : x ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := by
        rw [← hfib]
        exact hqx.symm
      refine ⟨⟨hxK, hFC hxF⟩, ?_⟩
      rw [Gaf02ChainE.zeroUnion_ZSP35, hfrU]
      exact mem_iUnion.mpr ⟨k, hxk⟩
  exact ⟨h1, h2, h3, h4⟩

/-- **Consumer: (SF) for ZSP04's `K₃`** (final family): for the compact smooth one-dimensional
`K₃` of `zsp04_row_ZSP35`, `∂D₃ = (∂K₃ ∩ int C₃) ⊔ (int K₃ ∩ ∂C₃)`, `∂M^slim = f⁻¹(∂D₃)` and
`M^slim ∩ ∂Z = f⁻¹(K₃ ∩ ∂C₃)`, with `∂C₃ = F₃` finite. -/
theorem zsp04_SF_C14Z_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    ∃ K₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      C.toChain.slimSlabImage_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
      C.slimC3_ZSP35 \
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) =
        C.slimFacePoints_ZSP35 ∧
      C.slimFacePoints_ZSP35.Finite ∧
      (K₃.carrier ∩ C.slimC3_ZSP35) \ Subtype.val '' interior
          (Subtype.val ⁻¹' (K₃.carrier ∩ C.slimC3_ZSP35) : Set C.slimBs_ZSP35) =
        ((K₃.carrier \
              Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
            Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
          (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
            C.slimFacePoints_ZSP35) ∧
      frontier (C.slimPiece_ZSP35 K₃.carrier) = C.slimMap_ZSP35 ⁻¹'
        ((K₃.carrier ∩ C.slimC3_ZSP35) \ Subtype.val '' interior
          (Subtype.val ⁻¹' (K₃.carrier ∩ C.slimC3_ZSP35) : Set C.slimBs_ZSP35)) ∧
      C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35 =
        C.slimMap_ZSP35 ⁻¹' (K₃.carrier ∩ C.slimFacePoints_ZSP35) := by
  obtain ⟨K₃, hKs, hKF, -⟩ := C.zsp04_row_ZSP35 hεr
  obtain ⟨-, hbd⟩ := C.zsp03_slim_boundary_eq_ZSP35 hεr
  obtain ⟨h1, -, h3, h4⟩ := C.zsp04_SF_ZSP35 hεr K₃.isCompact_carrier_BCF K₃.subset_base hKF
  rw [hbd] at h1 h4
  exact ⟨K₃, subset_union_left.trans hKs, hbd, (C.zsp03_slim_face_points_ZSP35 hεr).2, h1, h3,
    h4⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
