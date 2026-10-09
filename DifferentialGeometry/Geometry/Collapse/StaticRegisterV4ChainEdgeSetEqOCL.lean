import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdgeFactsAtOCL
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeCompactDomainEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimPieceFaces

/-!
# Draft 74 CL0, G6a: the regularity of `D₃` of `D_R` and FDC02's set equality at `D_R`

Lane O-CL1 (`_OCL`), group G6a. On the produced cut choice `D_R = S.goodCut_OCL B hT hεr`:

* **`goodCut_D₃_reg_OCL`** (`D₃ ⊆ closure (relint D₃)`) and **`goodCut_D₃_bdry_OCL`**
  (`D₃ \ relint D₃ = (∂K₃ ∩ int C₃) ∪ (int K₃ ∩ F₃)`): the two regularity inputs of lane
  S-EDP-FDC3's E1 lemmas, which the chosen `K₃, D₃` of `D_R` (a `Classical.choose` of
  `zsp0405_row_ZSP35`) do not carry as conjuncts. `reg` from the slim piece
  (`f₃(int M^slim) ⊆ relint D₃` because `∂M^slim = f₃⁻¹(∂D₃)`, and `M^slim = cl int M^slim`);
  `bdry` by set algebra from `∂C₃ = F₃` (`zsp03_slim_boundary_eq_ZSP35`) and the `K₃` contract;
* **`goodCut_edge_saturated_OCL`**: the WHOLE low part `{q₁ = q₁ x', A/s ≤ 4Δ}` of the fibre
  through a point `x'` of `M^edge` lies in `M₂` (EDP04's whole disk is connected; if it meets
  `∂M₂` it lies in `M₂` by S-EDP-FDC3's `edgeDisk_face_saturated_EFE`);
* **`goodCut_edgeSet_eq_OCL`**: FDC02's set equality at `D_R`,
  `M^edge = U₂ ∩ (q₁⁻¹(C₂) ∩ {A/s ≤ 4Δ})` — the `edgeSet_eq` field of the edge exit.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

/-- The closed disk is preconnected. -/
theorem closedCell_two_preconnectedSpace_OCL : PreconnectedSpace (ClosedCell 2) := by
  have hconv : Convex ℝ ({x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1} : Set _) := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 : ℝ))
  exact Subtype.preconnectedSpace hconv.isPreconnected

/-- Relative interiors in a subtype commute with intersections. -/
theorem relInt_inter_OCL {Y : Type*} [TopologicalSpace Y] {Bs : Set Y} (K C : Set Y) :
    Subtype.val '' interior (Subtype.val ⁻¹' (K ∩ C) : Set Bs) =
      Subtype.val '' interior (Subtype.val ⁻¹' K : Set Bs) ∩
        Subtype.val '' interior (Subtype.val ⁻¹' C : Set Bs) := by
  rw [preimage_inter, interior_inter, image_inter Subtype.val_injective]

/-- A relative interior lies in the set. -/
theorem relInt_subset_OCL {Y : Type*} [TopologicalSpace Y] {Bs : Set Y} (K : Set Y) :
    Subtype.val '' interior (Subtype.val ⁻¹' K : Set Bs) ⊆ K := by
  rintro _ ⟨b, hb, rfl⟩
  exact interior_subset (s := Subtype.val ⁻¹' K) hb

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- The slim stage map `f₃` is continuous on `X`. -/
theorem continuous_slimMap_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    Continuous S.chain.slimMap_ZSP35 :=
  (gafStageQ S.F.family.toLocalChartPacketsC14.toLocalChartFamily
    S.F.family.toLocalChartPacketsC14.zero 2).starProjection.continuous.comp
    S.chain.toChain.stage_smooth.2.2.continuous

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2)

/-- **`D₃` of `D_R` is regular**: `D₃ ⊆ closure (relint D₃)` (from the slim piece). -/
theorem goodCut_D₃_reg_OCL :
    (S.goodCut_OCL B hT hεr).D₃.carrier ⊆ closure (Subtype.val '' interior
      (Subtype.val ⁻¹' (S.goodCut_OCL B hT hεr).D₃.carrier : Set S.chain.slimBs_ZSP35)) := by
  have h := (S.chain.zsp0405_row_ZSP35 hεr).choose_spec.choose_spec
  have hSD := h.2.2.2.1
  have hcl := h.2.2.2.2.2.2.1
  have himg := h.2.2.2.2.2.2.2.1
  have hfr := h.2.2.2.2.2.2.2.2.2.2.1
  change (S.chain.slimD₃_OCL hεr).carrier ⊆ closure (Subtype.val '' interior
    (Subtype.val ⁻¹' (S.chain.slimD₃_OCL hεr).carrier : Set S.chain.slimBs_ZSP35))
  intro y hy
  change y ∈ (S.chain.zsp0405_row_ZSP35 hεr).choose_spec.choose.carrier at hy
  rw [← himg] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  rw [← hcl] at hp
  refine closure_mono ?_ (image_closure_subset_closure_image S.continuous_slimMap_OCL
    (mem_image_of_mem _ hp))
  rintro _ ⟨q, hq, rfl⟩
  have hqS := interior_subset hq
  rw [hSD] at hqS
  by_contra hn
  have hqf : q ∈ frontier (S.chain.slimPiece_ZSP35
      (S.chain.zsp0405_row_ZSP35 hεr).choose.carrier) := by
    rw [hfr]
    exact ⟨hqS, hn⟩
  exact disjoint_left.mp disjoint_interior_frontier hq hqf

/-- **The relative boundary of `D₃` of `D_R`**:
`D₃ \ relint D₃ = (∂K₃ ∩ int C₃) ∪ (int K₃ ∩ F₃)`. -/
theorem goodCut_D₃_bdry_OCL :
    (S.goodCut_OCL B hT hεr).D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' (S.goodCut_OCL B hT hεr).D₃.carrier : Set S.chain.slimBs_ZSP35) =
      (((S.goodCut_OCL B hT hεr).K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' (S.goodCut_OCL B hT hεr).K₃.carrier : Set S.chain.slimBs_ZSP35)) ∩
          Subtype.val '' interior
            (Subtype.val ⁻¹' S.chain.slimC3_ZSP35 : Set S.chain.slimBs_ZSP35)) ∪
        (Subtype.val '' interior
            (Subtype.val ⁻¹' (S.goodCut_OCL B hT hεr).K₃.carrier : Set S.chain.slimBs_ZSP35) ∩
          S.chain.slimFacePoints_ZSP35) := by
  obtain ⟨hFC, hbd⟩ := S.chain.zsp03_slim_boundary_eq_ZSP35 hεr
  have hKs := (S.goodCut_OCL B hT hεr).K₃_req
  rw [(S.goodCut_OCL B hT hεr).D₃_eq, relInt_inter_OCL]
  ext y
  constructor
  · rintro ⟨⟨hyK, hyC⟩, hn⟩
    by_cases hyiC : y ∈ Subtype.val '' interior
        (Subtype.val ⁻¹' S.chain.slimC3_ZSP35 : Set S.chain.slimBs_ZSP35)
    · exact Or.inl ⟨⟨hyK, fun hyiK => hn ⟨hyiK, hyiC⟩⟩, hyiC⟩
    · have hyF : y ∈ S.chain.slimFacePoints_ZSP35 := by
        rw [← hbd]
        exact ⟨hyC, hyiC⟩
      exact Or.inr ⟨hKs (Or.inr hyF), hyF⟩
  · rintro (⟨⟨hyK, hyniK⟩, hyiC⟩ | ⟨hyiK, hyF⟩)
    · exact ⟨⟨hyK, relInt_subset_OCL _ hyiC⟩, fun h => hyniK h.1⟩
    · refine ⟨⟨relInt_subset_OCL _ hyiK, hFC hyF⟩, fun h => ?_⟩
      rw [← hbd] at hyF
      exact hyF.2 h.2

/-- **The whole low part of the fibre through a point of `M^edge` lies in `M₂`** (EDP04's whole
disk is connected; S-EDP-FDC3's E1 face saturation `edgeDisk_face_saturated_EFE`). -/
theorem goodCut_edge_saturated_OCL (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    {x x' : M.X} (hx' : x' ∈ (S.goodCut_OCL B hT hεr).edgeSet)
    (hq : S.chain.toGaf02ChainE.cutQ_R74 1 x = S.chain.toGaf02ChainE.cutQ_R74 1 x')
    (hh : S.toE_RGC.toRowsSource_RGC.height x ≤ R.edgeLevel_R74) :
    x ∈ (S.goodCut_OCL B hT hεr).M₂ := by
  have hreg := S.chain.toGaf02ChainE.edgeRegion_eq_sublevel_R74
  have hx'2 := hx'.2
  rw [hreg] at hx'2
  obtain ⟨⟨hW, hrat⟩, hh'⟩ := hx'2
  have hw : S.chain.toGaf02ChainE.cutQ_R74 1 x' ∈ (S.goodCut_OCL B hT hεr).edgeBaseOpen :=
    (S.goodCut_OCL B hT hεr).edgeBaseOpen_sub ⟨x', hx', rfl⟩
  obtain ⟨φ, hφ, hr, -⟩ := S.goodCut_edge_disk_OCL B hT hNb hcw hεr hw
  have hh'' : S.toE_RGC.toRowsSource_RGC.height x' ≤ R.edgeLevel_R74 := by
    rw [S.height_eq_OCL]
    exact hh'
  have hxs : x ∈ range φ := by
    rw [hr]
    exact ⟨hq, hh⟩
  have hx's : x' ∈ range φ := by
    rw [hr]
    exact ⟨rfl, hh''⟩
  let cc : S.chain.toGaf02ChainE.edgeBaseOpens_EFE := ⟨⟨_, hW⟩, hrat⟩
  have hsub : range φ ⊆ Subtype.val '' {y : S.chain.toGaf02ChainE.edgeSource_EFE |
      S.chain.toGaf02ChainE.edgeProj_EFE y = cc ∧
        S.chain.toGaf02ChainE.edgeHeight_EFE y ≤ 4 * R.later.excl.Δ} := by
    rw [S.chain.toGaf02ChainE.edgeDisk_eq_EFE R.two_le_Δ_EDP23 cc, hr]
    intro y hy
    have h2 := hy.2
    rw [S.height_eq_OCL] at h2
    exact ⟨hy.1, h2⟩
  obtain ⟨hD, hKs, hKF, -⟩ := S.chain.slimDomains_spec_OCL hεr
  have hsat := S.chain.edgeDisk_face_saturated_EFE hεr R.two_le_Δ_EDP23
    (S.chain.slimK₃_OCL hεr) (S.chain.slimD₃_OCL hεr) hD hKs hKF
    (S.goodCut_D₃_reg_OCL B hT hεr) (S.goodCut_D₃_bdry_OCL B hT hεr) cc
  by_cases hfr : (range φ ∩ frontier (S.goodCut_OCL B hT hεr).M₂).Nonempty
  · obtain ⟨z, hz, hzf⟩ := hfr
    exact hsat ⟨z, hsub hz, hzf⟩ (hsub hxs)
  · by_contra hn
    obtain ⟨a, ha⟩ := hx's
    obtain ⟨b, hb⟩ := hxs
    have := closedCell_two_preconnectedSpace_OCL
    have hne : (frontier (φ ⁻¹' (S.goodCut_OCL B hT hεr).M₂)).Nonempty := by
      refine nonempty_frontier_iff.mpr ⟨⟨a, ?_⟩, fun h => hn ?_⟩
      · rw [mem_preimage, ha]
        exact hx'.1
      · have hbm : b ∈ φ ⁻¹' (S.goodCut_OCL B hT hεr).M₂ := by
          rw [h]
          exact mem_univ b
        rw [← hb]
        exact hbm
    obtain ⟨z, hz⟩ := hne
    exact hfr ⟨φ z, mem_range_self z, hφ.isEmbedding.continuous.frontier_preimage_subset _ hz⟩

/-- **FDC02's set equality at `D_R`** (the `edgeSet_eq` field of the edge exit):
`M^edge = U₂ ∩ (q₁⁻¹(C₂) ∩ {A/s ≤ 4Δ})`. -/
theorem goodCut_edgeSet_eq_OCL (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) :
    (S.goodCut_OCL B hT hεr).edgeSet =
      gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1 ∩
        (S.chain.toGaf02ChainE.cutQ_R74 1 ⁻¹' (S.goodCut_OCL B hT hεr).C₂ ∩
          {p | S.toE_RGC.toRowsSource_RGC.height p ≤ R.edgeLevel_R74}) := by
  have hreg := S.chain.toGaf02ChainE.edgeRegion_eq_sublevel_R74
  ext x
  constructor
  · intro hx
    have hx2 := hx.2
    rw [hreg] at hx2
    have hC : S.chain.toGaf02ChainE.cutQ_R74 1 x ∈ (S.goodCut_OCL B hT hεr).C₂ := ⟨x, hx, rfl⟩
    have hh : S.toE_RGC.toRowsSource_RGC.height x ≤ R.edgeLevel_R74 := by
      rw [S.height_eq_OCL]
      exact hx2.2
    exact ⟨S.goodCut_edge_local_OCL B hT hεr ((S.goodCut_OCL B hT hεr).edgeBaseOpen_sub hC) hh,
      hC, hh⟩
  · rintro ⟨-, ⟨x', hx', hq⟩, hh⟩
    refine ⟨S.goodCut_edge_saturated_OCL B hT hεr hNb hcw hx' hq.symm hh, ?_⟩
    have hx'2 := hx'.2
    rw [hreg] at hx'2 ⊢
    have h2 : S.toE_RGC.toRowsSource_RGC.height x ≤ R.edgeLevel_R74 := hh
    rw [S.height_eq_OCL] at h2
    refine ⟨?_, h2⟩
    rw [mem_preimage, ← hq]
    exact hx'2.1

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
