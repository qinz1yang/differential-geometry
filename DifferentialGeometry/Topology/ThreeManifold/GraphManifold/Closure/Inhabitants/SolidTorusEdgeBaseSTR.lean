import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusEdgeCellSTR
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialCircleRows
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialTorusCores
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageSlimOnly74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageGeometryH74

/-!
# S-SOLIDTORUS2 (suffix `_STR`), G2 part 4: the stage geometry and the edge facts

The actual stage geometry `A` (`stageGeometry_STR Z`, for every zero family `Z`: ball zero domains,
X135 cusp cores, empty slim stage, the edge stage of this file, the X135 circle stage), the cut
choice `D` (`edgeBaseOpen = circleBaseOpen = ⊤`, `C₂ = {0 ≤ t ≤ 1}`, `C₁` the planar region of the
circle base) and the cut-dependent edge facts `EdgeCutFacts74 A D` (EDP04 rank two, properness,
whole fibre disks, compact `C₂`, the face function of its endpoints).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_BaseSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_BaseSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

/-! ## Restricting the rank-two clause to an open base -/

theorem rank_two_restrict_STR {W : CompactCarrier.{0}} (E : EdgeStage74 W)
    (V : TopologicalSpace.Opens E.Base) (x : E.restrictParent V)
    (h : Surjective fun v : TangentSpace W.model (E.restrictIncl V x : W.Carrier) =>
      (mfderiv W.model (𝓡 1) E.proj (E.restrictIncl V x) v,
        mfderiv W.model 𝓘(ℝ, ℝ) E.height (E.restrictIncl V x) v)) :
    Surjective fun v : TangentSpace W.model (x : W.Carrier) =>
      (mfderiv W.model (𝓡 1) (E.restrictProj V) x v,
        mfderiv W.model 𝓘(ℝ, ℝ)
          (fun y : E.restrictParent V => E.height (E.restrictIncl V y)) x v) := by
  intro p
  obtain ⟨v, hv⟩ := h p
  refine ⟨v, ?_⟩
  have hid : mfderiv W.model W.model (E.restrictIncl V) x = ContinuousLinearMap.id ℝ _ :=
    DifferentialGeometry.mfderiv_opens_incl (E.restrictParent_le V) x
  have hinc : MDifferentiableAt W.model W.model (E.restrictIncl V) x :=
    ((contMDiff_inclusion (n := ∞) (E.restrictParent_le V)).mdifferentiableAt (by simp))
  have h1 := DifferentialGeometry.Topology.mfderiv_subtypeVal_comp (I := W.model) (J := 𝓡 1) V
    (E.restrictProj V) x
  have h1' : mfderiv W.model (𝓡 1) (Subtype.val ∘ E.restrictProj V) x =
      (mfderiv W.model (𝓡 1) E.proj (E.restrictIncl V x)).comp
        (mfderiv W.model W.model (E.restrictIncl V) x) :=
    mfderiv_comp x (E.proj_smooth.mdifferentiableAt (by simp)) hinc
  have h2 : mfderiv W.model 𝓘(ℝ, ℝ) (E.height ∘ E.restrictIncl V) x =
      (mfderiv W.model 𝓘(ℝ, ℝ) E.height (E.restrictIncl V x)).comp
        (mfderiv W.model W.model (E.restrictIncl V) x) :=
    mfderiv_comp x (E.height_smooth.mdifferentiableAt (by simp)) hinc
  rw [hid] at h1' h2
  refine Prod.ext ?_ ?_
  · have h3 := congrArg (fun L => L v) (h1.symm.trans h1')
    exact h3.trans (congrArg Prod.fst hv)
  · have h3 := congrArg (fun L => L v) h2
    exact h3.trans (congrArg Prod.snd hv)


/-! ## The edge base -/

/-- The identification `ℝ¹ ≃L ℝ`, `v ↦ v₀`. -/
def e1_STR : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun v => v 0
      invFun := fun t => EuclideanSpace.single (0 : Fin 1) t
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl
      left_inv := by
        intro v
        ext i
        fin_cases i
        simp
      right_inv := by
        intro t
        simp }

theorem e1_apply_STR (v : EuclideanSpace ℝ (Fin 1)) : e1_STR v = v 0 := rfl

/-- The whole edge base `⊤ ⊆ ℝ¹`, as a homeomorphism to `ℝ`. -/
def coordHomeo_STR : (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))) ≃ₜ ℝ :=
  (openDiffeomorphOfForall (I := 𝓡 1) (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1)))
    (fun _ => trivial)).toHomeomorph.trans e1_STR.toHomeomorph

theorem coordHomeo_apply_STR (c : (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1)))) :
    coordHomeo_STR c = c.val 0 := rfl

/-- The compact edge base `C₂ = {0 ≤ t ≤ 1}`. -/
def edgeC2_STR : Set (EuclideanSpace ℝ (Fin 1)) := {v | 0 ≤ v 0 ∧ v 0 ≤ 1}

theorem cbase_eq_STR :
    (Subtype.val ⁻¹' edgeC2_STR : Set (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1)))) =
      coordHomeo_STR ⁻¹' Icc (0 : ℝ) 1 := rfl

theorem cbase_compact_STR :
    IsCompact (Subtype.val ⁻¹' edgeC2_STR :
      Set (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1)))) := by
  rw [cbase_eq_STR]
  exact coordHomeo_STR.isCompact_preimage.mpr isCompact_Icc

theorem frontier_cbase_STR :
    frontier (Subtype.val ⁻¹' edgeC2_STR :
      Set (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1)))) =
      {c | c.val 0 = 0 ∨ c.val 0 = 1} := by
  rw [cbase_eq_STR, ← coordHomeo_STR.preimage_frontier, frontier_Icc zero_le_one]
  rfl


/-- The whole edge base as a type. -/
abbrev Base1_STR : Type := (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1)))

theorem hasFDerivAt_coord_STR (a b : ℝ) (v : EuclideanSpace ℝ (Fin 1)) :
    HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 1) => b + a * w 0)
      (a • (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)) v :=
  (((EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).hasFDerivAt).const_mul
    a).const_add b

theorem contMDiff_coord_STR (a b : ℝ) :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun c : Base1_STR => b + a * c.val 0) := by
  have h : ContDiff ℝ ∞ (fun w : EuclideanSpace ℝ (Fin 1) => b + a * w 0) :=
    contDiff_const.add (contDiff_const.mul (EuclideanSpace.proj (0 : Fin 1) :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).contDiff)
  exact h.contMDiff.comp contMDiff_subtype_val

theorem mfderiv_coord_ne_zero_STR {a : ℝ} (b : ℝ) (ha : a ≠ 0) (c : Base1_STR) :
    mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun c' : Base1_STR => b + a * c'.val 0) c ≠ 0 := by
  rw [DifferentialGeometry.mfderiv_restrict_open (I := 𝓡 1) (J := 𝓘(ℝ, ℝ))
    (fun w : EuclideanSpace ℝ (Fin 1) => b + a * w 0)
    (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))) c, mfderiv_eq_fderiv,
    (hasFDerivAt_coord_STR a b c.val).fderiv]
  intro h
  have h1 := congrArg (fun L => L (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) h
  have h2 : a * (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) (0 : Fin 1)) = 0 := h1
  have h3 : (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) (0 : Fin 1)) = 1 := by simp
  rw [h3, mul_one] at h2
  exact ha h2

/-- **FDC02 / EDP05: the face function at an endpoint of `C₂`**. -/
theorem cbase_domain_STR : ∀ c ∈ frontier (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR),
    ∃ U : TopologicalSpace.Opens Base1_STR, c ∈ U ∧
      ∃ φ : Base1_STR → ℝ, ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧
        mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧
        (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR) ∩ U = {c' | c' ∈ U ∧ 0 ≤ φ c'} := by
  intro c hc
  rw [frontier_cbase_STR] at hc
  rcases hc with h0 | h1
  · refine ⟨⟨{c' | c'.val 0 < 1 / 2}, isOpen_lt
      ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp continuous_subtype_val)
      continuous_const⟩, ?_, fun c' => 0 + 1 * c'.val 0, (contMDiff_coord_STR 1 0).contMDiffOn,
      ?_, mfderiv_coord_ne_zero_STR 0 one_ne_zero c, ?_⟩
    · change c.val 0 < 1 / 2
      rw [h0]
      norm_num
    · simp [h0]
    · ext c'
      constructor
      · rintro ⟨⟨ha, hb⟩, hU⟩
        exact ⟨hU, by linarith [ha]⟩
      · rintro ⟨hU, hφ⟩
        have hU' : c'.val 0 < 1 / 2 := hU
        exact ⟨⟨by linarith, by linarith⟩, hU⟩
  · refine ⟨⟨{c' | 1 / 2 < c'.val 0}, isOpen_lt continuous_const
      ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp continuous_subtype_val)⟩, ?_,
      fun c' => 1 + (-1) * c'.val 0, (contMDiff_coord_STR (-1) 1).contMDiffOn,
      ?_, mfderiv_coord_ne_zero_STR 1 (by norm_num) c, ?_⟩
    · change 1 / 2 < c.val 0
      rw [h1]
      norm_num
    · simp [h1]
    · ext c'
      constructor
      · rintro ⟨⟨ha, hb⟩, hU⟩
        have hU' : 1 / 2 < c'.val 0 := hU
        exact ⟨hU, by linarith⟩
      · rintro ⟨hU, hφ⟩
        have hU' : 1 / 2 < c'.val 0 := hU
        exact ⟨⟨by linarith, by linarith⟩, hU⟩


/-! ## The stage geometry `A` and the cut choice `D` -/

/-- **The circle stage** of the instance: the X135 circle bundle (`z₁`-phase circles over
`1/2 < ‖z₂‖² < 1`), without its trivializations. -/
def circleStage_STR : StageProj74 Wc 2 where
  Base := X135Radial.radialCircleBundle.Base
  parent := X135Radial.radialCircleBundle.domain
  parent_interior := X135Radial.radialCircleBundle.domain_interior
  proj := X135Radial.radialCircleBundle.proj
  proj_smooth := X135Radial.radialCircleBundle.proj_smooth
  proj_submersion := X135Radial.radialCircleBundle.proj_submersion

/-- **`A`: the actual stage geometry** of the solid torus instance (any zero family `Z`). -/
def stageGeometry_STR (Z : ZeroDomains Wc) : SmoothStageGeometry74 Wc X135Radial.boundary where
  zero := Z
  cusp := X135Radial.radialCuspCores
  slim := SlimStage74.empty Wc
  edge := edgeStage_STR
  circle := circleStage_STR

/-- The complex coordinate `z₂` of a point of the circle base. -/
def qOfBase_STR (b : circleStage_STR.Base) : ℂ := modelPlaneComplex b.val.val

/-- The remaining circle base `C₁ = {5/8 ≤ |q|² ≤ 15/16, Re q ≤ κ}`. -/
def circleC1_STR : Set circleStage_STR.Base :=
  {b | 5 / 8 ≤ ‖qOfBase_STR b‖ ^ 2 ∧ ‖qOfBase_STR b‖ ^ 2 ≤ 15 / 16 ∧ (qOfBase_STR b).re ≤ 4 / 5}

theorem edgeC2_nonempty_STR : edgeC2_STR ≠ ∅ := by
  intro h
  have : EuclideanSpace.single (0 : Fin 1) (0 : ℝ) ∈ edgeC2_STR := by simp [edgeC2_STR]
  rw [h] at this
  exact this

theorem slimReq_STR : (SlimStage74.empty Wc).slabImage ∪ (SlimStage74.empty Wc).facePoints ⊆
    interior (∅ : Set (SlimStage74.empty Wc).Base) := by
  change (∅ : Set PEmpty.{1}) ∪ ∅ ⊆ interior ∅
  simp

/-- **`D`: the cut choice** (`K₃ = D₃ = ∅`, `C₂ = {0 ≤ t ≤ 1}`, `C₁` planar, both open bases
`⊤`). -/
def cutChoice_STR (Z : ZeroDomains Wc) : StageCutChoice74 (stageGeometry_STR Z) where
  K₃ := ∅
  D₃ := ∅
  C₂ := edgeC2_STR
  C₁ := circleC1_STR
  edgeBaseOpen := ⊤
  circleBaseOpen := ⊤
  K₃_compact := isCompact_empty
  D₃_compact := isCompact_empty
  D₃_eq := (empty_inter _).symm
  K₃_req := slimReq_STR
  K₃_faces := by
    change Disjoint (frontier (∅ : Set PEmpty.{1})) (∅ : Set PEmpty.{1})
    simp
  C₂_sub := fun _ _ => trivial
  C₁_sub := fun _ _ => trivial
  edgeBaseOpen_empty := fun h => absurd h edgeC2_nonempty_STR

/-! ## The edge facts over the good open base -/

theorem edgeFacts_proper_STR (Z : ZeroDomains Wc)
    (K : Set (cutChoice_STR Z).edgeBaseOpen) (hK : IsCompact K) :
    IsCompact (Subtype.val '' {x : (cutChoice_STR Z).edgeSource |
      (stageGeometry_STR Z).edge.restrictProj (cutChoice_STR Z).edgeBaseOpen x ∈ K ∧
        (cutChoice_STR Z).edgeHeight x ≤ (stageGeometry_STR Z).edge.level}) := by
  have hK' : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
  convert edgeProper_STR _ hK' using 1
  ext y
  constructor
  · rintro ⟨x, ⟨hk, hh⟩, rfl⟩
    exact ⟨(stageGeometry_STR Z).edge.restrictParent_le _ x.2, ⟨_, hk, rfl⟩, hh⟩
  · rintro ⟨hy, ⟨k, hk, hkv⟩, hh⟩
    refine ⟨⟨y, (stageGeometry_STR Z).edge.mem_restrictParent_of hy trivial⟩, ⟨?_, hh⟩, rfl⟩
    have : (stageGeometry_STR Z).edge.restrictProj (cutChoice_STR Z).edgeBaseOpen
        ⟨y, (stageGeometry_STR Z).edge.mem_restrictParent_of hy trivial⟩ = k :=
      Subtype.ext hkv.symm
    rw [this]
    exact hk


theorem edgeFacts_fibre_STR (Z : ZeroDomains Wc) (c : (cutChoice_STR Z).edgeBaseOpen) :
    ∃ φ : ClosedCell 2 → Wc.Carrier, IsSmoothEmbedding (𝓡∂ 2) Wc.model ∞ φ ∧
      range φ = Subtype.val '' {x : (cutChoice_STR Z).edgeSource |
        (stageGeometry_STR Z).edge.restrictProj (cutChoice_STR Z).edgeBaseOpen x = c ∧
          (cutChoice_STR Z).edgeHeight x ≤ (stageGeometry_STR Z).edge.level} := by
  let v : EuclideanSpace ℝ (Fin 1) := c.val
  refine ⟨fun w => edgeToW_STR (cellPt_STR w (v 0)), edgeSlice_embedding_STR (v 0), ?_⟩
  rw [range_edgeSlice_STR]
  ext y
  constructor
  · rintro ⟨hy, ht, h1⟩
    refine ⟨⟨y, (stageGeometry_STR Z).edge.mem_restrictParent_of hy trivial⟩, ⟨?_, h1⟩, rfl⟩
    apply Subtype.ext
    change edgeProj_STR ⟨y, hy⟩ = v
    rw [edgeProj_eq_single_STR hy, ht]
    ext i
    fin_cases i
    simp
  · rintro ⟨x, ⟨hc, hh⟩, rfl⟩
    have hy : x.val ∈ edgeParent_STR := (stageGeometry_STR Z).edge.restrictParent_le _ x.2
    refine ⟨hy, ?_, hh⟩
    have h0 : (edgeProj_STR ⟨x.val, hy⟩) 0 = v 0 :=
      congrArg (fun k => (k.val : EuclideanSpace ℝ (Fin 1)) 0) hc
    rw [edgeProj_val_STR] at h0
    exact h0

/-- **The cut-dependent edge facts over `edgeBaseOpen = ⊤`.** -/
theorem edgeFacts_STR (Z : ZeroDomains Wc) :
    EdgeCutFacts74 (stageGeometry_STR Z) (cutChoice_STR Z) where
  rank_two x hx := rank_two_restrict_STR edgeStage_STR ⊤ x (edgeRank_two_STR _ hx)
  proper := edgeFacts_proper_STR Z
  fibre_disk := edgeFacts_fibre_STR Z
  cbase_compact := cbase_compact_STR
  cbase_domain := cbase_domain_STR

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
