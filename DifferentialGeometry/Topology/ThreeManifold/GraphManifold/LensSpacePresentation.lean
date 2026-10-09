import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.LensGluing

/-!
# A raw graph presentation of the lens spaces

For `p ≥ 1` and `q` coprime to `p`, the lens space `L(p, q)` of `lensSpaceFormGroup p q hpq` is the
union of the images of the two solid tori `‖z₁‖ ≤ ‖z₂‖` and `‖z₂‖ ≤ ‖z₁‖` of the three-sphere.
Each is a solid torus (`TwistedCover.pieceDiffeo`), the trivial circle bundle over the closed
disc, and they are glued along their boundary tori by the linear map `lensMatching` with matrix
`!![-q, a; p, b]`, `a p + b q = 1`, in their disc and circle coordinates. This gives the raw graph
presentation `lensSpaceRawGraphPresentation p q hpq` with two pieces, one pairing torus and no
external tori, the same shape as the presentation of the three-sphere.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold

namespace TwistedCover

variable {p : ℕ} [NeZero p] {e : ℤ} {W : Type} [TopologicalSpace W]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) W] [IsManifold (𝓡 3) ∞ W] (T : TwistedCover p e W)

theorem mem_range_torusPoint_iff (a : T.pieceSet) :
    a ∈ range T.torusPoint ↔ T.height a.val = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    exact T.height_torusPoint t
  · intro h
    exact T.exists_torusPoint_eq h

def pieceOf (w : W) : T.pieceSet :=
  if h : T.height w ≤ 0 then ⟨w, h⟩ else T.torusPoint 1

theorem contMDiffAt_pieceOf {w : W} (hw : T.height w < 0) :
    ContMDiffAt (𝓡 3) (𝓡∂ 3) ∞ T.pieceOf w := by
  have h : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ T.pieceOf) w := by
    apply contMDiffAt_id.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt T.contMDiff_height.continuous continuous_const).mem_nhds hw]
      with v hv
    change (T.pieceOf v).val = v
    have hv' : T.height v ≤ 0 := le_of_lt hv
    simp only [pieceOf, hv', ↓reduceDIte]
  exact contMDiffWithinAt_univ.mp ((T.pieceAtlas.contMDiffWithinAt_iff_subtype_val T.pieceOf
    univ w).mpr h.contMDiffWithinAt)

end TwistedCover

section Lens

variable (p : ℕ) [NeZero p] (q : ℤ) (hpq : IsCoprime (p : ℤ) q)

theorem cliffordHeight_lensAct (k : ZMod p) (x : LensSphere) :
    cliffordHeight (lensAct p q k x) = cliffordHeight x :=
  cliffordHeight_circlePairAct _ _ x

theorem lensAct_mem_solidTorusSet_iff (k : ZMod p) (x : LensSphere) :
    lensAct p q k x ∈ solidTorusSet.{0} ↔ x ∈ solidTorusSet.{0} := by
  change cliffordHeight _ ≤ 0 ↔ cliffordHeight _ ≤ 0
  rw [cliffordHeight_lensAct]

theorem lensAct_mem_complement_iff (k : ZMod p) (x : LensSphere) :
    0 ≤ cliffordHeight (lensAct p q k x) ↔ 0 ≤ cliffordHeight x := by
  rw [cliffordHeight_lensAct]

theorem image_lensCover_solidTorusSet :
    lensCover p q hpq '' solidTorusSet.{0} = (lensLeftCover p q hpq).pieceSet := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (lensLeftCover p q hpq).height ((lensLeftCover p q hpq).cover x) ≤ 0
    rw [TwistedCover.height_cover]
    exact hx
  · intro hw
    exact ⟨(lensLeftCover p q hpq).lift w, hw, (lensLeftCover p q hpq).cover_lift w⟩

theorem image_lensCover_complement :
    lensCover p q hpq '' {x | 0 ≤ cliffordHeight x} = (lensRightCover p q hpq).pieceSet := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : 0 ≤ cliffordHeight x := hx
    change (lensRightCover p q hpq).height ((lensLeftCover p q hpq).cover x) ≤ 0
    rw [lensRight_height, TwistedCover.height_cover]
    linarith
  · intro hw
    have hw' : (lensRightCover p q hpq).height w ≤ 0 := hw
    rw [lensRight_height] at hw'
    refine ⟨(lensLeftCover p q hpq).lift w, ?_, (lensLeftCover p q hpq).cover_lift w⟩
    change 0 ≤ (lensLeftCover p q hpq).height w
    linarith

theorem lensCut_isInteriorPoint_inl_iff (a : (lensLeftCover p q hpq).pieceSet) :
    (𝓡∂ 3).IsInteriorPoint (Sum.inl a : LensCut p q hpq) ↔
      (lensLeftCover p q hpq).height a.val < 0 := by
  rw [← (lensLeftCover p q hpq).piece_isInteriorPoint_iff]
  exact ⟨fun h => ModelWithCorners.isInteriorPoint_disjointUnion_left h rfl,
    ModelWithCorners.interiorPoint_inl a⟩

theorem lensCut_isInteriorPoint_inr_iff (b : (lensRightCover p q hpq).pieceSet) :
    (𝓡∂ 3).IsInteriorPoint (Sum.inr b : LensCut p q hpq) ↔
      (lensRightCover p q hpq).height b.val < 0 := by
  rw [← (lensRightCover p q hpq).piece_isInteriorPoint_iff]
  exact ⟨fun h => ModelWithCorners.isInteriorPoint_disjointUnion_right h rfl,
    ModelWithCorners.interiorPoint_inr b⟩

theorem lensCut_isBoundaryPoint_inl_iff (a : (lensLeftCover p q hpq).pieceSet) :
    (𝓡∂ 3).IsBoundaryPoint (Sum.inl a : LensCut p q hpq) ↔
      (lensLeftCover p q hpq).height a.val = 0 := by
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    lensCut_isInteriorPoint_inl_iff, not_lt]
  exact ⟨fun h => le_antisymm a.2 h, fun h => h.ge⟩

theorem lensCut_isBoundaryPoint_inr_iff (b : (lensRightCover p q hpq).pieceSet) :
    (𝓡∂ 3).IsBoundaryPoint (Sum.inr b : LensCut p q hpq) ↔
      (lensRightCover p q hpq).height b.val = 0 := by
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    lensCut_isInteriorPoint_inr_iff, not_lt]
  exact ⟨fun h => le_antisymm b.2 h, fun h => h.ge⟩

theorem lensCut_boundary :
    (𝓡∂ 3).boundary (LensCut p q hpq) =
      range (lensLeftTorus p q hpq) ∪ range (lensRightTorus p q hpq) := by
  ext x
  rcases x with a | b
  · change (𝓡∂ 3).IsBoundaryPoint (Sum.inl a : LensCut p q hpq) ↔ _
    rw [lensCut_isBoundaryPoint_inl_iff, ← TwistedCover.mem_range_torusPoint_iff]
    constructor
    · rintro ⟨t, rfl⟩
      exact Or.inl ⟨t, rfl⟩
    · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
      · exact ⟨t, Sum.inl_injective ht⟩
      · cases ht
  · change (𝓡∂ 3).IsBoundaryPoint (Sum.inr b : LensCut p q hpq) ↔ _
    rw [lensCut_isBoundaryPoint_inr_iff, ← TwistedCover.mem_range_torusPoint_iff]
    constructor
    · rintro ⟨t, rfl⟩
      exact Or.inr ⟨t, rfl⟩
    · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
      · cases ht
      · exact ⟨t, Sum.inr_injective ht⟩

def lensPieces : Fin 2 → TopologicalSpace.Opens (LensCut p q hpq) :=
  ![⟨range Sum.inl, isOpen_range_inl⟩, ⟨range Sum.inr, isOpen_range_inr⟩]

theorem lensPieceInterior_zero :
    (((lensCutCarrier p q hpq).pieceInterior (lensPieces p q hpq 0) :
      Set (lensCutCarrier p q hpq).Carrier)) =
      Sum.inl '' {a : (lensLeftCover p q hpq).pieceSet |
        (lensLeftCover p q hpq).height a.val < 0} := by
  ext x
  constructor
  · rintro ⟨⟨a, rfl⟩, hx⟩
    exact ⟨a, (lensCut_isInteriorPoint_inl_iff p q hpq a).mp hx, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, rfl⟩, (lensCut_isInteriorPoint_inl_iff p q hpq a).mpr ha⟩

theorem lensPieceInterior_one :
    (((lensCutCarrier p q hpq).pieceInterior (lensPieces p q hpq 1) :
      Set (lensCutCarrier p q hpq).Carrier)) =
      Sum.inr '' {b : (lensRightCover p q hpq).pieceSet |
        (lensRightCover p q hpq).height b.val < 0} := by
  ext x
  constructor
  · rintro ⟨⟨b, rfl⟩, hx⟩
    exact ⟨b, (lensCut_isInteriorPoint_inr_iff p q hpq b).mp hx, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, rfl⟩, (lensCut_isInteriorPoint_inr_iff p q hpq b).mpr hb⟩

abbrev lensComponents : (lensCutCarrier p q hpq).Components where
  count := 2
  count_pos := by decide
  piece := lensPieces p q hpq
  closed i := by
    fin_cases i
    · exact isClosed_range_inl
    · exact isClosed_range_inr
  connected i := by
    fin_cases i
    · exact isConnected_iff_connectedSpace.mp (isConnected_range continuous_inl)
    · exact isConnected_iff_connectedSpace.mp (isConnected_range continuous_inr)
  disjoint i j h := by
    fin_cases i <;> fin_cases j
    · exact (h rfl).elim
    · exact isCompl_range_inl_range_inr.disjoint
    · exact isCompl_range_inl_range_inr.disjoint.symm
    · exact (h rfl).elim
  covers := by
    refine eq_univ_of_forall fun x => ?_
    rcases x with a | b
    · exact mem_iUnion.mpr ⟨0, a, rfl⟩
    · exact mem_iUnion.mpr ⟨1, b, rfl⟩
  interior_connected i := by
    fin_cases i
    · apply isConnected_iff_connectedSpace.mp
      change IsConnected ((lensCutCarrier p q hpq).pieceInterior (lensPieces p q hpq 0) :
        Set (lensCutCarrier p q hpq).Carrier)
      rw [lensPieceInterior_zero]
      exact (lensLeftCover p q hpq).isConnected_piece_interior.image _
        continuous_inl.continuousOn
    · apply isConnected_iff_connectedSpace.mp
      change IsConnected ((lensCutCarrier p q hpq).pieceInterior (lensPieces p q hpq 1) :
        Set (lensCutCarrier p q hpq).Carrier)
      rw [lensPieceInterior_one]
      exact (lensRightCover p q hpq).isConnected_piece_interior.image _
        continuous_inr.continuousOn

def lensPieceTrivialization : (i : Fin 2) →
    (lensPieces p q hpq i) ≃ₘ⟮(lensCutCarrier p q hpq).model,
      (SurfaceModel.model unitDiscSurface.{0}.kind).prod (𝓡 1)⟯
      unitDiscSurface.{0}.Carrier × Circle
  | ⟨0, _⟩ => (sumInlRangeDiffeomorph (I := 𝓡∂ 3)).trans (lensLeftCover p q hpq).pieceDiffeo
  | ⟨1, _⟩ => (sumInrRangeDiffeomorph (I := 𝓡∂ 3)).trans (lensRightCover p q hpq).pieceDiffeo

def lensFibration (i : Fin (lensComponents p q hpq).count) :
    CircleFibration (lensCutCarrier p q hpq) ((lensComponents p q hpq).piece i) :=
  CircleFibration.ofProductDiffeomorph unitDiscSurface (lensPieceTrivialization p q hpq i)

abbrev lensPairing : TorusPairing (lensCutCarrier p q hpq) where
  count := 1
  gluing := lensGluing p q hpq
  leftParam _ := lensLeftParam p q hpq
  rightParam _ := lensRightParam p q hpq
  matching _ := lensMatching p q hpq
  matching_eq _ t := lensAttaching_leftParam p q hpq t
  leftCollar _ := lensLeftCollar p q hpq
  rightCollar _ := lensRightCollar p q hpq
  left_source _ := lensLeftCollar_source p q hpq
  right_source _ := lensRightCollar_source p q hpq
  left_zero _ _ := rfl
  right_zero _ _ := rfl
  reversing _ := lensReversing p q hpq

theorem lensPairing_blocks :
    (⋃ i, (lensPairing p q hpq).gluing.block i) =
      range (lensLeftTorus p q hpq) ∪ range (lensRightTorus p q hpq) :=
  iUnion_const (range (lensLeftTorus p q hpq) ∪ range (lensRightTorus p q hpq))

def lensInteriorImage : TopologicalSpace.Opens (LensCarrier p q hpq) :=
  ⟨{w | (lensLeftCover p q hpq).height w ≠ 0},
    isOpen_ne_fun (lensLeftCover p q hpq).contMDiff_height.continuous continuous_const⟩

theorem lensRight_height_neg {w : LensCarrier p q hpq}
    (h : ¬ (lensLeftCover p q hpq).height w < 0) (hne : (lensLeftCover p q hpq).height w ≠ 0) :
    (lensRightCover p q hpq).height w < 0 := by
  rw [lensRight_height]
  have : 0 < (lensLeftCover p q hpq).height w := lt_of_le_of_ne (not_lt.mp h) hne.symm
  linarith

theorem lensFold_mem_interiorImage (x : (lensCutCarrier p q hpq).interior) :
    lensFold p q hpq x.val ∈ lensInteriorImage p q hpq := by
  obtain ⟨x, hx⟩ := x
  change (𝓡∂ 3).IsInteriorPoint x at hx
  change (lensLeftCover p q hpq).height (lensFold p q hpq x) ≠ 0
  rcases x with a | b
  · exact ((lensCut_isInteriorPoint_inl_iff p q hpq a).mp hx).ne
  · have hb := (lensCut_isInteriorPoint_inr_iff p q hpq b).mp hx
    rw [lensRight_height] at hb
    change (lensLeftCover p q hpq).height b.val ≠ 0
    intro h
    rw [h, neg_zero] at hb
    exact lt_irrefl 0 hb

def lensInteriorForward (x : (lensCutCarrier p q hpq).interior) : lensInteriorImage p q hpq :=
  ⟨lensFold p q hpq x.val, lensFold_mem_interiorImage p q hpq x⟩

def lensInteriorBackward (w : lensInteriorImage p q hpq) : (lensCutCarrier p q hpq).interior :=
  if h : (lensLeftCover p q hpq).height w.val < 0 then
    ⟨Sum.inl ⟨w.val, h.le⟩, (lensCut_isInteriorPoint_inl_iff p q hpq ⟨w.val, h.le⟩).mpr h⟩
  else
    ⟨Sum.inr ⟨w.val, (lensRight_height_neg p q hpq h w.2).le⟩,
      (lensCut_isInteriorPoint_inr_iff p q hpq _).mpr (lensRight_height_neg p q hpq h w.2)⟩

theorem contMDiff_lensInteriorBackward_val :
    ContMDiff (𝓡 3) (𝓡∂ 3) ∞
      (fun w : lensInteriorImage p q hpq => (lensInteriorBackward p q hpq w).val) := by
  intro w
  have hval : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (Subtype.val : lensInteriorImage p q hpq → LensCarrier p q hpq) w :=
    contMDiff_subtype_val w
  have hcont : Continuous fun v : lensInteriorImage p q hpq =>
      (lensLeftCover p q hpq).height v.val :=
    (lensLeftCover p q hpq).contMDiff_height.continuous.comp continuous_subtype_val
  by_cases hw : (lensLeftCover p q hpq).height w.val < 0
  · have h1 : ContMDiffAt (𝓡 3) (𝓡∂ 3) ∞
        (fun v : lensInteriorImage p q hpq =>
          (Sum.inl ((lensLeftCover p q hpq).pieceOf v.val) : LensCut p q hpq)) w :=
      ContMDiff.inl.contMDiffAt.comp w
        (((lensLeftCover p q hpq).contMDiffAt_pieceOf hw).comp w hval)
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt hcont continuous_const).mem_nhds hw] with v hv
    have hv' : (lensLeftCover p q hpq).height v.val < 0 := hv
    have hv'' : (lensLeftCover p q hpq).height v.val ≤ 0 := hv'.le
    simp only [lensInteriorBackward, hv', TwistedCover.pieceOf, hv'', ↓reduceDIte]
  · have hpos : 0 < (lensLeftCover p q hpq).height w.val :=
      lt_of_le_of_ne (not_lt.mp hw) w.2.symm
    have hR := lensRight_height_neg p q hpq hw w.2
    have h1 : ContMDiffAt (𝓡 3) (𝓡∂ 3) ∞
        (fun v : lensInteriorImage p q hpq =>
          (Sum.inr ((lensRightCover p q hpq).pieceOf v.val) : LensCut p q hpq)) w :=
      ContMDiff.inr.contMDiffAt.comp w
        (((lensRightCover p q hpq).contMDiffAt_pieceOf hR).comp w hval)
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds hpos] with v hv
    have hv' : 0 < (lensLeftCover p q hpq).height v.val := hv
    have hn : ¬ (lensLeftCover p q hpq).height v.val < 0 := not_lt.mpr hv'.le
    have hR' : (lensRightCover p q hpq).height v.val ≤ 0 := by
      rw [lensRight_height]
      linarith
    simp only [lensInteriorBackward, hn, TwistedCover.pieceOf, hR', ↓reduceDIte]

def lensInteriorDiffeomorph :
    (lensCutCarrier p q hpq).interior ≃ₘ⟮(lensCutCarrier p q hpq).model, 𝓡 3⟯
      lensInteriorImage p q hpq where
  toFun := lensInteriorForward p q hpq
  invFun := lensInteriorBackward p q hpq
  left_inv := by
    rintro ⟨x, hx⟩
    change (𝓡∂ 3).IsInteriorPoint x at hx
    rcases x with a | b
    · have ha := (lensCut_isInteriorPoint_inl_iff p q hpq a).mp hx
      apply Subtype.ext
      change (lensInteriorBackward p q hpq ⟨a.val, _⟩).val = _
      simp only [lensInteriorBackward, ha, ↓reduceDIte]
    · have hb := (lensCut_isInteriorPoint_inr_iff p q hpq b).mp hx
      have hn : ¬ (lensLeftCover p q hpq).height b.val < 0 := by
        rw [lensRight_height] at hb
        linarith
      apply Subtype.ext
      change (lensInteriorBackward p q hpq ⟨b.val, _⟩).val = _
      simp only [lensInteriorBackward, hn, ↓reduceDIte]
  right_inv := by
    intro w
    apply Subtype.ext
    by_cases hw : (lensLeftCover p q hpq).height w.val < 0
    · change lensFold p q hpq (lensInteriorBackward p q hpq w).val = w.val
      simp only [lensInteriorBackward, hw, ↓reduceDIte]
      rfl
    · change lensFold p q hpq (lensInteriorBackward p q hpq w).val = w.val
      simp only [lensInteriorBackward, hw, ↓reduceDIte]
      rfl
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff (lensInteriorImage p q hpq) _).mp
    ((contMDiff_lensFold p q hpq).comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff (lensCutCarrier p q hpq).interior _).mp
    (contMDiff_lensInteriorBackward_val p q hpq)

def lensSpaceRawGraphPresentation :
    RawGraphPresentation (NoCuts.carrier (GC.Seifert.lensSpaceFormGroup p q hpq).manifold) where
  cutCarrier := lensCutCarrier p q hpq
  components := lensComponents p q hpq
  fibration := lensFibration p q hpq
  pairing := lensPairing p q hpq
  externalCount := 0
  external := emptyBoundaryTori _
  cutExternal := emptyBoundaryTori _
  external_exhausted := by
    rw [emptyBoundaryTori_image]
    exact ModelWithCorners.Boundaryless.boundary_eq_empty
  cut_boundary_exhausted := by
    rw [emptyBoundaryTori_image, union_empty, lensPairing_blocks]
    exact lensCut_boundary p q hpq
  external_disjoint := by
    rw [emptyBoundaryTori_image]
    exact disjoint_empty _
  reconstruction := lensReconstruction p q hpq
  quotient_smooth := contMDiff_lensFold p q hpq
  quotient_oriented x := ⟨(Manifold.differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) (lensFold p q hpq)
    (mfderiv_lensFold_bijective p q hpq) x).toLinearEquiv, fun _ => rfl,
      orientation_map_lensCutOrientation p q hpq x⟩
  interiorImage := lensInteriorImage p q hpq
  interiorDiffeomorph := lensInteriorDiffeomorph p q hpq
  interior_map _ := rfl
  seam _ := (lensLeftCover p q hpq).seam
  seam_source _ := rfl
  seam_zero _ t := ((lensLeftCover p q hpq).torusPoint_val t).symm
  seam_positive _ t s hs hs1 :=
    (lensFold_lensRightCollar p q hpq (t, halfPoint s hs) hs1).symm
  seam_negative _ t s hs hs1 := by
    change (lensLeftCover p q hpq).seamMap (t, s) =
      (lensLeftCover p q hpq).seamMap (t, -(halfPoint (-s) (neg_nonneg.mpr hs)).val 0)
    rw [halfPoint_val_zero, neg_neg]
  seam_interior _ _ _ := BoundarylessManifold.isInteriorPoint
  seam_disjoint i j h := (h (Subsingleton.elim i j)).elim
  marked_collar i := i.elim0
  external_seam_disjoint i := i.elim0
  leftPiece _ := 0
  rightPiece _ := 1
  left_owned _ := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  right_owned _ := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  externalPiece i := i.elim0
  external_owned i := i.elim0

theorem lensSpaceRawGraphPresentation_components_count :
    (lensSpaceRawGraphPresentation p q hpq).components.count = 2 := rfl

theorem lensSpaceRawGraphPresentation_pairing_count :
    (lensSpaceRawGraphPresentation p q hpq).pairing.count = 1 := rfl

theorem lensSpaceRawGraphPresentation_externalCount :
    (lensSpaceRawGraphPresentation p q hpq).externalCount = 0 := rfl

theorem lensSpaceRawGraphPresentation_matching (t : Torus) :
    (lensSpaceRawGraphPresentation p q hpq).pairing.matching (0 : Fin 1) t =
      (t.1 ^ (-q) * t.2 ^ lensCoeffP p q hpq, t.1 ^ (p : ℤ) * t.2 ^ lensCoeffQ p q hpq) := rfl

theorem lensSpaceRawGraphPresentation_matching_eq :
    (lensSpaceRawGraphPresentation p q hpq).pairing.matching (0 : Fin 1) =
      GC.Seifert.linearTorusDiffeomorph (lensMatrixUnit p q hpq) := rfl

omit [NeZero p] in
theorem lensMatrixUnit_val :
    ((lensMatrixUnit p q hpq : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![-q, lensCoeffP p q hpq; (p : ℤ), lensCoeffQ p q hpq] := rfl

theorem lensSpaceRawGraphPresentation_leftParam_coordinates (t : Torus) :
    ((lensLeftCover p q hpq).pieceDiffeo ((lensLeftCover p q hpq).torusPoint t)).1.down.val =
        t.1 ∧
      ((lensLeftCover p q hpq).pieceDiffeo ((lensLeftCover p q hpq).torusPoint t)).2 = t.2 :=
  (lensLeftCover p q hpq).pieceDiffeo_torusPoint t

theorem lensSpaceRawGraphPresentation_rightParam_coordinates (t : Torus) :
    ((lensRightCover p q hpq).pieceDiffeo ((lensRightCover p q hpq).torusPoint t)).1.down.val =
        t.1 ∧
      ((lensRightCover p q hpq).pieceDiffeo ((lensRightCover p q hpq).torusPoint t)).2 = t.2 :=
  (lensRightCover p q hpq).pieceDiffeo_torusPoint t

theorem lensSpaceRawGraphPresentation_shape :
    (lensSpaceRawGraphPresentation p q hpq).components.count =
        standardThreeSphereLiftRawGraphPresentation.{0}.components.count ∧
      (lensSpaceRawGraphPresentation p q hpq).pairing.count =
        standardThreeSphereLiftRawGraphPresentation.{0}.pairing.count ∧
      (lensSpaceRawGraphPresentation p q hpq).externalCount =
        standardThreeSphereLiftRawGraphPresentation.{0}.externalCount :=
  ⟨rfl, rfl, rfl⟩

end Lens

theorem lensSpaceRawGraphPresentation_one_zero_shape :
    (lensSpaceRawGraphPresentation 1 0 isCoprime_one_left).components.count = 2 ∧
      (lensSpaceRawGraphPresentation 1 0 isCoprime_one_left).pairing.count = 1 ∧
      (lensSpaceRawGraphPresentation 1 0 isCoprime_one_left).externalCount = 0 :=
  ⟨rfl, rfl, rfl⟩

theorem lensSpaceRawGraphPresentation_one_one_shape :
    (lensSpaceRawGraphPresentation 1 1 isCoprime_one_left).components.count = 2 ∧
      (lensSpaceRawGraphPresentation 1 1 isCoprime_one_left).pairing.count = 1 ∧
      (lensSpaceRawGraphPresentation 1 1 isCoprime_one_left).externalCount = 0 :=
  ⟨rfl, rfl, rfl⟩

end GC.GraphManifold
