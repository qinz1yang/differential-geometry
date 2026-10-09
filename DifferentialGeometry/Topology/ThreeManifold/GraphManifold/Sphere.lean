import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordReversal
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A raw graph presentation of the standard three-sphere

The standard three-sphere is the union of the two solid tori `‖z₁‖ ≤ ‖z₂‖` and `‖z₂‖ ≤ ‖z₁‖`
glued along the Clifford torus by the map exchanging the two circle factors. Each solid torus is
the trivial circle bundle over the closed disc. This gives a raw graph presentation of the
standard three-sphere with two pieces, one pairing torus and no external tori.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold
universe u

def sumInlRangeDiffeomorph {E H M M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace M'] [ChartedSpace H M'] [Nonempty M] :
    (⟨range (Sum.inl : M → M ⊕ M'), isOpen_range_inl⟩ : TopologicalSpace.Opens (M ⊕ M'))
      ≃ₘ⟮I, I⟯ M where
  toFun x := Sum.elim id (fun _ => Classical.arbitrary M) x.val
  invFun m := ⟨Sum.inl m, mem_range_self m⟩
  left_inv := by
    rintro ⟨_, m, rfl⟩
    rfl
  right_inv _ := rfl
  contMDiff_toFun := (ContMDiff.sumElim contMDiff_id contMDiff_const).comp contMDiff_subtype_val
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp ContMDiff.inl

def sumInrRangeDiffeomorph {E H M M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace M'] [ChartedSpace H M'] [Nonempty M'] :
    (⟨range (Sum.inr : M' → M ⊕ M'), isOpen_range_inr⟩ : TopologicalSpace.Opens (M ⊕ M'))
      ≃ₘ⟮I, I⟯ M' where
  toFun x := Sum.elim (fun _ => Classical.arbitrary M') id x.val
  invFun m := ⟨Sum.inr m, mem_range_self m⟩
  left_inv := by
    rintro ⟨_, m, rfl⟩
    rfl
  right_inv _ := rfl
  contMDiff_toFun := (ContMDiff.sumElim contMDiff_const contMDiff_id).comp contMDiff_subtype_val
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp ContMDiff.inr

theorem cliffordCut_isInteriorPoint_inl_iff (a : solidTorusSet.{u}) :
    (𝓡∂ 3).IsInteriorPoint (Sum.inl a : CliffordCut.{u}) ↔ cliffordHeight a.val < 0 := by
  rw [← solidTorus_isInteriorPoint_iff]
  exact ⟨fun h => ModelWithCorners.isInteriorPoint_disjointUnion_left h rfl,
    ModelWithCorners.interiorPoint_inl a⟩

theorem cliffordCut_isInteriorPoint_inr_iff (b : solidTorusSet.{u}) :
    (𝓡∂ 3).IsInteriorPoint (Sum.inr b : CliffordCut.{u}) ↔ cliffordHeight b.val < 0 := by
  rw [← solidTorus_isInteriorPoint_iff]
  exact ⟨fun h => ModelWithCorners.isInteriorPoint_disjointUnion_right h rfl,
    ModelWithCorners.interiorPoint_inr b⟩

theorem cliffordCut_isBoundaryPoint_inl_iff (a : solidTorusSet.{u}) :
    (𝓡∂ 3).IsBoundaryPoint (Sum.inl a : CliffordCut.{u}) ↔ cliffordHeight a.val = 0 := by
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    cliffordCut_isInteriorPoint_inl_iff, not_lt]
  exact ⟨fun h => le_antisymm a.2 h, fun h => h.ge⟩

theorem cliffordCut_isBoundaryPoint_inr_iff (b : solidTorusSet.{u}) :
    (𝓡∂ 3).IsBoundaryPoint (Sum.inr b : CliffordCut.{u}) ↔ cliffordHeight b.val = 0 := by
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    cliffordCut_isInteriorPoint_inr_iff, not_lt]
  exact ⟨fun h => le_antisymm b.2 h, fun h => h.ge⟩

theorem mem_range_cliffordTorusPoint_iff (a : solidTorusSet.{u}) :
    a ∈ range cliffordTorusPoint ↔ cliffordHeight a.val = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    exact cliffordHeight_cliffordTorusPoint t
  · intro h
    exact exists_cliffordTorusPoint_eq h

theorem cliffordCut_boundary :
    (𝓡∂ 3).boundary CliffordCut.{u} = range cliffordLeftTorus ∪ range cliffordRightTorus := by
  ext x
  rcases x with a | b
  · change (𝓡∂ 3).IsBoundaryPoint (Sum.inl a : CliffordCut.{u}) ↔ _
    rw [cliffordCut_isBoundaryPoint_inl_iff, ← mem_range_cliffordTorusPoint_iff]
    constructor
    · rintro ⟨t, rfl⟩
      exact Or.inl ⟨t, rfl⟩
    · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
      · exact ⟨t, Sum.inl_injective ht⟩
      · cases ht
  · change (𝓡∂ 3).IsBoundaryPoint (Sum.inr b : CliffordCut.{u}) ↔ _
    rw [cliffordCut_isBoundaryPoint_inr_iff, ← mem_range_cliffordTorusPoint_iff]
    constructor
    · rintro ⟨t, rfl⟩
      exact Or.inr ⟨t, rfl⟩
    · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
      · cases ht
      · exact ⟨t, Sum.inr_injective ht⟩

instance : ConnectedSpace UnitDisc.{u} := unitDiscSurface.{u}.connected

instance : ConnectedSpace solidTorusSet.{u} :=
  solidTorusDiscCircle.{u}.toHomeomorph.connectedSpace_iff.mpr inferInstance

theorem isConnected_unitDisc_interior :
    IsConnected {w : UnitDisc.{u} | ‖w.down.val‖ ^ 2 < 1} := by
  have hmem (z : ball (0 : ℂ) 1) : z.val ∈ unitDiscSet := by
    have hz : ‖z.val‖ < 1 := mem_ball_zero_iff.mp z.2
    change ‖z.val‖ ^ 2 ≤ 1
    nlinarith [norm_nonneg z.val]
  have heq : {w : UnitDisc.{u} | ‖w.down.val‖ ^ 2 < 1} =
      range (fun z : ball (0 : ℂ) 1 => (ULift.up ⟨z.val, hmem z⟩ : UnitDisc.{u})) := by
    ext w
    constructor
    · intro hw
      have hw' : ‖w.down.val‖ ^ 2 < 1 := hw
      have hlt : ‖w.down.val‖ < 1 := by nlinarith [norm_nonneg w.down.val]
      exact ⟨⟨w.down.val, mem_ball_zero_iff.mpr hlt⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      have hz : ‖z.val‖ < 1 := mem_ball_zero_iff.mp z.2
      change ‖z.val‖ ^ 2 < 1
      nlinarith [norm_nonneg z.val]
  rw [heq]
  have : ConnectedSpace (ball (0 : ℂ) 1) := isConnected_iff_connectedSpace.mp
    ((convex_ball (0 : ℂ) 1).isConnected (nonempty_ball.mpr one_pos))
  exact isConnected_range (continuous_uliftUp.comp
    (continuous_subtype_val.subtype_mk _))

theorem solidTorus_interior_eq_image :
    {a : solidTorusSet.{u} | cliffordHeight a.val < 0} =
      solidTorusDiscCircle.{u}.symm '' ({w : UnitDisc.{u} | ‖w.down.val‖ ^ 2 < 1} ×ˢ univ) := by
  rw [show solidTorusDiscCircle.{u}.symm '' ({w : UnitDisc.{u} | ‖w.down.val‖ ^ 2 < 1} ×ˢ univ)
      = solidTorusDiscCircle.{u} ⁻¹' ({w : UnitDisc.{u} | ‖w.down.val‖ ^ 2 < 1} ×ˢ univ) from
    congrFun (solidTorusDiscCircle.{u}.toHomeomorph.image_symm) _]
  ext a
  change cliffordHeight a.val < 0 ↔ ‖(discOfSolidTorus a).down.val‖ ^ 2 < 1 ∧ True
  rw [discOfSolidTorus_val, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, sqrt_two_sq,
    norm_sphereFirst_sq_eq, and_true]
  constructor <;> intro h <;> linarith

theorem isConnected_solidTorus_interior :
    IsConnected {a : solidTorusSet.{u} | cliffordHeight a.val < 0} := by
  rw [solidTorus_interior_eq_image]
  exact (isConnected_unitDisc_interior.prod isConnected_univ).image _
    solidTorusDiscCircle.{u}.symm.continuous.continuousOn

def cliffordPieces : Fin 2 → TopologicalSpace.Opens CliffordCut.{u} :=
  ![⟨range Sum.inl, isOpen_range_inl⟩, ⟨range Sum.inr, isOpen_range_inr⟩]

theorem cliffordPieceInterior_zero :
    ((cliffordCutCarrier.{u}.pieceInterior (cliffordPieces 0) :
      Set cliffordCutCarrier.{u}.Carrier)) =
      Sum.inl '' {a : solidTorusSet.{u} | cliffordHeight a.val < 0} := by
  ext x
  constructor
  · rintro ⟨⟨a, rfl⟩, hx⟩
    exact ⟨a, (cliffordCut_isInteriorPoint_inl_iff a).mp hx, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, rfl⟩, (cliffordCut_isInteriorPoint_inl_iff a).mpr ha⟩

theorem cliffordPieceInterior_one :
    ((cliffordCutCarrier.{u}.pieceInterior (cliffordPieces 1) :
      Set cliffordCutCarrier.{u}.Carrier)) =
      Sum.inr '' {a : solidTorusSet.{u} | cliffordHeight a.val < 0} := by
  ext x
  constructor
  · rintro ⟨⟨a, rfl⟩, hx⟩
    exact ⟨a, (cliffordCut_isInteriorPoint_inr_iff a).mp hx, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, rfl⟩, (cliffordCut_isInteriorPoint_inr_iff a).mpr ha⟩

abbrev cliffordComponents : cliffordCutCarrier.{u}.Components where
  count := 2
  count_pos := by decide
  piece := cliffordPieces
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
      change IsConnected (cliffordCutCarrier.{u}.pieceInterior (cliffordPieces 0) :
        Set cliffordCutCarrier.{u}.Carrier)
      rw [cliffordPieceInterior_zero]
      exact isConnected_solidTorus_interior.image _ continuous_inl.continuousOn
    · apply isConnected_iff_connectedSpace.mp
      change IsConnected (cliffordCutCarrier.{u}.pieceInterior (cliffordPieces 1) :
        Set cliffordCutCarrier.{u}.Carrier)
      rw [cliffordPieceInterior_one]
      exact isConnected_solidTorus_interior.image _ continuous_inr.continuousOn

def cliffordPieceTrivialization : (i : Fin 2) →
    (cliffordPieces.{u} i) ≃ₘ⟮cliffordCutCarrier.{u}.model,
      (SurfaceModel.model unitDiscSurface.{u}.kind).prod (𝓡 1)⟯ unitDiscSurface.{u}.Carrier × Circle
  | ⟨0, _⟩ => (sumInlRangeDiffeomorph (I := 𝓡∂ 3)).trans solidTorusDiscCircle
  | ⟨1, _⟩ => (sumInrRangeDiffeomorph (I := 𝓡∂ 3)).trans solidTorusDiscCircle

def cliffordFibration (i : Fin cliffordComponents.{u}.count) :
    CircleFibration cliffordCutCarrier.{u} (cliffordComponents.{u}.piece i) :=
  CircleFibration.ofProductDiffeomorph unitDiscSurface (cliffordPieceTrivialization i)

abbrev cliffordPairing : TorusPairing cliffordCutCarrier.{u} where
  count := 1
  gluing := cliffordGluing
  leftParam _ := cliffordLeftParam
  rightParam _ := cliffordRightParam
  matching _ := cliffordMatching
  matching_eq _ t := cliffordAttaching_leftParam t
  leftCollar _ := cliffordLeftCollar
  rightCollar _ := cliffordRightCollar
  left_source _ := cliffordLeftCollar_source
  right_source _ := cliffordRightCollar_source
  left_zero _ _ := rfl
  right_zero _ _ := rfl
  reversing _ := cliffordReversing

def emptyBoundaryTori (C : CompactCarrier.{u}) : BoundaryTori C 0 where
  collar i := i.elim0
  source_eq i := i.elim0
  boundary_zero i := i.elim0
  disjoint i := i.elim0

theorem emptyBoundaryTori_image (C : CompactCarrier.{u}) : (emptyBoundaryTori C).image = ∅ := by
  simp [BoundaryTori.image]

theorem cliffordPairing_blocks :
    (⋃ i, cliffordPairing.{u}.gluing.block i) =
      range cliffordLeftTorus ∪ range cliffordRightTorus :=
  iUnion_const (range cliffordLeftTorus ∪ range cliffordRightTorus)

def cliffordInteriorImage : TopologicalSpace.Opens SphereCarrier.{u} :=
  ⟨{p | cliffordHeight p ≠ 0}, isOpen_ne_fun contMDiff_cliffordHeight.continuous continuous_const⟩

theorem cliffordFold_mem_interiorImage (x : cliffordCutCarrier.{u}.interior) :
    cliffordFold x.val ∈ cliffordInteriorImage.{u} := by
  obtain ⟨x, hx⟩ := x
  change (𝓡∂ 3).IsInteriorPoint x at hx
  change cliffordHeight (cliffordFold x) ≠ 0
  rcases x with a | b
  · exact ((cliffordCut_isInteriorPoint_inl_iff a).mp hx).ne
  · rw [cliffordFold_inr, cliffordHeight_sphereSwap]
    exact neg_ne_zero.mpr ((cliffordCut_isInteriorPoint_inr_iff b).mp hx).ne

def cliffordInteriorForward (x : cliffordCutCarrier.{u}.interior) : cliffordInteriorImage.{u} :=
  ⟨cliffordFold x.val, cliffordFold_mem_interiorImage x⟩

theorem cliffordHeight_sphereSwap_neg_of_pos {p : SphereCarrier.{u}} (hp : ¬ cliffordHeight p < 0)
    (hne : cliffordHeight p ≠ 0) : cliffordHeight (sphereSwap p) < 0 := by
  rw [cliffordHeight_sphereSwap]
  have : 0 < cliffordHeight p := lt_of_le_of_ne (not_lt.mp hp) hne.symm
  linarith

def cliffordInteriorBackward (p : cliffordInteriorImage.{u}) : cliffordCutCarrier.{u}.interior :=
  if h : cliffordHeight p.val < 0 then
    ⟨Sum.inl ⟨p.val, h.le⟩, (cliffordCut_isInteriorPoint_inl_iff ⟨p.val, h.le⟩).mpr h⟩
  else
    ⟨Sum.inr ⟨sphereSwap p.val, (cliffordHeight_sphereSwap_neg_of_pos h p.2).le⟩,
      (cliffordCut_isInteriorPoint_inr_iff _).mpr (cliffordHeight_sphereSwap_neg_of_pos h p.2)⟩

def solidTorusOfSphere (p : SphereCarrier.{u}) : solidTorusSet.{u} :=
  if h : cliffordHeight p ≤ 0 then ⟨p, h⟩ else Classical.arbitrary _

theorem contMDiffAt_solidTorusOfSphere {p : SphereCarrier.{u}} (hp : cliffordHeight p < 0) :
    ContMDiffAt (𝓡 3) (𝓡∂ 3) ∞ solidTorusOfSphere p := by
  have h : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ solidTorusOfSphere) p := by
    apply contMDiffAt_id.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt contMDiff_cliffordHeight.continuous continuous_const).mem_nhds hp]
      with q hq
    change (solidTorusOfSphere q).val = q
    have hq' : cliffordHeight q ≤ 0 := le_of_lt hq
    simp only [solidTorusOfSphere, hq', ↓reduceDIte]
  exact contMDiffWithinAt_univ.mp ((solidTorusAtlas.contMDiffWithinAt_iff_subtype_val
    solidTorusOfSphere univ p).mpr h.contMDiffWithinAt)

theorem contMDiff_cliffordInteriorBackward_val :
    ContMDiff (𝓡 3) (𝓡∂ 3) ∞
      (fun p : cliffordInteriorImage.{u} => (cliffordInteriorBackward p).val) := by
  intro p
  have hval : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (Subtype.val : cliffordInteriorImage.{u} → _) p :=
    contMDiff_subtype_val p
  have hopen : IsOpen {q : cliffordInteriorImage.{u} | cliffordHeight q.val < 0} :=
    isOpen_lt (contMDiff_cliffordHeight.continuous.comp continuous_subtype_val) continuous_const
  have hopen' : IsOpen {q : cliffordInteriorImage.{u} | 0 < cliffordHeight q.val} :=
    isOpen_lt continuous_const (contMDiff_cliffordHeight.continuous.comp continuous_subtype_val)
  by_cases hp : cliffordHeight p.val < 0
  · have h1 : ContMDiffAt (𝓡 3) (𝓡∂ 3) ∞
        (fun q : cliffordInteriorImage.{u} => (Sum.inl (solidTorusOfSphere q.val) :
          CliffordCut.{u})) p :=
      ContMDiff.inl.contMDiffAt.comp p ((contMDiffAt_solidTorusOfSphere hp).comp p hval)
    apply h1.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hp] with q hq
    have hq' : cliffordHeight q.val < 0 := hq
    have hq'' : cliffordHeight q.val ≤ 0 := hq'.le
    simp only [cliffordInteriorBackward, hq', solidTorusOfSphere, hq'', ↓reduceDIte]
  · have hpos : 0 < cliffordHeight p.val := lt_of_le_of_ne (not_lt.mp hp) p.2.symm
    have hsw : cliffordHeight (sphereSwap p.val) < 0 := by
      rw [cliffordHeight_sphereSwap]
      linarith
    have h1 : ContMDiffAt (𝓡 3) (𝓡∂ 3) ∞
        (fun q : cliffordInteriorImage.{u} => (Sum.inr (solidTorusOfSphere (sphereSwap q.val)) :
          CliffordCut.{u})) p :=
      ContMDiff.inr.contMDiffAt.comp p ((contMDiffAt_solidTorusOfSphere hsw).comp p
        (sphereSwap.contMDiff.contMDiffAt.comp p hval))
    apply h1.congr_of_eventuallyEq
    filter_upwards [hopen'.mem_nhds hpos] with q hq
    have hq' : 0 < cliffordHeight q.val := hq
    have hn : ¬ cliffordHeight q.val < 0 := not_lt.mpr hq'.le
    have hsq : cliffordHeight (sphereSwap q.val) ≤ 0 := by
      rw [cliffordHeight_sphereSwap]
      linarith
    simp only [cliffordInteriorBackward, hn, solidTorusOfSphere, hsq, ↓reduceDIte]

def cliffordInteriorDiffeomorph :
    cliffordCutCarrier.{u}.interior ≃ₘ⟮cliffordCutCarrier.{u}.model, 𝓡 3⟯
      cliffordInteriorImage.{u} where
  toFun := cliffordInteriorForward
  invFun := cliffordInteriorBackward
  left_inv := by
    rintro ⟨x, hx⟩
    change (𝓡∂ 3).IsInteriorPoint x at hx
    rcases x with a | b
    · have ha := (cliffordCut_isInteriorPoint_inl_iff a).mp hx
      apply Subtype.ext
      change (cliffordInteriorBackward ⟨a.val, _⟩).val = _
      simp only [cliffordInteriorBackward, ha, ↓reduceDIte]
    · have hb := (cliffordCut_isInteriorPoint_inr_iff b).mp hx
      have hn : ¬ cliffordHeight (sphereSwap b.val) < 0 := by
        rw [cliffordHeight_sphereSwap]
        linarith
      apply Subtype.ext
      change (cliffordInteriorBackward ⟨sphereSwap b.val, _⟩).val = _
      simp only [cliffordInteriorBackward, hn, ↓reduceDIte]
      exact congrArg Sum.inr (Subtype.ext (sphereSwap_sphereSwap b.val))
  right_inv := by
    intro p
    apply Subtype.ext
    by_cases hp : cliffordHeight p.val < 0
    · change cliffordFold (cliffordInteriorBackward p).val = p.val
      simp only [cliffordInteriorBackward, hp, ↓reduceDIte]
      rfl
    · change cliffordFold (cliffordInteriorBackward p).val = p.val
      simp only [cliffordInteriorBackward, hp, ↓reduceDIte]
      exact sphereSwap_sphereSwap p.val
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff cliffordInteriorImage.{u} _).mp
    (contMDiff_cliffordFold.comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff cliffordCutCarrier.{u}.interior _).mp
    contMDiff_cliffordInteriorBackward_val

theorem cliffordReconstruction_quotientMap (x : CliffordCut.{u}) :
    cliffordReconstruction (cliffordPairing.{u}.quotientMap x) = cliffordFold x := rfl

def standardThreeSphereLiftRawGraphPresentation :
    RawGraphPresentation (NoCuts.carrier standardThreeSphereLift.{u}) where
  cutCarrier := cliffordCutCarrier
  components := cliffordComponents
  fibration := cliffordFibration
  pairing := cliffordPairing
  externalCount := 0
  external := emptyBoundaryTori _
  cutExternal := emptyBoundaryTori _
  external_exhausted := by
    rw [emptyBoundaryTori_image]
    exact ModelWithCorners.Boundaryless.boundary_eq_empty
  cut_boundary_exhausted := by
    rw [emptyBoundaryTori_image, union_empty, cliffordPairing_blocks]
    exact cliffordCut_boundary
  external_disjoint := by
    rw [emptyBoundaryTori_image]
    exact disjoint_empty _
  reconstruction := cliffordReconstruction
  quotient_smooth := contMDiff_cliffordFold
  quotient_oriented x := ⟨(Manifold.differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) cliffordFold
    mfderiv_cliffordFold_bijective x).toLinearEquiv, fun _ => rfl,
      orientation_map_cliffordCutOrientation x⟩
  interiorImage := cliffordInteriorImage
  interiorDiffeomorph := cliffordInteriorDiffeomorph
  interior_map _ := rfl
  seam _ := cliffordSeam
  seam_source _ := rfl
  seam_zero _ t := (cliffordTorusPoint_val t).symm
  seam_positive _ t s hs hs1 := by
    change cliffordSeamMap (t, s) =
      sphereSwap (cliffordSeamMap (((cliffordMatching t), -(halfPoint s hs).val 0)))
    rw [halfPoint_val_zero, cliffordMatching_apply]
    exact (sphereSwap_cliffordSeamMap_swap t (by linarith) hs1.le).symm
  seam_negative _ t s hs hs1 := by
    change cliffordSeamMap (t, s) =
      cliffordSeamMap (t, -(halfPoint (-s) (neg_nonneg.mpr hs)).val 0)
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

end GC.GraphManifold
