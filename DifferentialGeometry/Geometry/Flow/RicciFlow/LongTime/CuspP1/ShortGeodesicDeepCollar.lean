import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepCarrier
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Maps

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
  DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1

open DifferentialGeometry.Topology.Manifold in
/-- Reflection of the half collar: `(t, s) ↦ (t, b - s)` (clamped away from `0` outside
`s < 1`), landing in the cusp half-space. -/
def reflect_CPA2 (b : ℝ) (q : Torus × EuclideanHalfSpace 1) : CuspHalfSpace :=
  (q.1, halfSpaceOneLift (max (b - q.2.val 0) (b - 1)))

open DifferentialGeometry.Topology.Manifold in
theorem reflect_height_CPA2 (b : ℝ) (hb : 2 ≤ b) (q : Torus × EuclideanHalfSpace 1) :
    (reflect_CPA2 b q).2.val 0 = max (b - q.2.val 0) (b - 1) := by
  change max (max (b - q.2.val 0) (b - 1)) 0 = _
  exact max_eq_left (le_max_of_le_right (by linarith))

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)

theorem mem_deepSet_cuspMap_CPA2 {b : ℝ} (hb : 1 ≤ b) (i : Fin T.count) {q : CuspHalfSpace}
    (h0 : 0 < q.2.val 0) (h1 : q.2.val 0 ≤ b) : T.cuspMap i q ∈ deepSet_CPA2 T b := by
  change deepHeight_CPA2 T b _ ≤ 0
  rw [deepHeight_le_zero_iff_CPA2 T hb]
  intro j q' hq' hqq
  by_cases hij : j = i
  · subst hij
    have := (T.cuspEmbedding j).isEmbedding.injective hqq
    subst this
    exact h1
  · exfalso
    exact Set.disjoint_left.mp (T.cusp_disjoint hij) ⟨q', hqq⟩ ⟨q, rfl⟩

theorem cuspHeight_le_of_mem_deepSet_CPA2 {b : ℝ} (hb : 1 ≤ b) (i : Fin T.count)
    {p : H.Carrier} (hp : p ∈ deepSet_CPA2 T b) (hW : p ∈ cuspW_CPA2 T i) :
    cuspHeight_CPA2 T i p ≤ b := by
  obtain ⟨q, hq, rfl⟩ := hW
  rw [cuspHeight_apply_CPA2 T i hq]
  exact (deepHeight_le_zero_iff_CPA2 T hb _).mp hp i q hq rfl

open DifferentialGeometry.Topology.Manifold in
theorem contMDiffOn_reflect_CPA2 {b : ℝ} (hb : 2 ≤ b) :
    ContMDiffOn halfCollarModel halfCollarModel ∞ (reflect_CPA2 b)
      {q : Torus × EuclideanHalfSpace 1 | q.2.val 0 < 1} := by
  have hF : ContMDiff halfCollarModel 𝓘(ℝ, ℝ) ∞
      (fun q : Torus × EuclideanHalfSpace 1 => b - q.2.val 0) :=
    contMDiff_const.sub (contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd)
  have hg : ContMDiffOn halfCollarModel halfCollarModel ∞
      (fun q : Torus × EuclideanHalfSpace 1 => (q.1, halfSpaceOneLift (b - q.2.val 0)))
      {q : Torus × EuclideanHalfSpace 1 | q.2.val 0 < 1} := by
    refine contMDiff_fst.contMDiffOn.prodMk (contMDiffOn_halfSpaceOneLift.comp hF.contMDiffOn ?_)
    intro q hq
    have h0 : (0 : ℝ) ≤ q.2.val 0 := q.2.2
    have hq' : q.2.val 0 < 1 := hq
    change (0 : ℝ) ≤ b - q.2.val 0
    linarith
  refine hg.congr ?_
  intro q hq
  have hq' : q.2.val 0 < 1 := hq
  change (q.1, halfSpaceOneLift (max (b - q.2.val 0) (b - 1))) = _
  rw [max_eq_left (by linarith)]

section Collar

variable (hclosed : ∀ i, IsClosed (range (T.cuspMap i))) {b : ℝ} (hb : 2 ≤ b)

/-- The point of the deeper core at depth `b - s` of the `i`-th cusp (clamped). -/
def collarPoint_CPA2 (i : Fin T.count) (q : Torus × EuclideanHalfSpace 1) : deepSet_CPA2 T b :=
  ⟨T.cuspMap i (reflect_CPA2 b q), by
    apply mem_deepSet_cuspMap_CPA2 T (by linarith) i
    · rw [reflect_height_CPA2 b hb]
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    · rw [reflect_height_CPA2 b hb]
      refine max_le ?_ (by linarith)
      have : (0 : ℝ) ≤ q.2.val 0 := q.2.2
      linarith⟩

/-- Inverse of the collar: coordinates of a point of the deeper core inside the `i`-th cusp. -/
def collarInv_CPA2 (i : Fin T.count) (p : deepSet_CPA2 T b) : Torus × EuclideanHalfSpace 1 :=
  (((cuspChart_CPA2 T i).symm p.val).1,
    DifferentialGeometry.Topology.Manifold.halfSpaceOneLift (b - cuspHeight_CPA2 T i p.val))

/-- Target of the collar. -/
def collarTarget_CPA2 (i : Fin T.count) : Set (deepSet_CPA2 T b) :=
  {p | p.val ∈ cuspW_CPA2 T i ∧ b - 1 < cuspHeight_CPA2 T i p.val}

open DifferentialGeometry.Topology.Manifold in
theorem halfSpaceOneLift_coord_CPA2 (u : EuclideanHalfSpace 1) : halfSpaceOneLift (u.val 0) = u := by
  apply Subtype.ext
  ext i
  rw [Subsingleton.elim i 0]
  change max (u.val 0) 0 = u.val 0
  exact max_eq_left u.2

open DifferentialGeometry.Topology.Manifold in
theorem halfSpaceOneLift_val_CPA2 {t : ℝ} (ht : 0 ≤ t) : (halfSpaceOneLift t).val 0 = t := by
  change max t 0 = t
  exact max_eq_left ht

include hb in
theorem collarPoint_mem_target_CPA2 (i : Fin T.count) {q : Torus × EuclideanHalfSpace 1}
    (hq : q.2.val 0 < 1) : collarPoint_CPA2 T hb i q ∈ collarTarget_CPA2 T i := by
  have h0 : (0 : ℝ) ≤ q.2.val 0 := q.2.2
  have hh : 0 < (reflect_CPA2 b q).2.val 0 := by
    rw [reflect_height_CPA2 b hb]
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  refine ⟨mem_cuspW_cuspMap_CPA2 T i hh, ?_⟩
  change b - 1 < cuspHeight_CPA2 T i (T.cuspMap i (reflect_CPA2 b q))
  rw [cuspHeight_apply_CPA2 T i hh, reflect_height_CPA2 b hb, max_eq_left (by linarith)]
  linarith

include hb in
theorem collarInv_apply_CPA2 (i : Fin T.count) {p : deepSet_CPA2 T b}
    (hp : p ∈ collarTarget_CPA2 T i) :
    (collarInv_CPA2 T i p).2.val 0 = b - cuspHeight_CPA2 T i p.val := by
  have hle := cuspHeight_le_of_mem_deepSet_CPA2 T (by linarith) i p.2 hp.1
  exact halfSpaceOneLift_val_CPA2 (by linarith)

include hb in
theorem collarInv_mem_source_CPA2 (i : Fin T.count) {p : deepSet_CPA2 T b}
    (hp : p ∈ collarTarget_CPA2 T i) : (collarInv_CPA2 T i p).2.val 0 < 1 := by
  rw [collarInv_apply_CPA2 T hb i hp]
  linarith [hp.2]

include hb in
theorem collarInv_collarPoint_CPA2 (i : Fin T.count) {q : Torus × EuclideanHalfSpace 1}
    (hq : q.2.val 0 < 1) : collarInv_CPA2 T i (collarPoint_CPA2 T hb i q) = q := by
  have h0 : (0 : ℝ) ≤ q.2.val 0 := q.2.2
  have hh : 0 < (reflect_CPA2 b q).2.val 0 := by
    rw [reflect_height_CPA2 b hb]
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hs : reflect_CPA2 b q ∈ (cuspChart_CPA2 T i).source := by
    rw [cuspChart_source_CPA2]; exact hh
  have hinv : (cuspChart_CPA2 T i).symm (T.cuspMap i (reflect_CPA2 b q)) = reflect_CPA2 b q := by
    have := (cuspChart_CPA2 T i).left_inv hs
    rwa [cuspChart_apply_CPA2] at this
  have hheight : cuspHeight_CPA2 T i (T.cuspMap i (reflect_CPA2 b q)) = b - q.2.val 0 := by
    rw [cuspHeight_apply_CPA2 T i hh, reflect_height_CPA2 b hb, max_eq_left (by linarith)]
  apply Prod.ext
  · change ((cuspChart_CPA2 T i).symm (T.cuspMap i (reflect_CPA2 b q))).1 = q.1
    rw [hinv]; rfl
  · change DifferentialGeometry.Topology.Manifold.halfSpaceOneLift
      (b - cuspHeight_CPA2 T i (T.cuspMap i (reflect_CPA2 b q))) = q.2
    rw [hheight, sub_sub_cancel]
    exact halfSpaceOneLift_coord_CPA2 q.2

include hb in
theorem collarPoint_collarInv_CPA2 (i : Fin T.count) {p : deepSet_CPA2 T b}
    (hp : p ∈ collarTarget_CPA2 T i) : collarPoint_CPA2 T hb i (collarInv_CPA2 T i p) = p := by
  have hpt : p.val ∈ (cuspChart_CPA2 T i).target := by
    rw [cuspChart_target_CPA2]; exact hp.1
  have hle := cuspHeight_le_of_mem_deepSet_CPA2 T (by linarith) i p.2 hp.1
  apply Subtype.ext
  change T.cuspMap i (reflect_CPA2 b (collarInv_CPA2 T i p)) = p.val
  have hdr := (cuspChart_CPA2 T i).right_inv hpt
  rw [← cuspChart_apply_CPA2] at *
  conv_rhs => rw [← hdr]
  congr 1
  apply Prod.ext
  · rfl
  · change DifferentialGeometry.Topology.Manifold.halfSpaceOneLift
        (max (b - (collarInv_CPA2 T i p).2.val 0) (b - 1)) = ((cuspChart_CPA2 T i).symm p.val).2
    rw [collarInv_apply_CPA2 T hb i hp, sub_sub_cancel, max_eq_left (le_of_lt hp.2)]
    exact halfSpaceOneLift_coord_CPA2 _

include hclosed hb in
theorem contMDiffOn_collarPoint_CPA2 (i : Fin T.count) :
    let _ := (deepAtlas_CPA2 T hclosed hb).toChartedSpace
    ContMDiffOn halfCollarModel (𝓡∂ 3) ∞ (collarPoint_CPA2 T hb i)
      {q : Torus × EuclideanHalfSpace 1 | q.2.val 0 < 1} := by
  let C := deepAtlas_CPA2 T hclosed hb
  intro _
  refine (C.contMDiffOn_iff_subtype_val _ _).mpr ?_
  exact (T.cuspEmbedding i).contMDiff.comp_contMDiffOn (contMDiffOn_reflect_CPA2 hb)

include hclosed hb in
theorem contMDiffOn_collarInv_CPA2 (i : Fin T.count) :
    let _ := (deepAtlas_CPA2 T hclosed hb).toChartedSpace
    ContMDiffOn (𝓡∂ 3) halfCollarModel ∞ (collarInv_CPA2 (b := b) T i)
      (collarTarget_CPA2 (b := b) T i) := by
  let C := deepAtlas_CPA2 T hclosed hb
  intro _
  have hval : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : deepSet_CPA2 T b → H.Carrier) :=
    C.contMDiff_subtype_val
  have hmaps : MapsTo (Subtype.val : deepSet_CPA2 T b → H.Carrier) (collarTarget_CPA2 T i)
      (cuspChart_CPA2 T i).target := by
    intro p hp
    rw [cuspChart_target_CPA2]; exact hp.1
  have h1 : ContMDiffOn (𝓡∂ 3) torusModel ∞
      (fun p : deepSet_CPA2 T b => ((cuspChart_CPA2 T i).symm p.val).1) (collarTarget_CPA2 T i) := by
    have hs : ContMDiffOn (𝓡 3) halfCollarModel ∞ (cuspChart_CPA2 T i).symm
        (cuspChart_CPA2 T i).target := (cuspChart_CPA2 T i).symm.contMDiffOn
    exact contMDiff_fst.comp_contMDiffOn (hs.comp hval.contMDiffOn hmaps)
  have h2 : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞
      (fun p : deepSet_CPA2 T b => b - cuspHeight_CPA2 T i p.val) (collarTarget_CPA2 T i) := by
    have hh : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (cuspHeight_CPA2 T i) (cuspW_CPA2 T i) :=
      contMDiffOn_cuspHeight_CPA2 T i
    have := hh.comp hval.contMDiffOn (fun (p : deepSet_CPA2 T b)
      (hp : p ∈ collarTarget_CPA2 (b := b) T i) => (hp.1 : p.val ∈ cuspW_CPA2 T i))
    exact contMDiffOn_const.sub this
  refine h1.prodMk ?_
  refine DifferentialGeometry.Topology.Manifold.contMDiffOn_halfSpaceOneLift.comp h2 ?_
  intro p hp
  have hle := cuspHeight_le_of_mem_deepSet_CPA2 T (by linarith) i p.2 hp.1
  change (0 : ℝ) ≤ b - cuspHeight_CPA2 T i p.val
  linarith

include hclosed hb in
theorem isOpen_collarTarget_CPA2 (i : Fin T.count) : IsOpen (collarTarget_CPA2 (b := b) T i) := by
  have h1 : IsOpen (cuspW_CPA2 T i ∩ cuspHeight_CPA2 T i ⁻¹' Ioi (b - 1)) :=
    (contMDiffOn_cuspHeight_CPA2 T i).continuousOn.isOpen_inter_preimage
      (isOpen_cuspW_CPA2 T i) isOpen_Ioi
  exact h1.preimage continuous_subtype_val

/-- The half collar of the `i`-th boundary torus of the deeper core. -/
def deepCollar_CPA2 (i : Fin T.count) :
    PartialDiffeomorph halfCollarModel (deepCarrier_CPA2 T hclosed hb).model
      (Torus × EuclideanHalfSpace 1) (deepCarrier_CPA2 T hclosed hb).Carrier ∞ where
  toFun := collarPoint_CPA2 T hb i
  invFun := collarInv_CPA2 T i
  source := halfCollarSource
  target := collarTarget_CPA2 T i
  map_source' := fun q hq => collarPoint_mem_target_CPA2 T hb i (hq : q.2.val 0 < 1)
  map_target' := fun p hp => collarInv_mem_source_CPA2 T hb i hp
  left_inv' := fun q hq => collarInv_collarPoint_CPA2 T hb i hq
  right_inv' := fun p hp => collarPoint_collarInv_CPA2 T hb i hp
  open_source := isOpen_lt
    ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const
  open_target := isOpen_collarTarget_CPA2 T hclosed hb i
  contMDiffOn_toFun := contMDiffOn_collarPoint_CPA2 T hclosed hb i
  contMDiffOn_invFun := contMDiffOn_collarInv_CPA2 T hclosed hb i

include hclosed hb in
theorem collar_zero_isBoundaryPoint_CPA2 (i : Fin T.count) (t : Torus) :
    (deepCarrier_CPA2 T hclosed hb).model.IsBoundaryPoint
      (deepCollar_CPA2 T hclosed hb i (t, halfZero)) := by
  have hb1 : (1 : ℝ) ≤ b := by linarith
  refine (SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff (𝓡 3) (n := 2)
    finrank_euclideanSpace_fin (contMDiff_deepHeight_CPA2 T hclosed b) 0
    (deepHeight_regular_CPA2 T hclosed hb) (collarPoint_CPA2 T hb i (t, halfZero))).mpr ?_
  have hq : 0 < (reflect_CPA2 b (t, halfZero)).2.val 0 := by
    rw [reflect_height_CPA2 b hb]
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  change deepHeight_CPA2 T b (T.cuspMap i (reflect_CPA2 b (t, halfZero))) = 0
  rw [deepHeight_cuspMap_CPA2 T b i hq, reflect_height_CPA2 b hb]
  have : max (b - (halfZero.val 0)) (b - 1) = b := by
    have h0 : halfZero.val 0 = 0 := rfl
    rw [h0, sub_zero]
    exact max_eq_left (by linarith)
  rw [this, lam_eq_CPA2 hb1]
  ring

/-- The boundary tori of the deeper core. -/
def deepBoundary_CPA2 : BoundaryTori (deepCarrier_CPA2 T hclosed hb) T.count where
  collar := deepCollar_CPA2 T hclosed hb
  source_eq := fun _ => rfl
  boundary_zero := collar_zero_isBoundaryPoint_CPA2 T hclosed hb
  disjoint := by
    intro i j hij
    refine Set.disjoint_left.mpr fun p hpi hpj => ?_
    obtain ⟨q, -, hq⟩ := hpi.1
    obtain ⟨q', -, hq'⟩ := hpj.1
    exact Set.disjoint_left.mp (T.cusp_disjoint hij) ⟨q, hq⟩ ⟨q', hq'⟩

end Collar

end GC.LongTime.CuspP1
