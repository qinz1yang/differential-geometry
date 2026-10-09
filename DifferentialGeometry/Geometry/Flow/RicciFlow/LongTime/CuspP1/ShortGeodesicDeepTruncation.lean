import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepIso

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
  DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)

theorem range_deepCuspMap_subset_CPA2 (b : ℝ) (i : Fin T.count) :
    range (deepCuspMap_CPA2 T b i) ⊆ range (T.cuspMap i) := by
  rintro _ ⟨q, rfl⟩
  exact ⟨shift_CPA2 b q, rfl⟩

theorem halfZero_of_height_zero_CPA2 {u : EuclideanHalfSpace 1} (h : u.val 0 = 0) : u = halfZero := by
  apply Subtype.ext
  ext j
  rw [Subsingleton.elim j 0]
  exact h

/-- Points of the cusp at height `> b` are in the image of the deepened parametrization. -/
theorem exists_deepCuspMap_of_tail_CPA2 {b : ℝ} (hb : 0 ≤ b) (i : Fin T.count)
    {q : CuspHalfSpace} (hq : b ≤ q.2.val 0) :
    ∃ q' : CuspHalfSpace, deepCuspMap_CPA2 T b i q' = T.cuspMap i q := by
  refine ⟨(q.1, halfSpaceOneLift (q.2.val 0 - b)), ?_⟩
  change T.cuspMap i (shift_CPA2 b _) = _
  congr 1
  refine Prod.ext rfl ?_
  change halfSpaceOneLift (((halfSpaceOneLift (q.2.val 0 - b)).val 0) + b) = q.2
  rw [halfSpaceOneLift_val_CPA2 (by linarith), sub_add_cancel]
  apply Subtype.ext
  ext j
  rw [Subsingleton.elim j 0]
  change max (q.2.val 0) 0 = _
  exact max_eq_left q.2.2

section Assembly

variable (hclosed : ∀ i, IsClosed (range (T.cuspMap i))) {b : ℝ} (hb : 2 ≤ b)

include hclosed hb in
theorem deepCarrier_isInteriorPoint_iff_CPA2 (x : (deepCarrier_CPA2 T hclosed hb).Carrier) :
    (deepCarrier_CPA2 T hclosed hb).model.IsInteriorPoint x ↔ deepHeight_CPA2 T b x.val < 0 :=
  SmoothBoundaryAtlas.regularSublevel_isInteriorPoint_iff (𝓡 3) (n := 2)
    finrank_euclideanSpace_fin (contMDiff_deepHeight_CPA2 T hclosed b) 0
    (deepHeight_regular_CPA2 T hclosed hb) x

include hclosed hb in
theorem deepCarrier_isBoundaryPoint_iff_CPA2 (x : (deepCarrier_CPA2 T hclosed hb).Carrier) :
    (deepCarrier_CPA2 T hclosed hb).model.IsBoundaryPoint x ↔ deepHeight_CPA2 T b x.val = 0 :=
  SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff (𝓡 3) (n := 2)
    finrank_euclideanSpace_fin (contMDiff_deepHeight_CPA2 T hclosed b) 0
    (deepHeight_regular_CPA2 T hclosed hb) x

theorem deepCuspMap_zero_CPA2 (i : Fin T.count) (x : Torus) :
    deepCuspMap_CPA2 T b i (x, halfZero) = T.cuspMap i (x, halfSpaceOneLift b) := by
  change T.cuspMap i (x, halfSpaceOneLift ((halfZero : EuclideanHalfSpace 1).val 0 + b)) = _
  have : (halfZero : EuclideanHalfSpace 1).val 0 = 0 := rfl
  rw [this, zero_add]

include hb in
theorem collarPoint_zero_CPA2 (i : Fin T.count) (x : Torus) :
    (collarPoint_CPA2 T hb i (x, halfZero)).val = T.cuspMap i (x, halfSpaceOneLift b) := by
  change T.cuspMap i (reflect_CPA2 b (x, halfZero)) = _
  have : (halfZero : EuclideanHalfSpace 1).val 0 = 0 := rfl
  change T.cuspMap i (x, halfSpaceOneLift (max (b - (halfZero : EuclideanHalfSpace 1).val 0) (b - 1))) = _
  rw [this, sub_zero, max_eq_left (by linarith)]

include hclosed hb in
theorem deepBoundary_image_eq_CPA2 :
    (deepCarrier_CPA2 T hclosed hb).model.boundary (deepCarrier_CPA2 T hclosed hb).Carrier =
      (deepBoundary_CPA2 T hclosed hb).image := by
  ext x
  constructor
  · intro hx
    have h0 : deepHeight_CPA2 T b x.val = 0 :=
      (deepCarrier_isBoundaryPoint_iff_CPA2 T hclosed hb x).mp hx
    obtain ⟨i, q, hqb, hq⟩ := (deepHeight_eq_zero_iff_CPA2 T (by linarith) x.val).mp h0
    refine mem_iUnion.mpr ⟨i, q.1, ?_⟩
    apply Subtype.ext
    change (collarPoint_CPA2 T hb i (q.1, halfZero)).val = x.val
    rw [collarPoint_zero_CPA2 T hb, ← hq]
    congr 1
    refine Prod.ext rfl ?_
    change halfSpaceOneLift b = q.2
    rw [← hqb]
    exact halfSpaceOneLift_coord_CPA2 q.2
  · intro hx
    obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hx
    exact collar_zero_isBoundaryPoint_CPA2 T hclosed hb i t

include hb in
theorem deep_intersection_CPA2 (i : Fin T.count) :
    range (fun x : deepSet_CPA2 T b => x.val) ∩ range (deepCuspMap_CPA2 T b i) =
      range (fun x : Torus => deepCuspMap_CPA2 T b i (x, halfZero)) := by
  have hb0 : (0 : ℝ) ≤ b := by linarith
  ext p
  constructor
  · rintro ⟨⟨x, rfl⟩, q, hq⟩
    have hx := x.2
    have hq0 : 0 < (shift_CPA2 b q).2.val 0 := by
      rw [shift_height_CPA2 hb0]
      have : (0 : ℝ) ≤ q.2.val 0 := q.2.2
      linarith
    have hle := (deepHeight_le_zero_iff_CPA2 T (by linarith) x.val).mp hx i (shift_CPA2 b q) hq0 hq
    rw [shift_height_CPA2 hb0] at hle
    have hz : q.2.val 0 = 0 := le_antisymm (by linarith) q.2.2
    refine ⟨q.1, ?_⟩
    rw [← hq]
    change T.cuspMap i (shift_CPA2 b (q.1, halfZero)) = T.cuspMap i (shift_CPA2 b q)
    congr 2
    exact (halfZero_of_height_zero_CPA2 hz).symm ▸ rfl
  · rintro ⟨x, rfl⟩
    refine ⟨⟨⟨deepCuspMap_CPA2 T b i (x, halfZero), ?_⟩, rfl⟩, ⟨(x, halfZero), rfl⟩⟩
    rw [deepCuspMap_zero_CPA2]
    apply mem_deepSet_cuspMap_CPA2 T (by linarith) i
    · rw [halfSpaceOneLift_val_CPA2 hb0]; linarith
    · rw [halfSpaceOneLift_val_CPA2 hb0]

include hb in
theorem deep_exhausts_CPA2 :
    range (fun x : deepSet_CPA2 T b => x.val) ∪ ⋃ i, range (deepCuspMap_CPA2 T b i) = univ := by
  have hb0 : (0 : ℝ) ≤ b := by linarith
  ext p
  simp only [mem_union, mem_iUnion, mem_univ, iff_true]
  by_cases hp : p ∈ deepSet_CPA2 T b
  · exact Or.inl ⟨⟨p, hp⟩, rfl⟩
  · right
    have hp' : ¬ deepHeight_CPA2 T b p ≤ 0 := hp
    rw [deepHeight_le_zero_iff_CPA2 T (by linarith)] at hp'
    push Not at hp'
    obtain ⟨i, q, hq0, hqp, hqb⟩ := hp'
    obtain ⟨q', hq'⟩ := exists_deepCuspMap_of_tail_CPA2 T hb0 i (le_of_lt hqb)
    exact ⟨i, q', by rw [hq', hqp]⟩

include hclosed hb in
theorem deep_interior_image_CPA2 :
    (fun x : deepSet_CPA2 T b => x.val) ''
      (((deepCarrier_CPA2 T hclosed hb).interior : TopologicalSpace.Opens _) :
        Set (deepCarrier_CPA2 T hclosed hb).Carrier) = {p | deepHeight_CPA2 T b p < 0} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (deepCarrier_isInteriorPoint_iff_CPA2 T hclosed hb x).mp hx
  · intro hp
    have hp' : deepHeight_CPA2 T b p ≤ 0 := le_of_lt hp
    exact ⟨⟨p, hp'⟩, (deepCarrier_isInteriorPoint_iff_CPA2 T hclosed hb ⟨p, hp'⟩).mpr hp, rfl⟩

/-- **Deeper truncation.** Given a hyperbolic truncation `T` whose cusp ranges are closed and a
depth `b ≥ 2`, the core is enlarged by the cusp collars of height `≤ b`; the cusps are shifted by
`b` and their torus metrics rescaled by `e^{-b}` (`deepCusp_CPA`). -/
def deepenTruncation_CPA2 : HyperbolicTruncation H where
  core := deepCarrier_CPA2 T hclosed hb
  connected := isConnected_iff_connectedSpace.mp (isConnected_deepSet_CPA2 T (by linarith))
  inclusion := ⟨fun x => x.val, continuous_subtype_val⟩
  embedding := (deepAtlas_CPA2 T hclosed hb).isSmoothEmbedding_subtype_val
  interior_image := by
    have ho : IsOpen {p : H.Carrier | deepHeight_CPA2 T b p < 0} :=
      isOpen_lt (contMDiff_deepHeight_CPA2 T hclosed b).continuous continuous_const
    rw [← deep_interior_image_CPA2 T hclosed hb] at ho
    exact ho
  count := T.count
  boundary := deepBoundary_CPA2 T hclosed hb
  boundary_exhausted := deepBoundary_image_eq_CPA2 T hclosed hb
  cusp := fun i => deepCusp_CPA (T.cusp i) b
  cuspMap := deepCuspMap_CPA2 T b
  cuspEmbedding := fun i => isSmoothEmbedding_deepCuspMap_CPA2 T (by linarith) i
  cuspIsometry := fun i p v w => deepCuspIsometry_CPA2 T (by linarith) i p v w
  cusp_zero := fun i x =>
    (deepCuspMap_zero_CPA2 T i x).trans (collarPoint_zero_CPA2 T hb i x).symm
  cusp_disjoint := fun i j hij =>
    (T.cusp_disjoint hij).mono (range_deepCuspMap_subset_CPA2 T b i)
      (range_deepCuspMap_subset_CPA2 T b j)
  intersection := fun i => deep_intersection_CPA2 T hb i
  exhausts := deep_exhausts_CPA2 T hb

end Assembly

end GC.LongTime.CuspP1
