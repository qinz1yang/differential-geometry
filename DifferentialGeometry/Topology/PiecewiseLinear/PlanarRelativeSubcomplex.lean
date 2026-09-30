import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarFreeFace

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_isPLHomeomorphOn_eraseTriangleComplex_subcomplex
    (K L : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces]
    (hLK : L.faces ⊆ K.faces)
    (hpure : ∀ u ∈ K.faces, ∃ v ∈ K.faces, u ⊆ v ∧ v.card = 3)
    (hL : IsPLBall 2 L.space) {t s : Finset Plane} (ht : t ∈ L.faces)
    (htcard : t.card = 3) (hst : s ⊆ t) (hscard : s.card = 1 ∨ s.card = 2)
    (htrace : frontier L.space ∩ convexHull ℝ (t : Set Plane) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset Plane) : Set Plane))
    (hne : L.space ≠ convexHull ℝ (t : Set Plane))
    (hstar : ∀ u ∈ K.faces, u.card = 3 → s ⊆ u → u ∈ L.faces)
    (hinter : ∀ u ∈ K.faces, u.card = 3 → u ∉ L.faces →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s))
    {U : Set Plane} (hU : IsOpen U) (htU : convexHull ℝ (t : Set Plane) ⊆ U) :
    ∃ g : Plane ≃ₜ Plane, IsPLHomeomorphOn g univ univ ∧ EqOn g id Uᶜ ∧
      EqOn g id (frontier L.space \ convexHull ℝ (t : Set Plane)) ∧
      g '' K.space = (eraseTriangleComplex K t).space ∧
      g '' L.space = (eraseTriangleComplex L t).space ∧
      IsPLBall 2 (eraseTriangleComplex L t).space := by
  let _ : Finite L.faces := ((Set.toFinite K.faces).subset hLK).to_subtype
  let M := triangleMeshOfSubcomplex K K
  let e : K.vertices ↪ Plane := ⟨Subtype.val, Subtype.val_injective⟩
  let p : Finset M.Vertex → Prop := fun u => u.map e ∈ L.faces
  let N := M.restrictTriangles p
  have hNN : N = triangleMeshOfSubcomplex K L := triangleMeshOfSubcomplex_restrict K K L hLK
  have hMspace : M.toPlaneComplex.support = K.space :=
    triangleMeshOfSubcomplex_support (Subset.refl _) hpure
  have hNspace : N.toPlaneComplex.support = L.space := by
    rw [hNN]
    exact triangleMeshOfSubcomplex_support hLK
      (fun u hu => exists_face_superset_card_eq_of_isPLBall L hL hu)
  let r := t.subtype (fun v => v ∈ K.vertices)
  have hr : r.map e = t := Finset.subtype_map_of_mem fun v hv =>
    K.down_closed (hLK ht) (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hrcard : r.card = 3 := by rw [← Finset.card_map e, hr, htcard]
  have hrM : r ∈ M.triangles := (mem_triangleMeshOfSubcomplex_triangles (Subset.refl K.faces)).mpr
    ⟨hr.symm ▸ hLK ht, hrcard⟩
  have hrN : r ∈ N.triangles := (M.mem_restrictTriangles_triangles p).mpr
    ⟨hrM, by change r.map e ∈ L.faces; rw [hr]; exact ht⟩
  let T : N.Triangle := ⟨r, hrN⟩
  have hposition : N.position '' (T.1 : Set N.Vertex) = (t : Set Plane) := by
    change ((fun x : K.vertices => (x : Plane)) '' (r : Set K.vertices)) = (t : Set Plane)
    rw [← hr, Finset.coe_map]
    rfl
  have hcarrier : N.triangleCarrier T.1 = convexHull ℝ (t : Set Plane) :=
    congrArg (convexHull ℝ) hposition
  have hmore : 1 < N.triangles.card :=
    one_lt_triangles_card_of_support_ne_triangleCarrier N T (by rwa [hNspace, hcarrier])
  obtain ⟨a, ha, hs⟩ : ∃ a ∈ t, s = {a} ∨ s = t.erase a := by
    rcases hscard with hscard | hscard
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hscard
      exact ⟨a, hst (Finset.mem_singleton_self a), Or.inl rfl⟩
    · obtain ⟨a, hat, has⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : s.card < t.card)
      refine ⟨a, hat, Or.inr (Finset.eq_of_subset_of_card_le ?_ ?_)⟩
      · exact fun v hv => Finset.mem_erase.mpr ⟨fun hva => has (hva ▸ hv), hst hv⟩
      · rw [Finset.card_erase_of_mem hat, htcard, hscard]
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, N.position (N.orderedVertex T k) = a := by
    have ha' : a ∈ N.position '' (T.1 : Set N.Vertex) := hposition.symm ▸ ha
    rwa [← N.range_orderedVertex T, ← range_comp] at ha'
  let q := N.freeTriangleOrder T k
  have hq : Function.Injective q := (N.freeTriangleOrder_affineIndependent T k).injective
  have hq2 : q 2 = a := by simpa [q, TriangleMesh.freeTriangleOrder] using hk
  have htq : t = Finset.univ.image q := by
    apply Finset.coe_injective
    calc
      (t : Set Plane) = N.position '' (T.1 : Set N.Vertex) := hposition.symm
      _ = range q := (N.range_freeTriangleOrder T k).symm
      _ = (Finset.univ.image q : Finset Plane) := by ext x; simp
  have hspair (hs' : s = t.erase a) : s = {q 0, q 1} := by
    rw [hs', ← hq2, htq, ← Finset.image_erase hq]
    rw [show (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} by decide]
    simp
  have hfree : N.IsOneEdgeFreeTriangle T k ∨ N.IsTwoEdgeFreeTriangle T k := by
    rcases hs with hs | hs
    · left
      change frontier N.toPlaneComplex.support ∩ N.triangleCarrier T.1 = _
      rw [hNspace, hcarrier, htrace, hs, ← hq2, htq]
      exact iUnion_convexHull_erase_singleton_triangle q hq
    · right
      change frontier N.toPlaneComplex.support ∩ N.triangleCarrier T.1 = _
      rw [hNspace, hcarrier, htrace, hspair hs, htq]
      exact iUnion_convexHull_erase_pair_triangle q hq
  let eM : M.Vertex ↪ Plane := ⟨M.position, M.position_injective⟩
  let eN : N.Vertex ↪ Plane := ⟨N.position, N.position_injective⟩
  have hbaseImage : (N.freeTriangleBaseEdge T k).map eM = {q 0, q 1} := by
    change (N.freeTriangleBaseEdge T k).map eN = _
    apply Finset.coe_injective
    rw [Finset.coe_map, Finset.coe_pair]
    exact N.image_freeTriangleBaseEdge T k
  have hother (u : Finset M.Vertex) (hu : u ∈ M.triangles) (hpu : ¬p u) :
      u ∩ T.1 ⊆ N.freeTriangleBaseEdge T k ∧ (u ∩ T.1).card ≤ 1 := by
    have huK : u.map e ∈ K.faces ∧ u.card = 3 :=
      (mem_triangleMeshOfSubcomplex_triangles (Subset.refl K.faces)).mp hu
    have hucard : (u.map e : Finset Plane).card = 3 := (Finset.card_map e).trans huK.2
    have hcentre : ¬s ⊆ u.map e := fun hsub => hpu (hstar _ huK.1 hucard hsub)
    have hi := hinter (u.map e) huK.1 hucard hpu
    have himap : (u ∩ T.1).map eM = u.map e ∩ t := by
      exact (Finset.map_inter (f := eM) u r).trans
        (congrArg (fun v : Finset Plane => u.map e ∩ v) hr)
    have hicard : (u ∩ T.1).card ≤ 1 := by
      rw [← Finset.card_map eM, himap]
      exact hi.1
    refine ⟨?_, hicard⟩
    rcases hs with hs | hs
    · intro v hv
      have hvT : v ∈ range (N.orderedVertex T) := by
        rw [N.range_orderedVertex T]
        exact (Finset.mem_inter.mp hv).2
      obtain ⟨i, rfl⟩ := hvT
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩
      intro hik
      apply hcentre
      rw [hs, Finset.singleton_subset_iff, ← hk]
      exact Finset.mem_map.mpr ⟨N.orderedVertex T k, hik ▸ (Finset.mem_inter.mp hv).1, rfl⟩
    · have hsc : s.card = 2 := by rw [hs, Finset.card_erase_of_mem ha, htcard]
      have hm : (u ∩ T.1).map eM ⊆ (N.freeTriangleBaseEdge T k).map eM := by
        rw [himap, hbaseImage, ← hspair hs]
        exact hi.2 hsc
      exact Finset.map_subset_map.mp hm
  have hMerase : (M.eraseTriangle T.1).toPlaneComplex.support =
      (eraseTriangleComplex K t).space := by
    have he := triangleMeshOfSubcomplex_eraseTriangle_support (Subset.refl K.faces) r
    change (M.eraseTriangle r).toPlaneComplex.support =
      (eraseTriangleComplex K (r.map e)).space at he
    rw [hr] at he
    exact he
  have hNerase : (N.eraseTriangle T.1).toPlaneComplex.support =
      (eraseTriangleComplex L t).space := by
    have he := triangleMeshOfSubcomplex_eraseTriangle_support hLK r
    change ((triangleMeshOfSubcomplex K L).eraseTriangle r).toPlaneComplex.support =
      (eraseTriangleComplex L (r.map e)).space at he
    rw [hr] at he
    exact (congrArg (fun Q : TriangleMesh => Q.toPlaneComplex.support)
      (triangleMeshOfSubcomplex_restrict_eraseTriangle K K L hLK r)).trans he
  obtain ⟨g, hg, hfix, hboundary, -, hMimage, hNimage, hNball⟩ :=
    TriangleMesh.exists_isPLHomeomorphOn_eraseTriangle_restrictTriangles M p T k
      (hNspace.symm ▸ hL) hfree hmore (fun u hu hpu => (hother u hu hpu).1)
      (fun u hu hpu => (hother u hu hpu).2) hU (hcarrier.trans_le htU)
  refine ⟨g, hg, hfix, ?_, ?_, ?_, hNerase ▸ hNball⟩
  · change EqOn g id (frontier N.toPlaneComplex.support \ N.triangleCarrier T.1) at hboundary
    simpa only [hNspace, hcarrier] using hboundary
  · simpa only [hMspace, hMerase] using hMimage
  · change g '' N.toPlaneComplex.support = (N.eraseTriangle T.1).toPlaneComplex.support at hNimage
    simpa only [hNspace, hNerase] using hNimage

end DifferentialGeometry.Topology.PiecewiseLinear
