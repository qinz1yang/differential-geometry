/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CoveringTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import DifferentialGeometry.Topology.PiecewiseLinear.OrientationCocycle
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Set _root_.Topology
open scoped unitInterval

universe u

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
  {X' : Type u} [TopologicalSpace X'] {p : X' → K.space}
  [Finite (coveringVertex K p)]

local instance (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (s : Finset E) :
    Finite (faceStarComplex L s).faces := (faceStarComplex_faces_finite L s).to_subtype

open Classical in
noncomputable instance finite_coveringComplex_faces : Finite (coveringComplex K p).faces :=
  (coveringComplex_faces_finite K p).to_subtype

open Classical in
theorem IsCombinatorialManifold.coveringComplex
    (hp : IsCoveringMap p) {n : ℕ} (hK : IsCombinatorialManifold n K) :
    IsCombinatorialManifold n (coveringComplex K p) := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
    Classical.decEq _
  cases n with
  | zero =>
      intro z hz
      obtain ⟨v, rfl⟩ := exists_coveringVertexPoint_of_singleton_mem K p hz
      rw [Set.eq_empty_iff_forall_notMem]
      intro q hq
      have hbase := (coveringVertexLink_isGlueIso K p hp v).image₂ q hq
      rw [hK (coveringVertex.base v) (coveringVertex.singleton_base_mem_faces v)] at hbase
      exact hbase
  | succ n =>
      intro z hz
      obtain ⟨v, rfl⟩ := exists_coveringVertexPoint_of_singleton_mem K p hz
      exact (hK (coveringVertex.base v) (coveringVertex.singleton_base_mem_faces v))
        |>.of_isPLHomeomorphOn (coveringVertexLink_isGlueIso K p hp v).isPLHomeomorphOn

open Classical in
noncomputable def CoherentOrientation.coveringVertexLink {n : ℕ}
    (v : coveringVertex K p)
    (o : CoherentOrientation n
      (SimplicialComplex.geometricLink K {coveringVertex.base v}))
    (hp : IsCoveringMap p) :
    let _ : DecidableEq (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
      Classical.decEq _
    CoherentOrientation n
      (SimplicialComplex.geometricLink (coveringComplex K p)
        {coveringVertexPoint K p v}) := by
  dsimp only
  exact o.map (coveringVertexLink_isGlueIso K p hp v)

open Classical in
theorem isOrientable_coveringVertexLink_iff {n : ℕ}
    (hp : IsCoveringMap p) (v : coveringVertex K p) :
    let _ : DecidableEq (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
      Classical.decEq _
    IsOrientable n (SimplicialComplex.geometricLink K {coveringVertex.base v}) ↔
      IsOrientable n (SimplicialComplex.geometricLink (coveringComplex K p)
        {coveringVertexPoint K p v}) := by
  dsimp only
  exact isOrientable_iff_of_isGlueIso (coveringVertexLink_isGlueIso K p hp v)

open Classical in
theorem isOrientable_coveringVertexLink_of_isCombinatorialManifoldWithBoundary
    (hp : IsCoveringMap p) {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (v : coveringVertex K p) :
    let _ : DecidableEq (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
      Classical.decEq _
    IsOrientable n (SimplicialComplex.geometricLink (coveringComplex K p)
      {coveringVertexPoint K p v}) := by
  dsimp only
  apply (isOrientable_coveringVertexLink_iff hp v).mp
  rcases hK (coveringVertex.base v) (coveringVertex.singleton_base_mem_faces v) with hS | hB
  · exact isOrientable_of_isPLSphere hS
  · exact isOrientable_of_isPLBall hB

open Classical in
noncomputable instance SimplicialBoolCocycle.finite_coveringVertex
    (ε : SimplicialBoolCocycle K) :
    Finite (coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj) := by
  apply coveringVertex.finite K
  intro x
  apply Set.finite_coe_iff.mp
  apply Nat.finite_of_card_ne_zero
  rw [ε.card_fiber x]
  decide

open Classical in
theorem SimplicialBoolCocycle.coveringComplex_isCombinatorialManifoldWithBoundary
    (ε : SimplicialBoolCocycle K) {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary n K) :
    IsCombinatorialManifoldWithBoundary n
      (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj) :=
  isCombinatorialManifoldWithBoundary_coveringComplex K
    ε.toBoolCocycle.toFiberBundleCore.proj ε.isCoveringMap hK

open Classical in
theorem SimplicialBoolCocycle.coveringComplex_isCombinatorialManifold
    (ε : SimplicialBoolCocycle K) {n : ℕ} (hK : IsCombinatorialManifold n K) :
    IsCombinatorialManifold n
      (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj) :=
  hK.coveringComplex ε.isCoveringMap

open Classical in
noncomputable def SimplicialBoolCocycle.coveringComplexHomeomorph
    (ε : SimplicialBoolCocycle K) :
    (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj).space ≃ₜ
      ε.toBoolCocycle.toFiberBundleCore.TotalSpace :=
  coveringSpaceHomeomorph K ε.toBoolCocycle.toFiberBundleCore.proj ε.isCoveringMap

open Classical in
theorem SimplicialBoolCocycle.isOrientable_coveringComplex_vertexLink
    (ε : SimplicialBoolCocycle K) {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (v : coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj) :
    let _ : DecidableEq (EuclideanSpace ℝ
      (Fin (Nat.card (coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj)))) :=
        Classical.decEq _
    IsOrientable n (SimplicialComplex.geometricLink
      (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj)
      {coveringVertexPoint K ε.toBoolCocycle.toFiberBundleCore.proj v}) := by
  dsimp only
  exact isOrientable_coveringVertexLink_of_isCombinatorialManifoldWithBoundary
    ε.isCoveringMap hK v

open Classical in
omit [FiniteDimensional ℝ E] [Finite K.faces] in
private theorem vertex_eq_of_mem_openStar {a b : E}
    (ha : {a} ∈ K.faces) (h : a ∈ openStar K b) : a = b := by
  by_contra hab
  have haHull : a ∈ convexHull ℝ (({a} : Finset E) : Set E) :=
    subset_convexHull ℝ _ (by simp)
  exact h.2 (mem_iUnion₂.mpr
    ⟨{a}, ⟨ha, by simpa using Ne.symm hab⟩, haHull⟩)

open Classical in
omit [FiniteDimensional ℝ E] in
private theorem SimplicialBoolCocycle.toBoolCocycle_indexAt_vertex
    (ε : SimplicialBoolCocycle K) {a : E} (ha : {a} ∈ K.faces) :
    ε.toBoolCocycle.indexAt
      (⟨a, K.subset_space (by simpa using ha) (by simp)⟩ : K.space) = ⟨a, ha⟩ := by
  apply Subtype.ext
  symm
  let x : K.space := ⟨a, K.subset_space (by simpa using ha) (by simp)⟩
  have hmem := ε.toBoolCocycle.mem_baseSet_at x
  change a ∈ openStar K (ε.toBoolCocycle.indexAt x : E) at hmem
  exact vertex_eq_of_mem_openStar ha hmem

omit [FiniteDimensional ℝ E] in
private theorem SimplicialBoolCocycle.localTriv_side_eq_of_path
    (ε : SimplicialBoolCocycle K)
    (i : {v // {v} ∈ K.faces})
    (γ : C(I, ε.toBoolCocycle.toFiberBundleCore.TotalSpace))
    (hγ : ∀ t, (γ t).1 ∈ ε.toBoolCocycle.baseSet i) :
    ((ε.toBoolCocycle.toFiberBundleCore.localTriv i) (γ 0)).2 =
      ((ε.toBoolCocycle.toFiberBundleCore.localTriv i) (γ 1)).2 := by
  have hcont : Continuous fun t =>
      ((ε.toBoolCocycle.toFiberBundleCore.localTriv i) (γ t)).2 := by
    apply continuous_snd.comp
    apply (ε.toBoolCocycle.toFiberBundleCore.localTriv i).continuousOn_toFun.comp_continuous
      γ.continuous
    intro t
    exact hγ t
  exact ((IsLocallyConstant.iff_continuous _).2 hcont).apply_eq_of_preconnectedSpace 0 1

omit [FiniteDimensional ℝ E] in
private theorem SimplicialBoolCocycle.localTriv_side_change
    (ε : SimplicialBoolCocycle K)
    (i j : {v // {v} ∈ K.faces})
    (z : ε.toBoolCocycle.toFiberBundleCore.TotalSpace)
    (hzi : z.1 ∈ ε.toBoolCocycle.baseSet i)
    (hzj : z.1 ∈ ε.toBoolCocycle.baseSet j) :
    ((ε.toBoolCocycle.toFiberBundleCore.localTriv j) z).2 =
      Bool.xor ((ε.toBoolCocycle.toFiberBundleCore.localTriv i) z).2
        (ε.parity i j) := by
  rw [FiberBundleCore.localTriv_apply, FiberBundleCore.localTriv_apply]
  let side : Bool := z.2
  change Bool.xor side
      (ε.parity (ε.toBoolCocycle.indexAt z.1) j) =
    Bool.xor (Bool.xor side
      (ε.parity (ε.toBoolCocycle.indexAt z.1) i)) (ε.parity i j)
  rw [Bool.xor_assoc]
  have hcomp := ε.toBoolCocycle.parity_comp
    (ε.toBoolCocycle.indexAt z.1) i j z.1
      ⟨⟨ε.toBoolCocycle.mem_baseSet_at z.1, hzi⟩, hzj⟩
  change Bool.xor (ε.parity (ε.toBoolCocycle.indexAt z.1) i)
      (ε.parity i j) = ε.parity (ε.toBoolCocycle.indexAt z.1) j at hcomp
  rw [hcomp]

open Classical in
omit [Finite K.faces] [Finite (coveringVertex K p)] in
private theorem coveringEdgeLift_target
    (hp : IsCoveringMap p) (v : coveringVertex K p) (w : E)
    (hvw : {coveringVertex.base v, w} ∈ K.faces) :
    coveringEdgeLift hp v w hvw
      ⟨w, subset_convexHull ℝ _ (by simp)⟩ = (coveringNeighbor hp v w).1 := by
  rw [coveringNeighbor, dite_eq_left hvw]
  rfl

open Classical in
omit [FiniteDimensional ℝ E] in
private theorem SimplicialBoolCocycle.indexAt_coveringVertex
    (ε : SimplicialBoolCocycle K)
    (v : coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj) :
    ε.toBoolCocycle.indexAt v.1.1 =
      ⟨coveringVertex.base v, coveringVertex.singleton_base_mem_faces v⟩ := by
  apply Subtype.ext
  symm
  have hmem := ε.toBoolCocycle.mem_baseSet_at v.1.1
  change coveringVertex.base v ∈
    openStar K (ε.toBoolCocycle.indexAt v.1.1 : E) at hmem
  exact vertex_eq_of_mem_openStar (coveringVertex.singleton_base_mem_faces v) hmem

open Classical in
omit [FiniteDimensional ℝ E] in
private theorem SimplicialBoolCocycle.localTriv_coveringVertex_side
    (ε : SimplicialBoolCocycle K)
    (v : coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj) :
    ((ε.toBoolCocycle.toFiberBundleCore.localTriv
      ⟨coveringVertex.base v, coveringVertex.singleton_base_mem_faces v⟩) v.1).2 = v.1.2 := by
  rw [FiberBundleCore.localTriv_apply]
  change Bool.xor v.1.2
    (ε.parity (ε.toBoolCocycle.indexAt v.1.1)
      (coveringVertex.base v)) = v.1.2
  rw [ε.indexAt_coveringVertex]
  change Bool.xor v.1.2 (ε.parity (coveringVertex.base v) (coveringVertex.base v)) = v.1.2
  rw [ε.self _ (coveringVertex.singleton_base_mem_faces v)]
  cases v.1.2 <;> rfl

open Classical in
theorem SimplicialBoolCocycle.coveringNeighbor_side
    (ε : SimplicialBoolCocycle K)
    (v : coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj)
    (w : E) (hvw : {coveringVertex.base v, w} ∈ K.faces) :
    (coveringNeighbor ε.isCoveringMap v w).1.2 =
      Bool.xor v.1.2 (ε.parity (coveringVertex.base v) w) := by
  let a := coveringVertex.base v
  let s : Finset E := {a, w}
  let C := ε.toBoolCocycle
  let Z := C.toFiberBundleCore
  let g := coveringEdgeLift ε.isCoveringMap v w hvw
  let u := coveringNeighbor ε.isCoveringMap v w
  let sideV : Bool := v.1.2
  let sideU : Bool := u.1.2
  have ha : {a} ∈ K.faces := coveringVertex.singleton_base_mem_faces v
  have hw : {w} ∈ K.faces :=
    K.down_closed hvw (by simp) (Finset.singleton_nonempty w)
  have hs : s ∈ K.faces := by simpa [s, a] using hvw
  have huBase : coveringVertex.base u = w :=
    coveringNeighbor_base_of_face ε.isCoveringMap v w hvw
  let i : {x // {x} ∈ K.faces} := ⟨a, ha⟩
  let j : {x // {x} ∈ K.faces} := ⟨w, hw⟩
  let m : E := s.centroid ℝ id
  have hmOpen : m ∈ openSimplex s :=
    centroid_mem_openSimplex (K.nonempty_of_mem_faces hs)
  have hmHull : m ∈ convexHull ℝ (s : Set E) :=
    openSimplex_subset_convexHull s hmOpen
  have hmStarA : m ∈ openStar K a :=
    SimplicialBoolCocycle.mem_openStar_of_mem_openSimplex hs hmOpen (by simp [s])
  have hmStarW : m ∈ openStar K w :=
    SimplicialBoolCocycle.mem_openStar_of_mem_openSimplex hs hmOpen (by simp [s])
  let xa : convexHull ℝ (s : Set E) :=
    ⟨a, subset_convexHull ℝ _ (by simp [s])⟩
  let xw : convexHull ℝ (s : Set E) :=
    ⟨w, subset_convexHull ℝ _ (by simp [s])⟩
  let xm : convexHull ℝ (s : Set E) := ⟨m, hmHull⟩
  have hsegA : segment ℝ (xa : E) (xm : E) ⊆ convexHull ℝ (s : Set E) :=
    (convex_convexHull ℝ _).segment_subset xa.2 xm.2
  have hsegW : segment ℝ (xw : E) (xm : E) ⊆ convexHull ℝ (s : Set E) :=
    (convex_convexHull ℝ _).segment_subset xw.2 xm.2
  let α : Path xa xm := segmentPath xa xm hsegA
  let β : Path xw xm := segmentPath xw xm hsegW
  let γa : C(I, Z.TotalSpace) := g.comp α.toContinuousMap
  let γw : C(I, Z.TotalSpace) := g.comp β.toContinuousMap
  have hγaBase : ∀ t, (γa t).1 ∈ C.baseSet i := by
    intro t
    change ((g (α t)).1 : E) ∈ openStar K a
    have hproj := congrFun (coveringEdgeLift_projection ε.isCoveringMap v w hvw) (α t)
    have hval : ((g (α t)).1 : E) = (α t : E) := congrArg Subtype.val hproj
    rw [hval]
    apply (SimplicialBoolCocycle.starConvex_openStar ha).segment_subset hmStarA
    exact forall_mem_of_segmentPath xa xm hsegA t
  have hγwBase : ∀ t, (γw t).1 ∈ C.baseSet j := by
    intro t
    change ((g (β t)).1 : E) ∈ openStar K w
    have hproj := congrFun (coveringEdgeLift_projection ε.isCoveringMap v w hvw) (β t)
    have hval : ((g (β t)).1 : E) = (β t : E) := congrArg Subtype.val hproj
    rw [hval]
    apply (SimplicialBoolCocycle.starConvex_openStar hw).segment_subset hmStarW
    exact forall_mem_of_segmentPath xw xm hsegW t
  have hγaStart : γa 0 = v.1 := by
    change g (α 0) = v.1
    rw [α.source]
    exact coveringEdgeLift_source ε.isCoveringMap v w hvw
  have hγaEnd : γa 1 = g xm := by
    change g (α 1) = g xm
    rw [α.target]
  have hγwStart : γw 0 = u.1 := by
    change g (β 0) = u.1
    rw [β.source]
    exact coveringEdgeLift_target ε.isCoveringMap v w hvw
  have hγwEnd : γw 1 = g xm := by
    change g (β 1) = g xm
    rw [β.target]
  have hconstA := ε.localTriv_side_eq_of_path i γa hγaBase
  have hconstW := ε.localTriv_side_eq_of_path j γw hγwBase
  have hmidI : (g xm).1 ∈ C.baseSet i := by
    change ((g xm).1 : E) ∈ openStar K a
    have hproj := congrFun (coveringEdgeLift_projection ε.isCoveringMap v w hvw) xm
    have hval : ((g xm).1 : E) = (xm : E) := congrArg Subtype.val hproj
    rw [hval]
    exact hmStarA
  have hmidJ : (g xm).1 ∈ C.baseSet j := by
    change ((g xm).1 : E) ∈ openStar K w
    have hproj := congrFun (coveringEdgeLift_projection ε.isCoveringMap v w hvw) xm
    have hval : ((g xm).1 : E) = (xm : E) := congrArg Subtype.val hproj
    rw [hval]
    exact hmStarW
  have hchange := ε.localTriv_side_change i j (g xm) hmidI hmidJ
  have hchartU : ((Z.localTriv j) u.1).2 = sideU := by
    have hj :
        (⟨coveringVertex.base u, coveringVertex.singleton_base_mem_faces u⟩ :
          {x // {x} ∈ K.faces}) = j := by
      apply Subtype.ext
      exact huBase
    rw [← hj]
    exact ε.localTriv_coveringVertex_side u
  have hchartV : ((Z.localTriv i) v.1).2 = sideV :=
    ε.localTriv_coveringVertex_side v
  change sideU = Bool.xor sideV (ε.parity a w)
  calc
    sideU = ((Z.localTriv j) u.1).2 := hchartU.symm
    _ = ((Z.localTriv j) (γw 0)).2 :=
      congrArg (fun z : Z.TotalSpace => (((Z.localTriv j) z).2 : Bool)) hγwStart.symm
    _ = ((Z.localTriv j) (γw 1)).2 := hconstW
    _ = ((Z.localTriv j) (g xm)).2 :=
      congrArg (fun z : Z.TotalSpace => (((Z.localTriv j) z).2 : Bool)) hγwEnd
    _ = Bool.xor ((Z.localTriv i) (g xm)).2 (ε.parity i j) := hchange
    _ = Bool.xor ((Z.localTriv i) (γa 1)).2 (ε.parity i j) := by rw [hγaEnd]
    _ = Bool.xor ((Z.localTriv i) (γa 0)).2 (ε.parity i j) :=
      congrArg (fun side => Bool.xor side (ε.parity i j)) hconstA.symm
    _ = Bool.xor ((Z.localTriv i) v.1).2 (ε.parity i j) := by rw [hγaStart]
    _ = Bool.xor sideV (ε.parity i j) :=
      congrArg (fun side => Bool.xor side (ε.parity i j)) hchartV
    _ = Bool.xor sideV (ε.parity a w) := rfl

open Classical in
private noncomputable def coveringOrientationVertexKey
    (z : EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :
    E ×ₗ EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))) := by
  let _ : LinearOrder E := linearOrderOfSTO WellOrderingRel
  let _ : LinearOrder (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
    linearOrderOfSTO WellOrderingRel
  exact toLex (coveringBaseVertex K p z, z)

open Classical in
omit [FiniteDimensional ℝ E] [Finite K.faces] [TopologicalSpace X'] in
private theorem coveringOrientationVertexKey_injective :
    Function.Injective (coveringOrientationVertexKey (K := K) (p := p)) := by
  intro x y hxy
  have h := congrArg (fun z => (ofLex z).2) hxy
  simpa only [coveringOrientationVertexKey, ofLex_toLex] using h

open Classical in
@[instance_reducible]
private noncomputable def coveringOrientationVertexOrder :
    LinearOrder (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) := by
  let _ : LinearOrder E := linearOrderOfSTO WellOrderingRel
  let _ : LinearOrder (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
    linearOrderOfSTO WellOrderingRel
  exact LinearOrder.lift' (coveringOrientationVertexKey (K := K) (p := p))
    coveringOrientationVertexKey_injective

open Classical in
omit [FiniteDimensional ℝ E] [Finite K.faces] [TopologicalSpace X'] in
private theorem coveringOrientationVertexOrder_lt_iff
    {x y : EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))}
    (hxy : coveringBaseVertex K p x ≠ coveringBaseVertex K p y) :
    let _ := coveringOrientationVertexOrder (K := K) (p := p)
    x < y ↔
      let _ : LinearOrder E := linearOrderOfSTO WellOrderingRel
      coveringBaseVertex K p x < coveringBaseVertex K p y := by
  let _ : LinearOrder E := linearOrderOfSTO WellOrderingRel
  let _ : LinearOrder (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
    linearOrderOfSTO WellOrderingRel
  change toLex (coveringBaseVertex K p x, x) <
      toLex (coveringBaseVertex K p y, y) ↔ _
  rw [Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact h
    · exact False.elim (hxy h)
  · exact fun h => Or.inl h

open Classical in
omit [FiniteDimensional ℝ E] [Finite K.faces] in
private theorem coveringBaseVertex_injective_on_geometricFace
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))}
    (hq : q ∈ (coveringComplex K p).faces) :
    Set.InjOn (coveringBaseVertex K p) (q : Set _) := by
  let d := chosenCoveringGeometricFaceData K p hq
  rw [← d.image_eq]
  exact coveringBaseVertex_injective_on_face K p d.data

open Classical in
omit [FiniteDimensional ℝ E] [Finite K.faces] in
private theorem coveringBaseFace_mem
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))}
    (hq : q ∈ (coveringComplex K p).faces) :
    q.image (coveringBaseVertex K p) ∈ K.faces := by
  let d := chosenCoveringGeometricFaceData K p hq
  rw [← d.image_eq, coveringBaseVertex_image]
  exact d.data.face

open Classical in
omit [FiniteDimensional ℝ E] [Finite K.faces] in
private theorem coveringOrientationVertexOrder_lt_iff_of_mem_face
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))}
    (hq : q ∈ (coveringComplex K p).faces) {x y : _}
    (hx : x ∈ q) (hy : y ∈ q) :
    let _ := coveringOrientationVertexOrder (K := K) (p := p)
    x < y ↔
      let _ : LinearOrder E := linearOrderOfSTO WellOrderingRel
      coveringBaseVertex K p x < coveringBaseVertex K p y := by
  by_cases hxy : x = y
  · subst y
    simp
  · apply coveringOrientationVertexOrder_lt_iff
    intro hbase
    exact hxy (coveringBaseVertex_injective_on_geometricFace hq
      (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hbase)

open Classical in
omit [FiniteDimensional ℝ E] [Finite K.faces] in
private theorem coveringIncidenceIndex
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))}
    (hq : q ∈ (coveringComplex K p).faces) {y : _} (hy : y ∈ q) :
    incidenceIndex (coveringOrientationVertexOrder (K := K) (p := p)) q y =
      incidenceIndex (linearOrderOfSTO WellOrderingRel)
        (q.image (coveringBaseVertex K p)) (coveringBaseVertex K p y) := by
  let r := coveringOrientationVertexOrder (K := K) (p := p)
  have hinj := coveringBaseVertex_injective_on_geometricFace hq
  have hfilter :
      (q.filter fun x => @LT.lt _ r.toLT x y).image (coveringBaseVertex K p) =
        (q.image (coveringBaseVertex K p)).filter
          fun z => @LT.lt E (linearOrderOfSTO WellOrderingRel).toLT z
            (coveringBaseVertex K p y) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      have hx' := Finset.mem_filter.mp hx
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image_of_mem _ hx'.1,
        (coveringOrientationVertexOrder_lt_iff_of_mem_face hq hx'.1 hy).mp hx'.2⟩
    · intro hz
      have hz' := Finset.mem_filter.mp hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz'.1
      apply Finset.mem_image.mpr
      refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, rfl⟩
      exact (coveringOrientationVertexOrder_lt_iff_of_mem_face hq hx hy).mpr hz'.2
  change incidenceIndex r q y = incidenceIndex (linearOrderOfSTO WellOrderingRel)
    (q.image (coveringBaseVertex K p)) (coveringBaseVertex K p y)
  unfold incidenceIndex
  change (q.filter fun x => @LT.lt _ r.toLT x y).card =
    ((q.image (coveringBaseVertex K p)).filter
      fun z => @LT.lt E (linearOrderOfSTO WellOrderingRel).toLT z
        (coveringBaseVertex K p y)).card
  calc
    _ = ((q.filter fun x => @LT.lt _ r.toLT x y).image
        (coveringBaseVertex K p)).card :=
      (Finset.card_image_of_injOn (hinj.mono fun x hx =>
        Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1)).symm
    _ = _ := congrArg Finset.card hfilter

open Classical in
omit [FiniteDimensional ℝ E] [Finite K.faces] in
private theorem coveringSimplexBoundaryCoefficient
    {q f : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))}
    (hq : q ∈ (coveringComplex K p).faces) (hfq : f ⊆ q)
    (hcard : f.card + 1 = q.card) :
    simplexBoundaryCoefficient (coveringOrientationVertexOrder (K := K) (p := p)) q f =
      simplexBoundaryCoefficient (linearOrderOfSTO WellOrderingRel)
        (q.image (coveringBaseVertex K p)) (f.image (coveringBaseVertex K p)) := by
  obtain ⟨y, hyf, hqy⟩ := Finset.exists_eq_insert_iff.mpr ⟨hfq, hcard⟩
  have hyq : y ∈ q := hqy ▸ Finset.mem_insert_self y f
  have herase : q.erase y = f := by rw [← hqy, Finset.erase_insert hyf]
  let r := coveringOrientationVertexOrder (K := K) (p := p)
  let fCover := @Finset.erase _ r.toDecidableEq q y
  let fBase := @Finset.erase E (linearOrderOfSTO WellOrderingRel).toDecidableEq
    (q.image (coveringBaseVertex K p)) (coveringBaseVertex K p y)
  have hfCover : fCover = f := by
    calc
      fCover = q.erase y := by ext z; simp [fCover]
      _ = f := herase
  have hfBase : fBase = f.image (coveringBaseVertex K p) := by
    calc
      fBase = (q.image (coveringBaseVertex K p)).erase (coveringBaseVertex K p y) := by
        ext z
        simp [fBase]
      _ = (q.erase y).image (coveringBaseVertex K p) :=
        by
          apply Finset.ext
          intro z
          simp only [Finset.mem_erase, Finset.mem_image]
          constructor
          · rintro ⟨hzy, x, hxq, rfl⟩
            refine ⟨x, ⟨?_, hxq⟩, rfl⟩
            intro hxy
            apply hzy
            rw [hxy]
          · rintro ⟨x, ⟨hxy, hxq⟩, rfl⟩
            refine ⟨?_, x, hxq, rfl⟩
            intro hbase
            exact hxy (coveringBaseVertex_injective_on_geometricFace hq
              (Finset.mem_coe.mpr hxq) (Finset.mem_coe.mpr hyq) hbase)
      _ = f.image (coveringBaseVertex K p) := by rw [herase]
  calc
    simplexBoundaryCoefficient r q f = simplexBoundaryCoefficient r q fCover := by rw [hfCover]
    _ = incidenceSign r q y := simplexBoundaryCoefficient_erase r hyq
    _ = incidenceSign (linearOrderOfSTO WellOrderingRel)
        (q.image (coveringBaseVertex K p))
        (coveringBaseVertex K p y) := by
      rw [incidenceSign, incidenceSign, coveringIncidenceIndex hq hyq]
    _ = simplexBoundaryCoefficient (linearOrderOfSTO WellOrderingRel)
        (q.image (coveringBaseVertex K p)) fBase :=
      (simplexBoundaryCoefficient_erase (linearOrderOfSTO WellOrderingRel)
        (Finset.mem_image_of_mem _ hyq)).symm
    _ = simplexBoundaryCoefficient (linearOrderOfSTO WellOrderingRel)
        (q.image (coveringBaseVertex K p))
        (f.image (coveringBaseVertex K p)) := by rw [hfBase]

open Classical in
private noncomputable def SimplicialBoolCocycle.coveringFaceAnchor
    (ε : SimplicialBoolCocycle K)
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card
      (coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj))))}
    (hq : q ∈ (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj).faces) :
    coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj :=
  Classical.choose (Finset.image_nonempty.mp
    (K.nonempty_of_mem_faces
      (chosenCoveringGeometricFaceData K ε.toBoolCocycle.toFiberBundleCore.proj hq).data.face))

open Classical in
omit [FiniteDimensional ℝ E] in
private theorem SimplicialBoolCocycle.coveringFaceAnchor_mem_source
    (ε : SimplicialBoolCocycle K)
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card
      (coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj))))}
    (hq : q ∈ (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj).faces) :
    ε.coveringFaceAnchor hq ∈
      (chosenCoveringGeometricFaceData K ε.toBoolCocycle.toFiberBundleCore.proj hq).source :=
  Classical.choose_spec (Finset.image_nonempty.mp
    (K.nonempty_of_mem_faces
      (chosenCoveringGeometricFaceData K ε.toBoolCocycle.toFiberBundleCore.proj hq).data.face))

open Classical in
omit [FiniteDimensional ℝ E] in
private theorem SimplicialBoolCocycle.coveringFaceAnchor_point_mem
    (ε : SimplicialBoolCocycle K)
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card
      (coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj))))}
    (hq : q ∈ (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj).faces) :
    coveringVertexPoint K ε.toBoolCocycle.toFiberBundleCore.proj
      (ε.coveringFaceAnchor hq) ∈ q := by
  let d := chosenCoveringGeometricFaceData K ε.toBoolCocycle.toFiberBundleCore.proj hq
  have hmem : coveringVertexPoint K ε.toBoolCocycle.toFiberBundleCore.proj
      (ε.coveringFaceAnchor hq) ∈
      d.source.image (coveringVertexPoint K ε.toBoolCocycle.toFiberBundleCore.proj) :=
    Finset.mem_image.mpr
      ⟨ε.coveringFaceAnchor hq, ε.coveringFaceAnchor_mem_source hq, rfl⟩
  exact (congrArg (fun s => coveringVertexPoint K
    ε.toBoolCocycle.toFiberBundleCore.proj (ε.coveringFaceAnchor hq) ∈ s) d.image_eq).mp hmem

open Classical in
omit [FiniteDimensional ℝ E] in
private theorem SimplicialBoolCocycle.mem_chosenCoveringFaceSource_of_point_mem
    (ε : SimplicialBoolCocycle K)
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card
      (coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj))))}
    (hq : q ∈ (coveringComplex K ε.toBoolCocycle.toFiberBundleCore.proj).faces)
    {v : coveringVertex K ε.toBoolCocycle.toFiberBundleCore.proj}
    (hv : coveringVertexPoint K ε.toBoolCocycle.toFiberBundleCore.proj v ∈ q) :
    v ∈ (chosenCoveringGeometricFaceData K
      ε.toBoolCocycle.toFiberBundleCore.proj hq).source := by
  let d := chosenCoveringGeometricFaceData K ε.toBoolCocycle.toFiberBundleCore.proj hq
  have hvImage : coveringVertexPoint K ε.toBoolCocycle.toFiberBundleCore.proj v ∈
      d.source.image (coveringVertexPoint K ε.toBoolCocycle.toFiberBundleCore.proj) := by
    rw [d.image_eq]
    exact hv
  obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hvImage
  have hwv' : w = v := coveringVertexPoint_injective K
    ε.toBoolCocycle.toFiberBundleCore.proj hwv
  exact hwv' ▸ hw

private def orientationSheetSign : Bool → ℤ
  | false => 1
  | true => -1

open Classical in
private noncomputable def orientationCocycleCoveringSign
    {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex
      (barycentricSubdivision K)
      (orientationCocycle hK o).toBoolCocycle.toFiberBundleCore.proj))))) : ℤ :=
  let ε := orientationCocycle hK o
  if hq : q ∈ (coveringComplex (barycentricSubdivision K)
      ε.toBoolCocycle.toFiberBundleCore.proj).faces then
    let v := ε.coveringFaceAnchor hq
    orientationSheetSign v.1.2 * localSubdivisionOrientationSign o
      (coveringVertex.base v)
      (q.image (coveringBaseVertex (barycentricSubdivision K)
        ε.toBoolCocycle.toFiberBundleCore.proj))
  else 0

open Classical in
private theorem orientationCocycleCoveringSign_eq_of_point_mem
    {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex
      (barycentricSubdivision K)
      (orientationCocycle hK o).toBoolCocycle.toFiberBundleCore.proj))))}
    (hq : q ∈ (coveringComplex (barycentricSubdivision K)
      (orientationCocycle hK o).toBoolCocycle.toFiberBundleCore.proj).faces)
    (hqcard : q.card = n + 1)
    {v : coveringVertex (barycentricSubdivision K)
      (orientationCocycle hK o).toBoolCocycle.toFiberBundleCore.proj}
    (hv : coveringVertexPoint (barycentricSubdivision K)
      (orientationCocycle hK o).toBoolCocycle.toFiberBundleCore.proj v ∈ q) :
    orientationCocycleCoveringSign hK o q =
      orientationSheetSign v.1.2 * localSubdivisionOrientationSign o
        (coveringVertex.base v)
        (q.image (coveringBaseVertex (barycentricSubdivision K)
          (orientationCocycle hK o).toBoolCocycle.toFiberBundleCore.proj)) := by
  let B := barycentricSubdivision K
  let ε := orientationCocycle hK o
  let p := ε.toBoolCocycle.toFiberBundleCore.proj
  let d := chosenCoveringGeometricFaceData B p hq
  let a := ε.coveringFaceAnchor hq
  have haSource : a ∈ d.source := ε.coveringFaceAnchor_mem_source hq
  have hvSource : v ∈ d.source := ε.mem_chosenCoveringFaceSource_of_point_mem hq hv
  have hedge : {coveringVertex.base a, coveringVertex.base v} ∈ B.faces := by
    apply B.down_closed d.data.face
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_image.mpr ⟨a, haSource, rfl⟩
      · exact Finset.mem_image.mpr ⟨v, hvSource, rfl⟩
    · exact Finset.insert_nonempty _ _
  have hneighbor : coveringNeighbor ε.isCoveringMap a (coveringVertex.base v) = v :=
    coveringNeighbor_eq_of_mem_faceData ε.isCoveringMap d.data haSource hvSource
  have hside := ε.coveringNeighbor_side a (coveringVertex.base v) hedge
  rw [hneighbor] at hside
  have hparity : ε.parity (coveringVertex.base a) (coveringVertex.base v) =
      Bool.xor a.1.2 v.1.2 := by
    cases haSide : a.1.2 <;> cases hvSide : v.1.2 <;>
      cases hp : ε.parity (coveringVertex.base a) (coveringVertex.base v) <;> simp_all
  have hqBase : q.image (coveringBaseVertex B p) ∈ B.faces := coveringBaseFace_mem hq
  have hinj := coveringBaseVertex_injective_on_geometricFace hq
  have hqBaseCard : (q.image (coveringBaseVertex B p)).card = n + 1 := by
    rw [Finset.card_image_of_injOn hinj, hqcard]
  have haBase : coveringVertex.base a ∈ q.image (coveringBaseVertex B p) := by
    apply Finset.mem_image.mpr
    refine ⟨coveringVertexPoint B p a, ε.coveringFaceAnchor_point_mem hq, ?_⟩
    exact coveringBaseVertex_point B p a
  have hvBase : coveringVertex.base v ∈ q.image (coveringBaseVertex B p) := by
    apply Finset.mem_image.mpr
    refine ⟨coveringVertexPoint B p v, hv, ?_⟩
    exact coveringBaseVertex_point B p v
  have hflip := localSubdivisionOrientationSign_flip_of_orientationCocycle hK o
    hqBase haBase hvBase hqBaseCard a.1.2 v.1.2 hparity
  have hflip' : orientationSheetSign a.1.2 * localSubdivisionOrientationSign o
      (coveringVertex.base a) (q.image (coveringBaseVertex B p)) =
    orientationSheetSign v.1.2 * localSubdivisionOrientationSign o
      (coveringVertex.base v) (q.image (coveringBaseVertex B p)) := by
    cases haValue : a.1.2 <;> cases hvValue : v.1.2 <;>
      simpa [orientationSheetSign, haValue, hvValue] using hflip
  rw [orientationCocycleCoveringSign, dite_eq_left hq]
  simpa only [a, B, p, ε] using hflip'

open Classical in
private theorem orientationCocycleCoveringSign_eq_one_or_neg_one
    {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex
      (barycentricSubdivision K)
      (orientationCocycle hK o).toBoolCocycle.toFiberBundleCore.proj))))}
    (hq : q ∈ (coveringComplex (barycentricSubdivision K)
      (orientationCocycle hK o).toBoolCocycle.toFiberBundleCore.proj).faces)
    (hqcard : q.card = n + 1) :
    orientationCocycleCoveringSign hK o q = 1 ∨
      orientationCocycleCoveringSign hK o q = -1 := by
  let B := barycentricSubdivision K
  let ε := orientationCocycle hK o
  let p := ε.toBoolCocycle.toFiberBundleCore.proj
  let a := ε.coveringFaceAnchor hq
  have hqBase : q.image (coveringBaseVertex B p) ∈ B.faces := coveringBaseFace_mem hq
  have hqBaseCard : (q.image (coveringBaseVertex B p)).card = n + 1 := by
    rw [Finset.card_image_of_injOn (coveringBaseVertex_injective_on_geometricFace hq), hqcard]
  have haBase : coveringVertex.base a ∈ q.image (coveringBaseVertex B p) := by
    apply Finset.mem_image.mpr
    refine ⟨coveringVertexPoint B p a, ε.coveringFaceAnchor_point_mem hq, ?_⟩
    exact coveringBaseVertex_point B p a
  have hsign := orientationCocycleCoveringSign_eq_of_point_mem hK o hq hqcard
    (ε.coveringFaceAnchor_point_mem hq)
  have hlocal := localSubdivisionOrientationSign_eq_one_or_neg_one hK o
    hqBase haBase hqBaseCard
  rw [hsign]
  cases haValue : a.1.2 <;> rcases hlocal with hlocal | hlocal <;>
    simp [a, B, p, ε, orientationSheetSign, hlocal]

open Classical in
omit [Finite K.faces] in
private theorem coveringBaseFace_injective_of_inter_nonempty
    (hp : IsCoveringMap p)
    {q r : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))}
    (hq : q ∈ (coveringComplex K p).faces) (hr : r ∈ (coveringComplex K p).faces)
    (hqr : (q ∩ r).Nonempty)
    (hbase : q.image (coveringBaseVertex K p) = r.image (coveringBaseVertex K p)) :
    q = r := by
  let d := chosenCoveringGeometricFaceData K p hq
  let e := chosenCoveringGeometricFaceData K p hr
  have hsource : d.source.image coveringVertex.base = e.source.image coveringVertex.base := by
    calc
      d.source.image coveringVertex.base =
          (d.source.image (coveringVertexPoint K p)).image (coveringBaseVertex K p) :=
        (coveringBaseVertex_image K p d.source).symm
      _ = q.image (coveringBaseVertex K p) := congrArg
        (fun s => s.image (coveringBaseVertex K p)) d.image_eq
      _ = r.image (coveringBaseVertex K p) := hbase
      _ = (e.source.image (coveringVertexPoint K p)).image (coveringBaseVertex K p) :=
        congrArg (fun s => s.image (coveringBaseVertex K p)) e.image_eq.symm
      _ = e.source.image coveringVertex.base := coveringBaseVertex_image K p e.source
  let z := Classical.choose hqr
  have hz := Classical.choose_spec hqr
  have hzq : z ∈ q := Finset.mem_inter.mp hz |>.1
  have hzr : z ∈ r := Finset.mem_inter.mp hz |>.2
  have hzD : z ∈ d.source.image (coveringVertexPoint K p) := by
    rw [d.image_eq]
    exact hzq
  have hzE : z ∈ e.source.image (coveringVertexPoint K p) := by
    rw [e.image_eq]
    exact hzr
  obtain ⟨v, hvD, hvz⟩ := Finset.mem_image.mp hzD
  obtain ⟨w, hwE, hwz⟩ := Finset.mem_image.mp hzE
  have hvw : v = w := coveringVertexPoint_injective K p (hvz.trans hwz.symm)
  subst w
  have hy : coveringVertex.base v ∈ convexHull ℝ
      ((d.source.image coveringVertex.base : Finset E) : Set E) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, hvD, rfl⟩))
  have hlift : d.data.lift ⟨coveringVertex.base v, hy⟩ =
      e.data.lift ⟨coveringVertex.base v, hsource ▸ hy⟩ :=
    (d.data.vertices v hvD).trans (e.data.vertices v hwE).symm
  have hsources := d.data.eq_of_base_image_eq_of_lift_eq hp e.data hsource hy hlift
  calc
    q = d.source.image (coveringVertexPoint K p) := d.image_eq.symm
    _ = e.source.image (coveringVertexPoint K p) :=
      congrArg (fun s => s.image (coveringVertexPoint K p)) hsources
    _ = r := e.image_eq

open Classical in
noncomputable def orientationCocycleCoveringOrientation
    {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s)) :
    CoherentOrientation n (coveringComplex (barycentricSubdivision K)
      (orientationCocycle hK o).toBoolCocycle.toFiberBundleCore.proj) := by
  cases n with
  | zero =>
      exact Classical.choice (isOrientable_zero (coveringComplex (barycentricSubdivision K)
        (orientationCocycle hK o).toBoolCocycle.toFiberBundleCore.proj))
  | succ n =>
      let B := barycentricSubdivision K
      let ε := orientationCocycle hK o
      let p := ε.toBoolCocycle.toFiberBundleCore.proj
      let C := coveringComplex B p
      refine {
        vertexOrder := coveringOrientationVertexOrder (K := B) (p := p)
        sign := orientationCocycleCoveringSign hK o
        sign_top := ?_
        coherent := ?_ }
      · intro q hq hqcard
        exact orientationCocycleCoveringSign_eq_one_or_neg_one hK o hq hqcard
      · intro f hf hfcard hnotone
        have hB := hK.barycentricSubdivision
        have hC := ε.coveringComplex_isCombinatorialManifoldWithBoundary hB
        have htwo : (faceCofaces C f (n + 2)).card = 2 :=
          (hC.card_faceCofaces_eq_one_or_two C hf hfcard).resolve_left hnotone
        obtain ⟨q, r, hqr, hcofaces⟩ := Finset.card_eq_two.mp htwo
        have hqco : q ∈ faceCofaces C f (n + 2) := by
          rw [hcofaces]
          exact Finset.mem_insert_self q {r}
        have hrco : r ∈ faceCofaces C f (n + 2) := by
          rw [hcofaces]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self r)
        obtain ⟨hq, hqcard, hfq⟩ := (mem_faceCofaces C).mp hqco
        obtain ⟨hr, hrcard, hfr⟩ := (mem_faceCofaces C).mp hrco
        have hfne : f.Nonempty := Finset.card_pos.mp (by omega)
        let z := Classical.choose hfne
        have hzf : z ∈ f := Classical.choose_spec hfne
        have hzC : {z} ∈ C.faces :=
          C.down_closed hf (Finset.singleton_subset_iff.mpr hzf) (Finset.singleton_nonempty z)
        obtain ⟨u, huPoint⟩ := exists_coveringVertexPoint_of_singleton_mem B p hzC
        have huf : coveringVertexPoint B p u ∈ f := by
          rw [huPoint]
          exact hzf
        have huq : coveringVertexPoint B p u ∈ q := hfq huf
        have hur : coveringVertexPoint B p u ∈ r := hfr huf
        let fB := f.image (coveringBaseVertex B p)
        let qB := q.image (coveringBaseVertex B p)
        let rB := r.image (coveringBaseVertex B p)
        have hfB : fB ∈ B.faces := coveringBaseFace_mem hf
        have hqB : qB ∈ B.faces := coveringBaseFace_mem hq
        have hrB : rB ∈ B.faces := coveringBaseFace_mem hr
        have hfBcard : fB.card = n + 1 := by
          dsimp only [fB]
          rw [Finset.card_image_of_injOn
            (coveringBaseVertex_injective_on_geometricFace hf), hfcard]
        have hqBcard : qB.card = n + 2 := by
          dsimp only [qB]
          rw [Finset.card_image_of_injOn
            (coveringBaseVertex_injective_on_geometricFace hq), hqcard]
        have hrBcard : rB.card = n + 2 := by
          dsimp only [rB]
          rw [Finset.card_image_of_injOn
            (coveringBaseVertex_injective_on_geometricFace hr), hrcard]
        have hfqB : fB ⊆ qB := Finset.image_mono (coveringBaseVertex B p) hfq
        have hfrB : fB ⊆ rB := Finset.image_mono (coveringBaseVertex B p) hfr
        have hqrB : qB ≠ rB := by
          intro hbase
          apply hqr
          apply coveringBaseFace_injective_of_inter_nonempty ε.isCoveringMap hq hr
          · exact ⟨coveringVertexPoint B p u, Finset.mem_inter.mpr ⟨huq, hur⟩⟩
          · exact hbase
        have huBase : coveringVertex.base u ∈ fB := by
          apply Finset.mem_image.mpr
          refine ⟨coveringVertexPoint B p u, huf, ?_⟩
          exact coveringBaseVertex_point B p u
        have hsignQ := orientationCocycleCoveringSign_eq_of_point_mem hK o hq hqcard huq
        have hsignR := orientationCocycleCoveringSign_eq_of_point_mem hK o hr hrcard hur
        have hcoeffQ := coveringSimplexBoundaryCoefficient hq hfq (by omega)
        have hcoeffR := coveringSimplexBoundaryCoefficient hr hfr (by omega)
        have hcancel := localSubdivisionOrientationSign_pair_cancel hK o
          hfB hqB hrB huBase hfqB hfrB hqrB hfBcard hqBcard hrBcard
        rw [orientedBoundary_eq_sum_faceCofaces, hcofaces]
        simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton,
          hqr, not_false_eq_true]
        rw [hsignQ, hsignR, hcoeffQ, hcoeffR]
        calc
          _ = orientationSheetSign u.1.2 *
              (localSubdivisionOrientationSign o (coveringVertex.base u) qB *
                  simplexBoundaryCoefficient (linearOrderOfSTO WellOrderingRel) qB fB +
                localSubdivisionOrientationSign o (coveringVertex.base u) rB *
                  simplexBoundaryCoefficient (linearOrderOfSTO WellOrderingRel) rB fB) := by ring
          _ = 0 := by rw [hcancel, mul_zero]

open Classical in
theorem isOrientable_coveringComplex_orientationCocycle
    {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s)) :
    IsOrientable n (coveringComplex (barycentricSubdivision K)
      (orientationCocycle hK o).toBoolCocycle.toFiberBundleCore.proj) :=
  ⟨orientationCocycleCoveringOrientation hK o⟩

open Classical in
theorem IsOrientable.coveringComplex {n : ℕ} (hp : IsCoveringMap p)
    (hK : IsCombinatorialManifoldWithBoundary n K) (h : IsOrientable n K) :
    IsOrientable n (coveringComplex K p) := by
  cases n with
  | zero => exact isOrientable_zero (PiecewiseLinear.coveringComplex K p)
  | succ n =>
      obtain ⟨o₀⟩ := h
      let o := o₀.changeVertexOrder (linearOrderOfSTO WellOrderingRel)
      refine ⟨{
        vertexOrder := coveringOrientationVertexOrder (K := K) (p := p)
        sign := fun q => o.sign (q.image (coveringBaseVertex K p))
        sign_top := ?_
        coherent := ?_ }⟩
      · intro q hq hqcard
        refine o.sign_top _ (coveringBaseFace_mem hq) ?_
        rw [Finset.card_image_of_injOn (coveringBaseVertex_injective_on_geometricFace hq), hqcard]
      · intro f hf hfcard hnotone
        have hCman : IsCombinatorialManifoldWithBoundary (n + 1)
            (PiecewiseLinear.coveringComplex K p) :=
          isCombinatorialManifoldWithBoundary_coveringComplex K p hp hK
        have htwo : (faceCofaces (PiecewiseLinear.coveringComplex K p) f (n + 2)).card = 2 :=
          (hCman.card_faceCofaces_eq_one_or_two (PiecewiseLinear.coveringComplex K p) hf
            hfcard).resolve_left hnotone
        obtain ⟨q, w, hqw, hcofaces⟩ := Finset.card_eq_two.mp htwo
        have hqco : q ∈ faceCofaces (PiecewiseLinear.coveringComplex K p) f (n + 2) := by
          rw [hcofaces]
          exact Finset.mem_insert_self q {w}
        have hwco : w ∈ faceCofaces (PiecewiseLinear.coveringComplex K p) f (n + 2) := by
          rw [hcofaces]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w)
        obtain ⟨hq, hqcard, hfq⟩ :=
          (mem_faceCofaces (PiecewiseLinear.coveringComplex K p)).mp hqco
        obtain ⟨hw, hwcard, hfw⟩ :=
          (mem_faceCofaces (PiecewiseLinear.coveringComplex K p)).mp hwco
        have hfB : f.image (coveringBaseVertex K p) ∈ K.faces := coveringBaseFace_mem hf
        have hqB : q.image (coveringBaseVertex K p) ∈ K.faces := coveringBaseFace_mem hq
        have hwB : w.image (coveringBaseVertex K p) ∈ K.faces := coveringBaseFace_mem hw
        have hfBcard : (f.image (coveringBaseVertex K p)).card = n + 1 := by
          rw [Finset.card_image_of_injOn (coveringBaseVertex_injective_on_geometricFace hf),
            hfcard]
        have hqBcard : (q.image (coveringBaseVertex K p)).card = n + 2 := by
          rw [Finset.card_image_of_injOn (coveringBaseVertex_injective_on_geometricFace hq),
            hqcard]
        have hwBcard : (w.image (coveringBaseVertex K p)).card = n + 2 := by
          rw [Finset.card_image_of_injOn (coveringBaseVertex_injective_on_geometricFace hw),
            hwcard]
        have hfqB : f.image (coveringBaseVertex K p) ⊆ q.image (coveringBaseVertex K p) :=
          Finset.image_mono (coveringBaseVertex K p) hfq
        have hfwB : f.image (coveringBaseVertex K p) ⊆ w.image (coveringBaseVertex K p) :=
          Finset.image_mono (coveringBaseVertex K p) hfw
        obtain ⟨z, hzf⟩ : f.Nonempty := Finset.card_pos.mp (by omega)
        have hqwB : q.image (coveringBaseVertex K p) ≠ w.image (coveringBaseVertex K p) := by
          intro hbase
          exact hqw (coveringBaseFace_injective_of_inter_nonempty hp hq hw
            ⟨z, Finset.mem_inter.mpr ⟨hfq hzf, hfw hzf⟩⟩ hbase)
        have hpair : ({q.image (coveringBaseVertex K p), w.image (coveringBaseVertex K p)} :
            Finset (Finset E)).card = 2 := Finset.card_pair hqwB
        have hsub : ({q.image (coveringBaseVertex K p), w.image (coveringBaseVertex K p)} :
            Finset (Finset E)) ⊆ faceCofaces K (f.image (coveringBaseVertex K p)) (n + 2) := by
          intro s hs
          rcases Finset.mem_insert.mp hs with hsq | hsw
          · rw [hsq]
            exact (mem_faceCofaces K).mpr ⟨hqB, hqBcard, hfqB⟩
          · rw [Finset.mem_singleton.mp hsw]
            exact (mem_faceCofaces K).mpr ⟨hwB, hwBcard, hfwB⟩
        have hle : (faceCofaces K (f.image (coveringBaseVertex K p)) (n + 2)).card ≤ 2 := by
          rcases hK.card_faceCofaces_eq_one_or_two K hfB hfBcard with hcard | hcard <;> omega
        have heq : ({q.image (coveringBaseVertex K p), w.image (coveringBaseVertex K p)} :
            Finset (Finset E)) = faceCofaces K (f.image (coveringBaseVertex K p)) (n + 2) :=
          Finset.eq_of_subset_of_card_le hsub (by rw [hpair]; exact hle)
        have hnotone' : (faceCofaces K (f.image (coveringBaseVertex K p)) (n + 2)).card ≠ 1 := by
          rw [← heq, hpair]
          omega
        have hcoh : o.sign (q.image (coveringBaseVertex K p)) *
              simplexBoundaryCoefficient (linearOrderOfSTO WellOrderingRel)
                (q.image (coveringBaseVertex K p)) (f.image (coveringBaseVertex K p)) +
            o.sign (w.image (coveringBaseVertex K p)) *
              simplexBoundaryCoefficient (linearOrderOfSTO WellOrderingRel)
                (w.image (coveringBaseVertex K p)) (f.image (coveringBaseVertex K p)) = 0 := by
          have hzero := o.coherent (f.image (coveringBaseVertex K p)) hfB hfBcard hnotone'
          rw [orientedBoundary_eq_sum_faceCofaces, ← heq, Finset.sum_pair hqwB] at hzero
          exact hzero
        rw [orientedBoundary_eq_sum_faceCofaces, hcofaces, Finset.sum_pair hqw,
          coveringSimplexBoundaryCoefficient hq hfq (by omega),
          coveringSimplexBoundaryCoefficient hw hfw (by omega)]
        exact hcoh

end DifferentialGeometry.Topology.PiecewiseLinear
