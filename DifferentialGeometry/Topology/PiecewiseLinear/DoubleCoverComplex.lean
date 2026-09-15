import DifferentialGeometry.Topology.Covering.BoolCocycle
import DifferentialGeometry.Topology.Covering.DoubleCoverComponents
import DifferentialGeometry.Topology.Covering.SectionSplit
import DifferentialGeometry.Topology.FiberBundle.FiniteClosed
import DifferentialGeometry.Topology.PiecewiseLinear.OpenStar
import Mathlib.Analysis.Convex.PathConnected

noncomputable section

open Bundle Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
structure SimplicialBoolCocycle (K : Geometry.SimplicialComplex ℝ E) where
  parity : E → E → Bool
  symm : ∀ a b, {a, b} ∈ K.faces → parity a b = parity b a
  self : ∀ a, {a} ∈ K.faces → parity a a = false
  cocycle : ∀ a b c, {a, b, c} ∈ K.faces →
    Bool.xor (parity a b) (parity b c) = parity a c

namespace SimplicialBoolCocycle

variable {K : Geometry.SimplicialComplex ℝ E}

open Classical in
def IsCoboundary (ε : SimplicialBoolCocycle K) : Prop :=
  ∃ δ : E → Bool, ∀ a b, {a, b} ∈ K.faces →
    ε.parity a b = Bool.xor (δ a) (δ b)

open Classical in
theorem face_of_mem_openStar {s : Finset E} (hs : s.Nonempty) {x : E}
    (hx : ∀ v ∈ s, x ∈ openStar K v) : s ∈ K.faces := by
  obtain ⟨v, hv⟩ := hs
  obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex K (hx v hv).1
  apply K.down_closed ht
  · intro w hw
    by_contra hwt
    exact (hx w hw).2 (mem_iUnion₂.mpr
      ⟨t, ⟨ht, hwt⟩, openSimplex_subset_convexHull t hxt⟩)
  · exact ⟨v, hv⟩

open Classical in
theorem mem_openStar_self {v : E} (hv : {v} ∈ K.faces) : v ∈ openStar K v :=
  (mem_openStar_iff K hv).2 (Or.inl rfl)

open Classical in
theorem starConvex_openStar {v : E} (hv : {v} ∈ K.faces) :
    StarConvex ℝ v (openStar K v) := by
  rw [starConvex_iff_forall_pos (mem_openStar_self hv)]
  intro y hy a b ha hb hab
  rcases (mem_openStar_iff K hv).1 hy with rfl | ⟨z, hz, s, hs, hs', rfl⟩
  · simpa [← add_smul, hab]
  · apply (mem_openStar_iff K hv).2
    refine Or.inr ⟨z, hz, b * s, mul_pos hb hs, ?_, ?_⟩
    · nlinarith
    · rw [smul_add, smul_smul]
      rw [← add_assoc, ← add_smul, hab, one_smul]

noncomputable def openStarSubtypeHomeomorph {v : E} :
    ((Subtype.val : K.space → E) ⁻¹' openStar K v) ≃ₜ openStar K v where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, openStar_subset_space K v x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

open Classical in
theorem connectedSpace_openStarSubtype {v : E} (hv : {v} ∈ K.faces) :
    ConnectedSpace ((Subtype.val : K.space → E) ⁻¹' openStar K v) := by
  have h : ConnectedSpace (openStar K v) :=
    isConnected_iff_connectedSpace.mp
      ((starConvex_openStar hv).isPathConnected (mem_openStar_self hv)).isConnected
  exact (openStarSubtypeHomeomorph (K := K) (v := v)).connectedSpace_iff.mpr h

open Classical in
noncomputable def toBoolCocycle [Finite K.faces] (ε : SimplicialBoolCocycle K) :
    DifferentialGeometry.Topology.BoolCocycle {v // {v} ∈ K.faces} K.space where
  baseSet v := (Subtype.val : K.space → E) ⁻¹' openStar K v
  isOpen_baseSet v := isOpen_preimage_openStar K v
  indexAt x := ⟨Classical.choose (exists_vertex_mem_openStar K x.2),
    (Classical.choose_spec (exists_vertex_mem_openStar K x.2)).1⟩
  mem_baseSet_at x := (Classical.choose_spec (exists_vertex_mem_openStar K x.2)).2
  parity v w _ := ε.parity v w
  parity_self v _ _ := ε.self v v.2
  continuousOn_parity _ _ := continuousOn_const
  parity_comp i j k x hx := by
    apply ε.cocycle
    refine face_of_mem_openStar (K := K)
      (s := {(i : E), (j : E), (k : E)}) (x := (x : E)) (by simp) ?_
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hx.1.1
    · exact hx.1.2
    · exact hx.2

theorem isCoveringMap [Finite K.faces] (ε : SimplicialBoolCocycle K) :
    IsCoveringMap ε.toBoolCocycle.toFiberBundleCore.proj :=
  ε.toBoolCocycle.isCoveringMap_proj

theorem card_fiber [Finite K.faces] (ε : SimplicialBoolCocycle K) (x : K.space) :
    Nat.card (ε.toBoolCocycle.toFiberBundleCore.proj ⁻¹' {x}) = 2 := by
  rw [Nat.card_congr
    ((ε.toBoolCocycle.toFiberBundleCore.localTrivAt x).preimageSingletonHomeomorph
      (ε.toBoolCocycle.toFiberBundleCore.mem_localTrivAt_baseSet x)).toEquiv]
  simp

def deck [Finite K.faces] (ε : SimplicialBoolCocycle K)
    (z : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) :
    ε.toBoolCocycle.toFiberBundleCore.TotalSpace :=
  ⟨z.1, !z.2⟩

theorem deck_projects [Finite K.faces] (ε : SimplicialBoolCocycle K)
    (z : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) :
    ε.toBoolCocycle.toFiberBundleCore.proj (ε.deck z) =
      ε.toBoolCocycle.toFiberBundleCore.proj z :=
  rfl

theorem deck_ne_self [Finite K.faces] (ε : SimplicialBoolCocycle K)
    (z : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) : ε.deck z ≠ z := by
  intro h
  have hs := congrArg
    (fun w : ε.toBoolCocycle.toFiberBundleCore.TotalSpace => w.2) h
  rcases z with ⟨z, side⟩
  cases side <;> simp [deck] at hs

theorem fiber_cases [Finite K.faces] (ε : SimplicialBoolCocycle K)
    (x y : ε.toBoolCocycle.toFiberBundleCore.TotalSpace)
    (h : ε.toBoolCocycle.toFiberBundleCore.proj y =
      ε.toBoolCocycle.toFiberBundleCore.proj x) :
    y = x ∨ y = ε.deck x := by
  rcases x with ⟨x, s⟩
  rcases y with ⟨y, t⟩
  change y = x at h
  subst y
  cases s <;> cases t <;> simp [deck]

theorem deck_chart [Finite K.faces] (ε : SimplicialBoolCocycle K)
    (i : {v // {v} ∈ K.faces})
    (z : ε.toBoolCocycle.toFiberBundleCore.TotalSpace) :
    ((ε.toBoolCocycle.toFiberBundleCore.localTriv i) (ε.deck z)).2 =
      !((ε.toBoolCocycle.toFiberBundleCore.localTriv i z).2) := by
  change Bool.xor (!z.2) (ε.parity _ _) = !(Bool.xor z.2 (ε.parity _ _))
  exact Bool.not_xor _ _

theorem deck_continuous [Finite K.faces] (ε : SimplicialBoolCocycle K) :
    Continuous ε.deck := by
  rw [continuous_iff_continuousAt]
  intro z
  rw [FiberBundle.continuousAt_totalSpace Bool]
  refine ⟨ε.isCoveringMap.continuous.continuousAt, ?_⟩
  let T := ε.toBoolCocycle.toFiberBundleCore.localTrivAt z.1
  have hT : ContinuousAt
      (fun w : ε.toBoolCocycle.toFiberBundleCore.TotalSpace => (T w).2) z :=
    (T.continuousAt FiberBundle.mem_trivializationAt_proj_source).snd
  have hn : Continuous (fun side : Bool => !side) := continuous_of_discreteTopology
  convert hn.continuousAt.comp hT using 1
  ext w
  exact ε.deck_chart (ε.toBoolCocycle.toFiberBundleCore.indexAt z.1) w

def openStarVertex (v : {v // {v} ∈ K.faces}) :
    ((Subtype.val : K.space → E) ⁻¹' openStar K v) :=
  ⟨⟨v, openStar_subset_space K v (mem_openStar_self v.2)⟩, mem_openStar_self v.2⟩

theorem mem_openStar_of_mem_openSimplex {t : Finset E} (ht : t ∈ K.faces) {x v : E}
    (hx : x ∈ openSimplex t) (hv : v ∈ t) : x ∈ openStar K v :=
  ⟨K.convexHull_subset_space ht (openSimplex_subset_convexHull t hx),
    notMem_avoidingUnion_of_mem_openSimplex K ht hx hv⟩

open Classical in
theorem exists_section_of_isCoboundary [Finite K.faces] (ε : SimplicialBoolCocycle K)
    (hε : ε.IsCoboundary) :
    ∃ s : C(K.space, ε.toBoolCocycle.toFiberBundleCore.TotalSpace),
      Function.RightInverse s ε.toBoolCocycle.toFiberBundleCore.proj := by
  obtain ⟨δ, hδ⟩ := hε
  let C := ε.toBoolCocycle
  refine ⟨⟨fun x => ⟨x, δ (C.indexAt x)⟩, ?_⟩, fun _ => rfl⟩
  rw [continuous_iff_continuousAt]
  intro x
  rw [FiberBundle.continuousAt_totalSpace Bool]
  refine ⟨continuous_id.continuousAt, ?_⟩
  let i := C.indexAt x
  have hbase : C.baseSet i ∈ 𝓝 x :=
    (C.isOpen_baseSet i).mem_nhds (C.mem_baseSet_at x)
  refine (continuousAt_const : ContinuousAt (fun _ : K.space => δ (i : E)) x).congr_of_eventuallyEq ?_
  filter_upwards [hbase] with y hy
  have hj : (y : E) ∈ openStar K (C.indexAt y) := C.mem_baseSet_at y
  have hi : (y : E) ∈ openStar K i := hy
  have hface : {(C.indexAt y : E), (i : E)} ∈ K.faces := by
    apply face_of_mem_openStar (s := {(C.indexAt y : E), (i : E)})
      (x := (y : E)) (by simp)
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hj
    · exact hi
  change Bool.xor (δ (C.indexAt y)) (ε.parity (C.indexAt y) i) = δ i
  rw [hδ _ _ hface]
  simp

open Classical in
theorem isCoboundary_of_section [Finite K.faces] (ε : SimplicialBoolCocycle K)
    (s : C(K.space, ε.toBoolCocycle.toFiberBundleCore.TotalSpace))
    (hs : Function.RightInverse s ε.toBoolCocycle.toFiberBundleCore.proj) :
    ε.IsCoboundary := by
  let C := ε.toBoolCocycle
  let δ : E → Bool := fun v =>
    if hv : {v} ∈ K.faces then
      C.sectionCoord s hs ⟨v, hv⟩ (openStarVertex ⟨v, hv⟩)
    else false
  refine ⟨δ, ?_⟩
  intro a b hab
  have ha : {a} ∈ K.faces :=
    K.down_closed hab (by simp) (Finset.singleton_nonempty a)
  have hb : {b} ∈ K.faces :=
    K.down_closed hab (by simp) (Finset.singleton_nonempty b)
  let i : {v // {v} ∈ K.faces} := ⟨a, ha⟩
  let j : {v // {v} ∈ K.faces} := ⟨b, hb⟩
  have hopen : ({a, b} : Finset E).centroid ℝ id ∈ openSimplex {a, b} :=
    centroid_mem_openSimplex (K.nonempty_of_mem_faces hab)
  let x : K.space :=
    ⟨({a, b} : Finset E).centroid ℝ id,
      K.convexHull_subset_space hab (openSimplex_subset_convexHull _ hopen)⟩
  have hxi : x ∈ C.baseSet i := by
    exact mem_openStar_of_mem_openSimplex hab hopen (by simp [i])
  have hxj : x ∈ C.baseSet j := by
    exact mem_openStar_of_mem_openSimplex hab hopen (by simp [j])
  let xi : C.baseSet i := ⟨x, hxi⟩
  let xj : C.baseSet j := ⟨x, hxj⟩
  have hc := C.sectionCoord_change s hs i j x hxi hxj
  have hci : C.sectionCoord s hs i xi = C.sectionCoord s hs i (openStarVertex i) := by
    let _ : ConnectedSpace (C.baseSet i) := connectedSpace_openStarSubtype i.2
    exact (C.isLocallyConstant_sectionCoord s hs i).apply_eq_of_preconnectedSpace
      xi (openStarVertex i)
  have hcj : C.sectionCoord s hs j xj = C.sectionCoord s hs j (openStarVertex j) := by
    let _ : ConnectedSpace (C.baseSet j) := connectedSpace_openStarSubtype j.2
    exact (C.isLocallyConstant_sectionCoord s hs j).apply_eq_of_preconnectedSpace
      xj (openStarVertex j)
  rw [hci, hcj] at hc
  have hδi : δ a = C.sectionCoord s hs i (openStarVertex i) := by
    simp [δ, i, ha]
  have hδj : δ b = C.sectionCoord s hs j (openStarVertex j) := by
    simp [δ, j, hb]
  rw [← hδi, ← hδj] at hc
  change ε.parity a b = Bool.xor (δ a) (δ b)
  calc
    ε.parity a b = Bool.xor (δ a) (Bool.xor (δ a) (ε.parity a b)) := by simp
    _ = Bool.xor (δ a) (δ b) := congrArg (Bool.xor (δ a)) hc.symm

theorem not_connectedSpace_of_isCoboundary [Finite K.faces] [Nonempty K.space]
    (ε : SimplicialBoolCocycle K) (hε : ε.IsCoboundary) :
    ¬ ConnectedSpace ε.toBoolCocycle.toFiberBundleCore.TotalSpace := by
  obtain ⟨s, hs⟩ := ε.exists_section_of_isCoboundary hε
  exact DifferentialGeometry.Topology.Covering.not_connected_of_double_cover_section
    ε.isCoveringMap ε.deck ε.deck_continuous ε.deck_projects ε.deck_ne_self ε.fiber_cases s hs

open Classical in
theorem isCoboundary_of_not_connectedSpace [Finite K.faces] [ConnectedSpace K.space]
    (ε : SimplicialBoolCocycle K)
    (hnot : ¬ ConnectedSpace ε.toBoolCocycle.toFiberBundleCore.TotalSpace) :
    ε.IsCoboundary := by
  let _ : Nonempty ε.toBoolCocycle.toFiberBundleCore.TotalSpace :=
    ⟨⟨Classical.choice inferInstance, false⟩⟩
  obtain ⟨s, hs⟩ :=
    DifferentialGeometry.Topology.Covering.exists_section_of_not_connected_double_cover
      ε.isCoveringMap
      (DifferentialGeometry.Topology.FiberBundle.isClosedMap_projection_of_finite
        ε.toBoolCocycle.toFiberBundleCore)
      ε.deck ε.fiber_cases hnot
  exact ε.isCoboundary_of_section s hs

open Classical in
theorem connectedSpace_iff [Finite K.faces] [ConnectedSpace K.space]
    (ε : SimplicialBoolCocycle K) :
    ConnectedSpace ε.toBoolCocycle.toFiberBundleCore.TotalSpace ↔ ¬ ε.IsCoboundary := by
  constructor
  · intro hconn hε
    exact ε.not_connectedSpace_of_isCoboundary hε hconn
  · intro hε
    by_contra hnot
    exact hε (ε.isCoboundary_of_not_connectedSpace hnot)

end SimplicialBoolCocycle

end DifferentialGeometry.Topology.PiecewiseLinear
