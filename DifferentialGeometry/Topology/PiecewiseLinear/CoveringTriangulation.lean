import DifferentialGeometry.Topology.Covering.Separation
import DifferentialGeometry.Topology.PiecewiseLinear.CoveringLift
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBall
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialImage

noncomputable section

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X' : Type u} [TopologicalSpace X']

def coveringVertex (K : Geometry.SimplicialComplex ℝ E) (p : X' → K.space) :=
  {x : X' // ((p x : K.space) : E) ∈ K.vertices}

namespace coveringVertex

variable {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space}

def base (v : coveringVertex K p) : E := p v.1

omit [TopologicalSpace X'] in
@[simp]
theorem base_mem_vertices (v : coveringVertex K p) : base v ∈ K.vertices := v.2

omit [TopologicalSpace X'] in
@[simp]
theorem singleton_base_mem_faces (v : coveringVertex K p) : {base v} ∈ K.faces := v.2

omit [TopologicalSpace X'] in
theorem finite (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {p : X' → K.space} (hfin : ∀ x, (p ⁻¹' {x}).Finite) :
    Finite (coveringVertex K p) := by
  have hvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  have hpre : ((fun x : X' => ((p x : K.space) : E)) ⁻¹' K.vertices).Finite :=
    hvertices.preimage' fun y hy => by
      have hyK : y ∈ K.space := K.subset_space hy (by simp)
      have heq : (fun x : X' => ((p x : K.space) : E)) ⁻¹' {y} =
          p ⁻¹' {(⟨y, hyK⟩ : K.space)} := by
        ext x
        simp only [mem_preimage, mem_singleton_iff, Subtype.ext_iff]
      rw [heq]
      exact hfin ⟨y, hyK⟩
  exact hpre.to_subtype

end coveringVertex

open Classical in
structure CoveringFaceData (K : Geometry.SimplicialComplex ℝ E) (p : X' → K.space)
    (s : Finset (coveringVertex K p)) where
  face : s.image coveringVertex.base ∈ K.faces
  lift : C(convexHull ℝ ((s.image coveringVertex.base : Finset E) : Set E), X')
  projection : ∀ x, p (lift x) = ⟨x, K.convexHull_subset_space face x.2⟩
  vertices : ∀ (v) (hv : v ∈ s),
    lift ⟨coveringVertex.base v,
      subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, hv, rfl⟩))⟩ = v.1

namespace CoveringFaceData

variable {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space}
  {s t : Finset (coveringVertex K p)}

open Classical in
def mono (d : CoveringFaceData K p s) (hts : t ⊆ s) (ht : t.Nonempty) :
    CoveringFaceData K p t := by
  have hbase : t.image coveringVertex.base ⊆ s.image coveringVertex.base :=
    Finset.image_mono coveringVertex.base hts
  have htface : t.image coveringVertex.base ∈ K.faces :=
    K.down_closed d.face hbase (Finset.image_nonempty.mpr ht)
  let i : C(convexHull ℝ ((t.image coveringVertex.base : Finset E) : Set E),
      convexHull ℝ ((s.image coveringVertex.base : Finset E) : Set E)) :=
    ⟨fun x => ⟨x, convexHull_mono (Finset.coe_subset.mpr hbase) x.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  refine ⟨htface, d.lift.comp i, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    exact congrArg Subtype.val (d.projection (i x))
  · intro v hv
    exact d.vertices v (hts hv)

end CoveringFaceData

open Classical in
theorem CoveringFaceData.base_injective
    {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space}
    {s : Finset (coveringVertex K p)} (d : CoveringFaceData K p s) :
    Set.InjOn (coveringVertex.base (K := K) (p := p)) (s : Set _) := by
  intro v hv w hw hbase
  apply Subtype.ext
  have hx : (⟨coveringVertex.base v,
      subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, hv, rfl⟩))⟩ :
        convexHull ℝ ((s.image coveringVertex.base : Finset E) : Set E)) =
      ⟨coveringVertex.base w,
        subset_convexHull ℝ _ (Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨w, hw, rfl⟩))⟩ := Subtype.ext hbase
  exact (d.vertices v hv).symm.trans ((congrArg d.lift hx).trans (d.vertices w hw))

def faceInclusion (K : Geometry.SimplicialComplex ℝ E) {s : Finset E}
    (hs : s ∈ K.faces) : C(convexHull ℝ (s : Set E), K.space) :=
  ⟨fun x => ⟨x, K.convexHull_subset_space hs x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem IsCoveringMap.exists_unique_lift_of_face [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space} (hp : IsCoveringMap p)
    {s : Finset E} (hs : s ∈ K.faces) (x₀ : convexHull ℝ (s : Set E)) (e₀ : X')
    (h₀ : p e₀ = faceInclusion K hs x₀) :
    ∃! g : C(convexHull ℝ (s : Set E), X'),
      p ∘ g = faceInclusion K hs ∧ g x₀ = e₀ := by
  have hcard : s.card = (s.card - 1) + 1 :=
    (Nat.sub_add_cancel (Finset.card_pos.mpr (K.nonempty_of_mem_faces hs))).symm
  exact hp.exists_unique_lift_of_isPLBall
    (isPLBall_convexHull_of_affineIndependent s (K.indep hs) hcard)
    (faceInclusion K hs) x₀ e₀ h₀

open Classical in
def coveringEdgeLift [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space} (hp : IsCoveringMap p)
    (v : coveringVertex K p) (w : E) (hvw : {coveringVertex.base v, w} ∈ K.faces) :
    C(convexHull ℝ (({coveringVertex.base v, w} : Finset E) : Set E), X') := by
  let x₀ : convexHull ℝ (({coveringVertex.base v, w} : Finset E) : Set E) :=
    ⟨coveringVertex.base v, subset_convexHull ℝ _ (by simp)⟩
  have h₀ : p v.1 = faceInclusion K hvw x₀ := by
    apply Subtype.ext
    rfl
  exact Classical.choose
    (DifferentialGeometry.Topology.PiecewiseLinear.IsCoveringMap.exists_unique_lift_of_face
      hp hvw x₀ v.1 h₀)

open Classical in
theorem coveringEdgeLift_projection [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space} (hp : IsCoveringMap p)
    (v : coveringVertex K p) (w : E) (hvw : {coveringVertex.base v, w} ∈ K.faces) :
    p ∘ coveringEdgeLift hp v w hvw = faceInclusion K hvw := by
  unfold coveringEdgeLift
  dsimp only
  exact (Classical.choose_spec
    (DifferentialGeometry.Topology.PiecewiseLinear.IsCoveringMap.exists_unique_lift_of_face hp hvw
      (⟨coveringVertex.base v, subset_convexHull ℝ _ (by simp)⟩ :
        convexHull ℝ (({coveringVertex.base v, w} : Finset E) : Set E)) v.1
      (by apply Subtype.ext; rfl))).1.1

open Classical in
theorem coveringEdgeLift_source [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space} (hp : IsCoveringMap p)
    (v : coveringVertex K p) (w : E) (hvw : {coveringVertex.base v, w} ∈ K.faces) :
    coveringEdgeLift hp v w hvw
      ⟨coveringVertex.base v, subset_convexHull ℝ _ (by simp)⟩ = v.1 := by
  unfold coveringEdgeLift
  dsimp only
  exact (Classical.choose_spec
    (DifferentialGeometry.Topology.PiecewiseLinear.IsCoveringMap.exists_unique_lift_of_face hp hvw
      (⟨coveringVertex.base v, subset_convexHull ℝ _ (by simp)⟩ :
        convexHull ℝ (({coveringVertex.base v, w} : Finset E) : Set E)) v.1
      (by apply Subtype.ext; rfl))).1.2

open Classical in
def coveringVertexOfLift {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space}
    {s : Finset E} (hs : s ∈ K.faces)
    (g : C(convexHull ℝ (s : Set E), X'))
    (hg : p ∘ g = faceInclusion K hs) (v : s) : coveringVertex K p := by
  refine ⟨g ⟨v, subset_convexHull ℝ _ (Finset.mem_coe.mpr v.2)⟩, ?_⟩
  have hv := congrArg Subtype.val
    (congrFun hg ⟨v, subset_convexHull ℝ _ (Finset.mem_coe.mpr v.2)⟩)
  have hv' : ((p (g ⟨v, subset_convexHull ℝ _
      (Finset.mem_coe.mpr v.2)⟩) : K.space) : E) = v := by
    simpa only [Function.comp_apply, faceInclusion, ContinuousMap.coe_mk] using hv
  have hsv : {v.1} ∈ K.faces :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr v.2) (Finset.singleton_nonempty _)
  change {((p (g ⟨v, subset_convexHull ℝ _ (Finset.mem_coe.mpr v.2)⟩) : K.space) : E)} ∈
    K.faces
  rw [hv']
  exact hsv

open Classical in
@[simp]
theorem coveringVertexOfLift_base {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space}
    {s : Finset E} (hs : s ∈ K.faces)
    (g : C(convexHull ℝ (s : Set E), X'))
    (hg : p ∘ g = faceInclusion K hs) (v : s) :
    coveringVertex.base (coveringVertexOfLift hs g hg v) = v := by
  exact congrArg Subtype.val
    (congrFun hg ⟨v, subset_convexHull ℝ _ (Finset.mem_coe.mpr v.2)⟩)

open Classical in
def coveringNeighbor [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space} (hp : IsCoveringMap p)
    (v : coveringVertex K p) (w : E) : coveringVertex K p :=
  if h : {coveringVertex.base v, w} ∈ K.faces then
    coveringVertexOfLift h (coveringEdgeLift hp v w h)
      (coveringEdgeLift_projection hp v w h) ⟨w, by simp⟩
  else v

open Classical in
theorem coveringNeighbor_base_of_face [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space} (hp : IsCoveringMap p)
    (v : coveringVertex K p) (w : E) (hvw : {coveringVertex.base v, w} ∈ K.faces) :
    coveringVertex.base (coveringNeighbor hp v w) = w := by
  rw [coveringNeighbor, dif_pos hvw, coveringVertexOfLift_base]

open Classical in
def coveringFaceVertices {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space}
    {s : Finset E} (hs : s ∈ K.faces)
    (g : C(convexHull ℝ (s : Set E), X'))
    (hg : p ∘ g = faceInclusion K hs) : Finset (coveringVertex K p) :=
  s.attach.image (coveringVertexOfLift hs g hg)

open Classical in
theorem coveringFaceVertices_base_image {K : Geometry.SimplicialComplex ℝ E}
    {p : X' → K.space} {s : Finset E} (hs : s ∈ K.faces)
    (g : C(convexHull ℝ (s : Set E), X'))
    (hg : p ∘ g = faceInclusion K hs) :
    (coveringFaceVertices hs g hg).image coveringVertex.base = s := by
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hu
    rw [coveringVertexOfLift_base]
    exact w.2
  · intro v hv
    have hw : (⟨v, hv⟩ : s) ∈ s.attach := Finset.mem_attach _ _
    exact Finset.mem_image.mpr
      ⟨coveringVertexOfLift hs g hg ⟨v, hv⟩,
        Finset.mem_image.mpr ⟨⟨v, hv⟩, hw, rfl⟩, by simp⟩

open Classical in
def coveringFaceDataOfLift {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space}
    {s : Finset E} (hs : s ∈ K.faces)
    (g : C(convexHull ℝ (s : Set E), X'))
    (hg : p ∘ g = faceInclusion K hs) :
    CoveringFaceData K p (coveringFaceVertices hs g hg) := by
  let b := coveringFaceVertices hs g hg
  have hb : b.image coveringVertex.base = s := coveringFaceVertices_base_image hs g hg
  have hbface : b.image coveringVertex.base ∈ K.faces := hb ▸ hs
  let i : C(convexHull ℝ ((b.image coveringVertex.base : Finset E) : Set E),
      convexHull ℝ (s : Set E)) :=
    ⟨fun x => ⟨x, hb ▸ x.2⟩, continuous_subtype_val.subtype_mk _⟩
  refine ⟨hbface, g.comp i, ?_, ?_⟩
  · intro x
    exact congrFun hg (i x)
  · intro v hv
    obtain ⟨w, -, hvw⟩ := Finset.mem_image.mp hv
    have hbase : coveringVertex.base v = w := by
      rw [← hvw]
      exact coveringVertexOfLift_base hs g hg w
    change g (i ⟨coveringVertex.base v, _⟩) = v.1
    rw [show i ⟨coveringVertex.base v, _⟩ =
      ⟨w, subset_convexHull ℝ _ (Finset.mem_coe.mpr w.2)⟩ from Subtype.ext hbase]
    exact congrArg Subtype.val hvw

open Classical in
theorem coveringFaceDataOfLift_apply {K : Geometry.SimplicialComplex ℝ E}
    {p : X' → K.space} {s : Finset E} (hs : s ∈ K.faces)
    (g : C(convexHull ℝ (s : Set E), X'))
    (hg : p ∘ g = faceInclusion K hs) (x : convexHull ℝ (s : Set E)) :
    (coveringFaceDataOfLift hs g hg).lift
      ⟨x, by rw [coveringFaceVertices_base_image hs g hg]; exact x.2⟩ = g x := by
  rfl

open Classical in
theorem CoveringFaceData.lift_eq_of_mem_inter [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space} (hp : IsCoveringMap p)
    {s t : Finset (coveringVertex K p)} (d : CoveringFaceData K p s)
    (e : CoveringFaceData K p t) {y : E}
    (hy : y ∈ convexHull ℝ (((s ∩ t).image coveringVertex.base : Finset E) : Set E)) :
    d.lift ⟨y, convexHull_mono (Finset.coe_subset.mpr
        (Finset.image_mono coveringVertex.base Finset.inter_subset_left)) hy⟩ =
      e.lift ⟨y, convexHull_mono (Finset.coe_subset.mpr
        (Finset.image_mono coveringVertex.base Finset.inter_subset_right)) hy⟩ := by
  have hu : (s ∩ t).Nonempty :=
    Finset.image_nonempty.mp (nonempty_of_mem_convexHull hy)
  let du := d.mono Finset.inter_subset_left hu
  let de := e.mono Finset.inter_subset_right hu
  let v : coveringVertex K p := Classical.choose hu
  have hv : v ∈ s ∩ t := Classical.choose_spec hu
  let x₀ : convexHull ℝ (((s ∩ t).image coveringVertex.base : Finset E) : Set E) :=
    ⟨coveringVertex.base v,
      subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, hv, rfl⟩))⟩
  have h₀ : p v.1 = faceInclusion K du.face x₀ := by
    apply Subtype.ext
    rfl
  obtain ⟨g, hg, huniq⟩ :=
    DifferentialGeometry.Topology.PiecewiseLinear.IsCoveringMap.exists_unique_lift_of_face
      hp du.face x₀ v.1 h₀
  have hdu : p ∘ du.lift = faceInclusion K du.face := by
    funext x
    exact du.projection x
  have hde : p ∘ de.lift = faceInclusion K du.face := by
    funext x
    apply Subtype.ext
    exact congrArg Subtype.val (de.projection x)
  have hdux : du.lift x₀ = v.1 := du.vertices v hv
  have hdex : de.lift x₀ = v.1 := de.vertices v hv
  have hdug : du.lift = g := huniq du.lift ⟨hdu, hdux⟩
  have hdeg : de.lift = g := huniq de.lift ⟨hde, hdex⟩
  have hmaps : du.lift = de.lift := hdug.trans hdeg.symm
  have heval := congrArg (fun f : C(convexHull ℝ
    (((s ∩ t).image coveringVertex.base : Finset E) : Set E), X') => f ⟨y, hy⟩) hmaps
  exact heval

open Classical in
theorem CoveringFaceData.eq_of_base_image_eq_of_lift_eq [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space} (hp : IsCoveringMap p)
    {s t : Finset (coveringVertex K p)} (d : CoveringFaceData K p s)
    (e : CoveringFaceData K p t)
    (hbase : s.image coveringVertex.base = t.image coveringVertex.base)
    {y : E} (hy : y ∈ convexHull ℝ ((s.image coveringVertex.base : Finset E) : Set E))
    (heq : d.lift ⟨y, hy⟩ = e.lift ⟨y, hbase ▸ hy⟩) : s = t := by
  let j : C(convexHull ℝ ((s.image coveringVertex.base : Finset E) : Set E),
      convexHull ℝ ((t.image coveringVertex.base : Finset E) : Set E)) :=
    ⟨fun x => ⟨x, hbase ▸ x.2⟩, continuous_subtype_val.subtype_mk _⟩
  let eg : C(convexHull ℝ ((s.image coveringVertex.base : Finset E) : Set E), X') :=
    e.lift.comp j
  let x₀ : convexHull ℝ ((s.image coveringVertex.base : Finset E) : Set E) := ⟨y, hy⟩
  have h₀ : p (d.lift x₀) = faceInclusion K d.face x₀ := d.projection x₀
  obtain ⟨g, hg, huniq⟩ :=
    DifferentialGeometry.Topology.PiecewiseLinear.IsCoveringMap.exists_unique_lift_of_face
      hp d.face x₀ (d.lift x₀) h₀
  have hdproj : p ∘ d.lift = faceInclusion K d.face := funext d.projection
  have heproj : p ∘ eg = faceInclusion K d.face := by
    funext x
    apply Subtype.ext
    exact congrArg Subtype.val (e.projection (j x))
  have heg : eg x₀ = d.lift x₀ := heq.symm
  have hdg : d.lift = g := huniq d.lift ⟨hdproj, rfl⟩
  have hegg : eg = g := huniq eg ⟨heproj, heg⟩
  have hmaps : d.lift = eg := hdg.trans hegg.symm
  have hst : s ⊆ t := by
    intro v hv
    have hvbase : coveringVertex.base v ∈ t.image coveringVertex.base := by
      rw [← hbase]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hbw⟩ := Finset.mem_image.mp hvbase
    let xv : convexHull ℝ ((s.image coveringVertex.base : Finset E) : Set E) :=
      ⟨coveringVertex.base v, subset_convexHull ℝ _
        (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, hv, rfl⟩))⟩
    let xw : convexHull ℝ ((t.image coveringVertex.base : Finset E) : Set E) :=
      ⟨coveringVertex.base w, subset_convexHull ℝ _
        (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw, rfl⟩))⟩
    have hx : j xv = xw := Subtype.ext hbw.symm
    have heval := congrArg (fun f : C(convexHull ℝ
      ((s.image coveringVertex.base : Finset E) : Set E), X') => f xv) hmaps
    have hvw : v.1 = w.1 := calc
      v.1 = d.lift xv := (d.vertices v hv).symm
      _ = eg xv := heval
      _ = e.lift (j xv) := rfl
      _ = e.lift xw := congrArg e.lift hx
      _ = w.1 := e.vertices w hw
    exact Subtype.ext hvw ▸ hw
  apply Finset.eq_of_subset_of_card_le hst
  exact (calc
    s.card = (s.image coveringVertex.base).card :=
      (Finset.card_image_of_injOn d.base_injective).symm
    _ = (t.image coveringVertex.base).card := congrArg Finset.card hbase
    _ = t.card := Finset.card_image_of_injOn e.base_injective).ge

open Classical in
theorem coveringNeighbor_eq_of_mem_faceData [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space} (hp : IsCoveringMap p)
    {s : Finset (coveringVertex K p)} (d : CoveringFaceData K p s)
    {v w : coveringVertex K p} (hv : v ∈ s) (hw : w ∈ s) :
    coveringNeighbor hp v (coveringVertex.base w) = w := by
  have hedge : {coveringVertex.base v, coveringVertex.base w} ∈ K.faces := by
    apply K.down_closed d.face
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
      · exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
    · exact Finset.insert_nonempty _ _
  let u : Finset (coveringVertex K p) := {v, w}
  have hus : u ⊆ s := by
    intro x hx
    simp only [u, Finset.mem_insert, Finset.mem_singleton] at hx
    exact hx.elim (fun h => h ▸ hv) (fun h => h ▸ hw)
  have hune : u.Nonempty := Finset.insert_nonempty _ _
  let du := d.mono hus hune
  let g := coveringEdgeLift hp v (coveringVertex.base w) hedge
  have hg := coveringEdgeLift_projection hp v (coveringVertex.base w) hedge
  let a := coveringFaceDataOfLift hedge g hg
  have haBase : (coveringFaceVertices hedge g hg).image coveringVertex.base =
      {coveringVertex.base v, coveringVertex.base w} :=
    coveringFaceVertices_base_image hedge g hg
  have huBase : u.image coveringVertex.base =
      {coveringVertex.base v, coveringVertex.base w} := by
    simp [u]
  have hbase : (coveringFaceVertices hedge g hg).image coveringVertex.base =
      u.image coveringVertex.base := haBase.trans huBase.symm
  have hy : coveringVertex.base v ∈ convexHull ℝ
      (((coveringFaceVertices hedge g hg).image coveringVertex.base : Finset E) : Set E) := by
    rw [haBase]
    exact subset_convexHull ℝ _ (by simp)
  let ya : convexHull ℝ
      (((coveringFaceVertices hedge g hg).image coveringVertex.base : Finset E) : Set E) :=
    ⟨coveringVertex.base v, hy⟩
  let x₀ : convexHull ℝ
      (({coveringVertex.base v, coveringVertex.base w} : Finset E) : Set E) :=
    ⟨coveringVertex.base v, subset_convexHull ℝ _ (by simp)⟩
  have haya : ya = ⟨x₀, by rw [haBase]; exact x₀.2⟩ := Subtype.ext rfl
  have hav : a.lift ya = v.1 := calc
    a.lift ya = a.lift ⟨x₀, by rw [haBase]; exact x₀.2⟩ := congrArg a.lift haya
    _ = g x₀ := coveringFaceDataOfLift_apply hedge g hg x₀
    _ = v.1 := coveringEdgeLift_source hp v (coveringVertex.base w) hedge
  have hduv : du.lift ⟨coveringVertex.base v, hbase ▸ hy⟩ = v.1 := by
    have hvu : v ∈ u := by simp [u]
    exact du.vertices v hvu
  have heq : a.lift ya = du.lift ⟨coveringVertex.base v, hbase ▸ hy⟩ :=
    hav.trans hduv.symm
  have hau : coveringFaceVertices hedge g hg = u :=
    a.eq_of_base_image_eq_of_lift_eq hp du hbase hy heq
  have hnA : coveringNeighbor hp v (coveringVertex.base w) ∈
      coveringFaceVertices hedge g hg := by
    rw [coveringNeighbor, dif_pos hedge]
    exact Finset.mem_image.mpr
      ⟨(⟨coveringVertex.base w, by simp⟩ :
          ({coveringVertex.base v, coveringVertex.base w} : Finset E)),
        Finset.mem_attach _ _, rfl⟩
  have hnu : coveringNeighbor hp v (coveringVertex.base w) ∈ u := hau ▸ hnA
  apply du.base_injective hnu (by simp [u])
  exact coveringNeighbor_base_of_face hp v (coveringVertex.base w) hedge

open Classical in
def coveringPrecomplex (K : Geometry.SimplicialComplex ℝ E) (p : X' → K.space) :
    PreAbstractSimplicialComplex (coveringVertex K p) where
  faces := {s | Nonempty (CoveringFaceData K p s)}
  isRelLowerSet_faces := by
    intro s hs
    obtain ⟨d⟩ := hs
    refine ⟨Finset.image_nonempty.mp (K.nonempty_of_mem_faces d.face), ?_⟩
    intro t hts ht
    exact ⟨d.mono hts ht⟩

namespace coveringPrecomplex

variable {K : Geometry.SimplicialComplex ℝ E} {p : X' → K.space}

theorem mem_faces_iff {s : Finset (coveringVertex K p)} :
    s ∈ (coveringPrecomplex K p).faces ↔ Nonempty (CoveringFaceData K p s) := Iff.rfl

theorem finite_faces [Finite (coveringVertex K p)] : (coveringPrecomplex K p).faces.Finite :=
  by
    let _ := Fintype.ofFinite (coveringVertex K p)
    exact Set.finite_univ.subset (Set.subset_univ _)

end coveringPrecomplex

section Realization

variable (K : Geometry.SimplicialComplex ℝ E) (p : X' → K.space)
  [Finite (coveringVertex K p)]

def coveringVertexEquiv : coveringVertex K p ≃ Fin (Nat.card (coveringVertex K p)) :=
  Finite.equivFin _

def coveringVertexPoint (v : coveringVertex K p) :
    EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))) :=
  EuclideanSpace.single (coveringVertexEquiv K p v) 1

def coveringBasisVertices :
    Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
  Finset.univ.image fun i => (EuclideanSpace.single i 1 :
    EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))

omit [TopologicalSpace X'] in
theorem coveringVertexPoint_injective : Function.Injective (coveringVertexPoint K p) := by
  intro v w h
  apply (coveringVertexEquiv K p).injective
  by_contra hvw
  have hcoord := congrArg
    (fun z : EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))) =>
      z (coveringVertexEquiv K p v)) h
  simp only [coveringVertexPoint, PiLp.single_apply, if_neg hvw] at hcoord
  exact one_ne_zero hcoord

omit [TopologicalSpace X'] in
theorem mem_coveringBasisVertices (v : coveringVertex K p) :
    coveringVertexPoint K p v ∈ coveringBasisVertices K p := by
  classical
  rw [coveringBasisVertices]
  exact Finset.mem_image.mpr ⟨coveringVertexEquiv K p v, Finset.mem_univ _, rfl⟩

omit [TopologicalSpace X'] [Finite (coveringVertex K p)] in
theorem coveringBasisVertices_affineIndependent :
    AffineIndependent ℝ ((↑) : coveringBasisVertices K p →
      EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) := by
  classical
  have hlin : LinearIndependent ℝ fun i : Fin (Nat.card (coveringVertex K p)) =>
      (EuclideanSpace.single i 1 :
        EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) := by
    have heq : (fun i : Fin (Nat.card (coveringVertex K p)) =>
        (EuclideanSpace.single i 1 :
          EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))) =
        ⇑(EuclideanSpace.basisFun
          (Fin (Nat.card (coveringVertex K p))) ℝ).toBasis := by
      funext i
      exact (EuclideanSpace.basisFun_apply
        (𝕜 := ℝ) (ι := Fin (Nat.card (coveringVertex K p))) i).symm
    rw [heq]
    exact (EuclideanSpace.basisFun
      (Fin (Nat.card (coveringVertex K p))) ℝ).toBasis.linearIndependent
  have h := hlin.affineIndependent.range
  have hrange :
      ((coveringBasisVertices K p : Finset
          (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))) : Set _) =
        Set.range (fun i => (EuclideanSpace.single i 1 :
          EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))) := by
    rw [coveringBasisVertices, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rwa [← hrange] at h

open Classical in
def coveringSimplexComplex : Geometry.SimplicialComplex ℝ
    (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
  simplexComplex (coveringBasisVertices K p) (coveringBasisVertices_affineIndependent K p)

open Classical in
theorem coveringPrecomplex_map_faces_subset :
    ((coveringPrecomplex K p).map (coveringVertexPoint K p)).faces ⊆
      (coveringSimplexComplex K p).faces := by
  rintro q ⟨s, hs, rfl⟩
  refine ⟨Finset.image_nonempty.mpr ((coveringPrecomplex K p).isRelLowerSet_faces hs).1, ?_⟩
  intro x hx
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
  exact mem_coveringBasisVertices K p v

open Classical in
def coveringComplex : Geometry.SimplicialComplex ℝ
    (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) where
  faces := ((coveringPrecomplex K p).map (coveringVertexPoint K p)).faces
  isRelLowerSet_faces :=
    ((coveringPrecomplex K p).map (coveringVertexPoint K p)).isRelLowerSet_faces
  indep hs := (coveringSimplexComplex K p).indep
    (coveringPrecomplex_map_faces_subset K p hs)
  inter_subset_convexHull hs ht := (coveringSimplexComplex K p).inter_subset_convexHull
    (coveringPrecomplex_map_faces_subset K p hs)
    (coveringPrecomplex_map_faces_subset K p ht)

theorem coveringComplex_faces_finite : (coveringComplex K p).faces.Finite :=
  by
    classical
    change (Set.image (fun s => s.image (coveringVertexPoint K p))
      (coveringPrecomplex K p).faces).Finite
    exact (coveringPrecomplex.finite_faces (K := K) (p := p)).image
      (fun s => s.image (coveringVertexPoint K p))

open Classical in
def coveringBaseVertex
    (z : EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) : E :=
  if h : ∃ v, coveringVertexPoint K p v = z then coveringVertex.base h.choose else 0

open Classical in
omit [TopologicalSpace X'] in
theorem coveringBaseVertex_point (v : coveringVertex K p) :
    coveringBaseVertex K p (coveringVertexPoint K p v) = coveringVertex.base v := by
  rw [coveringBaseVertex, dif_pos ⟨v, rfl⟩]
  exact congrArg coveringVertex.base
    (coveringVertexPoint_injective K p (Classical.choose_spec
      (show ∃ w, coveringVertexPoint K p w = coveringVertexPoint K p v from ⟨v, rfl⟩)))

def coveringBaseMap
    (z : EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) : E :=
  simplicialMap (coveringComplex K p) (coveringBaseVertex K p) z

open Classical in
theorem mem_coveringComplex_faces_iff
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))} :
    q ∈ (coveringComplex K p).faces ↔
      ∃ s ∈ (coveringPrecomplex K p).faces,
        q = s.image (coveringVertexPoint K p) := by
  change (∃ s ∈ (coveringPrecomplex K p).faces,
    s.image (coveringVertexPoint K p) = q) ↔ _
  constructor
  · rintro ⟨s, hs, hsq⟩
    exact ⟨s, hs, hsq.symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩

open Classical in
omit [TopologicalSpace X'] in
theorem coveringBaseVertex_image (s : Finset (coveringVertex K p)) :
    (s.image (coveringVertexPoint K p)).image (coveringBaseVertex K p) =
      s.image coveringVertex.base := by
  rw [Finset.image_image]
  exact Finset.image_congr fun v _ => coveringBaseVertex_point K p v

open Classical in
theorem coveringBaseVertex_injective_on_face {s : Finset (coveringVertex K p)}
    (d : CoveringFaceData K p s) :
    Set.InjOn (coveringBaseVertex K p) (s.image (coveringVertexPoint K p)) := by
  intro x hx y hy hxy
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  apply congrArg (coveringVertexPoint K p)
  exact d.base_injective hv hw
    (by simpa only [coveringBaseVertex_point] using hxy)

open Classical in
theorem coveringBaseMap_mem_convexHull {s : Finset (coveringVertex K p)}
    (d : CoveringFaceData K p s)
    {z : EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))}
    (hz : z ∈ convexHull ℝ ((s.image (coveringVertexPoint K p) : Finset _) : Set _)) :
    coveringBaseMap K p z ∈
      convexHull ℝ ((s.image coveringVertex.base : Finset E) : Set E) := by
  rw [← coveringBaseVertex_image K p s]
  exact simplicialMap_mem_convexHull_image (coveringComplex K p)
    (coveringBaseVertex K p) ⟨s, ⟨d⟩, rfl⟩ hz

open Classical in
theorem coveringBaseMap_image_convexHull {s : Finset (coveringVertex K p)}
    (d : CoveringFaceData K p s) :
    coveringBaseMap K p ''
        convexHull ℝ ((s.image (coveringVertexPoint K p) : Finset _) : Set _) =
      convexHull ℝ ((s.image coveringVertex.base : Finset E) : Set E) := by
  change simplicialMap (coveringComplex K p) (coveringBaseVertex K p) '' _ = _
  rw [image_convexHull_simplicialMap (coveringComplex K p) (coveringBaseVertex K p)
      ⟨s, ⟨d⟩, rfl⟩ (coveringBaseVertex_injective_on_face K p d),
    coveringBaseVertex_image]

open Classical in
theorem coveringBaseMap_mem_openSimplex {s : Finset (coveringVertex K p)}
    (d : CoveringFaceData K p s)
    {z : EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))}
    (hz : z ∈ openSimplex (s.image (coveringVertexPoint K p))) :
    coveringBaseMap K p z ∈ openSimplex (s.image coveringVertex.base) := by
  have hq : s.image (coveringVertexPoint K p) ∈ (coveringComplex K p).faces :=
    ⟨s, ⟨d⟩, rfl⟩
  rw [← coveringBaseVertex_image K p s,
    ← image_openSimplex_simplicialMap (coveringComplex K p) (coveringBaseVertex K p)
      hq (coveringBaseVertex_injective_on_face K p d)]
  exact ⟨z, hz, rfl⟩

open Classical in
theorem coveringBaseMap_injective_on_face {s : Finset (coveringVertex K p)}
    (d : CoveringFaceData K p s) :
    Set.InjOn (coveringBaseMap K p)
      (convexHull ℝ ((s.image (coveringVertexPoint K p) : Finset _) : Set _)) := by
  let q := s.image (coveringVertexPoint K p)
  have hq : q ∈ (coveringComplex K p).faces := ⟨s, ⟨d⟩, rfl⟩
  have hinj : Set.InjOn (coveringBaseVertex K p) (q : Set _) :=
    coveringBaseVertex_injective_on_face K p d
  have himage : q.image (coveringBaseVertex K p) = s.image coveringVertex.base :=
    coveringBaseVertex_image K p s
  have himageAI : AffineIndependent ℝ ((↑) : q.image (coveringBaseVertex K p) → E) := by
    rw [himage]
    exact K.indep d.face
  have hAI : AffineIndependent ℝ (fun v : q => coveringBaseVertex K p v) :=
    (affineIndependent_image_iff q (coveringBaseVertex K p)).mpr ⟨hinj, himageAI⟩
  exact injOn_simplicialMap_convexHull (coveringComplex K p)
    (coveringBaseVertex K p) hq hAI

open Classical in
theorem exists_affineMap_eqOn_coveringBaseMap
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))}
    (hq : q ∈ (coveringComplex K p).faces) :
    ∃ A : EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))) →ᵃ[ℝ] E,
      EqOn (coveringBaseMap K p) A (convexHull ℝ (q : Set _)) :=
  exists_affineMap_eqOn_simplicialMap (coveringComplex K p) (coveringBaseVertex K p) hq

open Classical in
structure CoveringGeometricFaceData
    (q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))) where
  source : Finset (coveringVertex K p)
  data : CoveringFaceData K p source
  image_eq : source.image (coveringVertexPoint K p) = q

open Classical in
theorem exists_coveringGeometricFaceData
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))}
    (hq : q ∈ (coveringComplex K p).faces) : Nonempty (CoveringGeometricFaceData K p q) := by
  obtain ⟨s, hs, hq⟩ := (mem_coveringComplex_faces_iff K p).mp hq
  exact ⟨s, Classical.choice hs, hq.symm⟩

open Classical in
def chosenCoveringGeometricFaceData
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))}
    (hq : q ∈ (coveringComplex K p).faces) : CoveringGeometricFaceData K p q :=
  Classical.choice (exists_coveringGeometricFaceData K p hq)

open Classical in
def CoveringGeometricFaceData.map [FiniteDimensional ℝ E]
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))}
    (d : CoveringGeometricFaceData K p q) :
    C(convexHull ℝ (q : Set (EuclideanSpace ℝ
      (Fin (Nat.card (coveringVertex K p))))), X') := by
  let _ : Finite (coveringComplex K p).faces :=
    (coveringComplex_faces_finite K p).to_subtype
  have hc : ContinuousOn (coveringBaseMap K p) (convexHull ℝ
      (q : Set (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))))) :=
    (isPiecewiseAffineOn_simplicialMap (coveringComplex K p)
      (coveringBaseVertex K p)).continuousOn.mono
      ((coveringComplex K p).convexHull_subset_space
        (d.image_eq ▸ (show d.source.image (coveringVertexPoint K p) ∈
          (coveringComplex K p).faces from ⟨d.source, ⟨d.data⟩, rfl⟩)))
  have hb (z : convexHull ℝ
      (q : Set (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))))) :
      coveringBaseMap K p z ∈
        convexHull ℝ ((d.source.image coveringVertex.base : Finset E) : Set E) :=
    coveringBaseMap_mem_convexHull K p d.data (by rw [d.image_eq]; exact z.2)
  let b : C(convexHull ℝ
      (q : Set (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))),
      convexHull ℝ ((d.source.image coveringVertex.base : Finset E) : Set E)) :=
    ⟨fun z => ⟨coveringBaseMap K p z, hb z⟩,
      (continuousOn_iff_continuous_domRestrict.mp hc).subtype_mk _⟩
  exact d.data.lift.comp b

open Classical in
theorem CoveringGeometricFaceData.map_eq_lift [FiniteDimensional ℝ E]
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))}
    (d : CoveringGeometricFaceData K p q)
    (z : convexHull ℝ (q : Set (EuclideanSpace ℝ
      (Fin (Nat.card (coveringVertex K p)))))) :
    d.map K p z = d.data.lift
      ⟨coveringBaseMap K p z,
        coveringBaseMap_mem_convexHull K p d.data (by rw [d.image_eq]; exact z.2)⟩ := by
  rfl

open Classical in
theorem CoveringGeometricFaceData.map_projection [FiniteDimensional ℝ E]
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))}
    (d : CoveringGeometricFaceData K p q)
    (z : convexHull ℝ (q : Set (EuclideanSpace ℝ
      (Fin (Nat.card (coveringVertex K p)))))) :
    ((p (d.map K p z) : K.space) : E) = coveringBaseMap K p z := by
  exact congrArg Subtype.val (d.data.projection _)

open Classical in
theorem CoveringGeometricFaceData.map_eq_of_mem_inter [FiniteDimensional ℝ E]
    {q r : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))}
    (hp : IsCoveringMap p) (d : CoveringGeometricFaceData K p q)
    (e : CoveringGeometricFaceData K p r)
    {z : EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))}
    (hzq : z ∈ convexHull ℝ (q : Set (EuclideanSpace ℝ
      (Fin (Nat.card (coveringVertex K p))))))
    (hzr : z ∈ convexHull ℝ (r : Set (EuclideanSpace ℝ
      (Fin (Nat.card (coveringVertex K p)))))) :
    d.map K p ⟨z, hzq⟩ = e.map K p ⟨z, hzr⟩ := by
  have hq : q ∈ (coveringComplex K p).faces := d.image_eq ▸
    (show d.source.image (coveringVertexPoint K p) ∈ (coveringComplex K p).faces from
      ⟨d.source, ⟨d.data⟩, rfl⟩)
  have hr : r ∈ (coveringComplex K p).faces := e.image_eq ▸
    (show e.source.image (coveringVertexPoint K p) ∈ (coveringComplex K p).faces from
      ⟨e.source, ⟨e.data⟩, rfl⟩)
  have hzinter : z ∈ convexHull ℝ ((q ∩ r : Finset _) : Set _) := by
    simpa only [Finset.coe_inter] using
      (coveringComplex K p).inter_subset_convexHull hq hr ⟨hzq, hzr⟩
  have hzsource : z ∈ convexHull ℝ
      (((d.source ∩ e.source).image (coveringVertexPoint K p) : Finset _) : Set _) := by
    rw [Finset.image_inter d.source e.source (coveringVertexPoint_injective K p),
      d.image_eq, e.image_eq]
    exact hzinter
  have hu : (d.source ∩ e.source).Nonempty :=
    Finset.image_nonempty.mp (nonempty_of_mem_convexHull hzsource)
  let du := d.data.mono Finset.inter_subset_left hu
  have hy : coveringBaseMap K p z ∈ convexHull ℝ
      (((d.source ∩ e.source).image coveringVertex.base : Finset E) : Set E) :=
    coveringBaseMap_mem_convexHull K p du hzsource
  exact d.data.lift_eq_of_mem_inter hp e.data hy

open Classical in
def coveringSpaceMap [FiniteDimensional ℝ E]
    (z : (coveringComplex K p).space) : X' :=
  let q := carrierFace (coveringComplex K p) z.1
  let hq : q ∈ (coveringComplex K p).faces := carrierFace_mem z.2
  let d := chosenCoveringGeometricFaceData K p hq
  d.map K p ⟨z.1, mem_convexHull_carrierFace z.2⟩

open Classical in
theorem coveringSpaceMap_projection [FiniteDimensional ℝ E]
    (z : (coveringComplex K p).space) :
    ((p (coveringSpaceMap K p z) : K.space) : E) = coveringBaseMap K p z := by
  exact (chosenCoveringGeometricFaceData K p (carrierFace_mem z.2)).map_projection K p _

open Classical in
theorem coveringSpaceMap_eq_face [FiniteDimensional ℝ E]
    (hp : IsCoveringMap p)
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))}
    (hq : q ∈ (coveringComplex K p).faces) (d : CoveringGeometricFaceData K p q)
    {z : EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))}
    (hz : z ∈ convexHull ℝ (q : Set (EuclideanSpace ℝ
      (Fin (Nat.card (coveringVertex K p)))))) :
    coveringSpaceMap K p ⟨z, (coveringComplex K p).convexHull_subset_space hq hz⟩ =
      d.map K p ⟨z, hz⟩ := by
  let c := carrierFace (coveringComplex K p) z
  let hc : c ∈ (coveringComplex K p).faces := carrierFace_mem
    ((coveringComplex K p).convexHull_subset_space hq hz)
  let a := chosenCoveringGeometricFaceData K p hc
  change a.map K p ⟨z, mem_convexHull_carrierFace
    ((coveringComplex K p).convexHull_subset_space hq hz)⟩ = d.map K p ⟨z, hz⟩
  exact a.map_eq_of_mem_inter K p hp d
    (mem_convexHull_carrierFace ((coveringComplex K p).convexHull_subset_space hq hz)) hz

def coveringFaceSet
    (q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))) :
    Set (coveringComplex K p).space :=
  {z | z.1 ∈ convexHull ℝ (q : Set (EuclideanSpace ℝ
    (Fin (Nat.card (coveringVertex K p)))))}

theorem isClosed_coveringFaceSet
    (q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))) :
    IsClosed (coveringFaceSet K p q) :=
  (q.finite_toSet.isCompact_convexHull ℝ).isClosed.preimage continuous_subtype_val

open Classical in
theorem iUnion_coveringFaceSet :
    ⋃ q : (coveringComplex K p).faces, coveringFaceSet K p q.1 = Set.univ := by
  apply eq_univ_of_forall
  intro z
  let q : (coveringComplex K p).faces :=
    ⟨carrierFace (coveringComplex K p) z.1, carrierFace_mem z.2⟩
  exact mem_iUnion.mpr ⟨q, mem_convexHull_carrierFace z.2⟩

open Classical in
theorem continuousOn_coveringSpaceMap_face [FiniteDimensional ℝ E]
    (hp : IsCoveringMap p)
    (q : (coveringComplex K p).faces) :
    ContinuousOn (coveringSpaceMap K p) (coveringFaceSet K p q.1) := by
  let d := chosenCoveringGeometricFaceData K p q.2
  let j : C(coveringFaceSet K p q.1,
      convexHull ℝ (q.1 : Set (EuclideanSpace ℝ
        (Fin (Nat.card (coveringVertex K p)))))) :=
    ⟨fun z => ⟨z.1.1, z.2⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  rw [continuousOn_iff_continuous_domRestrict]
  have hcont : Continuous (fun z => d.map K p (j z)) := d.map.continuous.comp j.continuous
  apply hcont.congr
  intro z
  change d.map K p (j z) = coveringSpaceMap K p z.1
  have heq := coveringSpaceMap_eq_face K p hp q.2 d z.2
  exact heq.symm

open Classical in
theorem continuous_coveringSpaceMap [FiniteDimensional ℝ E]
    (hp : IsCoveringMap p) : Continuous (coveringSpaceMap K p) := by
  let _ : Finite (coveringComplex K p).faces :=
    (coveringComplex_faces_finite K p).to_subtype
  exact (locallyFinite_of_finite fun q : (coveringComplex K p).faces =>
    coveringFaceSet K p q.1).continuous (iUnion_coveringFaceSet K p)
      (fun q => isClosed_coveringFaceSet K p q.1)
      (fun q => continuousOn_coveringSpaceMap_face K p hp q)

open Classical in
theorem injective_coveringSpaceMap [FiniteDimensional ℝ E]
    (hp : IsCoveringMap p) : Function.Injective (coveringSpaceMap K p) := by
  intro z w hzw
  have hbase : coveringBaseMap K p z = coveringBaseMap K p w := calc
    coveringBaseMap K p z = ((p (coveringSpaceMap K p z) : K.space) : E) :=
      (coveringSpaceMap_projection K p z).symm
    _ = ((p (coveringSpaceMap K p w) : K.space) : E) :=
      congrArg (fun x => ((p x : K.space) : E)) hzw
    _ = coveringBaseMap K p w := coveringSpaceMap_projection K p w
  let q := carrierFace (coveringComplex K p) z.1
  let r := carrierFace (coveringComplex K p) w.1
  have hq : q ∈ (coveringComplex K p).faces := carrierFace_mem z.2
  have hr : r ∈ (coveringComplex K p).faces := carrierFace_mem w.2
  let d := chosenCoveringGeometricFaceData K p hq
  let e := chosenCoveringGeometricFaceData K p hr
  have hzopen : z.1 ∈ openSimplex q := mem_openSimplex_carrierFace z.2
  have hwopen : w.1 ∈ openSimplex r := mem_openSimplex_carrierFace w.2
  have hzsource : z.1 ∈ openSimplex (d.source.image (coveringVertexPoint K p)) := by
    rw [d.image_eq]
    exact hzopen
  have hwsource : w.1 ∈ openSimplex (e.source.image (coveringVertexPoint K p)) := by
    rw [e.image_eq]
    exact hwopen
  have hyz : coveringBaseMap K p z ∈ openSimplex
      (d.source.image coveringVertex.base) :=
    coveringBaseMap_mem_openSimplex K p d.data hzsource
  have hyw : coveringBaseMap K p w ∈ openSimplex
      (e.source.image coveringVertex.base) :=
    coveringBaseMap_mem_openSimplex K p e.data hwsource
  have hyw' : coveringBaseMap K p z ∈ openSimplex
      (e.source.image coveringVertex.base) := by
    rw [hbase]
    exact hyw
  have hbaseFaces : d.source.image coveringVertex.base =
      e.source.image coveringVertex.base :=
    face_eq_of_mem_openSimplex K d.data.face e.data.face hyz hyw'
  have hzconv : z.1 ∈ convexHull ℝ (q : Set _) :=
    openSimplex_subset_convexHull q hzopen
  have hwconv : w.1 ∈ convexHull ℝ (r : Set _) :=
    openSimplex_subset_convexHull r hwopen
  let zz : convexHull ℝ (q : Set _) := ⟨z.1, hzconv⟩
  let ww : convexHull ℝ (r : Set _) := ⟨w.1, hwconv⟩
  have hzd : coveringSpaceMap K p z = d.map K p zz := by
    simpa only [zz] using coveringSpaceMap_eq_face K p hp hq d hzconv
  have hwe : coveringSpaceMap K p w = e.map K p ww := by
    simpa only [ww] using coveringSpaceMap_eq_face K p hp hr e hwconv
  have hde : d.map K p zz = e.map K p ww :=
    hzd.symm.trans (hzw.trans hwe)
  let yd : convexHull ℝ ((d.source.image coveringVertex.base : Finset E) : Set E) :=
    ⟨coveringBaseMap K p z, openSimplex_subset_convexHull _ hyz⟩
  let ye : convexHull ℝ ((e.source.image coveringVertex.base : Finset E) : Set E) :=
    ⟨coveringBaseMap K p z, hbaseFaces ▸ openSimplex_subset_convexHull _ hyz⟩
  have hdm : d.map K p zz = d.data.lift yd := by
    simpa only [yd] using d.map_eq_lift K p zz
  have hem₀ := e.map_eq_lift K p ww
  have hearg : (⟨coveringBaseMap K p w,
      coveringBaseMap_mem_convexHull K p e.data (by rw [e.image_eq]; exact ww.2)⟩ :
        convexHull ℝ ((e.source.image coveringVertex.base : Finset E) : Set E)) = ye :=
    Subtype.ext hbase.symm
  have hem : e.map K p ww = e.data.lift ye := hem₀.trans (congrArg e.data.lift hearg)
  have hlift : d.data.lift yd = e.data.lift ye := hdm.symm.trans (hde.trans hem)
  have hsources := d.data.eq_of_base_image_eq_of_lift_eq hp e.data hbaseFaces
    (openSimplex_subset_convexHull _ hyz) hlift
  have hwsource' : w.1 ∈ convexHull ℝ
      ((d.source.image (coveringVertexPoint K p) : Finset _) : Set _) := by
    rw [hsources, e.image_eq]
    exact hwconv
  have hzinj := coveringBaseMap_injective_on_face K p d.data
    (openSimplex_subset_convexHull _ hzsource) hwsource' hbase
  exact Subtype.ext hzinj

open Classical in
theorem surjective_coveringSpaceMap [FiniteDimensional ℝ E]
    (hp : IsCoveringMap p) : Function.Surjective (coveringSpaceMap K p) := by
  intro x
  let y : K.space := p x
  let t := carrierFace K (y : E)
  have ht : t ∈ K.faces := carrierFace_mem y.2
  have hyt : (y : E) ∈ convexHull ℝ (t : Set E) := mem_convexHull_carrierFace y.2
  let x₀ : convexHull ℝ (t : Set E) := ⟨y, hyt⟩
  have h₀ : p x = faceInclusion K ht x₀ := by
    apply Subtype.ext
    rfl
  obtain ⟨g, ⟨hg, hgx⟩, -⟩ :=
    DifferentialGeometry.Topology.PiecewiseLinear.IsCoveringMap.exists_unique_lift_of_face
      hp ht x₀ x h₀
  let s := coveringFaceVertices ht g hg
  let d := coveringFaceDataOfLift ht g hg
  let q := s.image (coveringVertexPoint K p)
  have hq : q ∈ (coveringComplex K p).faces := ⟨s, ⟨d⟩, rfl⟩
  have hybase : (y : E) ∈
      convexHull ℝ ((s.image coveringVertex.base : Finset E) : Set E) := by
    rw [coveringFaceVertices_base_image ht g hg]
    exact hyt
  have hyimage : (y : E) ∈ coveringBaseMap K p ''
      convexHull ℝ ((q : Finset _) : Set _) := by
    rw [coveringBaseMap_image_convexHull K p d]
    exact hybase
  obtain ⟨z, hz, hzy⟩ := hyimage
  let z' : (coveringComplex K p).space :=
    ⟨z, (coveringComplex K p).convexHull_subset_space hq hz⟩
  let qd : CoveringGeometricFaceData K p q := ⟨s, d, rfl⟩
  have hzmap : coveringSpaceMap K p z' = qd.map K p ⟨z, hz⟩ := by
    simpa only [z'] using coveringSpaceMap_eq_face K p hp hq qd hz
  let xb : convexHull ℝ ((s.image coveringVertex.base : Finset E) : Set E) :=
    ⟨y, hybase⟩
  have harg : (⟨coveringBaseMap K p z,
      coveringBaseMap_mem_convexHull K p d (by exact hz)⟩ :
        convexHull ℝ ((s.image coveringVertex.base : Finset E) : Set E)) = xb :=
    Subtype.ext hzy
  have hdm := qd.map_eq_lift K p ⟨z, hz⟩
  have hdx : d.lift xb = x := calc
    d.lift xb = g x₀ := coveringFaceDataOfLift_apply ht g hg x₀
    _ = x := hgx
  refine ⟨z', hzmap.trans ?_⟩
  exact hdm.trans ((congrArg d.lift harg).trans hdx)

open Classical in
def coveringSpaceHomeomorph [FiniteDimensional ℝ E]
    (hp : IsCoveringMap p) : (coveringComplex K p).space ≃ₜ X' := by
  let _ : Finite (coveringComplex K p).faces :=
    (coveringComplex_faces_finite K p).to_subtype
  let _ : CompactSpace (coveringComplex K p).space :=
    isCompact_iff_compactSpace.mp (isPolyhedron_space (coveringComplex K p)).isCompact
  let _ : T2Space X' :=
    DifferentialGeometry.Topology.Covering.t2Space_of_isCoveringMap hp
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (coveringSpaceMap K p)
      ⟨injective_coveringSpaceMap K p hp, surjective_coveringSpaceMap K p hp⟩)
    (continuous_coveringSpaceMap K p hp)

@[simp]
theorem coveringSpaceHomeomorph_apply [FiniteDimensional ℝ E]
    (hp : IsCoveringMap p) (z : (coveringComplex K p).space) :
    coveringSpaceHomeomorph K p hp z = coveringSpaceMap K p z := by
  rw [coveringSpaceHomeomorph]
  rfl

omit [Finite (coveringVertex K p)] in
open Classical in
theorem exists_coveringFaceData_at_vertex [FiniteDimensional ℝ E]
    (hp : IsCoveringMap p) (v : coveringVertex K p) {t : Finset E}
    (ht : t ∈ K.faces) (hv : coveringVertex.base v ∈ t) :
    ∃ s : Finset (coveringVertex K p), ∃ _ : CoveringFaceData K p s,
      v ∈ s ∧ s.image coveringVertex.base = t := by
  let x₀ : convexHull ℝ (t : Set E) :=
    ⟨coveringVertex.base v, subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)⟩
  have h₀ : p v.1 = faceInclusion K ht x₀ := by
    apply Subtype.ext
    rfl
  obtain ⟨g, ⟨hg, hgx⟩, -⟩ :=
    DifferentialGeometry.Topology.PiecewiseLinear.IsCoveringMap.exists_unique_lift_of_face
      hp ht x₀ v.1 h₀
  let s := coveringFaceVertices ht g hg
  let d := coveringFaceDataOfLift ht g hg
  have hsource : coveringVertexOfLift ht g hg ⟨coveringVertex.base v, hv⟩ = v := by
    apply Subtype.ext
    exact hgx
  refine ⟨s, d, ?_, coveringFaceVertices_base_image ht g hg⟩
  exact Finset.mem_image.mpr
    ⟨⟨coveringVertex.base v, hv⟩, Finset.mem_attach _ _, hsource⟩

open Classical in
def coveringLinkForward [FiniteDimensional ℝ E]
    (hp : IsCoveringMap p) (v : coveringVertex K p) (w : E) :
    EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))) :=
  coveringVertexPoint K p (coveringNeighbor hp v w)

open Classical in
theorem coveringLinkForward_base_of_face [FiniteDimensional ℝ E]
    (hp : IsCoveringMap p) (v : coveringVertex K p) (w : E)
    (hvw : {coveringVertex.base v, w} ∈ K.faces) :
    coveringBaseVertex K p (coveringLinkForward K p hp v w) = w := by
  rw [coveringLinkForward, coveringBaseVertex_point,
    coveringNeighbor_base_of_face hp v w hvw]

open Classical in
theorem coveringLinkForward_image_mem_geometricLink [FiniteDimensional ℝ E]
    (hp : IsCoveringMap p) (v : coveringVertex K p) {t : Finset E}
    (ht : t ∈ (SimplicialComplex.geometricLink K {coveringVertex.base v}).faces) :
    t.image (coveringLinkForward K p hp v) ∈
      (SimplicialComplex.geometricLink (coveringComplex K p)
        {coveringVertexPoint K p v}).faces := by
  obtain ⟨htne, hvt, hins⟩ :=
    (SimplicialComplex.mem_geometricLink_singleton K (coveringVertex.base v) t).mp ht
  obtain ⟨s, d, hv, hbase⟩ := exists_coveringFaceData_at_vertex K p hp v hins (by simp)
  have hsub : insert v (t.image (coveringNeighbor hp v)) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_image] at hx
    rcases hx with rfl | ⟨w, hw, rfl⟩
    · exact hv
    · have hwb : w ∈ s.image coveringVertex.base := by
        rw [hbase]
        exact Finset.mem_insert_of_mem hw
      obtain ⟨u, hu, hub⟩ := Finset.mem_image.mp hwb
      have hnu : coveringNeighbor hp v w = u := by
        rw [← hub]
        exact coveringNeighbor_eq_of_mem_faceData hp d hv hu
      rw [hnu]
      exact hu
  let e := d.mono hsub (Finset.insert_nonempty _ _)
  have himage :
      (insert v (t.image (coveringNeighbor hp v))).image (coveringVertexPoint K p) =
        insert (coveringVertexPoint K p v) (t.image (coveringLinkForward K p hp v)) := by
    rw [Finset.image_insert, Finset.image_image]
    rfl
  have hface : insert (coveringVertexPoint K p v)
      (t.image (coveringLinkForward K p hp v)) ∈ (coveringComplex K p).faces := by
    rw [← himage]
    exact ⟨insert v (t.image (coveringNeighbor hp v)), ⟨e⟩, rfl⟩
  refine (SimplicialComplex.mem_geometricLink_singleton
    (coveringComplex K p) (coveringVertexPoint K p v) _).mpr
    ⟨htne.image _, ?_, hface⟩
  intro hmem
  obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hmem
  have hedge : {coveringVertex.base v, w} ∈ K.faces :=
    K.down_closed hins (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr hw) (Finset.insert_nonempty _ _)
  have hn : coveringNeighbor hp v w = v :=
    coveringVertexPoint_injective K p hwv
  have hwb : w = coveringVertex.base v := by
    rw [← coveringNeighbor_base_of_face hp v w hedge, hn]
  exact hvt (hwb ▸ hw)

open Classical in
theorem coveringBaseVertex_image_mem_geometricLink [FiniteDimensional ℝ E]
    (v : coveringVertex K p)
    {q : Finset (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))}
    (hq : q ∈ (SimplicialComplex.geometricLink (coveringComplex K p)
      {coveringVertexPoint K p v}).faces) :
    q.image (coveringBaseVertex K p) ∈
      (SimplicialComplex.geometricLink K {coveringVertex.base v}).faces := by
  obtain ⟨hqne, hvq, hins⟩ :=
    (SimplicialComplex.mem_geometricLink_singleton
      (coveringComplex K p) (coveringVertexPoint K p v) q).mp hq
  obtain ⟨s, hs, himage⟩ := (mem_coveringComplex_faces_iff K p).mp hins
  let d : CoveringFaceData K p s := Classical.choice hs
  have hvimage : coveringVertexPoint K p v ∈ s.image (coveringVertexPoint K p) := by
    rw [← himage]
    exact Finset.mem_insert_self _ _
  obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hvimage
  have huv' : u = v := coveringVertexPoint_injective K p huv
  have hv : v ∈ s := huv' ▸ hu
  refine (SimplicialComplex.mem_geometricLink_singleton K (coveringVertex.base v) _).mpr
    ⟨hqne.image _, ?_, ?_⟩
  · intro hmem
    obtain ⟨z, hz, hzb⟩ := Finset.mem_image.mp hmem
    have hzimage : z ∈ s.image (coveringVertexPoint K p) := by
      rw [← himage]
      exact Finset.mem_insert_of_mem hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hzimage
    have hbase : coveringVertex.base w = coveringVertex.base v := by
      rw [← coveringBaseVertex_point K p w, hwz]
      exact hzb
    have hwv : w = v := d.base_injective hw hv hbase
    apply hvq
    rw [← hwv, hwz]
    exact hz
  · apply K.down_closed d.face
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_image] at hx
      rcases hx with rfl | ⟨z, hz, rfl⟩
      · exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
      · have hzimage : z ∈ s.image (coveringVertexPoint K p) := by
          rw [← himage]
          exact Finset.mem_insert_of_mem hz
        obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hzimage
        rw [← hwz, coveringBaseVertex_point]
        exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
    · exact Finset.insert_nonempty _ _

open Classical in
theorem coveringVertexLink_isGlueIso [FiniteDimensional ℝ E]
    (hp : IsCoveringMap p) (v : coveringVertex K p) :
    let _ : DecidableEq (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
      Classical.decEq _
    IsGlueIso
      (SimplicialComplex.geometricLink K {coveringVertex.base v})
      (SimplicialComplex.geometricLink (coveringComplex K p)
        {coveringVertexPoint K p v})
      (coveringLinkForward K p hp v) (coveringBaseVertex K p) := by
  dsimp only
  have hdec : Classical.decEq
      (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) =
        (inferInstance : DecidableEq
          (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p))))) :=
    Subsingleton.elim _ _
  rw [hdec]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun t ht => coveringLinkForward_image_mem_geometricLink K p hp v ht
  · exact fun q hq => coveringBaseVertex_image_mem_geometricLink K p v hq
  · intro t ht w hw
    obtain ⟨-, -, hins⟩ :=
      (SimplicialComplex.mem_geometricLink_singleton K (coveringVertex.base v) t).mp ht
    have hedge : {coveringVertex.base v, w} ∈ K.faces :=
      K.down_closed hins (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr hw) (Finset.insert_nonempty _ _)
    exact coveringLinkForward_base_of_face K p hp v w hedge
  · intro q hq z hz
    obtain ⟨-, -, hins⟩ :=
      (SimplicialComplex.mem_geometricLink_singleton
        (coveringComplex K p) (coveringVertexPoint K p v) q).mp hq
    obtain ⟨s, hs, himage⟩ := (mem_coveringComplex_faces_iff K p).mp hins
    let d : CoveringFaceData K p s := Classical.choice hs
    have hvimage : coveringVertexPoint K p v ∈ s.image (coveringVertexPoint K p) := by
      rw [← himage]
      exact Finset.mem_insert_self _ _
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hvimage
    have huv' : u = v := coveringVertexPoint_injective K p huv
    have hv : v ∈ s := huv' ▸ hu
    have hzimage : z ∈ s.image (coveringVertexPoint K p) := by
      rw [← himage]
      exact Finset.mem_insert_of_mem hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hzimage
    have hn : coveringNeighbor hp v (coveringVertex.base w) = w :=
      coveringNeighbor_eq_of_mem_faceData hp d hv hw
    calc
      coveringLinkForward K p hp v (coveringBaseVertex K p z) =
          coveringVertexPoint K p (coveringNeighbor hp v (coveringVertex.base w)) := by
            rw [← hwz, coveringBaseVertex_point]
            rfl
      _ = coveringVertexPoint K p w := congrArg (coveringVertexPoint K p) hn
      _ = z := hwz

open Classical in
theorem exists_coveringVertexPoint_of_singleton_mem
    {z : EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))}
    (hz : {z} ∈ (coveringComplex K p).faces) :
    ∃ v : coveringVertex K p, coveringVertexPoint K p v = z := by
  obtain ⟨s, -, himage⟩ := (mem_coveringComplex_faces_iff K p).mp hz
  have hzimage : z ∈ s.image (coveringVertexPoint K p) := by
    rw [← himage]
    exact Finset.mem_singleton_self z
  obtain ⟨v, -, hvz⟩ := Finset.mem_image.mp hzimage
  exact ⟨v, hvz⟩

open Classical in
theorem isCombinatorialManifoldWithBoundary_coveringComplex [FiniteDimensional ℝ E]
    [Finite K.faces] (hp : IsCoveringMap p) {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary n K) :
    IsCombinatorialManifoldWithBoundary n (coveringComplex K p) := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin (Nat.card (coveringVertex K p)))) :=
    Classical.decEq _
  let _ : Finite (coveringComplex K p).faces :=
    (coveringComplex_faces_finite K p).to_subtype
  cases n with
  | zero =>
      intro z hz
      obtain ⟨v, hvz⟩ := exists_coveringVertexPoint_of_singleton_mem K p hz
      subst z
      rw [Set.eq_empty_iff_forall_notMem]
      intro q hq
      have hbase := (coveringVertexLink_isGlueIso K p hp v).image₂ q hq
      rw [hK (coveringVertex.base v) (coveringVertex.singleton_base_mem_faces v)] at hbase
      exact hbase
  | succ m =>
      intro z hz
      obtain ⟨v, hvz⟩ := exists_coveringVertexPoint_of_singleton_mem K p hz
      subst z
      have hiso := coveringVertexLink_isGlueIso K p hp v
      have hpl := hiso.isPLHomeomorphOn
      rcases hK (coveringVertex.base v) (coveringVertex.singleton_base_mem_faces v) with hs | hb
      · exact Or.inl (hs.of_isPLHomeomorphOn hpl)
      · exact Or.inr (hb.of_isPLHomeomorphOn hpl)

end Realization

open Classical in
theorem exists_lift_simplicialComplex [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {X' : Type u} [TopologicalSpace X'] {p : X' → K.space}
    (hp : IsCoveringMap p) (hfin : ∀ x, (p ⁻¹' {x}).Finite) :
    ∃ (N : ℕ)
      (K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (e : K'.space ≃ₜ X'),
      K'.faces.Finite ∧
      (∀ q, ∀ hq : q ∈ K'.faces,
        ∃ t ∈ K.faces,
        ∃ A : EuclideanSpace ℝ (Fin N) →ᵃ[ℝ] E,
          (∀ x (hx : x ∈ convexHull ℝ (q : Set _)),
            ((p (e ⟨x, K'.convexHull_subset_space hq hx⟩) : K.space) : E) = A x) ∧
          A '' convexHull ℝ (q : Set _) = convexHull ℝ (t : Set E)) ∧
      ∀ n, IsCombinatorialManifoldWithBoundary n K →
        IsCombinatorialManifoldWithBoundary n K' := by
  let _ : Finite (coveringVertex K p) := coveringVertex.finite K hfin
  refine ⟨Nat.card (coveringVertex K p), coveringComplex K p,
    coveringSpaceHomeomorph K p hp, coveringComplex_faces_finite K p, ?_, ?_⟩
  · intro q hq
    obtain ⟨s, hs, hqeq⟩ := (mem_coveringComplex_faces_iff K p).mp hq
    let d : CoveringFaceData K p s := Classical.choice hs
    obtain ⟨A, hA⟩ := exists_affineMap_eqOn_coveringBaseMap K p hq
    refine ⟨s.image coveringVertex.base, d.face, A, ?_, ?_⟩
    · intro x hx
      calc
        ((p (coveringSpaceHomeomorph K p hp
              ⟨x, (coveringComplex K p).convexHull_subset_space hq hx⟩) : K.space) : E) =
            ((p (coveringSpaceMap K p
              ⟨x, (coveringComplex K p).convexHull_subset_space hq hx⟩) : K.space) : E) := by
                rw [coveringSpaceHomeomorph_apply]
        _ = coveringBaseMap K p x := coveringSpaceMap_projection K p _
        _ = A x := hA hx
    · calc
        A '' convexHull ℝ (q : Set _) =
            coveringBaseMap K p '' convexHull ℝ (q : Set _) := by
              apply Set.image_congr
              intro x hx
              exact (hA hx).symm
        _ = convexHull ℝ ((s.image coveringVertex.base : Finset E) : Set E) := by
          rw [hqeq]
          exact coveringBaseMap_image_convexHull K p d
  · intro n hn
    exact isCombinatorialManifoldWithBoundary_coveringComplex K p hp hn

end DifferentialGeometry.Topology.PiecewiseLinear
