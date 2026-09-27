import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Interior
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DirectSmooth
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.LocalMaps
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Locality

set_option autoImplicit false
noncomputable section
open Set Function Metric Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SelfAttachment

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  (c d : BallChart 3 (𝓡 3) M)
  (hcd : Disjoint (c.chart '' closedBall 0 2) (d.chart '' closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

theorem bandInteriorInclusion_not_mem_range_coreInclusion (p : bandInterior) :
    bandInteriorInclusion c d hcd a p ∉ range (coreInclusion c d hcd a) := by
  rintro ⟨x, hx⟩
  obtain ⟨⟨b, z⟩, hb, _⟩ := (bandInclusion_eq_coreInclusion_iff c d hcd a _ x).mp hx.symm
  have ht := congrArg (fun q : Band (n := 3) => q.2.val) hb
  cases b
  · change 0 = p.val.2 at ht
    exact (ne_of_gt p.property.2.1) ht.symm
  · change 1 = p.val.2 at ht
    exact (ne_of_lt p.property.2.2) ht.symm

end DifferentialGeometry.Topology.SelfAttachment

namespace DifferentialGeometry.Topology.SmoothSelfAttachment

universe u v
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {c d : OrientedBallChart M.toClosedOrientedManifold}
  {hcd : Disjoint (c.chart '' closedBall 0 2) (d.chart '' closedBall 0 2)}
  {a : BoundaryAttachment} (S : SmoothSelfAttachment c d hcd a)
  {Z : ClosedOrientedManifold.{v} 3}
  (F : ClosedOrientedManifold.OrientedDiffeomorph S.toConnectedClosedOrientedManifold.toClosedOrientedManifold Z)
  {ι : Type*} (b : ι → OrientedBallChart Z)
  (hb : ∀ i, (b i).chart '' closedBall (0 : E3) 1 ⊆
    range (F.val ∘ SelfAttachment.coreInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph))

include hb in
theorem bandInteriorInclusion_not_mem_closedBall_union (p : SelfAttachment.bandInterior) :
    F.val (SelfAttachment.bandInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph p) ∉
      ⋃ i, (b i).chart '' closedBall (0 : E3) 1 := by
  intro hp
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  obtain ⟨x, hx⟩ := hb i hi
  exact SelfAttachment.bandInteriorInclusion_not_mem_range_coreInclusion
    c.toBallChart d.toBallChart hcd a.val.toHomeomorph p ⟨x, F.val.injective hx⟩

def bandInteriorComplement (p : SelfAttachment.bandInterior) :
    {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} :=
  ⟨F.val (SelfAttachment.bandInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph p),
    fun h => S.bandInteriorInclusion_not_mem_closedBall_union F b hb p
      (iUnion_mono (fun _ => image_mono ball_subset_closedBall) h)⟩

variable [Finite ι]
  (C : SmoothBoundaryAtlas (𝓡 3) 3 {y : Z.Carrier | y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1})

theorem bandInteriorComplement_isLocalDiffeomorph :
    let _ : ChartedSpace (EuclideanHalfSpace 3) {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := C.toChartedSpace
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞ (S.bandInteriorComplement F b hb) := by
  let _ := S.charts
  let _ : ChartedSpace (EuclideanHalfSpace 3) {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := C.toChartedSpace
  dsimp only
  intro p
  have hclosed : IsClosed (⋃ i, (b i).chart '' closedBall (0 : E3) 1) :=
    isClosed_iUnion_of_finite fun i => (b i).toBallChart.isCompact_closedBall_image.isClosed
  have hopen := hclosed.isOpen_compl
  have hsub : (⋃ i, (b i).chart '' closedBall (0 : E3) 1)ᶜ ⊆
      {y : Z.Carrier | y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} :=
    compl_subset_compl.mpr (iUnion_mono fun _ => image_mono ball_subset_closedBall)
  apply C.isLocalDiffeomorphAt_of_subtype_val (f := S.bandInteriorComplement F b hb) (x := p)
    (mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
      (hopen.mem_nhds (S.bandInteriorInclusion_not_mem_closedBall_union F b hb p)) hsub))
  exact (S.band_localDiffeomorph p).comp (𝓡 3) _ (F.val.isLocalDiffeomorph _)

private def seamBandParameter (p : SelfAttachment.directSeamDomain) : SelfAttachment.bandInterior :=
  ⟨(p.val.1, 1 / 2 - p.val.2), mem_univ _,
    by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩

def directSeamComplement (p : SelfAttachment.directSeamDomain) :
    {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} :=
  S.bandInteriorComplement F b hb (seamBandParameter p)

theorem directSeamComplement_isLocalDiffeomorph :
    let _ : ChartedSpace (EuclideanHalfSpace 3) {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := C.toChartedSpace
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞ (S.directSeamComplement F b hb) := by
  let _ := S.charts
  let _ : ChartedSpace (EuclideanHalfSpace 3) {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := C.toChartedSpace
  dsimp only
  intro p
  have hclosed : IsClosed (⋃ i, (b i).chart '' closedBall (0 : E3) 1) :=
    isClosed_iUnion_of_finite fun i => (b i).toBallChart.isCompact_closedBall_image.isClosed
  have hsub : (⋃ i, (b i).chart '' closedBall (0 : E3) 1)ᶜ ⊆
      {y : Z.Carrier | y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} :=
    compl_subset_compl.mpr (iUnion_mono fun _ => image_mono ball_subset_closedBall)
  apply C.isLocalDiffeomorphAt_of_subtype_val (f := S.directSeamComplement F b hb) (x := p)
    (mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
      (hclosed.isOpen_compl.mem_nhds
        (S.bandInteriorInclusion_not_mem_closedBall_union F b hb (seamBandParameter p))) hsub))
  have h := (S.directToBand_comp_directSeam_isLocalDiffeomorph p).comp (𝓡 3) _ (F.val.isLocalDiffeomorph _)
  have heq : (Subtype.val ∘ S.directSeamComplement F b hb) =
      F.val ∘ (SelfAttachment.directToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph ∘
        SelfAttachment.directSeam c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := by
    funext q
    exact congrArg F.val (SelfAttachment.directToBand_directSeam c.toBallChart d.toBallChart hcd a.val.toHomeomorph q).symm
  exact heq.symm ▸ h

end DifferentialGeometry.Topology.SmoothSelfAttachment

namespace DifferentialGeometry.Topology.SmoothSelfAttachment

universe u v
variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {c d : OrientedBallChart M.toClosedOrientedManifold}
  {hcd : Disjoint (c.chart '' closedBall 0 2) (d.chart '' closedBall 0 2)}
  {a : BoundaryAttachment} (S : SmoothSelfAttachment c d hcd a)
  {Z : ClosedOrientedManifold.{v} 3}
  (F : ClosedOrientedManifold.OrientedDiffeomorph S.toConnectedClosedOrientedManifold.toClosedOrientedManifold Z)
  {ι : Type*} (e : ι → OrientedBallChart M.toClosedOrientedManifold)
  (b : ι → OrientedBallChart Z)
  (hec : ∀ i x, x ∈ closedBall (0 : E3) 2 → (e i).chart x ∉ c.chart '' closedBall 0 2)
  (hed : ∀ i x, x ∈ closedBall (0 : E3) 2 → (e i).chart x ∉ d.chart '' closedBall 0 2)
  (hb : ∀ i x, x ∈ closedBall (0 : E3) 2 →
    ∃ hx : (e i).chart x ∈ (c.chart '' ball 0 1 ∪ d.chart '' ball 0 1)ᶜ,
      (b i).chart x = F.val (SelfAttachment.coreInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph
        ⟨(e i).chart x, hx⟩))

include hec hed hb in
theorem coreToBand_mem_ball_union_iff (x : c.toBallChart.DoublePunctured d.toBallChart) :
    F.val (SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph x) ∈
      ⋃ i, (b i).chart '' ball (0 : E3) 1 ↔ x.val ∈ ⋃ i, (e i).chart '' ball (0 : E3) 1 := by
  let U : Set (c.toBallChart.DoublePunctured d.toBallChart) :=
    {y | y.val ∈ ⋃ i, (e i).chart '' ball (0 : E3) 1}
  have hball : ball (0 : E3) 1 ⊆ closedBall (0 : E3) 2 :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  have hU (y : c.toBallChart.DoublePunctured d.toBallChart) (hy : y ∈ U) :
      y.val ∉ c.chart '' closedBall 0 2 ∧ y.val ∉ d.chart '' closedBall 0 2 := by
    obtain ⟨i, z, hz, hzy⟩ := mem_iUnion.mp hy
    exact ⟨hzy ▸ hec i z (hball hz), hzy ▸ hed i z (hball hz)⟩
  have heq : F.val (SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph x) ∈
      ⋃ i, (b i).chart '' ball (0 : E3) 1 ↔
      SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph x ∈
        SelfAttachment.coreInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph '' U := by
    constructor
    · intro h
      obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp h
      obtain ⟨hz', hbz⟩ := hb i z (hball hz)
      exact ⟨⟨(e i).chart z, hz'⟩, mem_iUnion.mpr ⟨i, z, hz, rfl⟩,
        F.val.injective (hbz.symm.trans hzx)⟩
    · rintro ⟨y, hy, hyx⟩
      obtain ⟨i, z, hz, hzy⟩ := mem_iUnion.mp hy
      obtain ⟨hz', hbz⟩ := hb i z (hball hz)
      refine mem_iUnion.mpr ⟨i, z, hz, hbz.trans ?_⟩
      exact congrArg F.val ((congrArg (SelfAttachment.coreInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
        (Subtype.ext hzy)).trans hyx)
  exact heq.trans (SelfAttachment.coreToBand_mem_core_image_iff c.toBallChart d.toBallChart hcd a.val.toHomeomorph
    U (fun y hy => (hU y hy).1) (fun y hy => (hU y hy).2) x)

variable {K : Set M.Carrier}
  (hK : ∀ x, x ∈ K ↔ x ∉ (c.chart '' ball 0 1 ∪ d.chart '' ball 0 1) ∪
    ⋃ i, (e i).chart '' ball (0 : E3) 1)
  (C : SmoothBoundaryAtlas (𝓡 3) 3 K)
  (D : SmoothBoundaryAtlas (𝓡 3) 3 {y : Z.Carrier | y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1})
  (f : K → {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1})
  (hf : ∀ x : K, ∃ hx,
    (f x).val = F.val (SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph ⟨x.val, hx⟩))

include hK hec hed hb hf in
theorem coreToBand_complement_isLocalDiffeomorphAt (x : K)
    (hx : x.val ∈ SelfAttachment.coreInterior c.toBallChart d.toBallChart) :
    let _ : ChartedSpace (EuclideanHalfSpace 3) K := C.toChartedSpace
    let _ : ChartedSpace (EuclideanHalfSpace 3) {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.toChartedSpace
    IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡∂ 3) ∞ f x := by
  let _ := S.charts
  let _ : ChartedSpace (EuclideanHalfSpace 3) K := C.toChartedSpace
  let _ : ChartedSpace (EuclideanHalfSpace 3) {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.toChartedSpace
  dsimp only
  let g : SelfAttachment.coreInterior c.toBallChart d.toBallChart → Z.Carrier :=
    F.val ∘ (SelfAttachment.coreToBand c.toBallChart d.toBallChart hcd a.val.toHomeomorph ∘
      SelfAttachment.coreInteriorToCore c.toBallChart d.toBallChart)
  have hg : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ g :=
    DifferentialGeometry.isLocalDiffeomorph_comp F.val.isLocalDiffeomorph S.coreToBand_isLocalDiffeomorph
  apply C.isLocalDiffeomorphAt_of_open_ambient_map D (SelfAttachment.coreInterior c.toBallChart d.toBallChart) g hg
  · intro y
    rw [hK]
    have he := S.coreToBand_mem_ball_union_iff F e b hec hed hb
      (SelfAttachment.coreInteriorToCore c.toBallChart d.toBallChart y)
    have hy : y.val ∉ c.chart '' ball 0 1 ∪ d.chart '' ball 0 1 :=
      (SelfAttachment.coreInteriorToCore c.toBallChart d.toBallChart y).property
    change ¬(y.val ∈ c.chart '' ball 0 1 ∪ d.chart '' ball 0 1 ∨
      y.val ∈ ⋃ i, (e i).chart '' ball (0 : E3) 1) ↔ _
    simp only [hy, false_or]
    exact not_congr he.symm
  · intro y hy
    obtain ⟨hy', hfy⟩ := hf y
    exact hfy
  · exact hx

end DifferentialGeometry.Topology.SmoothSelfAttachment
