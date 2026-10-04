import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSurgery
import DifferentialGeometry.Topology.ThreeManifold.Surgery.CutCap.CapFundamentalGroup
import
  DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.SelectedCoreAmbientFundamentalGroup

/-!
# Actual port maps through spherical cut and cap

Restricting the spherical tubes to their open height interval gives actual buffered necks with
exactly the original cut core. A torus avoiding the surgery region lifts to that core and its
basepoint component, with literal ambient and capped composite maps. Ambient injection and the
actual capping fundamental-group bijection compare injectivity of those torus maps.
-/

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology ContinuousMap
universe u

namespace GC.Seifert
open DifferentialGeometry.Topology.ThreeManifold.Surgery

private local instance cutCapTubeBounds : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

def cutCapTubeCoordinate (z : bufferedCylinder 1) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (-2 : ℝ) 2 :=
  (z.val.1, ⟨z.val.2, by
    have hz := z.property
    norm_num [bufferedCylinder] at hz
    exact ⟨hz.1.le, hz.2.le⟩⟩)

theorem cutCapTubeCoordinate_continuous : Continuous cutCapTubeCoordinate :=
  (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

theorem cutCapTubeCoordinate_isEmbedding : _root_.Topology.IsEmbedding cutCapTubeCoordinate := by
  let g : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (-2 : ℝ) 2) →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ :=
    fun z => (z.1, z.2.val)
  have hg : Continuous g := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  apply _root_.Topology.IsEmbedding.of_comp cutCapTubeCoordinate_continuous hg
  change _root_.Topology.IsEmbedding (Subtype.val : bufferedCylinder 1 → _)
  exact _root_.Topology.IsEmbedding.subtypeVal

variable {M P : ClosedOrientedManifold.{u} 3}

def cutCapPortBufferedMap (T : SphericalTubeSystem M) (a : T.Index) :
    bufferedCylinder 1 → M.Carrier := T.tube a ∘ cutCapTubeCoordinate

theorem cutCapPortBufferedMap_range (T : SphericalTubeSystem M) (a : T.Index) :
    range (cutCapPortBufferedMap T a) =
      T.tube a '' {z | (-2 : ℝ) < z.2.val ∧ z.2.val < 2} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨cutCapTubeCoordinate z, ?_, rfl⟩
    have hz := z.property
    norm_num [bufferedCylinder] at hz
    exact hz
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨(z.1, z.2.val), ?_⟩, ?_⟩
    · norm_num [bufferedCylinder]
      exact hz
    · apply congrArg (T.tube a)
      exact Prod.ext rfl (Subtype.ext rfl)

theorem cutCapPortBufferedMap_isOpenEmbedding (T : SphericalTubeSystem M) (a : T.Index) :
    _root_.Topology.IsOpenEmbedding (cutCapPortBufferedMap T a) := by
  refine ⟨(T.smooth a).isEmbedding.comp cutCapTubeCoordinate_isEmbedding, ?_⟩
  rw [cutCapPortBufferedMap_range]
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨z, hz, rfl⟩
  apply immersion_image_mem_nhds ((T.smooth a).isImmersion.isImmersionAt z)
  · simp [EuclideanSpace, Module.finrank_prod]
  · change z ∈ ((𝓡 2).prod (𝓡∂ 1)).interior
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (-2 : ℝ) 2)
    rw [ModelWithCorners.interior_prod]
    exact ⟨BoundarylessManifold.isInteriorPoint, Icc_isInteriorPoint_interior hz⟩
  · exact ((isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)).mem_nhds hz

theorem cutCapPortBufferedMap_disjoint (T : SphericalTubeSystem M) :
    Pairwise (fun a b => Disjoint (range (cutCapPortBufferedMap T a))
      (range (cutCapPortBufferedMap T b))) := by
  intro a b hab
  apply (T.disjoint hab).mono
  · rintro y ⟨z, rfl⟩
    exact ⟨cutCapTubeCoordinate z, rfl⟩
  · rintro y ⟨z, rfl⟩
    exact ⟨cutCapTubeCoordinate z, rfl⟩

theorem cutCapPortBufferedCore_eq (T : SphericalTubeSystem M) :
    cutCore (cutCapPortBufferedMap T) = T.core := by
  apply congrArg compl
  congr 1
  ext a y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨cutCapTubeCoordinate z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨(z.1, z.2.val), ?_⟩, hz, ?_⟩
    · have hz' : -2 < z.2.val ∧ z.2.val < 2 :=
        ⟨by linarith [hz.1], by linarith [hz.2]⟩
      norm_num [bufferedCylinder]
      exact hz'
    · apply congrArg (T.tube a)
      exact Prod.ext rfl (Subtype.ext rfl)

def cutCapCoreHomeomorph (T : SphericalTubeSystem M) :
    T.core ≃ₜ cutCore (cutCapPortBufferedMap T) :=
  Homeomorph.setCongr (cutCapPortBufferedCore_eq T).symm

theorem cutCapCoreHomeomorph_val (T : SphericalTubeSystem M) (x : T.core) :
    (cutCapCoreHomeomorph T x).val = x.val := by
  simp [cutCapCoreHomeomorph, Homeomorph.setCongr]

def cutCapCoreComponentHomeomorph (T : SphericalTubeSystem M) (x : T.core) :
    connectedComponent x ≃ₜ
      retainedCore (cutCapPortBufferedMap T)
        {ConnectedComponents.mk (cutCapCoreHomeomorph T x)} := by
  let e := cutCapCoreHomeomorph T
  have hmem (y : connectedComponent x) :
      e y.val ∈ retainedCore (cutCapPortBufferedMap T) {ConnectedComponents.mk (e x)} := by
    change ConnectedComponents.mk (e y.val) = ConnectedComponents.mk (e x)
    exact ConnectedComponents.coe_eq_coe'.mpr
      (e.continuous.image_connectedComponent_subset x ⟨y.val, y.property, rfl⟩)
  have hinv (z : retainedCore (cutCapPortBufferedMap T) {ConnectedComponents.mk (e x)}) :
      e.symm z.val ∈ connectedComponent x := by
    have hz : z.val ∈ connectedComponent (e x) := ConnectedComponents.coe_eq_coe'.mp z.property
    have h := e.symm.continuous.image_connectedComponent_subset (e x) ⟨z.val, hz, rfl⟩
    rwa [e.symm_apply_apply] at h
  exact {
    toFun := fun y => ⟨e y.val, hmem y⟩
    invFun := fun z => ⟨e.symm z.val, hinv z⟩
    left_inv := fun y => Subtype.ext (e.symm_apply_apply y.val)
    right_inv := fun z => Subtype.ext (e.apply_symm_apply z.val)
    continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk hmem
    continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk hinv }

private theorem cutCapPortMap_comp {A B C : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] (f : C(A, B)) (g : C(B, C)) (a : A) :
    FundamentalGroup.map (g.comp f) a =
      (FundamentalGroup.map g (f a)).comp (FundamentalGroup.map f a) := by
  ext p
  exact Path.Homotopic.Quotient.map_comp

def cutCapCoreComponentAmbient (T : SphericalTubeSystem M) (x : T.core) :
    C(connectedComponent x, M.Carrier) :=
  ⟨fun y => y.val.val, continuous_subtype_val.comp continuous_subtype_val⟩

theorem cutCapCoreComponentAmbient_injective (T : SphericalTubeSystem M)
    (x : T.core) (y : connectedComponent x) :
    Injective (FundamentalGroup.map (cutCapCoreComponentAmbient T x) y) := by
  let : LocallyPathConnectedSpace M.Carrier :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M.Carrier
  let e := cutCapCoreComponentHomeomorph T x
  let f : C(connectedComponent x, retainedCore (cutCapPortBufferedMap T)
      {ConnectedComponents.mk (cutCapCoreHomeomorph T x)}) := e
  let g : C(retainedCore (cutCapPortBufferedMap T)
      {ConnectedComponents.mk (cutCapCoreHomeomorph T x)}, connectedComponent x) := e.symm
  have he := injective_fundamentalGroup_map_of_leftInverse f g e.left_inv y
  have hi := injective_fundamentalGroup_retainedCoreAmbientInclusion
    (fun a : T.Index => (by norm_num : (0 : ℝ) < 1)) (cutCapPortBufferedMap T)
    (cutCapPortBufferedMap_isOpenEmbedding T) (cutCapPortBufferedMap_disjoint T)
    (ConnectedComponents.mk (cutCapCoreHomeomorph T x)) (f y)
  have hcomp : cutCapCoreComponentAmbient T x =
      (retainedCoreAmbientInclusion (cutCapPortBufferedMap T)
        {ConnectedComponents.mk (cutCapCoreHomeomorph T x)}).comp f := by
    ext z
    exact (cutCapCoreHomeomorph_val T z.val).symm
  rw [hcomp, cutCapPortMap_comp]
  exact hi.comp he


variable {Q : ConnectedClosedOrientedManifold.{u} 3}

def cutCapPortCoreLift (X : SphericalCutCapTransition Q.toClosedOrientedManifold P)
    (G : TorusPresentation (NoCuts.carrier Q)) (j : Fin G.pairing.count)
    (havoid : Disjoint (range (G.seamTorus j)) X.tubes.surgeryRegion) :
    C(Torus, X.tubes.core) := by
  have hmem (t : Torus) : G.seamTorus j t ∈ X.tubes.core := by
    intro ht
    obtain ⟨a, z, hz, he⟩ := by
      simpa only [SphericalTubeSystem.core, mem_compl_iff, mem_iUnion,
        SphericalTubeSystem.removedBand, mem_image] using ht
    have hreg : G.seamTorus j t ∈ X.tubes.surgeryRegion :=
      mem_iUnion.mpr ⟨a, z, ⟨by linarith [hz.1], by linarith [hz.2]⟩, he⟩
    exact disjoint_left.mp havoid (mem_range_self t) hreg
  exact ⟨fun t => ⟨G.seamTorus j t, hmem t⟩, (G.seamTorus j).continuous.subtype_mk hmem⟩

def cutCapPortComponentLift (X : SphericalCutCapTransition Q.toClosedOrientedManifold P)
    (G : TorusPresentation (NoCuts.carrier Q)) (j : Fin G.pairing.count)
    (havoid : Disjoint (range (G.seamTorus j)) X.tubes.surgeryRegion) (t₀ : Torus) :
    C(Torus, connectedComponent (cutCapPortCoreLift X G j havoid t₀)) :=
  ⟨fun t => ⟨cutCapPortCoreLift X G j havoid t,
      (cutCapPortCoreLift X G j havoid).continuous.image_connectedComponent_subset t₀
        ⟨t, by simp only [PreconnectedSpace.connectedComponent_eq_univ, mem_univ], rfl⟩⟩,
    (cutCapPortCoreLift X G j havoid).continuous.subtype_mk _⟩

def cutCapPortCappedMap (X : SphericalCutCapTransition Q.toClosedOrientedManifold P)
    (G : TorusPresentation (NoCuts.carrier Q)) (j : Fin G.pairing.count)
    (havoid : Disjoint (range (G.seamTorus j)) X.tubes.surgeryRegion) (t₀ : Torus) :
    C(Torus, (X.capped.component (ConnectedComponents.mk
      (X.capping.coreInclusion (cutCapPortCoreLift X G j havoid t₀)))).Carrier) :=
  (X.coreComponentCapMap
    (ConnectedComponents.mk (X.capping.coreInclusion (cutCapPortCoreLift X G j havoid t₀)))
    (cutCapPortCoreLift X G j havoid t₀) rfl).comp
      (cutCapPortComponentLift X G j havoid t₀)

theorem cutCapPortComponentLift_ambient
    (X : SphericalCutCapTransition Q.toClosedOrientedManifold P)
    (G : TorusPresentation (NoCuts.carrier Q)) (j : Fin G.pairing.count)
    (havoid : Disjoint (range (G.seamTorus j)) X.tubes.surgeryRegion) (t₀ : Torus) :
    (cutCapCoreComponentAmbient X.tubes (cutCapPortCoreLift X G j havoid t₀)).comp
      (cutCapPortComponentLift X G j havoid t₀) = G.seamTorus j :=
  ContinuousMap.ext fun t => (rfl : G.seamTorus j t = G.seamTorus j t)

theorem cutCapPortCappedMap_inclusion
    (X : SphericalCutCapTransition Q.toClosedOrientedManifold P)
    (G : TorusPresentation (NoCuts.carrier Q)) (j : Fin G.pairing.count)
    (havoid : Disjoint (range (G.seamTorus j)) X.tubes.surgeryRegion) (t₀ : Torus) :
    (⟨Subtype.val, continuous_subtype_val⟩ :
      C((X.capped.component (ConnectedComponents.mk
        (X.capping.coreInclusion (cutCapPortCoreLift X G j havoid t₀)))).Carrier,
          X.capped.Carrier)).comp (cutCapPortCappedMap X G j havoid t₀) =
            X.capping.coreInclusion.comp (cutCapPortCoreLift X G j havoid) :=
  ContinuousMap.ext fun t =>
    (rfl : X.capping.coreInclusion (cutCapPortCoreLift X G j havoid t) =
      X.capping.coreInclusion (cutCapPortCoreLift X G j havoid t))

theorem cutCapPortInjective_iff
    (X : SphericalCutCapTransition Q.toClosedOrientedManifold P)
    (G : TorusPresentation (NoCuts.carrier Q)) (j : Fin G.pairing.count)
    (havoid : Disjoint (range (G.seamTorus j)) X.tubes.surgeryRegion) (t₀ : Torus) :
    Injective (FundamentalGroup.map (G.seamTorus j) t₀) ↔
      Injective (FundamentalGroup.map (cutCapPortCappedMap X G j havoid t₀) t₀) := by
  let i := cutCapPortComponentLift X G j havoid t₀
  let x := cutCapPortCoreLift X G j havoid t₀
  let κ := X.coreComponentCapMap (ConnectedComponents.mk (X.capping.coreInclusion x)) x rfl
  have ha := cutCapCoreComponentAmbient_injective X.tubes x (i t₀)
  have hc := (X.fundamentalGroup_map_coreComponentCapMap_bijective
    (ConnectedComponents.mk (X.capping.coreInclusion x)) x rfl (i t₀)).injective
  rw [← cutCapPortComponentLift_ambient X G j havoid t₀]
  change Injective (FundamentalGroup.map ((cutCapCoreComponentAmbient X.tubes x).comp i) t₀) ↔
    Injective (FundamentalGroup.map (κ.comp i) t₀)
  rw [cutCapPortMap_comp, cutCapPortMap_comp]
  constructor
  · intro h
    have hi : Injective (FundamentalGroup.map i t₀) := by
      intro a b hab
      exact h (congrArg (FundamentalGroup.map (cutCapCoreComponentAmbient X.tubes x) (i t₀)) hab)
    exact hc.comp hi
  · intro h
    have hi : Injective (FundamentalGroup.map i t₀) := by
      intro a b hab
      exact h (congrArg (FundamentalGroup.map κ (i t₀)) hab)
    exact ha.comp hi

end GC.Seifert
