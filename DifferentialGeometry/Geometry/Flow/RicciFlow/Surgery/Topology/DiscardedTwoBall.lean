import DifferentialGeometry.Topology.ThreeManifold.TwoBallCover
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapCollar
import Mathlib.Analysis.Normed.Module.Connected
import DifferentialGeometry.Topology.ThreeManifold.TwoBallCharts
import DifferentialGeometry.Topology.Manifold.Components
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedOrientedStage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapMaps
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeInvarianceObstruction

noncomputable section

open Set Metric Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S3" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem exists_sphere_diffeomorph_of_discarded_cap_and_complementary_ball
    (c : ConnectedComponents D.Carrier)
    (boundary : E.trace.tubes.Boundary) (hdiscarded : E.trace.capDiscarded boundary)
    (A B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3
      (D.toClosedOrientedManifold.component c).Carrier ∞)
    (hA : closedBall (0 : E3) 1 ⊆ A.source)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hcap : ∀ (z : E3) (hz : z ∈ closedBall (0 : E3) 1),
      (A z).val = E.trace.discardedCap boundary hdiscarded ⟨z, hz⟩)
    (hcover : B '' ball (0 : E3) 1 = (A '' closedBall (0 : E3) 1)ᶜ) :
    ∃ e : S3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ (D.toClosedOrientedManifold.component c).Carrier,
      (∃ a b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞,
        a.source = univ ∧ b.source = univ ∧
        a '' closedBall (0 : E3) 1 = (b '' ball (0 : E3) 1)ᶜ ∧
        (∀ (z : E3) (hz : z ∈ closedBall (0 : E3) 1),
          (e (a z)).val = E.trace.discardedCap boundary hdiscarded ⟨z, hz⟩) ∧
        ∃ F : E3 ≃ₘ[ℝ] E3,
          F '' closedBall (0 : E3) 1 = closedBall (0 : E3) 1 ∧
          ∀ z ∈ closedBall (0 : E3) 1, e (b z) = B (F z)) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (D.toClosedOrientedManifold.component c).toClosedOrientedManifold
        standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  obtain ⟨e, a, b, ha, hb, hab, heA, F, hF, heB⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_complementary_ball_charts
      A B hA hB hcover
  refine ⟨e, ⟨a, b, ha, hb, hab, ?_, F, hF, heB⟩, ?_⟩
  · intro z hz
    rw [heA z hz]
    exact hcap z hz
  · exact nonempty_orientedDiffeomorph_standardThreeSphere_of_diffeomorph
      (D.toClosedOrientedManifold.component c)
      ⟨e.symm.trans standardThreeSphereLiftDiffeomorph⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

universe u

local notation "S3" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem exists_discardedCap_sphere_model_of_component_ball_cover
    (c : ConnectedComponents D.Carrier)
    (boundary : E.trace.tubes.Boundary) (hdiscarded : E.trace.capDiscarded boundary)
    (A B : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace
      (D.toClosedOrientedManifold.component c).Carrier ∞)
    (hA : closedBall (0 : ThreeSpace) 1 ⊆ A.source)
    (hB : closedBall (0 : ThreeSpace) 1 ⊆ B.source)
    (hcover : B '' closedBall (0 : ThreeSpace) 1 ∪ A '' closedBall (0 : ThreeSpace) 1 = univ)
    (hcap : range (E.trace.discardedCap boundary hdiscarded) ⊆
      (Subtype.val : (D.toClosedOrientedManifold.component c).Carrier → D.Carrier) ''
        (B '' closedBall (0 : ThreeSpace) 1)) :
    let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
    ∃ (e : (D.toClosedOrientedManifold.component c).Carrier ≃ₘ⟮ThreeModel,ThreeModel⟯ S3)
      (a : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace S3 ∞)
      (fCap : C(ThreeBall,S3)),
      a.source = univ ∧
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ fCap ∧
      (∀ x : ThreeBall, (e.symm (fCap x)).val = E.trace.discardedCap boundary hdiscarded x) ∧
      (∀ x : ThreeBall, fCap x = a (B.symm (e.symm (fCap x)))) ∧
      (∀ s : Sphere 2, (e.symm (fCap (sphereToThreeBall s))).val =
        E.trace.discardedCoreInclusion
          ⟨E.trace.tubes.coreBoundarySphere boundary (E.trace.capping.attaching boundary s),
            E.trace.capDiscarded_coreBoundarySphere_not_mem_retainedCore boundary hdiscarded _⟩) ∧
      (∃ U : Set (D.toClosedOrientedManifold.component c).Carrier,
        IsOpen U ∧ B '' closedBall (0 : ThreeSpace) 1 ⊆ U ∧
          U ⊆ (B.symm.trans a).source ∧ EqOn e (B.symm.trans a) U) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (D.toClosedOrientedManifold.component c).toClosedOrientedManifold
        standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  let U₀ := D.toClosedOrientedManifold.componentOpen c
  let : IsManifold ThreeModel ∞ U₀ := (D.toClosedOrientedManifold.component c).smooth
  have hmem (x : ThreeBall) : E.trace.discardedCap boundary hdiscarded x ∈ U₀ := by
    obtain ⟨y,hy,he⟩ := hcap (mem_range_self x)
    exact he ▸ y.property
  let j : ThreeBall → U₀ := fun x => ⟨E.trace.discardedCap boundary hdiscarded x,hmem x⟩
  have hj : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ j := by
    apply DifferentialGeometry.Topology.isSmoothEmbedding_of_lift_through_localDiffeomorph
      (I := 𝓡∂ 3) (J := ThreeModel) (N := U₀) (g := j)
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val U₀)
      (E.discardedCap_isSmoothEmbedding boundary hdiscarded)
      ((E.trace.discardedCap boundary hdiscarded).continuous.subtype_mk hmem)
    intro x
    rfl
  have hjB (x : ThreeBall) : j x ∈ B '' closedBall (0 : ThreeSpace) 1 := by
    obtain ⟨y,hy,he⟩ := hcap (mem_range_self x)
    have hyj : y = j x := Subtype.ext he
    exact hyj ▸ hy
  obtain ⟨e,a,b,G,ha,_,_,_,_,_,_,_,_,U,hU,hBU,hUs,hEq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_ball_chart_cover A B hA hB hcover
  let fCap : C(ThreeBall,S3) := ⟨e ∘ j,e.continuous.comp hj.contMDiff.continuous⟩
  have hf : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ fCap :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
      (𝓡∂ 3) ThreeModel j hj e
  have hfj (x : ThreeBall) : e.symm (fCap x) = j x := e.symm_apply_apply _
  refine ⟨e,a,fCap,ha,hf,?_,?_,?_,⟨U,hU,hBU,hUs,hEq⟩,?_⟩
  · intro x
    exact congrArg Subtype.val (hfj x)
  · intro x
    rw [hfj]
    exact hEq (hBU (hjB x))
  · intro s
    exact (congrArg Subtype.val (hfj (sphereToThreeBall s))).trans
      (E.trace.discardedCap_boundary boundary hdiscarded s)
  · exact nonempty_orientedDiffeomorph_standardThreeSphere_of_diffeomorph
      (D.toClosedOrientedManifold.component c)
      ⟨e.trans standardThreeSphereLiftDiffeomorph⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

universe u

local notation "S3" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem exists_discardedCap_sphere_collar_of_component_ball_cover
    (component : ConnectedComponents D.Carrier)
    (boundary : E.trace.tubes.Boundary) (hdiscarded : E.trace.capDiscarded boundary)
    (A B : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace
      (D.toClosedOrientedManifold.component component).Carrier ∞)
    (hA : closedBall (0 : ThreeSpace) 1 ⊆ A.source)
    (hB : closedBall (0 : ThreeSpace) 1 ⊆ B.source)
    (hcover : B '' closedBall (0 : ThreeSpace) 1 ∪ A '' closedBall (0 : ThreeSpace) 1 = univ)
    (hcapB : range (E.trace.discardedCap boundary hdiscarded) ⊆
      (Subtype.val : (D.toClosedOrientedManifold.component component).Carrier → D.Carrier) ''
        (B '' closedBall (0 : ThreeSpace) 1))
    (c : SmoothTwoSidedCollar (𝓡 2) ThreeModel
      (fun z : Sphere 2 => E.trace.discardedCap boundary hdiscarded (sphereToThreeBall z)))
    (capSide : {q : Sphere 2 × symmetricOpenInterval c.radius // q.2.val ≤ 0} → ThreeBall)
    (hcap : ∀ q (hq : q.2.val ≤ 0), c.toFun q = E.trace.discardedCap boundary hdiscarded (capSide ⟨q,hq⟩)) :
    let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
    ∃ (e : (D.toClosedOrientedManifold.component component).Carrier ≃ₘ⟮ThreeModel,ThreeModel⟯ S3)
      (a : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace S3 ∞)
      (fCap : C(ThreeBall,S3)) (profile : C(Sphere 2 × symmetricOpenInterval c.radius,S3)),
      a.source = univ ∧ IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ fCap ∧
      (∀ x : ThreeBall, (e.symm (fCap x)).val = E.trace.discardedCap boundary hdiscarded x) ∧
      ContMDiff ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ profile ∧
      (∀ q, (e.symm (profile q)).val = c.toFun q) ∧
      (∀ q (hq : q.2.val ≤ 0), profile q = fCap (capSide ⟨q,hq⟩)) ∧
      (∃ U : Set (D.toClosedOrientedManifold.component component).Carrier,
        IsOpen U ∧ B '' closedBall (0 : ThreeSpace) 1 ⊆ U ∧
          U ⊆ (B.symm.trans a).source ∧ EqOn e (B.symm.trans a) U) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (D.toClosedOrientedManifold.component component).toClosedOrientedManifold
        standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  obtain ⟨e,a,fCap,ha,hf,hfe,hfa,hfb,⟨U,hU,hBU,hUs,hEq⟩,horiented⟩ :=
    E.exists_discardedCap_sphere_model_of_component_ball_cover component boundary hdiscarded A B hA hB hcover hcapB
  let U₀ := D.toClosedOrientedManifold.componentOpen component
  let : IsManifold ThreeModel ∞ U₀ := (D.toClosedOrientedManifold.component component).smooth
  let : PreconnectedSpace (Sphere 2) := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) 1)
  let : PreconnectedSpace (symmetricOpenInterval c.radius) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  let v : Sphere 2 := ⟨EuclideanSpace.single 0 1,by simp⟩
  have hcU (q : Sphere 2 × symmetricOpenInterval c.radius) : c.toFun q ∈ U₀ := by
    have hconn := isPreconnected_range c.isOpenEmbedding_toFun.continuous
    have hs := hconn.subset_connectedComponent
      (mem_range_self (v,⟨0,neg_lt_zero.mpr c.radius_pos,c.radius_pos⟩))
    have h := hs (mem_range_self q)
    rw [c.toFun_zero] at h
    change ConnectedComponents.mk (c.toFun q) = component
    exact (ConnectedComponents.coe_eq_coe'.mpr h).trans
      ((congrArg ConnectedComponents.mk (hfe (sphereToThreeBall v))).symm.trans
        (e.symm (fCap (sphereToThreeBall v))).property)
  let j : Sphere 2 × symmetricOpenInterval c.radius → U₀ := fun q => ⟨c.toFun q,hcU q⟩
  have hj : ContMDiff ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ j := by
    apply (ContMDiff.subtypeVal_comp_iff U₀ _).mp
    change ContMDiff ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ c.toFun
    exact contMDiff_subtype_val.comp c.toDiffeomorph.contMDiff
  let profile : C(Sphere 2 × symmetricOpenInterval c.radius,S3) :=
    ⟨e ∘ j,e.continuous.comp hj.continuous⟩
  have hp (q : Sphere 2 × symmetricOpenInterval c.radius) : e.symm (profile q) = j q := e.symm_apply_apply _
  refine ⟨e,a,fCap,profile,ha,hf,hfe,e.contMDiff.comp hj,?_,?_,⟨U,hU,hBU,hUs,hEq⟩,horiented⟩
  · intro q
    exact congrArg Subtype.val (hp q)
  · intro q hq
    apply e.symm.injective
    apply Subtype.ext
    exact (congrArg Subtype.val (hp q)).trans ((hcap q hq).trans (hfe _).symm)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition
