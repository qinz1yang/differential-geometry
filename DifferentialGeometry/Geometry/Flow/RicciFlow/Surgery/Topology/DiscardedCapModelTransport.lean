import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapMaps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedOrientedStage
import DifferentialGeometry.Topology.Manifold.Components
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

noncomputable section

open Set Metric Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

universe u

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem exists_discardedCap_model_collar_of_component_diffeomorph
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ThreeSpace Y]
    [IsManifold ThreeModel ∞ Y]
    (component : ConnectedComponents D.Carrier)
    (e : (D.toClosedOrientedManifold.component component).Carrier
      ≃ₘ⟮ThreeModel, ThreeModel⟯ Y)
    (boundary : E.trace.tubes.Boundary) (hdiscarded : E.trace.capDiscarded boundary)
    (hcomponent : ConnectedComponents.mk
      (E.trace.discardedCap boundary hdiscarded (0 : ThreeBall)) = component)
    (c : SmoothTwoSidedCollar (𝓡 2) ThreeModel
      (fun z : Sphere 2 => E.trace.discardedCap boundary hdiscarded (sphereToThreeBall z)))
    (capSide : {q : Sphere 2 × symmetricOpenInterval c.radius // q.2.val ≤ 0} → ThreeBall)
    (hcap : ∀ q (hq : q.2.val ≤ 0),
      c.toFun q = E.trace.discardedCap boundary hdiscarded (capSide ⟨q, hq⟩)) :
    let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
    ∃ (fCap : C(ThreeBall, Y))
      (profile : C(Sphere 2 × symmetricOpenInterval c.radius, Y)),
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ fCap ∧
      (∀ x : ThreeBall, (e.symm (fCap x)).val =
        E.trace.discardedCap boundary hdiscarded x) ∧
      (∀ z : Sphere 2, (e.symm (fCap (sphereToThreeBall z))).val =
        E.trace.discardedCoreInclusion
          ⟨E.trace.tubes.coreBoundarySphere boundary (E.trace.capping.attaching boundary z),
            E.trace.capDiscarded_coreBoundarySphere_not_mem_retainedCore boundary hdiscarded _⟩) ∧
      ContMDiff ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ profile ∧
      (∀ q, (e.symm (profile q)).val = c.toFun q) ∧
      (∀ q (hq : q.2.val ≤ 0), profile q = fCap (capSide ⟨q, hq⟩)) := by
  let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  let U := D.toClosedOrientedManifold.componentOpen component
  let : IsManifold ThreeModel ∞ U := (D.toClosedOrientedManifold.component component).smooth
  let : PreconnectedSpace ThreeBall := isPreconnected_iff_preconnectedSpace.mp
    (convex_closedBall (0 : ThreeSpace) 1).isPreconnected
  have hmem (x : ThreeBall) : E.trace.discardedCap boundary hdiscarded x ∈ U := by
    have hconn := isPreconnected_range (E.trace.discardedCap boundary hdiscarded).continuous
    have hsub := hconn.subset_connectedComponent (mem_range_self (0 : ThreeBall))
    change ConnectedComponents.mk (E.trace.discardedCap boundary hdiscarded x) = component
    exact (ConnectedComponents.coe_eq_coe'.mpr (hsub (mem_range_self x))).trans hcomponent
  let j : ThreeBall → U := fun x => ⟨E.trace.discardedCap boundary hdiscarded x, hmem x⟩
  have hj : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ j := by
    apply DifferentialGeometry.Topology.isSmoothEmbedding_of_lift_through_localDiffeomorph
      (I := 𝓡∂ 3) (J := ThreeModel) (N := U) (g := j)
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val U)
      (E.discardedCap_isSmoothEmbedding boundary hdiscarded)
      ((E.trace.discardedCap boundary hdiscarded).continuous.subtype_mk hmem)
    intro x
    rfl
  let fCap : C(ThreeBall, Y) := ⟨e ∘ j, e.continuous.comp hj.contMDiff.continuous⟩
  have hf : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ fCap :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
      (𝓡∂ 3) ThreeModel j hj e
  have hfe (x : ThreeBall) : (e.symm (fCap x)).val =
      E.trace.discardedCap boundary hdiscarded x :=
    congrArg Subtype.val (e.symm_apply_apply (j x))
  let : PreconnectedSpace (Sphere 2) := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) 1)
  let : PreconnectedSpace (symmetricOpenInterval c.radius) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  let v : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hcU (q : Sphere 2 × symmetricOpenInterval c.radius) : c.toFun q ∈ U := by
    have hconn := isPreconnected_range c.isOpenEmbedding_toFun.continuous
    have hs := hconn.subset_connectedComponent
      (mem_range_self (v, ⟨0, neg_lt_zero.mpr c.radius_pos, c.radius_pos⟩))
    have h := hs (mem_range_self q)
    rw [c.toFun_zero] at h
    change ConnectedComponents.mk (c.toFun q) = component
    exact (ConnectedComponents.coe_eq_coe'.mpr h).trans (hmem (sphereToThreeBall v))
  let k : Sphere 2 × symmetricOpenInterval c.radius → U := fun q => ⟨c.toFun q, hcU q⟩
  have hk : ContMDiff ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ k := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    change ContMDiff ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ c.toFun
    exact contMDiff_subtype_val.comp c.toDiffeomorph.contMDiff
  let profile : C(Sphere 2 × symmetricOpenInterval c.radius, Y) :=
    ⟨e ∘ k, e.continuous.comp hk.continuous⟩
  have hp (q : Sphere 2 × symmetricOpenInterval c.radius) :
      (e.symm (profile q)).val = c.toFun q :=
    congrArg Subtype.val (e.symm_apply_apply (k q))
  refine ⟨fCap, profile, hf, hfe, ?_, e.contMDiff.comp hk, hp, ?_⟩
  · intro z
    exact (hfe (sphereToThreeBall z)).trans (E.trace.discardedCap_boundary boundary hdiscarded z)
  · intro q hq
    apply e.symm.injective
    apply Subtype.ext
    exact (hp q).trans ((hcap q hq).trans (hfe _).symm)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition
