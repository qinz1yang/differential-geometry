import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedMapOrientation
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport

noncomputable section
open Set Manifold Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem isClosed_diffeomorph_orientation_locus
    {M Y : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [TopologicalSpace Y] [ChartedSpace ThreeSpace Y]
    [IsManifold ThreeModel ∞ Y]
    (e : Diffeomorph ThreeModel ThreeModel M Y ∞)
    (oM : TangentOrientationSection M) (oY : TangentOrientationSection Y) :
    IsClosed {x : M | Orientation.map (Fin 3)
      (e.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv (oM.orientation x) =
      oY.orientation (e x)} := by
  let OM : DifferentialGeometry.ManifoldOrientation ThreeModel M 3 :=
    ⟨by simp [ThreeSpace], oM.orientation, oM.locally_constant⟩
  let OY : DifferentialGeometry.ManifoldOrientation ThreeModel Y 3 :=
    ⟨by simp [ThreeSpace], oY.orientation, oY.locally_constant⟩
  let L := fun x => e.mfderivToContinuousLinearEquiv (by simp) x
  have hpush := DifferentialGeometry.Topology.Manifold.isCompatibleOrientation_diffeomorph_map e
    OY.dimension_eq OM.orientation
    (DifferentialGeometry.Topology.Manifold.isCompatibleOrientation_of_manifoldOrientation OM)
  obtain ⟨OP, hOP⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_compatibleOrientation
      ThreeModel OY.dimension_eq
      (fun y => Orientation.map (Fin 3) (L (e.symm y)).toLinearEquiv (OM.orientation (e.symm y))) hpush
  have hclosed : IsClosed {y : Y | OP.orientation y = OY.orientation y} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    have hychart : y ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source ThreeSpace y
    obtain ⟨UP, hUP, hyP, hUPsrc, hP⟩ := OP.locally_constant y y hychart
    obtain ⟨UY, hUY, hyY, hUYsrc, hY⟩ := OY.locally_constant y y hychart
    apply Filter.mem_of_superset ((hUP.inter hUY).mem_nhds ⟨hyP, hyY⟩)
    intro z hz hzeq
    have heq : DifferentialGeometry.tangentChartEquiv ThreeModel Y y z (hUPsrc hz.1) =
        DifferentialGeometry.tangentChartEquiv ThreeModel Y y z (hUYsrc hz.2) := by
      rw [Subsingleton.elim (hUPsrc hz.1) (hUYsrc hz.2)]
    have htransport := (hP z hz.1).symm
    rw [heq, hzeq, hY z hz.2] at htransport
    exact hy ((Orientation.map (Fin 3)
      (DifferentialGeometry.tangentChartEquiv ThreeModel Y y y hychart)).injective htransport)
  have hpre := hclosed.preimage e.continuous
  have heq : e ⁻¹' {y : Y | OP.orientation y = OY.orientation y} =
      {x : M | Orientation.map (Fin 3)
        (e.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv (oM.orientation x) =
        oY.orientation (e x)} := by
    ext x
    change OP.orientation (e x) = OY.orientation (e x) ↔ _
    rw [hOP]
    beta_reduce
    erw [e.symm_apply_apply]
    rfl
  exact heq ▸ hpre


namespace SmoothCutCapTransition

universe u

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace ThreeSpace Y] [IsManifold ThreeModel ∞ Y]
  (oY : TangentOrientationSection Y)
  [hCompact : CompactSpace {x : E.trace.tubes.core // x ∉ E.trace.retainedCore}]
  (fCore : C({x : E.trace.tubes.core // x ∉ E.trace.retainedCore}, Y))
  (fCap : (b : {b : E.trace.tubes.Boundary // E.trace.capDiscarded b}) → C(ThreeBall, Y))
  (hboundary : ∀ (b : {b : E.trace.tubes.Boundary // E.trace.capDiscarded b}) (s : Sphere 2),
    fCap b (sphereToThreeBall s) = fCore
      ⟨E.trace.tubes.coreBoundarySphere b.1 (E.trace.capping.attaching b.1 s),
        E.trace.capDiscarded_coreBoundarySphere_not_mem_retainedCore b.1 b.2 _⟩)

include hCompact in
theorem discardedDesc_preservesTangentOrientation_of_piece_orientations
    (e : Diffeomorph ThreeModel ThreeModel D.Carrier Y ∞)
    (heq : (e : D.Carrier → Y) = E.trace.discardedDesc fCore fCap hboundary)
    (hcore : letI : ChartedSpace (EuclideanHalfSpace 3) {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} :=
        E.coreOpensCharts E.trace.discardedCoreOpen
      ∀ x : {x : E.trace.tubes.core // x ∉ E.trace.retainedCore}, (𝓡∂ 3).IsInteriorPoint x →
        ContMDiffAt (𝓡∂ 3) ThreeModel ∞ fCore x ∧
        ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
            (fun z : {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} => (z.val : P.Carrier)) x),
        ∃ hk : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel fCore x),
          Orientation.map (Fin 3)
            ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
              (fun z : {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} => (z.val : P.Carrier)) x).toLinearMap hi).symm.trans
              (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel fCore x).toLinearMap hk))
            (P.orientation.orientation x.val.val) = oY.orientation (fCore x))
    (hcap : letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
      ∀ (b : {b : E.trace.tubes.Boundary // E.trace.capDiscarded b}) (x : ThreeBall),
        (𝓡∂ 3).IsInteriorPoint x → ContMDiffAt (𝓡∂ 3) ThreeModel ∞ (fCap b) x ∧
        ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel (Subtype.val : ThreeBall → ThreeSpace) x),
        ∃ hk : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel (fCap b) x),
          Orientation.map (Fin 3)
            ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
              (Subtype.val : ThreeBall → ThreeSpace) x).toLinearMap hi).symm.trans
              (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel (fCap b) x).toLinearMap hk))
            ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
              (if b.1.2 then (1 : ℝˣ) else -1) • oY.orientation (fCap b x)) :
    PreservesTangentOrientation D.orientation oY (E.trace.discardedDesc fCore fCap hboundary) := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.trace.tubes.core := E.coreCharts
  let : IsManifold (𝓡∂ 3) ∞ E.trace.tubes.core := E.coreSmooth
  let : ChartedSpace (EuclideanHalfSpace 3) {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} :=
    E.coreOpensCharts E.trace.discardedCoreOpen
  let : IsManifold (𝓡∂ 3) ∞ {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} :=
    inferInstanceAs (IsManifold (𝓡∂ 3) ∞ E.trace.discardedCoreOpen)
  let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  let : IsManifold (𝓡∂ 3) ∞ ThreeBall := E.ballSmooth
  let A : Set D.Carrier := {y | Orientation.map (Fin 3)
    (e.mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv (D.orientation.orientation y) =
      oY.orientation (e y)}
  have hA : IsClosed A := isClosed_diffeomorph_orientation_locus e D.orientation oY
  have hfrom (y : D.Carrier)
      (hp : ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel
        (E.trace.discardedDesc fCore fCap hboundary) y),
        PreservesTangentOrientationAt D.orientation oY (E.trace.discardedDesc fCore fCap hboundary) y hf) :
      y ∈ A := by
    obtain ⟨hf, hp⟩ := hp
    have hlin : (e.mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv =
        LinearEquiv.ofBijective
          (mfderiv ThreeModel ThreeModel (E.trace.discardedDesc fCore fCap hboundary) y).toLinearMap hf := by
      apply LinearEquiv.ext
      intro v
      change mfderiv ThreeModel ThreeModel (e : D.Carrier → Y) y v = _
      rw [heq]
      rfl
    change Orientation.map (Fin 3) _ _ = _
    rw [hlin]
    have hvalue := congrFun heq y
    erw [hvalue]
    exact hp
  have hcoreAll (x : {x : E.trace.tubes.core // x ∉ E.trace.retainedCore}) :
      E.trace.discardedCoreInclusion x ∈ A := by
    have hc : IsClosed (E.trace.discardedCoreInclusion ⁻¹' A) :=
      hA.preimage E.trace.discardedCoreInclusion.continuous
    have hin : (𝓡∂ 3).interior {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} ⊆
        E.trace.discardedCoreInclusion ⁻¹' A := by
      intro z hz
      exact hfrom _ (E.discardedDesc_preservesTangentOrientationAt_core oY fCore fCap hboundary
        z hz (hcore z hz).1 (hcore z hz).2)
    have hall := closure_minimal hin hc
    rw [(ModelWithCorners.dense_interior (𝓡∂ 3)).closure_eq] at hall
    exact hall (mem_univ x)
  have hcapAll (b : {b : E.trace.tubes.Boundary // E.trace.capDiscarded b}) (x : ThreeBall) :
      E.trace.discardedCap b.1 b.2 x ∈ A := by
    have hc : IsClosed (E.trace.discardedCap b.1 b.2 ⁻¹' A) :=
      hA.preimage (E.trace.discardedCap b.1 b.2).continuous
    have hin : (𝓡∂ 3).interior ThreeBall ⊆ E.trace.discardedCap b.1 b.2 ⁻¹' A := by
      intro z hz
      exact hfrom _ (E.discardedDesc_preservesTangentOrientationAt_cap oY fCore fCap hboundary
        b z hz (hcap b z hz).1 (hcap b z hz).2)
    have hall := closure_minimal hin hc
    rw [(ModelWithCorners.dense_interior (𝓡∂ 3)).closure_eq] at hall
    exact hall (mem_univ x)
  have hpres : ∀ y : D.Carrier, y ∈ A := by
    intro y
    have hy : y ∈ range E.trace.discardedCoreInclusion ∪
        ⋃ b : {b : E.trace.tubes.Boundary // E.trace.capDiscarded b}, range (E.trace.discardedCap b.1 b.2) := by
      rw [E.trace.discardedCoreInclusion_union_discardedCaps]
      exact mem_univ _
    rcases hy with ⟨x, rfl⟩ | hy
    · exact hcoreAll x
    · obtain ⟨b, x, rfl⟩ := mem_iUnion.mp hy
      exact hcapAll b x
  rw [← heq]
  refine ⟨e.contMDiff, fun y => ⟨(e.mfderivToContinuousLinearEquiv (by simp) y).bijective, ?_⟩⟩
  have hlin : LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel (e : D.Carrier → Y) y).toLinearMap
      (e.mfderivToContinuousLinearEquiv (by simp) y).bijective =
      (e.mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    rfl
  unfold PreservesTangentOrientationAt
  rw [hlin]
  exact hpres y

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
