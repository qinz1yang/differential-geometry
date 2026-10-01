import DifferentialGeometry.Topology.ThreeManifold.Surgery.CutCap.SphericalRealization
import DifferentialGeometry.Topology.ThreeManifold.Surgery.Capping.CoreCapIntersection

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

variable {P Q D N : OrientedThreeStage.{u}}

theorem smooth_boundarySphere_ofSmoothCutCapTransition (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary) :
    ContMDiff (𝓡 2) (𝓡 3) ∞
      ((SphericalTubeSystem.ofSmoothCutCapTransition X).boundarySphere b) := by
  change ContMDiff (𝓡 2) (𝓡 3) ∞
    (fun z => (SphericalTubeSystem.ofSmoothCutCapTransition X).tube b.1
      (z, DifferentialGeometry.Topology.SphericalTubeSystem.boundaryLevel b.2))
  exact (X.tube_smooth b.1).contMDiff.comp (contMDiff_id.prodMk contMDiff_const)

theorem mfderiv_attaching_boundarySphere_apply (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (v : TangentSpace (𝓡 2) z) :
    mfderiv (𝓡 2) (𝓡 3)
        (((SphericalTubeSystem.ofSmoothCutCapTransition X).boundarySphere b) ∘
          ⇑(X.attaching b)) z v =
      mfderiv (𝓡 2) (𝓡 3) ((SphericalTubeSystem.ofSmoothCutCapTransition X).boundarySphere b)
        (X.attaching b z) (mfderiv (𝓡 2) (𝓡 2) (⇑(X.attaching b)) z v) :=
  mfderiv_comp_apply z
    ((smooth_boundarySphere_ofSmoothCutCapTransition X b).mdifferentiableAt (by norm_num))
    ((X.attaching b).contMDiff.mdifferentiableAt (by norm_num)) v

def SmoothCutCapTransition.attachingFrameReversing (X : SmoothCutCapTransition P Q D N) : Prop :=
  ∀ (b : (SphericalTubeSystem.ofSmoothCutCapTransition X).Boundary)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (v w : TangentSpace (𝓡 2) z),
    let A := mfderiv (𝓡 2) (𝓡 2) (⇑(X.attaching b)) z
    let e := mfderiv (𝓡 2) (𝓡 3)
      (Subtype.val : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 →
        EuclideanSpace ℝ (Fin 3)) (X.attaching b z)
    (if b.2 then (1 : ℝ) else -1) *
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
        (Fin.cons (X.attaching b z).1 (Fin.cons (e (A v)) (Fin.cons (e (A w)) ![]))) < 0 ↔
      (if b.2 then (1 : ℝ) else -1) *
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
        (Fin.cons z.1 (Fin.cons
          ((mfderiv (𝓡 2) (𝓡 3)
            (Subtype.val : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 →
              EuclideanSpace ℝ (Fin 3)) z) v)
          (Fin.cons ((mfderiv (𝓡 2) (𝓡 3)
            (Subtype.val : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 →
              EuclideanSpace ℝ (Fin 3)) z) w) ![]))) < 0

theorem SmoothCutCapTransition.boundaryFrameReversing_iff_attachingFrameReversing
    (X : SmoothCutCapTransition P Q D N)
    (h : (SphericalTubeSystem.ofSmoothCutCapTransition X)
      |>.outwardNormalFirstIsStandardSphereOrientation) :
    X.boundaryFrameReversing ↔ X.attachingFrameReversing := by
  constructor
  · intro hX b z v w
    have hh := h b (X.attaching b z)
      (mfderiv (𝓡 2) (𝓡 2) (⇑(X.attaching b)) z v)
      (mfderiv (𝓡 2) (𝓡 2) (⇑(X.attaching b)) z w)
    simp only [] at hh
    rw [← mfderiv_attaching_boundarySphere_apply X b z v,
      ← mfderiv_attaching_boundarySphere_apply X b z w] at hh
    exact hh.symm.trans (hX b z v w)
  · intro hX b z v w
    have hh := h b (X.attaching b z)
      (mfderiv (𝓡 2) (𝓡 2) (⇑(X.attaching b)) z v)
      (mfderiv (𝓡 2) (𝓡 2) (⇑(X.attaching b)) z w)
    simp only [] at hh
    rw [← mfderiv_attaching_boundarySphere_apply X b z v,
      ← mfderiv_attaching_boundarySphere_apply X b z w] at hh
    exact hh.trans (hX b z v w)

theorem SmoothCutCapTransition.boundaryFrameReversing_of_attachingFrameReversing
    (X : SmoothCutCapTransition P Q D N)
    (h : (SphericalTubeSystem.ofSmoothCutCapTransition X)
      |>.outwardNormalFirstIsStandardSphereOrientation)
    (hX : X.attachingFrameReversing) : X.boundaryFrameReversing :=
  (X.boundaryFrameReversing_iff_attachingFrameReversing h).mpr hX

theorem SmoothCutCapTransition.attachingFrameReversing_of_attaching_eq_refl
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : ∀ b, X.attaching b = Diffeomorph.refl (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞) :
    X.attachingFrameReversing := by
  intro b z v w
  have hz : X.attaching b z = z := by rw [h b, Diffeomorph.coe_refl]; rfl
  have hA : mfderiv (𝓡 2) (𝓡 2) (⇑(X.attaching b)) z =
      ContinuousLinearMap.id ℝ (TangentSpace (𝓡 2) z) := by
    rw [h b, Diffeomorph.coe_refl]
    exact mfderiv_id
  rw [hA, hz]
  simp only [ContinuousLinearMap.id_apply]

theorem SmoothCutCapTransition.boundaryFrameReversing_of_attaching_eq_refl
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : ∀ b, X.attaching b = Diffeomorph.refl (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (hout : (SphericalTubeSystem.ofSmoothCutCapTransition X)
      |>.outwardNormalFirstIsStandardSphereOrientation) :
    X.boundaryFrameReversing :=
  (X.boundaryFrameReversing_iff_attachingFrameReversing hout).mpr
    (X.attachingFrameReversing_of_attaching_eq_refl h)

theorem SmoothCutCapTransition.outwardNormalFirst_iff_boundaryFrameReversing_of_attaching_eq_refl
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : ∀ b, X.attaching b = Diffeomorph.refl (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞) :
    ((SphericalTubeSystem.ofSmoothCutCapTransition X)
        |>.outwardNormalFirstIsStandardSphereOrientation) ↔ X.boundaryFrameReversing := by
  refine ⟨fun hout => X.boundaryFrameReversing_of_attaching_eq_refl h hout, fun hb => ?_⟩
  intro b z v w
  have hb' := hb b z v w
  simp only [Function.comp_apply] at hb'
  rw [h b] at hb'
  simp only [Diffeomorph.coe_refl, id_eq, Function.comp_id] at hb'
  exact hb'

theorem SmoothCutCapTransition.nonempty_sphericalCappingCompletion_of_attaching_eq_refl
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : ∀ b, X.attaching b = Diffeomorph.refl (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (hout : (SphericalTubeSystem.ofSmoothCutCapTransition X)
      |>.outwardNormalFirstIsStandardSphereOrientation) :
    Nonempty (SphericalCappingCompletion X) :=
  ⟨X.toSphericalCappingCompletion (X.boundaryFrameReversing_of_attaching_eq_refl h hout)⟩

theorem SmoothCutCapTransition.nonempty_smoothCutCapCompletion_of_attaching_eq_refl
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : ∀ b, X.attaching b = Diffeomorph.refl (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (hout : (SphericalTubeSystem.ofSmoothCutCapTransition X)
      |>.outwardNormalFirstIsStandardSphereOrientation) :
    Nonempty (SmoothCutCapCompletion X) :=
  ⟨X.toSmoothCutCapCompletion (X.boundaryFrameReversing_of_attaching_eq_refl h hout)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
