import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalCappingCompletion
import DifferentialGeometry.Topology.ThreeManifold.CoreCapOppositeSides

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

def FrameReversingFactor (c : ℝ) : Prop :=
  ∀ d : ℝ, 0 < c * d ↔ d < 0

theorem frameReversingFactor_iff_neg (c : ℝ) : FrameReversingFactor c ↔ c < 0 := by
  refine ⟨fun h => ?_, fun hc d => ?_⟩
  · have h1 := (h (-1)).mpr (by norm_num : (-1 : ℝ) < 0)
    simpa only [mul_neg, mul_one, neg_pos] using h1
  · rw [mul_pos_iff]
    constructor
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact absurd h (not_lt.mpr hc.le)
      · exact h
    · exact fun hd => Or.inr ⟨hc, hd⟩

theorem frameReversingFactor_neg_one : FrameReversingFactor (-1 : ℝ) :=
  (frameReversingFactor_iff_neg (-1)).mpr (by norm_num)

theorem not_frameReversingFactor_one : ¬ FrameReversingFactor (1 : ℝ) :=
  fun h => absurd ((frameReversingFactor_iff_neg 1).mp h) (by norm_num)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
