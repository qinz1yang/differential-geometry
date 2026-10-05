import DifferentialGeometry.Geometry.Curvature.Surface.FiniteFlatCover
import DifferentialGeometry.Geometry.Curvature.Surface.PeriodicGaussBonnetApplications
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible

/-!
# Universal finite flat covers and a finite Euclidean consumer

The covering plane is actually simply connected. The Euclidean metric reindexed at finite order
four supplies a concrete complete flat surface to the general finite-cover producer.
-/

set_option autoImplicit false

noncomputable section

open Bundle DifferentialGeometry Set Function
open scoped Manifold ContDiff InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteFlatSurface

local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

theorem euclideanCover_domain_simplyConnected : SimplyConnectedSpace E2 := inferInstance

def euclideanFiniteMetric : ContMDiffRiemannianMetric (𝓡 2) 4 E2
    (TangentSpace (𝓡 2) : E2 → Type _) :=
  { riemannianMetricVectorSpace E2 with
    contMDiff := (riemannianMetricVectorSpace E2).contMDiff.of_le le_top }

theorem euclideanFiniteMetric_flat (x : E2) (v w : TangentSpace (𝓡 2) x) :
    euclideanFiniteMetric.sectionalCurvature x v w = 0 := by
  let e : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 3 :=
    (Diffeomorph.refl (𝓡 2) E2 3).toPartialDiffeomorph
  have hes : (e.symm : E2 → E2) = id := rfl
  have hc : (fun y =>
      (euclideanFiniteMetric.inner (e.symm y) : E2 →L[ℝ] E2 →L[ℝ] ℝ).bilinearComp
        (mfderiv (𝓡 2) (𝓡 2) e.symm y : E2 →L[ℝ] E2)
        (mfderiv (𝓡 2) (𝓡 2) e.symm y : E2 →L[ℝ] E2)) = fun y => innerSL ℝ := by
    funext y
    ext u z
    change inner ℝ (mfderiv (𝓡 2) (𝓡 2) e.symm y u)
      (mfderiv (𝓡 2) (𝓡 2) e.symm y z) = inner ℝ u z
    rw [hes, mfderiv_id]
    rfl
  have hk := euclideanFiniteMetric.sectionalCurvature_eq_coefficientSectional
    (by norm_num) e (p := x) (mem_univ x) v w
  have hcoeff := congrArg (fun b : E2 → E2 →L[ℝ] E2 →L[ℝ] ℝ =>
    Analysis.coefficientSectional b (e x) (mfderiv (𝓡 2) (𝓡 2) e x v)
      (mfderiv (𝓡 2) (𝓡 2) e x w)) hc
  exact hk.trans (hcoeff.trans
    (Analysis.coefficientSectional_const_eq_zero finrank_euclideanSpace_fin
      (innerSL ℝ) (fun u v => by exact real_inner_comm v u)
      (fun u hu => real_inner_self_pos.mpr hu) _ _ _))

theorem euclideanFiniteMetric_cover : ∃ f : E2 → E2, f 0 = 0 ∧
    ContMDiff (𝓡 2) (𝓡 2) 3 f ∧ IsLocalDiffeomorph (𝓡 2) (𝓡 2) 3 f ∧
    (∀ x v w, euclideanFiniteMetric.inner (f x) (mfderiv (𝓡 2) (𝓡 2) f x v)
      (mfderiv (𝓡 2) (𝓡 2) f x w) = inner ℝ v w) ∧
    IsCoveringMap f ∧ Surjective f := by
  apply exists_euclideanCover_of_finite_flat (r := 3) euclideanFiniteMetric le_rfl
  · intro x v
    change ‖(v : E2)‖ₑ = ENNReal.ofReal (Real.sqrt (inner ℝ (v : E2) v))
    rw [← norm_eq_sqrt_real_inner, ofReal_norm]
  · exact euclideanFiniteMetric_flat

variable {Z : Type*} [MetricSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [RiemannianBundle (fun x : Z => TangentSpace (𝓡 2) x)]
  [IsRiemannianManifold (𝓡 2) Z] [CompleteSpace Z] [ConnectedSpace Z]

theorem exists_universalEuclideanCover_of_finite_flat {r : ℕ∞}
    (k : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2
      (TangentSpace (𝓡 2) : Z → Type _)) (hr : 3 ≤ r)
    (hnorm : ∀ (x : Z) (v : TangentSpace (𝓡 2) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x v v)))
    (hflat : ∀ x (v w : TangentSpace (𝓡 2) x), k.sectionalCurvature x v w = 0) :
    ∃ f : E2 → Z, SimplyConnectedSpace E2 ∧ ContMDiff (𝓡 2) (𝓡 2) r f ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) r f ∧
      (∀ x v w, k.inner (f x) (mfderiv (𝓡 2) (𝓡 2) f x v)
        (mfderiv (𝓡 2) (𝓡 2) f x w) = inner ℝ v w) ∧
      IsCoveringMap f ∧ Surjective f := by
  obtain ⟨p⟩ := (inferInstance : Nonempty Z)
  obtain ⟨f, hf0, hfc, hfl, hfi, hcover, hsurj⟩ :=
    exists_euclideanCover_of_finite_flat k hr hnorm hflat p
  exact ⟨f, euclideanCover_domain_simplyConnected, hfc, hfl, hfi, hcover, hsurj⟩

end DifferentialGeometry.Geometry.FiniteFlatSurface
