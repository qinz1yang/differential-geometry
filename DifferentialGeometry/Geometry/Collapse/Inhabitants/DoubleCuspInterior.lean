import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspProfile
import DifferentialGeometry.Topology.Manifold.ImmersionInterior
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature

/-!
The physical double cusp coordinate is a local diffeomorphism on the actual open
interior. Its genuine metric pullback transports real-base sectional bounds there.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Topology.Manifold
open GC.Endpoint GC.Seifert Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

@[reducible] def doubleCuspInteriorDomain : TopologicalSpace.Opens (productSet.{u} 2) :=
  ⟨(𝓡∂ 3).interior (productSet.{u} 2), (𝓡∂ 3).isOpen_interior (n := ∞) (by simp)⟩

def doubleCuspInteriorCoordinate : doubleCuspInteriorDomain.{u} → ℝ × Torus :=
  fun x => doubleCuspCoordinate x.val

theorem doubleCuspInteriorCoordinate_localDiffeomorph :
    IsLocalDiffeomorph (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel) ∞
      doubleCuspInteriorCoordinate.{u} := by
  apply isLocalDiffeomorph_restrict_open doubleCuspInteriorDomain.{u}
  intro p
  apply isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv
    doubleCuspCoordinate_smooth.{u}
  · exact p.property
  · simp
  · exact doubleCuspCoordinate_immersion.{u} p.val

private theorem doubleCuspInteriorCoordinate_derivative
    (x : doubleCuspInteriorDomain.{u}) (v : TangentSpace (𝓡∂ 3) x) :
    mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel) doubleCuspInteriorCoordinate.{u} x v =
      mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel) doubleCuspCoordinate.{u} x.val v := by
  change mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel)
    (doubleCuspCoordinate.{u} ∘ Subtype.val) x v = _
  rw [mfderiv_comp x (doubleCuspCoordinate_smooth.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := (𝓡∂ 3)) (n := ∞)).mdifferentiableAt (by simp))]
  change mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel) doubleCuspCoordinate.{u} x.val
    (mfderiv (𝓡∂ 3) (𝓡∂ 3) Subtype.val x v) = _
  rw [mfderiv_subtype_val_apply]

private theorem doubleCuspInterior_metric_eq (a : ℝ) (ha : 0 < a) :
    localPullMetric (doubleCuspMetric.{u} a ha)
        (Subtype.val : doubleCuspInteriorDomain.{u} → productSet.{u} 2)
        (isLocalDiffeomorph_subtype_val doubleCuspInteriorDomain.{u}) =
      localPullMetric (doubleCuspRealMetric a ha) doubleCuspInteriorCoordinate.{u}
        doubleCuspInteriorCoordinate_localDiffeomorph.{u} := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, localPullMetric_inner,
    mfderiv_subtype_val_apply, mfderiv_subtype_val_apply,
    doubleCuspInteriorCoordinate_derivative, doubleCuspInteriorCoordinate_derivative]
  rfl

theorem doubleCuspMetric_sectional_interior (a : ℝ) (ha : 0 < a) (C : ℝ)
    (hC : ∀ q : ℝ × Torus, SectionalBoundedBelowAt (doubleCuspRealMetric a ha) q (-C))
    (p : productSet.{u} 2) (hp : p ∈ annulusCircleCarrier.{u}.interior) :
    SectionalBoundedBelowAt (doubleCuspMetric.{u} a ha) p (-C) := by
  change (𝓡∂ 3).IsInteriorPoint p at hp
  let x : doubleCuspInteriorDomain.{u} := ⟨p, hp⟩
  intro v w
  let vv : TangentSpace (𝓡∂ 3) x := v
  let ww : TangentSpace (𝓡∂ 3) x := w
  have hv : mfderiv (𝓡∂ 3) (𝓡∂ 3)
      (Subtype.val : doubleCuspInteriorDomain.{u} → productSet.{u} 2) x vv = v := by
    rw [mfderiv_subtype_val_apply]
  have hw : mfderiv (𝓡∂ 3) (𝓡∂ 3)
      (Subtype.val : doubleCuspInteriorDomain.{u} → productSet.{u} 2) x ww = w := by
    rw [mfderiv_subtype_val_apply]
  have h1 := metricRm04StandardAt_localPullMetric (doubleCuspMetric.{u} a ha)
    (Subtype.val : doubleCuspInteriorDomain.{u} → productSet.{u} 2)
    (isLocalDiffeomorph_subtype_val doubleCuspInteriorDomain.{u}) x vv ww ww vv
  have h2 := metricRm04StandardAt_localPullMetric (doubleCuspRealMetric a ha)
    doubleCuspInteriorCoordinate.{u} doubleCuspInteriorCoordinate_localDiffeomorph.{u}
    x vv ww ww vv
  rw [doubleCuspInterior_metric_eq a ha, h2, hv, hw] at h1
  have hdv : mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel)
      doubleCuspInteriorCoordinate.{u} x vv =
      mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel) doubleCuspCoordinate.{u} p v :=
    doubleCuspInteriorCoordinate_derivative x vv
  have hdw : mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel)
      doubleCuspInteriorCoordinate.{u} x ww =
      mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel) doubleCuspCoordinate.{u} p w :=
    doubleCuspInteriorCoordinate_derivative x ww
  have hcx : doubleCuspInteriorCoordinate x = doubleCuspCoordinate.{u} p := rfl
  rw [hdv, hdw, hcx] at h1
  rw [← h1]
  change (-C) * ((doubleCuspMetric.{u} a ha).inner p v v *
    (doubleCuspMetric.{u} a ha).inner p w w -
    (doubleCuspMetric.{u} a ha).inner p v w ^ 2) ≤ _
  simpa only [doubleCuspMetric, SmoothRiemannianMetric.pullback_inner] using
    hC (doubleCuspCoordinate.{u} p)
      (mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel) doubleCuspCoordinate.{u} p v)
      (mfderiv (𝓡∂ 3) (𝓘(ℝ, ℝ).prod torusModel) doubleCuspCoordinate.{u} p w)

end DifferentialGeometry.Geometry.Collapse
