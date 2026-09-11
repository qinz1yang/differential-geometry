import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardMetricComparisonNecks
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OpenTensorJets


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance comparisonRestrictionSourceC1
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) : IsManifold I3 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance comparisonRestrictionLimitC1
    (L : PointedRiemannianManifold.{u, 0, 0} (I := I3)) : IsManifold I3 1 L.M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance comparisonRestrictionBufferSigma (epsilon : ℝ) :
    SigmaCompactSpace (spatialNeckBuffer epsilon) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen SpatialNeckCylinderModel (spatialNeckBuffer epsilon).isOpen)

private def restrictedCylinderTensor
    {L : PointedRiemannianManifold.{u, 0, 0} (I := I3)}
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (epsilon : ℝ) (A : Tensor0SField (I := I3) (M := L.M) (n := ∞) 2) :
    Tensor0SField (I := SpatialNeckCylinderModel) (M := spatialNeckBuffer epsilon) (n := ∞) 2 :=
  restrictOpen0S (I := SpatialNeckCylinderModel) 2 (V := spatialNeckBuffer epsilon)
    (pullbackTensor02FieldCross e A)

private theorem restrictedCylinderTensor_apply
    {L : PointedRiemannianManifold.{u, 0, 0} (I := I3)}
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (epsilon : ℝ) (A : Tensor0SField (I := I3) (M := L.M) (n := ∞) 2)
    (x : spatialNeckBuffer epsilon) (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x) :
    restrictedCylinderTensor e epsilon A x v = A (e x)
      (fun j => mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) (v j)) :=
  (restrictOpenTensor02Field_apply (spatialNeckBuffer epsilon)
    (pullbackTensor02FieldCross e A) x v).trans
      (pullbackTensor02FieldCross_apply e A (x : SpatialNeckCylinder) v)

private theorem restrictedCylinderTensor_norm
    {L : PointedRiemannianManifold.{u, 0, 0} (I := I3)}
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (epsilon : ℝ) (A : Tensor0SField (I := I3) (M := L.M) (n := ∞) 2)
    (g : SmoothRiemannianMetric I3 L.M) (a : ℕ) (x : spatialNeckBuffer epsilon) :
    tensor02CovDerivNormWith a (restrictedCylinderTensor e epsilon A)
        ((DifferentialGeometry.Diffeomorph.pullbackMetricCross g e).restrictOpen
          (spatialNeckBuffer epsilon))
        ((DifferentialGeometry.Diffeomorph.pullbackMetricCross g e).restrictOpen
          (spatialNeckBuffer epsilon)) x =
      tensor02CovDerivNormWith a A g g (e x) := by
  unfold restrictedCylinderTensor
  rw [tensor02CovDerivNormWith_restrictOpen0S,
    tensor02CovDerivNormWith_pullbackTensor02FieldCross]


def backwardMetricComparison_cylindricalRestriction
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {L : PointedRiemannianManifold.{u, 0, 0} (I := I3)} {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (I := I3) (backwardSliceSequence F tau htau q) L phi)
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (epsilon : ℝ) (i : ℕ) {h : ℝ → SmoothRiemannianMetric I3 L.M}
    {K : Set L.M} {order : ℕ} {eta : ℝ}
    (C : MetricComparisonOn h (backwardScaledMetric F.S (tau (phi i)) (htau (phi i)))
      (Phi.map i) K (Icc (1 : ℝ) 3) order eta)
    (hsource : e '' (spatialNeckBuffer epsilon : Set SpatialNeckCylinder) ⊆ Phi.source i)
    (hK : ∀ x : spatialNeckBuffer epsilon, e (x : SpatialNeckCylinder) ∈ K)
    (hmetric : ∀ theta ∈ Icc (1 : ℝ) 3,
      strongNeckBackgroundMetric epsilon (1 - theta) =
        (DifferentialGeometry.Diffeomorph.pullbackMetricCross (h theta) e).restrictOpen
          (spatialNeckBuffer epsilon)) :
    MetricComparisonOn (fun theta => strongNeckBackgroundMetric epsilon (1 - theta))
      (backwardScaledMetric F.S (tau (phi i)) (htau (phi i)))
      (fun x : spatialNeckBuffer epsilon => Phi.map i (e (x : SpatialNeckCylinder)))
      univ (Icc (1 : ℝ) 3) order eta := by
  let U := spatialNeckBuffer epsilon
  let pb (theta : ℝ) := restrictedCylinderTensor e epsilon (C.pullback theta)
  let J (b : ℕ) (theta : ℝ) :=
    if b = 0 then pb theta - metricTensorField (strongNeckBackgroundMetric epsilon (1 - theta))
    else restrictedCylinderTensor e epsilon (C.jet b theta)
  have hzero (theta : ℝ) (x : U) (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x) :
      J 0 theta x v = pb theta x v -
        (strongNeckBackgroundMetric epsilon (1 - theta)).inner x (v 0) (v 1) := by
    change (pb theta x - metricTensorField
      (strongNeckBackgroundMetric epsilon (1 - theta)) x) v = _
    rw [Tensor0SSpace.sub_apply, metricTensorField_apply]
  have hinner (theta : ℝ) (htheta : theta ∈ Icc (1 : ℝ) 3) (x : U)
      (v w : TangentSpace SpatialNeckCylinderModel x) :
      (strongNeckBackgroundMetric epsilon (1 - theta)).inner x v w =
        (h theta).inner (e x)
          (mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) v)
          (mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) w) := by
    rw [hmetric theta htheta]
    exact (SmoothRiemannianMetric.restrictOpen_inner
      (DifferentialGeometry.Diffeomorph.pullbackMetricCross (h theta) e) U x v w).trans
        (DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner
          (h theta) e (x : SpatialNeckCylinder) v w)
  have hJvalue (b : ℕ) (theta : ℝ) (htheta : theta ∈ Icc (1 : ℝ) 3)
      (x : U) (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x) :
      J b theta x v = C.jet b theta (e x)
        (fun j => mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) (v j)) := by
    by_cases hb : b = 0
    · subst b
      rw [hzero, C.jet_zero, hinner theta htheta]
      exact congrArg (fun r : ℝ => r - (h theta).inner (e x)
        (mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) (v 0))
        (mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) (v 1)))
          (restrictedCylinderTensor_apply e epsilon (C.pullback theta) x v)
    · simp only [J, if_neg hb, restrictedCylinderTensor_apply]
  have hJfield (b : ℕ) (theta : ℝ) (htheta : theta ∈ Icc (1 : ℝ) 3) :
      J b theta = restrictedCylinderTensor e epsilon (C.jet b theta) := by
    apply ContMDiffSection.ext
    intro x
    apply tensor0SSpace_ext 2 x
    intro v
    exact (hJvalue b theta htheta x v).trans
      (restrictedCylinderTensor_apply e epsilon (C.jet b theta) x v).symm
  have hd (x : U) (v : TangentSpace SpatialNeckCylinderModel x) :
      mfderiv SpatialNeckCylinderModel I3
          (fun z : U => Phi.map i (e (z : SpatialNeckCylinder))) x v =
        mfderiv I3 I3 (Phi.map i) (e x)
          (mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) v) := by
    have he := e.mdifferentiable (by decide) (x : SpatialNeckCylinder)
    have hval : MDifferentiableAt SpatialNeckCylinderModel SpatialNeckCylinderModel
        (Subtype.val : U → SpatialNeckCylinder) x :=
      (contMDiff_subtype_val (I := SpatialNeckCylinderModel) (U := U) (n := ∞)).mdifferentiable
        (by decide) x
    have hmap : MDifferentiableAt I3 I3 (Phi.map i) (e x) :=
      (Phi.partialDiffeomorph i).mdifferentiableAt (by decide) (hsource ⟨x, x.property, rfl⟩)
    have hcomp := mfderiv_comp x hmap (he.comp x hval)
    rw [mfderiv_comp x he hval, mfderiv_subtype_val] at hcomp
    exact DFunLike.congr_fun hcomp v
  refine {
    pullback := pb
    pullback_eq := ?_
    jet := J
    jet_zero := hzero
    jet_succ := ?_
    equivalence := ?_
    close := ?_ }
  · intro theta x _hx v
    rw [hd x (v 0), hd x (v 1)]
    exact (restrictedCylinderTensor_apply e epsilon (C.pullback theta) x v).trans
      (C.pullback_eq theta (e x) (hK x) _)
  · intro b theta htheta x _hx v
    rw [hJvalue (b + 1) theta htheta, C.jet_succ b theta htheta (e x) (hK x)]
    exact derivWithin_congr (fun t ht => (hJvalue b t ht x v).symm)
      (hJvalue b theta htheta x v).symm
  · intro theta htheta x _hx v
    rw [hinner theta htheta]
    simpa only [pb, restrictedCylinderTensor_apply] using
      C.equivalence theta htheta (e x) (hK x)
        (mfderiv SpatialNeckCylinderModel I3 e (x : SpatialNeckCylinder) v)
  · intro a b hab theta htheta x _hx
    rw [hJfield b theta htheta, hmetric theta htheta]
    exact (restrictedCylinderTensor_norm e epsilon (C.jet b theta) (h theta) a x).le.trans
      (C.close a b hab theta htheta (e x) (hK x))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
