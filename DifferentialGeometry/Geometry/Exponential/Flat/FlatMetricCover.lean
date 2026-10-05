import DifferentialGeometry.Geometry.Exponential.Flat.MetricDeckIsometries

/-!
# Isometric deck coordinates for an actual flat exponential cover

The original tangent metric provides orthonormal coordinates for the exponential covering.
Its proved pullback metric identity then produces isometries for every actual deck map. No
isometric action, lattice, or group classification is assumed.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry Bundle Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.FlatSurface

variable {E : Type*} [instE : NormedAddCommGroup E] [instER : NormedSpace ℝ E]
  [instFD : FiniteDimensional ℝ E] [instDim : NeZero (Module.finrank ℝ E)]
  {H : Type*} [instH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [instBoundary : I.Boundaryless] {M : Type*} [instM : TopologicalSpace M]
  [instCM : ChartedSpace H M] [instMF : IsManifold I ∞ M]
  [instSigma : SigmaCompactSpace M] [instT2 : T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [instR : RiemannianBundle (fun x : M => TangentSpace I x)]
  [instEM : PseudoEMetricSpace M] [instRM : IsRiemannianManifold I M]
  [instComplete : CompleteSpace M]
  [instContinuous : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [instConn : ConnectedSpace M]

local notation "T" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_isometric_flat_cover (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita g) x X Y Z = 0) :
    ∃ p : T → M, IsLocalDiffeomorph 𝓘(ℝ, T) I ∞ p ∧ IsCoveringMap p ∧
      Function.Surjective p ∧ ∀ γ : coveringDeckGroup p, Isometry (γ.1 : T → T) := by
  classical
  obtain ⟨a⟩ := (inferInstance : Nonempty M)
  let F : E → M := fun x => expMapIntrinsic g hEnorm a (show TangentSpace I a from x)
  obtain ⟨hF, hmetricF, hcovF, hsurjF⟩ :=
    flat_expMapIntrinsic_isLocalIsometry_isCoveringMap g hEnorm hR a
  let o := (stdOrthonormalBasis ℝ (TangentSpace I a)).repr
  let e : E ≃L[ℝ] T := o.toLinearEquiv.toContinuousLinearEquiv
  let p : T → M := F ∘ e.symm
  have hl : IsLocalDiffeomorph 𝓘(ℝ, T) I ∞ p := by
    intro x
    exact (e.symm.toDiffeomorph.isLocalDiffeomorph x).comp I M (hF (e.symm x))
  have hmetric : ∀ (x v w : T), g.inner (p x) (mfderiv 𝓘(ℝ, T) I p x v)
      (mfderiv 𝓘(ℝ, T) I p x w) = inner ℝ v w := by
    intro x v w
    have hD (z : T) : mfderiv 𝓘(ℝ, T) I p x z =
        mfderiv 𝓘(ℝ, E) I F (e.symm x) (e.symm z) := by
      have hc := mfderiv_comp x ((hF.contMDiff (e.symm x)).mdifferentiableAt (by simp))
        ((e.symm.toDiffeomorph.contMDiff x).mdifferentiableAt (by simp))
      rw [e.symm.mfderiv_eq] at hc
      exact congrArg (fun D => D z) hc
    change g.inner (F (e.symm x)) (mfderiv 𝓘(ℝ, T) I p x v)
      (mfderiv 𝓘(ℝ, T) I p x w) = inner ℝ v w
    rw [hD v, hD w, hmetricF]
    exact o.symm.inner_map_map v w
  exact ⟨p, hl, hcovF.comp_homeomorph e.symm.toHomeomorph,
    hsurjF.comp e.symm.surjective, deck_isometry_of_metric_derivative g p hl hmetric⟩

end DifferentialGeometry.Geometry.FlatSurface
