import DifferentialGeometry.Geometry.Comparison.Volume.IntrinsicLaunchScaling

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff

namespace Poincare.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrJetResidual_two_zero_eq_six
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (a b : E) :
    (intrinsicJetResidual (I := I) g hEnorm p 0 a b 2 (0, 1) : E) =
      (6 : ℝ) •
        (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 2 (0, 1) : E) := by
  let f : ℝ → ℝ → M := fun r t ↦
    intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((r, 0), t)
  let V : ∀ r t : ℝ, TangentSpace I (f r t) := fun r t ↦
    intrinsicLaunchJ (I := I) g hEnorm p 0 a b (r, t)
  let W : ∀ r t : ℝ, TangentSpace I (f r t) := fun r t ↦
    intrinsicLaunchJet (I := I) g hEnorm p 0 a b 2 (r, t)
  let γ : ℝ → M := fun t ↦ f 0 t
  let W0 : ∀ t : ℝ, TangentSpace I (γ t) := fun t ↦ W 0 t
  let X : TangentSpace I p :=
    show TangentSpace I p from
      (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 2 (0, 1) : E)
  have hcurve : γ = fun _ : ℝ ↦ p := by
    funext t
    dsimp only [γ, f, intrinsicLaunch3]
    have hz :
        (show TangentSpace I p from (0 : E) + (0 : ℝ) • a + (0 : ℝ) • b) =
          (0 : TangentSpace I p) := by
      apply (tangentSpaceModelContinuousLinearEquiv (I := I) p).injective
      change (0 : E) + (0 : ℝ) • a + (0 : ℝ) • b = 0
      module
    have hcast := congrArg
      (fun v : TangentSpace I p ↦ intrinsicGeodesic (I := I) g hEnorm p v t) hz
    have hscale0 := intrinsicGeodesic_smul (I := I) g hEnorm p
      (0 : TangentSpace I p) t
    rw [smul_zero] at hscale0
    have hzero1 : intrinsicGeodesic (I := I) g hEnorm p
        (0 : TangentSpace I p) 1 = p := by
      change expMapIntrinsic (I := I) g hEnorm p (0 : TangentSpace I p) = p
      exact expMapIntrinsic_zero (I := I) g hEnorm p
    exact hcast.trans (hscale0.symm.trans hzero1)
  have hW : ∀ t : ℝ, (W0 t : E) = t ^ 3 • (X : E) := by
    intro t
    have hs := intrinsicLaunchJet_zero_scale (I := I) g hEnorm p a b 2 0 t
    dsimp only [W0, W, X]
    rw [mul_zero] at hs
    exact hs
  have hD1 : ∀ t : ℝ,
      (covDerivAlong (I := I) g γ W0 t : E) =
        (3 * t ^ 2) • (X : E) := by
    intro t
    let P : ℝ → TangentSpace I p := fun s ↦
      show TangentSpace I p from s ^ 3 • (X : E)
    have hc := covDerivAlong_congr_curve (I := I) g (t := t)
      W0 P
      (Filter.Eventually.of_forall (fun s ↦ congrFun hcurve s))
      (Filter.Eventually.of_forall (fun s ↦ hW s))
    have hcE := congrArg (fun z ↦ (z : E)) hc
    exact hcE.trans (covDerivAlong_const_cubic (I := I) g p X t)
  have hD2 :
      (covDerivAlong (I := I) g γ
        (fun t ↦ covDerivAlong (I := I) g γ W0 t) 1 : E) =
        (6 : ℝ) • (X : E) := by
    let P1 : ℝ → TangentSpace I p := fun s ↦
      show TangentSpace I p from (3 * s ^ 2) • (X : E)
    have hc := covDerivAlong_congr_curve (I := I) g (t := (1 : ℝ))
      (fun t ↦ covDerivAlong (I := I) g γ W0 t) P1
      (Filter.Eventually.of_forall (fun s ↦ congrFun hcurve s))
      (Filter.Eventually.of_forall (fun s ↦ hD1 s))
    have hcE := congrArg (fun z ↦ (z : E)) hc
    have hp :
        (covDerivAlong (I := I) g (fun _ : ℝ ↦ p) P1 1 : E) =
          (6 : ℝ) • (X : E) := by
      simpa only [mul_one] using
        (covDerivAlong_const_cubic_first (I := I) g p X 1)
    exact hcE.trans hp
  have hT : varSnd (I := I) f 0 1 = 0 := by
    unfold varSnd
    have hconst : (fun t : ℝ ↦ f 0 t) = fun _ : ℝ ↦ p := hcurve
    rw [hconst, mfderiv_const]
    rfl
  have hcurv : jacobianCurv (I := I) g f W 0 1 = 0 := by
    unfold jacobianCurv curvAlong
    change
      (DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
        (f 0 1)) (W 0 1) (varSnd (I := I) f 0 1) (varSnd (I := I) f 0 1) = 0
    rw [hT]
    exact map_zero _
  change
    (jacobianResidual (I := I) g f
      (covFstIter (I := I) g f 2 V) 0 1 : E) = _
  have hWV : covFstIter (I := I) g f 2 V = W := by
    funext r t
    rfl
  rw [hWV]
  unfold jacobianResidual covSnd2 covSnd
  rw [hcurv, add_zero]
  change
    (covDerivAlong (I := I) g γ
      (fun t ↦ covDerivAlong (I := I) g γ W0 t) 1 : E) = _
  exact hD2

end Poincare.Geometry.Riemannian.VolumeComparison
