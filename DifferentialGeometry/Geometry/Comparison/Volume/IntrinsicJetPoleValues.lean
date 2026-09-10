import DifferentialGeometry.Geometry.Comparison.Volume.PolarTwoJet

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
theorem intrinsicLaunch3_base_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) (t : ℝ) :
    intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), t) = p := by
  have hs := intrinsicGeodesic_smul (I := I) g hEnorm p
    (0 : TangentSpace I p) t
  rw [smul_zero] at hs
  have hzero : intrinsicGeodesic (I := I) g hEnorm p
      (0 : TangentSpace I p) 1 = p := by
    with_unfolding_all exact expMapIntrinsic_zero (I := I) g hEnorm p
  dsimp only [intrinsicLaunch3]
  simp only [zero_smul, add_zero]
  exact hs.symm.trans hzero

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrJetAtom_bJet_zero_pole
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) :
    ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 0).eval
      (I := I) g hEnorm p 0 a b (0, 1) : E) = b := by
  change (intrinsicLaunchJ (I := I) g hEnorm p 0 a b (0, 1) : E) = b
  exact intrinsicLaunchJ_base_zero (I := I) g hEnorm p a b 1 |>.trans (one_smul ℝ b)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrJetAtom_aJet_zero_pole
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) :
    ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aJet 0).eval
      (I := I) g hEnorm p 0 a b (0, 1) : E) = a := by
  have hself := DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.a_jet_eq_self
    (I := I) g hEnorm p 0 a b 0 0 1
  exact (congrArg (fun z ↦ (z : E)) hself).trans
    (intrJetAtom_bJet_zero_pole (I := I) g hEnorm p a a)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrJetAtom_bJet_one_pole
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) :
    ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 1).eval
      (I := I) g hEnorm p 0 a b (0, 1) : E) = 0 := by
  change (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 1 (0, 1) : E) = 0
  exact congrArg (fun z ↦ (z : E))
    (intrinsicLaunchJet_one_zero (I := I) g hEnorm p a b)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrJetAtom_aJet_one_pole
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) :
    ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aJet 1).eval
      (I := I) g hEnorm p 0 a b (0, 1) : E) = 0 := by
  have hself := DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.a_jet_eq_self
    (I := I) g hEnorm p 0 a b 1 0 1
  exact (congrArg (fun z ↦ (z : E)) hself).trans
    (intrJetAtom_bJet_one_pole (I := I) g hEnorm p a a)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrJetAtom_bTime_zero_pole
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) :
    ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bTime 0).eval
      (I := I) g hEnorm p 0 a b (0, 1) : E) = b := by
  let f : ℝ → ℝ → M := fun r t ↦
    intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((r, 0), t)
  let B : ∀ r t : ℝ, TangentSpace I (f r t) := fun r t ↦
    intrinsicLaunchJ (I := I) g hEnorm p 0 a b (r, t)
  have hcurve : (fun t : ℝ ↦ f 0 t) = fun _ : ℝ ↦ p := by
    funext t
    exact intrinsicLaunch3_base_zero (I := I) g hEnorm p a b t
  have hfield : ∀ t : ℝ, (B 0 t : E) = t • b := by
    intro t
    exact intrinsicLaunchJ_base_zero (I := I) g hEnorm p a b t
  have hcongr := covDerivAlong_congr_curve (I := I) g (t := (1 : ℝ))
    (fun t : ℝ ↦ B 0 t)
    (fun t : ℝ ↦ (show TangentSpace I p from t • b))
    (Filter.Eventually.of_forall (fun t ↦ congrFun hcurve t))
    (Filter.Eventually.of_forall hfield)
  have hcongrE := congrArg (fun z ↦ (z : E)) hcongr
  change (covDerivAlong (I := I) g (fun t : ℝ ↦ f 0 t)
    (fun t : ℝ ↦ B 0 t) 1 : E) = b
  exact hcongrE.trans (covDerivAlong_const_linear (I := I) g p
    (show TangentSpace I p from b) 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrJetAtom_aTime_zero_pole
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) :
    ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0).eval
      (I := I) g hEnorm p 0 a b (0, 1) : E) = a := by
  have hself := DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.a_time_eq_self
    (I := I) g hEnorm p 0 a b 0 0 1
  exact (congrArg (fun z ↦ (z : E)) hself).trans
    (intrJetAtom_bTime_zero_pole (I := I) g hEnorm p a a)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrJetAtom_bTime_one_pole
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) :
    ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bTime 1).eval
      (I := I) g hEnorm p 0 a b (0, 1) : E) = 0 := by
  let f : ℝ → ℝ → M := fun r t ↦
    intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((r, 0), t)
  let W : ∀ r t : ℝ, TangentSpace I (f r t) := fun r t ↦
    intrinsicLaunchJet (I := I) g hEnorm p 0 a b 1 (r, t)
  have hcurve : (fun t : ℝ ↦ f 0 t) = fun _ : ℝ ↦ p := by
    funext t
    exact intrinsicLaunch3_base_zero (I := I) g hEnorm p a b t
  have hfield : ∀ t : ℝ, (W 0 t : E) = 0 := by
    intro t
    have hs := intrinsicLaunchJet_zero_scale (I := I) g hEnorm p a b 1 0 t
    rw [mul_zero] at hs
    have hzero := congrArg (fun z ↦ (z : E))
      (intrinsicLaunchJet_one_zero (I := I) g hEnorm p a b)
    rw [hzero, smul_zero] at hs
    exact hs
  have hcongr := covDerivAlong_congr_curve (I := I) g (t := (1 : ℝ))
    (fun t : ℝ ↦ W 0 t)
    (fun _ : ℝ ↦ (0 : TangentSpace I p))
    (Filter.Eventually.of_forall (fun t ↦ congrFun hcurve t))
    (Filter.Eventually.of_forall hfield)
  have hzero := covDerivAlong_zero (I := I) g (fun _ : ℝ ↦ p) 1
  change (covDerivAlong (I := I) g (fun t : ℝ ↦ f 0 t)
    (fun t : ℝ ↦ W 0 t) 1 : E) = 0
  exact (congrArg (fun z ↦ (z : E)) hcongr).trans
    (congrArg (fun z ↦ (z : E)) hzero)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrJetAtom_aTime_one_pole
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) :
    ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 1).eval
      (I := I) g hEnorm p 0 a b (0, 1) : E) = 0 := by
  have hself := DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.a_time_eq_self
    (I := I) g hEnorm p 0 a b 1 0 1
  exact (congrArg (fun z ↦ (z : E)) hself).trans
    (intrJetAtom_bTime_one_pole (I := I) g hEnorm p a a)

end Poincare.Geometry.Riemannian.VolumeComparison
