import DifferentialGeometry.Geometry.Comparison.Volume.PolarExpansion
import DifferentialGeometry.Geometry.Comparison.Volume.IntrinsicLaunchResidual
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Jacobi.CurvatureJet

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicLaunchJ_base_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) (t : ℝ) :
    (intrinsicLaunchJ (I := I) g hEnorm p 0 a b (0, t) : E) = t • b := by
  rw [intrinsicLaunchJ_zero]
  have hraw := intrinsic_jacobi_at (I := I) g hEnorm p (0 : E) b t
  rw [smul_zero] at hraw
  change
    (intrinsicJacobi (I := I) g hEnorm p
        (show TangentSpace I p from (0 : E))
        (show TangentSpace I p from b) t : E) =
      (mfderiv (modelWithCornersSelf ℝ E) I
        (fun v : E =>
          expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from v))
        (0 : E)) (t • b) at hraw
  rw [mfderiv_expMapIntrinsic_at_zero (I := I) g hEnorm p] at hraw
  with_unfolding_all exact hraw

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrAtom_pathT_base_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) (t : ℝ) :
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
      (I := I) g hEnorm p 0 a b (0, t) : E) = 0 := by
  let f : ℝ → ℝ → M := fun r v =>
    intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((r, 0), v)
  change (Variation.varSnd (I := I) f 0 t : E) = 0
  unfold Variation.varSnd
  have hconst : (fun v : ℝ => f 0 v) = fun _ : ℝ => p := by
    funext v
    have hs := intrinsicGeodesic_smul (I := I) g hEnorm p
      (0 : TangentSpace I p) v
    rw [smul_zero] at hs
    have hzero : intrinsicGeodesic (I := I) g hEnorm p
        (0 : TangentSpace I p) 1 = p := by
      with_unfolding_all exact expMapIntrinsic_zero (I := I) g hEnorm p
    dsimp only [f, intrinsicLaunch3]
    simp only [zero_smul, add_zero]
    exact hs.symm.trans hzero
  rw [hconst, mfderiv_const]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrJetResidual_one_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) (t : ℝ) :
    (intrinsicJetResidual (I := I) g hEnorm p 0 a b 1 (0, t) : E) = 0 := by
  have heval := DifferentialGeometry.CheegerGromovCompactness.intrinsic_jacobi_residual_term_eval
    (I := I) g hEnorm p 0 a b 1
  have hpoint := congrFun (congrFun heval 0) t
  rw [hpoint]
  let T := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT
  let dT := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathDt
  let A := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aJet 0)
  let dA := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0)
  let B := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 0)
  let dB := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bTime 0)
  let s3 (x y z : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
      Fin 3 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm :=
    Fin.cons x (Fin.cons y (fun _ ↦ z))
  let s4 (w x y z : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
      Fin 4 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm :=
    Fin.cons w (s3 x y z)
  have hterm : DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiResidualTerm 1 =
      0 + (-1 : ℝ) •
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1 (s4 T A T B) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 dA T B) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 A dT B) +
          (2 : ℝ) • DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
            (s3 A T dB) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1 (s4 A B T T) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 B dA T) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 B T dA)) := by
    rfl
  rw [hterm]
  have hevalAdd (x y : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
      (x + y).eval (I := I) g hEnorm p 0 a b (0, t) =
        x.eval (I := I) g hEnorm p 0 a b (0, t) +
          y.eval (I := I) g hEnorm p 0 a b (0, t) := rfl
  have hevalScale (c : ℝ)
      (x : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
      (c • x).eval (I := I) g hEnorm p 0 a b (0, t) =
        c • x.eval (I := I) g hEnorm p 0 a b (0, t) := rfl
  rw [hevalAdd, hevalScale]
  repeat' rw [hevalAdd]
  rw [hevalScale]
  have hT : (T.eval (I := I) g hEnorm p 0 a b (0, t) : E) = 0 :=
    intrAtom_pathT_base_zero (I := I) g hEnorm p a b t
  have hdT : (dT.eval (I := I) g hEnorm p 0 a b (0, t) : E) = 0 := by
    exact congrArg (fun z ↦ (z : E))
      (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.path_dt_zero
        (I := I) g hEnorm p 0 a b 0 t)
  have hz (k : ℕ)
      (slots : Fin (k + 3) → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
      (i : Fin (k + 3))
      (hi : (slots i).eval (I := I) g hEnorm p 0 a b (0, t) = 0) :
      (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv k slots).eval
          (I := I) g hEnorm p 0 a b (0, t) = 0 := by
    exact DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero_at
      (I := I) g k _ _ i hi
  rw [hz 1 (s4 T A T B) 0 (by exact hT)]
  rw [hz 0 (s3 dA T B) 1 (by exact hT)]
  rw [hz 0 (s3 A dT B) 1 (by exact hdT)]
  rw [hz 0 (s3 A T dB) 1 (by exact hT)]
  rw [hz 1 (s4 A B T T) 2 (by exact hT)]
  rw [hz 0 (s3 B dA T) 2 (by exact hT)]
  rw [hz 0 (s3 B T dA) 1 (by exact hT)]
  simp
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicLaunchJet_one_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) :
    intrinsicLaunchJet (I := I) g hEnorm p 0 a b 1 (0, 1) = 0 := by
  let f : ℝ → ℝ → M := fun r t =>
    intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((r, 0), t)
  let W : ∀ r t : ℝ, TangentSpace I (f r t) := fun r t =>
    intrinsicLaunchJet (I := I) g hEnorm p 0 a b 1 (r, t)
  let C : E := (W 0 1 : E)
  have hcurve (t : ℝ) : f 0 t = p := by
    have hs := intrinsicGeodesic_smul (I := I) g hEnorm p
      (0 : TangentSpace I p) t
    rw [smul_zero] at hs
    have hzero : intrinsicGeodesic (I := I) g hEnorm p
        (0 : TangentSpace I p) 1 = p := by
      with_unfolding_all exact expMapIntrinsic_zero (I := I) g hEnorm p
    dsimp only [f, intrinsicLaunch3]
    simp only [zero_smul, add_zero]
    exact hs.symm.trans hzero
  have hW (t : ℝ) : (W 0 t : E) = t ^ 2 • C := by
    have hs := intrinsicLaunchJet_zero_scale (I := I) g hEnorm p a b 1 0 t
    dsimp only [W, C]
    rw [mul_zero] at hs
    exact hs
  have hpoly (t : ℝ) : HasDerivAt (fun s : ℝ => s ^ 2 • C)
      ((2 * t) • C) t := by
    have h := (hasDerivAt_pow 2 t).smul_const C
    convert h using 1
    all_goals norm_num
  have hDW (t : ℝ) :
      (Variation.covSnd (I := I) g f W 0 t : E) = (2 * t) • C := by
    have hcongr := covDerivAlong_congr_curve (I := I) g (t := t)
      (fun s : ℝ => W 0 s)
      (fun s : ℝ => (show TangentSpace I p from s ^ 2 • C))
      (Filter.Eventually.of_forall hcurve)
      (Filter.Eventually.of_forall hW)
    have hconst := covDerivAlong_const (I := I) g p
      (fun s : ℝ => (show TangentSpace I p from s ^ 2 • C)) t
      (hpoly t).differentiableAt
    have hcongrE := congrArg (fun z ↦ (z : E)) hcongr
    have hconstE := congrArg (fun z ↦ (z : E)) hconst
    change (covDerivAlong (I := I) g (fun s : ℝ => f 0 s)
      (fun s : ℝ => W 0 s) t : E) = _
    exact hcongrE.trans (hconstE.trans (hpoly t).deriv)
  have hlin (t : ℝ) : HasDerivAt (fun s : ℝ => (2 * s) • C)
      ((2 : ℝ) • C) t := by
    simpa only [id_eq, one_mul, mul_comm] using
      (((hasDerivAt_id t).const_mul 2).smul_const C)
  have hDDW (t : ℝ) :
      (Variation.covSnd2 (I := I) g f W 0 t : E) = (2 : ℝ) • C := by
    have hcongr := covDerivAlong_congr_curve (I := I) g (t := t)
      (fun s : ℝ => Variation.covSnd (I := I) g f W 0 s)
      (fun s : ℝ => (show TangentSpace I p from (2 * s) • C))
      (Filter.Eventually.of_forall hcurve)
      (Filter.Eventually.of_forall hDW)
    have hconst := covDerivAlong_const (I := I) g p
      (fun s : ℝ => (show TangentSpace I p from (2 * s) • C)) t
      (hlin t).differentiableAt
    have hcongrE := congrArg (fun z ↦ (z : E)) hcongr
    have hconstE := congrArg (fun z ↦ (z : E)) hconst
    change (covDerivAlong (I := I) g (fun s : ℝ => f 0 s)
      (fun s : ℝ => Variation.covSnd (I := I) g f W 0 s) t : E) = _
    exact hcongrE.trans (hconstE.trans (hlin t).deriv)
  have hT : Variation.varSnd (I := I) f 0 1 = 0 := by
    change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
      (I := I) g hEnorm p 0 a b (0, 1) = 0
    exact intrAtom_pathT_base_zero (I := I) g hEnorm p a b 1
  have hcurv : Variation.jacobianCurv (I := I) g f W 0 1 = 0 := by
    unfold Variation.jacobianCurv Variation.curvAlong
    change
      (DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
        (f 0 1)) (W 0 1) (Variation.varSnd (I := I) f 0 1)
          (Variation.varSnd (I := I) f 0 1) = 0
    rw [hT]
    exact map_zero _
  have hres := intrJetResidual_one_zero (I := I) g hEnorm p a b 1
  change Variation.covSnd2 (I := I) g f W 0 1 +
      Variation.jacobianCurv (I := I) g f W 0 1 = 0 at hres
  have hD2zero : Variation.covSnd2 (I := I) g f W 0 1 = 0 := by
    rw [hcurv] at hres
    exact (add_eq_zero_iff_eq_neg.mp hres).trans neg_zero
  have hD2zeroRaw := congrArg (fun z ↦ (z : E)) hD2zero
  have hzP : ((0 : TangentSpace I (f 0 1)) : E) = (0 : E) := by rfl
  have hD2zeroE : (Variation.covSnd2 (I := I) g f W 0 1 : E) = (0 : E) :=
    hD2zeroRaw.trans hzP
  have htwoC : (2 : ℝ) • C = 0 := (hDDW 1).symm.trans hD2zeroE
  have hC : C = 0 := by
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    exact (smul_eq_zero.mp htwoC).resolve_left htwo
  apply (tangentSpaceModelContinuousLinearEquiv (I := I) (f 0 1)).injective
  change C = ((0 : TangentSpace I (f 0 1)) : E)
  exact hC.trans hzP.symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrAtom_bTime_zero_base
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) (t : ℝ) :
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bTime 0).eval
        (I := I) g hEnorm p 0 a b (0, t) =
      (show TangentSpace I p from b) := by
  let f : ℝ → ℝ → M := fun r s =>
    intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((r, 0), s)
  let J : ∀ s : ℝ, TangentSpace I (f 0 s) := fun s =>
    intrinsicLaunchJ (I := I) g hEnorm p 0 a b (0, s)
  have hcurve (s : ℝ) : f 0 s = p := by
    have hs := intrinsicGeodesic_smul (I := I) g hEnorm p
      (0 : TangentSpace I p) s
    rw [smul_zero] at hs
    have hzero : intrinsicGeodesic (I := I) g hEnorm p
        (0 : TangentSpace I p) 1 = p := by
      with_unfolding_all exact expMapIntrinsic_zero (I := I) g hEnorm p
    dsimp only [f, intrinsicLaunch3]
    simp only [zero_smul, add_zero]
    exact hs.symm.trans hzero
  have hJ (s : ℝ) : (J s : E) = s • b :=
    intrinsicLaunchJ_base_zero (I := I) g hEnorm p a b s
  have hcongr := covDerivAlong_congr_curve (I := I) g (t := t) J
    (fun s : ℝ => (show TangentSpace I p from s • b))
    (Filter.Eventually.of_forall hcurve)
    (Filter.Eventually.of_forall hJ)
  have hline : HasDerivAt (fun s : ℝ => s • b) b t := by
    convert (hasDerivAt_id t).smul_const b using 1 <;> simp
  have hconst := covDerivAlong_const (I := I) g p
    (fun s : ℝ => (show TangentSpace I p from s • b)) t
    hline.differentiableAt
  have hcongrE := congrArg (fun z ↦ (z : E)) hcongr
  have hconstE := congrArg (fun z ↦ (z : E)) hconst
  change covDerivAlong (I := I) g (fun s : ℝ => f 0 s) J t = _
  apply (tangentSpaceModelContinuousLinearEquiv (I := I) p).injective
  change (covDerivAlong (I := I) g (fun s : ℝ => f 0 s) J t : E) = b
  exact hcongrE.trans (hconstE.trans hline.deriv)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrAtom_bTime_one_base_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) (t : ℝ) :
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bTime 1).eval
        (I := I) g hEnorm p 0 a b (0, t) = 0 := by
  let f : ℝ → ℝ → M := fun r s =>
    intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((r, 0), s)
  let W : ∀ s : ℝ, TangentSpace I (f 0 s) := fun s =>
    intrinsicLaunchJet (I := I) g hEnorm p 0 a b 1 (0, s)
  have hcurve (s : ℝ) : f 0 s = p := by
    have hs := intrinsicGeodesic_smul (I := I) g hEnorm p
      (0 : TangentSpace I p) s
    rw [smul_zero] at hs
    have hzero : intrinsicGeodesic (I := I) g hEnorm p
        (0 : TangentSpace I p) 1 = p := by
      with_unfolding_all exact expMapIntrinsic_zero (I := I) g hEnorm p
    dsimp only [f, intrinsicLaunch3]
    simp only [zero_smul, add_zero]
    exact hs.symm.trans hzero
  have hW (s : ℝ) : W s = 0 := by
    have hs := intrinsicLaunchJet_zero_scale (I := I) g hEnorm p a b 1 0 s
    rw [mul_zero] at hs
    have hone := intrinsicLaunchJet_one_zero (I := I) g hEnorm p a b
    dsimp only [W]
    rw [hs, hone, smul_zero]
    rfl
  have hcongr := covDerivAlong_congr_curve (I := I) g (t := t) W
    (fun _ : ℝ => (0 : TangentSpace I p))
    (Filter.Eventually.of_forall hcurve)
    (Filter.Eventually.of_forall (fun s => congrArg (fun z => (z : E)) (hW s)))
  have hzero := covDerivAlong_zero (I := I) g (fun _ : ℝ => p) t
  change covDerivAlong (I := I) g (fun s : ℝ => f 0 s) W t = 0
  exact hcongr.trans hzero

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicLaunchJet_one_swap_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) :
    intrinsicLaunchJet (I := I) g hEnorm p 0 a b 1 (0, 1) =
      intrinsicLaunchJet (I := I) g hEnorm p 0 b a 1 (0, 1) := by
  let f : ℝ → ℝ → M := fun r t =>
    intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((r, 0), t)
  let V : ∀ r t : ℝ, TangentSpace I (f r t) := fun r t =>
    intrinsicLaunchJ (I := I) g hEnorm p 0 a b (r, t)
  let f' : ℝ → ℝ → M := fun r t =>
    intrinsicLaunch3 (I := I) g hEnorm p 0 b a ((r, 0), t)
  let V' : ∀ r t : ℝ, TangentSpace I (f' r t) := fun r t =>
    intrinsicLaunchJ (I := I) g hEnorm p 0 b a (r, t)
  have hcomm := intrinsicLaunch_commute (I := I) g hEnorm p 0 a b 1
  dsimp only at hcomm
  have hcurve : (fun s : ℝ =>
      intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, s), 1)) =
      (fun s : ℝ => f' s 1) := by
    funext s
    simp [f', intrinsicLaunch3]
  have hfield : ∀ s : ℝ,
      (mfderiv (modelWithCornersSelf ℝ ℝ) I
          (fun r : ℝ => intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((r, s), 1))
          0 1 : E) = (V' s 1 : E) := by
    intro s
    have hfun :
        (fun r : ℝ => intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((r, s), 1)) =
        (fun r : ℝ => intrinsicLaunch3 (I := I) g hEnorm p 0 b a ((s, r), 1)) := by
      funext r
      simp [intrinsicLaunch3, add_comm]
    rw [hfun]
    exact congrArg (fun z => (z : E))
      (intrinsicLaunchJ_eq (I := I) g hEnorm p 0 b a (s, 1)).symm
  have hcongr := covDerivAlong_congr_curve (I := I) g (t := (0 : ℝ))
    (fun s : ℝ => mfderiv (modelWithCornersSelf ℝ ℝ) I
      (fun r : ℝ => intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((r, s), 1)) 0 1)
    (fun s : ℝ => V' s 1)
    (Filter.Eventually.of_forall (fun s => congrFun hcurve s))
    (Filter.Eventually.of_forall hfield)
  change covFst (I := I) g f V 0 1 = covFst (I := I) g f' V' 0 1
  simp only [f, V, f', V', covFst, intrinsicLaunchJ_eq]
  exact hcomm.trans (by simpa only [f', V', intrinsicLaunchJ_eq] using hcongr)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicLaunchJet_one_diag_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a : E) :
    intrinsicLaunchJet (I := I) g hEnorm p 0 a a 1 (0, 1) = 0 := by
  let f : ℝ → ℝ → M := fun r t =>
    intrinsicLaunch3 (I := I) g hEnorm p 0 a a ((r, 0), t)
  let V : ∀ r t : ℝ, TangentSpace I (f r t) := fun r t =>
    intrinsicLaunchJ (I := I) g hEnorm p 0 a a (r, t)
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p
    (show TangentSpace I p from a)
  have hfV : ∀ r t, Variation.varFst (I := I) f r t = V r t := by
    intro r t
    exact intrinsicLaunchA_self (I := I) g hEnorm p 0 a r t
  have hcurve : (fun r : ℝ => f r 1) = γ := by
    funext r
    simp only [f, intrinsicLaunch3, zero_add, zero_smul, add_zero]
    exact intrinsicGeodesic_smul (I := I) g hEnorm p
      (show TangentSpace I p from a) r
  have hfield : ∀ r : ℝ, (V r 1 : E) =
      (curveVelocity (I := I) γ r : E) := by
    intro r
    rw [← hfV r 1]
    unfold Variation.varFst curveVelocity
    have hfun : (fun s : ℝ => f s 1) = γ := hcurve
    rw [hfun]
    rfl
  have hcongr := covDerivAlong_congr_curve (I := I) g (t := (0 : ℝ))
    (fun r : ℝ => V r 1) (fun r : ℝ => curveVelocity (I := I) γ r)
    (Filter.Eventually.of_forall (fun r => congrFun hcurve r))
    (Filter.Eventually.of_forall hfield)
  have hγsmooth : ContMDiffAt (modelWithCornersSelf ℝ ℝ) I 2 γ 0 :=
    ((intrinsicGeodesic_contMDiffOn_infty (I := I) g hEnorm p
      (show TangentSpace I p from a)).contMDiffAt Filter.univ_mem).of_le
        ENat.LEInfty.out
  have hgeo :
      DifferentialGeometry.Geometry.Riemannian.Geodesic.HasGeodesicEquationAt
        (I := I) g γ 0 :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from a) 0
  have hzero := covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
    (I := I) g γ 0 hγsmooth hgeo
  change covFst (I := I) g f V 0 1 = 0
  change covDerivAlong (I := I) g (fun r : ℝ => f r 1)
    (fun r : ℝ => V r 1) 0 = 0
  exact hcongr.trans hzero

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicFrameMetric_radial
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (z w : E) :
    intrinsicFrameMetric (I := I) g hEnorm p z z w = Inner.inner ℝ z w := by
  let hNorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := hEnorm
  change intrinsicFrameMetric (I := I) g hNorm p z z w = _
  rw [intrinsic_metric_jacobi (I := I) g hNorm p z z w,
    intrinsicJacobi_self (I := I) g hNorm p (normalFrame (I := I) g p z),
    intrinsicFrame_apply (I := I) g hNorm p z]
  change g.inner
      (intrinsicGeodesic (I := I) g hNorm p (normalFrame (I := I) g p z) 1)
      (curveVelocity (I := I)
        (intrinsicGeodesic (I := I) g hNorm p (normalFrame (I := I) g p z)) 1)
      (intrinsicJacobi (I := I) g hNorm p
        (normalFrame (I := I) g p z) (normalFrame (I := I) g p w) 1) = _
  have h := intrinsicJacobi_perp (I := I) g hNorm p
    (normalFrame (I := I) g p z) (normalFrame (I := I) g p w)
  rw [normalFrame_inner] at h
  change g.inner
      (intrinsicGeodesic (I := I) g hNorm p (normalFrame (I := I) g p z) 1)
      (curveVelocity (I := I)
        (intrinsicGeodesic (I := I) g hNorm p (normalFrame (I := I) g p z)) 1)
      (intrinsicJacobi (I := I) g hNorm p
        (normalFrame (I := I) g p z) (normalFrame (I := I) g p w) 1) = _ at h
  exact h

private theorem neg_one_smul_add_self_eq_neg_two_smul
    {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) :
    (-1 : ℝ) • (v + v) = (-2 : ℝ) • v := by
  module

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private theorem intrJetResidual_two_zero_internal
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) :
    (intrinsicJetResidual (I := I) g hEnorm p 0 a b 2 (0, 1) : E) =
      (-2 : ℝ) •
        (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p)
          (show TangentSpace I p from b)
          (show TangentSpace I p from a)
          (show TangentSpace I p from a) := by
  let T := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT
  let pathD := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathDt
  let A := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aJet 0)
  let dA := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0)
  let B := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 0)
  let dB := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bTime 0)
  let s3 (x y z : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
      Fin 3 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm :=
    Fin.cons x (Fin.cons y (fun _ ↦ z))
  have hbase : intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1) = p := by
    have hs := intrinsicGeodesic_smul (I := I) g hEnorm p
      (0 : TangentSpace I p) 1
    rw [smul_zero] at hs
    have hzero : intrinsicGeodesic (I := I) g hEnorm p
        (0 : TangentSpace I p) 1 = p := by
      with_unfolding_all exact expMapIntrinsic_zero (I := I) g hEnorm p
    simp only [intrinsicLaunch3, zero_smul, add_zero]
    exact hs.symm.trans hzero
  have hTzero :
      DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    apply (tangentSpaceModelContinuousLinearEquiv (I := I)
      (intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1))).injective
    exact intrAtom_pathT_base_zero (I := I) g hEnorm p a b 1
  have hBzero :
      (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 1).eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    change intrinsicLaunchJet (I := I) g hEnorm p 0 a b 1 (0, 1) = 0
    exact intrinsicLaunchJet_one_zero (I := I) g hEnorm p a b
  have hPathDzero :
      DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathDt.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0 :=
    DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.path_dt_zero
      (I := I) g hEnorm p 0 a b 0 1
  have hdAonezero :
      (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 1).eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    rw [DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.a_time_eq_self]
    exact intrAtom_bTime_one_base_zero (I := I) g hEnorm p a a 1
  have hBval :
      (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 0).eval
          (I := I) g hEnorm p 0 a b (0, 1) =
        (show TangentSpace I p from b) := by
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) p).injective
    change (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 0 (0, 1) : E) = b
    rw [intrinsicLaunchJet_zero]
    simpa using intrinsicLaunchJ_base_zero (I := I) g hEnorm p a b 1
  have hAval :
      (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aJet 0).eval
          (I := I) g hEnorm p 0 a b (0, 1) =
        (show TangentSpace I p from a) := by
    rw [DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.a_jet_eq_self]
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) p).injective
    change (intrinsicLaunchJet (I := I) g hEnorm p 0 a a 0 (0, 1) : E) = a
    rw [intrinsicLaunchJet_zero]
    simpa using intrinsicLaunchJ_base_zero (I := I) g hEnorm p a a 1
  have hdAval :
      (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0).eval
          (I := I) g hEnorm p 0 a b (0, 1) =
        (show TangentSpace I p from a) := by
    rw [DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.a_time_eq_self]
    exact intrAtom_bTime_zero_base (I := I) g hEnorm p a a 1
  have hAdA :
      A.eval (I := I) g hEnorm p 0 a b (0, 1) =
        dA.eval (I := I) g hEnorm p 0 a b (0, 1) := by
    exact hAval.trans hdAval.symm
  have hcurv3Eval (x y z : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
      ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
        (s3 x y z)).launchDeriv).eval
          (I := I) g hEnorm p 0 a b (0, 1) =
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
          (Fin.cons A (s3 x y z))).eval
            (I := I) g hEnorm p 0 a b (0, 1) +
        ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (Function.update (s3 x y z) 0 x.launchDeriv)).eval
            (I := I) g hEnorm p 0 a b (0, 1) +
        ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (Function.update (s3 x y z) 1 y.launchDeriv)).eval
            (I := I) g hEnorm p 0 a b (0, 1) +
        ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (Function.update (s3 x y z) 2 z.launchDeriv)).eval
          (I := I) g hEnorm p 0 a b (0, 1) + 0))) := by
    rfl
  have hcurv4Eval (w x y z : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
      ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
        (Fin.cons w (s3 x y z))).launchDeriv).eval
          (I := I) g hEnorm p 0 a b (0, 1) =
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 2
          (Fin.cons A (Fin.cons w (s3 x y z)))).eval
            (I := I) g hEnorm p 0 a b (0, 1) +
        ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
          (Function.update (Fin.cons w (s3 x y z)) 0 w.launchDeriv)).eval
            (I := I) g hEnorm p 0 a b (0, 1) +
        ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
          (Function.update (Fin.cons w (s3 x y z)) 1 x.launchDeriv)).eval
            (I := I) g hEnorm p 0 a b (0, 1) +
        ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
          (Function.update (Fin.cons w (s3 x y z)) 2 y.launchDeriv)).eval
            (I := I) g hEnorm p 0 a b (0, 1) +
        ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
          (Function.update (Fin.cons w (s3 x y z)) 3 z.launchDeriv)).eval
            (I := I) g hEnorm p 0 a b (0, 1) + 0)))) := by
    rfl
  have hz (k : ℕ)
      (slots : Fin (k + 3) → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
      (i : Fin (k + 3))
      (hi : (slots i).eval (I := I) g hEnorm p 0 a b (0, 1) = 0) :
      (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv k slots).eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    exact DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero_at
      (I := I) g k _ _ i hi
  have hcurvA := hz 0 (s3 A T A) (1 : Fin 3) (by
    change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
      (I := I) g hEnorm p 0 a b (0, 1) = 0
    exact hTzero)
  have hdAlaunchZero : dA.launchDeriv.eval
      (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    change
      (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 1).eval
          (I := I) g hEnorm p 0 a b (0, 1) +
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (s3 A T A)).eval (I := I) g hEnorm p 0 a b (0, 1) = 0
    rw [hdAonezero, hcurvA, add_zero]
  have hBlaunchZero : B.launchDeriv.eval
      (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    change (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 1).eval
      (I := I) g hEnorm p 0 a b (0, 1) = 0
    exact hBzero
  have hAlaunchZero : A.launchDeriv.eval
      (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    change (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aJet 1).eval
      (I := I) g hEnorm p 0 a b (0, 1) = 0
    rw [DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.a_jet_eq_self]
    change intrinsicLaunchJet (I := I) g hEnorm p 0 a a 1 (0, 1) = 0
    exact intrinsicLaunchJet_one_zero (I := I) g hEnorm p a a
  have hPathDlaunchZero : pathD.launchDeriv.eval
      (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    rfl
  have hdBlaunchZero : dB.launchDeriv.eval
      (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    have hcurvAB := hz 0 (s3 A T B) (1 : Fin 3) (by
      change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
        (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hTzero)
    change
      (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bTime 1).eval
          (I := I) g hEnorm p 0 a b (0, 1) +
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (s3 A T B)).eval (I := I) g hEnorm p 0 a b (0, 1) = 0
    rw [intrAtom_bTime_one_base_zero (I := I) g hEnorm p a b 1,
      hcurvAB, add_zero]
  have hcurvRepeated (X Z : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
      (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
        (s3 X X Z)).eval (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    change DifferentialGeometry.CheegerGromovCompactness.curvOpN (I := I) g 0
      (intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1))
      (fun i => (s3 X X Z i).eval (I := I) g hEnorm p 0 a b (0, 1)) = 0
    have hslots :
        (fun i => (s3 X X Z i).eval (I := I) g hEnorm p 0 a b (0, 1)) =
        DifferentialGeometry.Geometry.Curvature.vec3 (I := I)
          (X.eval (I := I) g hEnorm p 0 a b (0, 1))
          (X.eval (I := I) g hEnorm p 0 a b (0, 1))
          (Z.eval (I := I) g hEnorm p 0 a b (0, 1)) := by
      funext i
      fin_cases i <;> rfl
    rw [hslots, DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero]
    change
      (DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
        (intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1)))
        (X.eval (I := I) g hEnorm p 0 a b (0, 1))
        (X.eval (I := I) g hEnorm p 0 a b (0, 1))
        (Z.eval (I := I) g hEnorm p 0 a b (0, 1)) = 0
    have hswap := DifferentialGeometry.Geometry.Curvature.riemannOp_swap
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
      (intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1))
      (X.eval (I := I) g hEnorm p 0 a b (0, 1))
      (X.eval (I := I) g hEnorm p 0 a b (0, 1))
      (Z.eval (I := I) g hEnorm p 0 a b (0, 1))
    linear_combination (norm := module) (1 / 2 : ℝ) • hswap
  have hcurvAdA (Z : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
      (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
        (s3 A dA Z)).eval (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    change DifferentialGeometry.CheegerGromovCompactness.curvOpN (I := I) g 0
      (intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1))
      (fun i => (s3 A dA Z i).eval (I := I) g hEnorm p 0 a b (0, 1)) = 0
    have hslots :
        (fun i => (s3 A dA Z i).eval (I := I) g hEnorm p 0 a b (0, 1)) =
        DifferentialGeometry.Geometry.Curvature.vec3 (I := I)
          (A.eval (I := I) g hEnorm p 0 a b (0, 1))
          (dA.eval (I := I) g hEnorm p 0 a b (0, 1))
          (Z.eval (I := I) g hEnorm p 0 a b (0, 1)) := by
      funext i
      fin_cases i <;> rfl
    rw [hslots, DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero]
    change
      (DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
        (intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1)))
        (A.eval (I := I) g hEnorm p 0 a b (0, 1))
        (dA.eval (I := I) g hEnorm p 0 a b (0, 1))
        (Z.eval (I := I) g hEnorm p 0 a b (0, 1)) = 0
    rw [← hAdA]
    have hswap := DifferentialGeometry.Geometry.Curvature.riemannOp_swap
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
      (intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1))
      (A.eval (I := I) g hEnorm p 0 a b (0, 1))
      (A.eval (I := I) g hEnorm p 0 a b (0, 1))
      (Z.eval (I := I) g hEnorm p 0 a b (0, 1))
    linear_combination (norm := module) (1 / 2 : ℝ) • hswap
  have hlast :
      ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
        (s3 B T dA)).launchDeriv).eval
          (I := I) g hEnorm p 0 a b (0, 1) =
        (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p)
          (show TangentSpace I p from b)
          (show TangentSpace I p from a)
          (show TangentSpace I p from a) := by
    have hlastX :
        ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (s3 B T dA)).launchDeriv).eval
            (I := I) g hEnorm p 0 a b (0, 1) =
          (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1)))
            ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 0).eval
              (I := I) g hEnorm p 0 a b (0, 1))
            ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0).eval
              (I := I) g hEnorm p 0 a b (0, 1))
            ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0).eval
              (I := I) g hEnorm p 0 a b (0, 1)) := by
      let baseSlots : Fin 3 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm :=
        s3 B T dA
      let leadSlots : Fin 4 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm :=
        Fin.cons A baseSlots
      let B1 := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
        (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 1)
      let dT := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
        (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0)
      let dA1 := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
          (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 1) +
        DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 A T A)
      have hlaunch :
          (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
            baseSlots).launchDeriv =
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1 leadSlots +
            (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
              (Function.update baseSlots 0 B1) +
            (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
              (Function.update baseSlots 1 dT) +
            (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
              (Function.update baseSlots 2 dA1) + 0))) := by
        rfl
      have hz (k : ℕ)
          (slots : Fin (k + 3) → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
          (i : Fin (k + 3))
          (hi : (slots i).eval (I := I) g hEnorm p 0 a b (0, 1) = 0) :
          (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv k slots).eval
              (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
        exact DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero_at
          (I := I) g k _ _ i hi
      have hlead := hz 1 leadSlots (2 : Fin 4) (by
        change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
        exact hTzero)
      have hfirst := hz 0 (Function.update baseSlots 0 B1) (0 : Fin 3) (by
        change (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 1).eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
        exact hBzero)
      have hcurvA := hz 0 (s3 A T A) (1 : Fin 3) (by
        change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
        exact hTzero)
      have hdA1zero : dA1.eval (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
        change
          (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 1).eval
              (I := I) g hEnorm p 0 a b (0, 1) +
            (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
              (s3 A T A)).eval (I := I) g hEnorm p 0 a b (0, 1) = 0
        rw [hdAonezero, hcurvA, add_zero]
      have hthird := hz 0 (Function.update baseSlots 2 dA1) (2 : Fin 3) (by
        change dA1.eval (I := I) g hEnorm p 0 a b (0, 1) = 0
        exact hdA1zero)
      rw [show DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (s3 B T dA) =
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 baseSlots by rfl,
        hlaunch]
      change
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1 leadSlots).eval
            (I := I) g hEnorm p 0 a b (0, 1) +
          ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
              (Function.update baseSlots 0 B1)).eval
              (I := I) g hEnorm p 0 a b (0, 1) +
          ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
              (Function.update baseSlots 1 dT)).eval
              (I := I) g hEnorm p 0 a b (0, 1) +
          ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
              (Function.update baseSlots 2 dA1)).eval
              (I := I) g hEnorm p 0 a b (0, 1) + 0))) = _
      rw [hlead, hfirst, hthird]
      simp only [zero_add, add_zero]
      change
        DifferentialGeometry.CheegerGromovCompactness.curvOpN (I := I) g 0
          (intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1))
          (fun i => (Function.update baseSlots 1 dT i).eval
            (I := I) g hEnorm p 0 a b (0, 1)) = _
      have hslots :
          (fun i => (Function.update baseSlots 1 dT i).eval
            (I := I) g hEnorm p 0 a b (0, 1)) =
          DifferentialGeometry.Geometry.Curvature.vec3 (I := I)
            ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 0).eval
              (I := I) g hEnorm p 0 a b (0, 1))
            ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0).eval
              (I := I) g hEnorm p 0 a b (0, 1))
            ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0).eval
              (I := I) g hEnorm p 0 a b (0, 1)) := by
        funext i
        fin_cases i <;> rfl
      rw [hslots, DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero]
    rw [hlastX]
    rw [hBval, hdAval, hbase]
  have hpenult :
      ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
        (s3 B dA T)).launchDeriv).eval
          (I := I) g hEnorm p 0 a b (0, 1) =
        (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p)
          (show TangentSpace I p from b)
          (show TangentSpace I p from a)
          (show TangentSpace I p from a) := by
    rw [hcurv3Eval]
    rw [hz 1 (Fin.cons A (s3 B dA T)) (3 : Fin 4) (by
      change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
        (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hTzero)]
    rw [hz 0 (Function.update (s3 B dA T) 0 B.launchDeriv) (0 : Fin 3) (by
      change B.launchDeriv.eval (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hBlaunchZero)]
    rw [hz 0 (Function.update (s3 B dA T) 1 dA.launchDeriv) (1 : Fin 3) (by
      change dA.launchDeriv.eval (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hdAlaunchZero)]
    simp only [zero_add]
    have hmid :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (Function.update (s3 B dA T) 2 T.launchDeriv)).eval
            (I := I) g hEnorm p 0 a b (0, 1) =
          (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1)))
            ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 0).eval
              (I := I) g hEnorm p 0 a b (0, 1))
            ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0).eval
              (I := I) g hEnorm p 0 a b (0, 1))
            ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0).eval
              (I := I) g hEnorm p 0 a b (0, 1)) := by
      change DifferentialGeometry.CheegerGromovCompactness.curvOpN (I := I) g 0
        (intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1))
        (fun i => (Function.update (s3 B dA T) 2 T.launchDeriv i).eval
          (I := I) g hEnorm p 0 a b (0, 1)) = _
      have hslots :
          (fun i => (Function.update (s3 B dA T) 2 T.launchDeriv i).eval
            (I := I) g hEnorm p 0 a b (0, 1)) =
          DifferentialGeometry.Geometry.Curvature.vec3 (I := I)
            ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 0).eval
              (I := I) g hEnorm p 0 a b (0, 1))
            ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0).eval
              (I := I) g hEnorm p 0 a b (0, 1))
            ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0).eval
              (I := I) g hEnorm p 0 a b (0, 1)) := by
        funext i
        fin_cases i <;> rfl
      rw [hslots, DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero]
    rw [hmid, add_zero, hBval, hdAval, hbase]
  have hfirstLaunch :
      ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
        (Fin.cons T (s3 A T B))).launchDeriv).eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    rw [hcurv4Eval]
    rw [hz 2 (Fin.cons A (Fin.cons T (s3 A T B))) (1 : Fin 5) (by
      change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
        (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hTzero)]
    rw [hz 1 (Function.update (Fin.cons T (s3 A T B)) 0 T.launchDeriv)
      (2 : Fin 4) (by
        change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
        exact hTzero)]
    rw [hz 1 (Function.update (Fin.cons T (s3 A T B)) 1 A.launchDeriv)
      (0 : Fin 4) (by
        change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
        exact hTzero)]
    rw [hz 1 (Function.update (Fin.cons T (s3 A T B)) 2 T.launchDeriv)
      (0 : Fin 4) (by
        change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
        exact hTzero)]
    rw [hz 1 (Function.update (Fin.cons T (s3 A T B)) 3 B.launchDeriv)
      (0 : Fin 4) (by
        change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
        exact hTzero)]
    simp
  have hfifthLaunch :
      ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
        (Fin.cons A (s3 B T T))).launchDeriv).eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    rw [hcurv4Eval]
    rw [hz 2 (Fin.cons A (Fin.cons A (s3 B T T))) (3 : Fin 5) (by
      change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
        (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hTzero)]
    rw [hz 1 (Function.update (Fin.cons A (s3 B T T)) 0 A.launchDeriv)
      (2 : Fin 4) (by
        change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
        exact hTzero)]
    rw [hz 1 (Function.update (Fin.cons A (s3 B T T)) 1 B.launchDeriv)
      (2 : Fin 4) (by
        change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
        exact hTzero)]
    rw [hz 1 (Function.update (Fin.cons A (s3 B T T)) 2 T.launchDeriv)
      (3 : Fin 4) (by
        change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
        exact hTzero)]
    rw [hz 1 (Function.update (Fin.cons A (s3 B T T)) 3 T.launchDeriv)
      (2 : Fin 4) (by
        change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
        exact hTzero)]
    simp
  have hsecondLaunch :
      ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
        (s3 dA T B)).launchDeriv).eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    rw [hcurv3Eval]
    rw [hz 1 (Fin.cons A (s3 dA T B)) (2 : Fin 4) (by
      change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
        (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hTzero)]
    rw [hz 0 (Function.update (s3 dA T B) 0 dA.launchDeriv) (0 : Fin 3) (by
      change dA.launchDeriv.eval (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hdAlaunchZero)]
    have hmiddle :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (Function.update (s3 dA T B) 1 T.launchDeriv)).eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      change (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
        (s3 dA dA B)).eval (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hcurvRepeated dA B
    rw [hmiddle]
    rw [hz 0 (Function.update (s3 dA T B) 2 B.launchDeriv) (2 : Fin 3) (by
      change B.launchDeriv.eval (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hBlaunchZero)]
    simp
  have hthirdLaunch :
      ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
        (s3 A pathD B)).launchDeriv).eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    rw [hcurv3Eval]
    rw [hz 1 (Fin.cons A (s3 A pathD B)) (2 : Fin 4) (by
      change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathDt.eval
        (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hPathDzero)]
    rw [hz 0 (Function.update (s3 A pathD B) 0 A.launchDeriv) (0 : Fin 3) (by
      change A.launchDeriv.eval (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hAlaunchZero)]
    rw [hz 0 (Function.update (s3 A pathD B) 1 pathD.launchDeriv) (1 : Fin 3) (by
      change pathD.launchDeriv.eval (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hPathDlaunchZero)]
    rw [hz 0 (Function.update (s3 A pathD B) 2 B.launchDeriv) (2 : Fin 3) (by
      change B.launchDeriv.eval (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hBlaunchZero)]
    simp
  have hfourthLaunch :
      ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
        (s3 A T dB)).launchDeriv).eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    rw [hcurv3Eval]
    rw [hz 1 (Fin.cons A (s3 A T dB)) (2 : Fin 4) (by
      change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
        (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hTzero)]
    rw [hz 0 (Function.update (s3 A T dB) 0 A.launchDeriv) (0 : Fin 3) (by
      change A.launchDeriv.eval (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hAlaunchZero)]
    have hmiddle :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (Function.update (s3 A T dB) 1 T.launchDeriv)).eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      change (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
        (s3 A dA dB)).eval (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hcurvAdA dB
    rw [hmiddle]
    rw [hz 0 (Function.update (s3 A T dB) 2 dB.launchDeriv) (2 : Fin 3) (by
      change dB.launchDeriv.eval (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hdBlaunchZero)]
    simp
  let s4 (w x y z : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
      Fin 4 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm :=
    Fin.cons w (s3 x y z)
  have hcorr0Launch :
      (DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiCorrectionTerm 0).launchDeriv.eval
          (I := I) g hEnorm p 0 a b (0, 1) =
          (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p)
            (show TangentSpace I p from b)
            (show TangentSpace I p from a)
            (show TangentSpace I p from a) +
          (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p)
            (show TangentSpace I p from b)
            (show TangentSpace I p from a)
            (show TangentSpace I p from a) := by
    have hterm : DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiCorrectionTerm 0 =
        DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1 (s4 T A T B) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 dA T B) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 A pathD B) +
          (2 : ℝ) • DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
            (s3 A T dB) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1 (s4 A B T T) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 B dA T) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 B T dA) := by
      rfl
    rw [hterm]
    have hlaunchTerm :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1 (s4 T A T B) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 dA T B) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 A pathD B) +
          (2 : ℝ) • DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
            (s3 A T dB) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1 (s4 A B T T) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 B dA T) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
            (s3 B T dA)).launchDeriv =
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
            (s4 T A T B)).launchDeriv +
          (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
            (s3 dA T B)).launchDeriv +
          (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
            (s3 A pathD B)).launchDeriv +
          (2 : ℝ) • (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
            (s3 A T dB)).launchDeriv +
          (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
            (s4 A B T T)).launchDeriv +
          (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
            (s3 B dA T)).launchDeriv +
          (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
            (s3 B T dA)).launchDeriv := by
      rfl
    rw [hlaunchTerm]
    change
      ((((((
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
          (s4 T A T B)).launchDeriv.eval
            (I := I) g hEnorm p 0 a b (0, 1) +
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (s3 dA T B)).launchDeriv.eval
            (I := I) g hEnorm p 0 a b (0, 1)) +
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (s3 A pathD B)).launchDeriv.eval
            (I := I) g hEnorm p 0 a b (0, 1)) +
        (2 : ℝ) • (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (s3 A T dB)).launchDeriv.eval
            (I := I) g hEnorm p 0 a b (0, 1)) +
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
          (s4 A B T T)).launchDeriv.eval
            (I := I) g hEnorm p 0 a b (0, 1)) +
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (s3 B dA T)).launchDeriv.eval
            (I := I) g hEnorm p 0 a b (0, 1)) +
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (s3 B T dA)).launchDeriv.eval
            (I := I) g hEnorm p 0 a b (0, 1)) = _
    rw [hfirstLaunch, hsecondLaunch, hthirdLaunch, hfourthLaunch,
      hfifthLaunch]
    rw [smul_zero]
    repeat' rw [zero_add]
    rw [hpenult, hlast]
    rfl
  let B1 := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 1)
  let dB1 := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bTime 1)
  have hdB1zero : dB1.eval (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    exact intrAtom_bTime_one_base_zero (I := I) g hEnorm p a b 1
  have hcorr1 :
      (DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiCorrectionTerm 1).eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
    have hterm : DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiCorrectionTerm 1 =
        DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1 (s4 T A T B1) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 dA T B1) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 A pathD B1) +
          (2 : ℝ) • DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
            (s3 A T dB1) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1 (s4 A B1 T T) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 B1 dA T) +
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 (s3 B1 T dA) := by
      rfl
    rw [hterm]
    change
      ((((((
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
          (s4 T A T B1)).eval (I := I) g hEnorm p 0 a b (0, 1) +
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (s3 dA T B1)).eval (I := I) g hEnorm p 0 a b (0, 1)) +
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (s3 A pathD B1)).eval (I := I) g hEnorm p 0 a b (0, 1)) +
        (2 : ℝ) • (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (s3 A T dB1)).eval (I := I) g hEnorm p 0 a b (0, 1)) +
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
          (s4 A B1 T T)).eval (I := I) g hEnorm p 0 a b (0, 1)) +
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (s3 B1 dA T)).eval (I := I) g hEnorm p 0 a b (0, 1)) +
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
          (s3 B1 T dA)).eval (I := I) g hEnorm p 0 a b (0, 1)) = 0
    rw [hz 1 (s4 T A T B1) (0 : Fin 4) (by
      change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
        (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hTzero)]
    rw [hz 0 (s3 dA T B1) (1 : Fin 3) (by
      change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
        (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hTzero)]
    rw [hz 0 (s3 A pathD B1) (1 : Fin 3) (by
      change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathDt.eval
        (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hPathDzero)]
    rw [hz 0 (s3 A T dB1) (1 : Fin 3) (by
      change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
        (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hTzero)]
    rw [hz 1 (s4 A B1 T T) (2 : Fin 4) (by
      change DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
        (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hTzero)]
    rw [hz 0 (s3 B1 dA T) (0 : Fin 3) (by
      change B1.eval (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hBzero)]
    rw [hz 0 (s3 B1 T dA) (0 : Fin 3) (by
      change B1.eval (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hBzero)]
    simp
  have heval := DifferentialGeometry.CheegerGromovCompactness.intrinsic_jacobi_residual_term_eval
    (I := I) g hEnorm p 0 a b 2
  have hpoint := congrFun (congrFun heval 0) 1
  rw [hpoint]
  have hterm : DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiResidualTerm 2 =
      (0 + (-1 : ℝ) •
          (DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiCorrectionTerm 0).launchDeriv) +
        (-1 : ℝ) • DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiCorrectionTerm 1 := by
    rfl
  rw [hterm]
  change
    (0 + (-1 : ℝ) •
        (DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiCorrectionTerm 0).launchDeriv.eval
          (I := I) g hEnorm p 0 a b (0, 1)) +
      (-1 : ℝ) •
        (DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiCorrectionTerm 1).eval
          (I := I) g hEnorm p 0 a b (0, 1) = _
  rw [hcorr0Launch, hcorr1, smul_zero, add_zero, zero_add]
  exact neg_one_smul_add_self_eq_neg_two_smul
    ((DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p)
      (show TangentSpace I p from b)
      (show TangentSpace I p from a)
      (show TangentSpace I p from a))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicLaunchJet_two_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (a b : E) :
    intrinsicLaunchJet (I := I) g hEnorm p 0 a b 2 (0, 1) =
      -(1 / 3 : ℝ) •
        (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p)
          (show TangentSpace I p from b)
          (show TangentSpace I p from a)
          (show TangentSpace I p from a) := by
  let X : E :=
    (intrinsicLaunchJet (I := I) g hEnorm p 0 a b 2 (0, 1) : E)
  let R : E := show E from
    (DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p)
      (show TangentSpace I p from b)
      (show TangentSpace I p from a)
      (show TangentSpace I p from a)
  change X = -(1 / 3 : ℝ) • R
  have hsix : (6 : ℝ) • X = (-2 : ℝ) • R :=
    (intrJetResidual_two_zero_eq_six (I := I) g hEnorm p a b).symm.trans
      (intrJetResidual_two_zero_internal (I := I) g hEnorm p a b)
  linear_combination (norm := module) (1 / 6 : ℝ) • hsix

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
