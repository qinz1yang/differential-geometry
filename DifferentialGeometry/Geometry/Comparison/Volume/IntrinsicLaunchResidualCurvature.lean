import DifferentialGeometry.Geometry.Comparison.Volume.IntrinsicJetPoleValues
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Jacobi.CurvatureJet

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

private def residualSlots3
    (x y z : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
    Fin 3 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm :=
  Fin.cons x (Fin.cons y (fun _ ↦ z))

private def residualSlots4
    (w x y z : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
    Fin 4 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm :=
  Fin.cons w (residualSlots3 x y z)

private def residualCorrTerm (n : ℕ) :
    DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm :=
  let T := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT
  let dT := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathDt
  let A := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aJet 0)
  let dA := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0)
  let B := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet n)
  let dB := DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
    (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bTime n)
  DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
      (residualSlots4 T A T B) +
    DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
      (residualSlots3 dA T B) +
    DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
      (residualSlots3 A dT B) +
    (2 : ℝ) • DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
      (residualSlots3 A T dB) +
    DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1
      (residualSlots4 A B T T) +
    DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
      (residualSlots3 B dA T) +
    DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0
      (residualSlots3 B T dA)

open DifferentialGeometry.CheegerGromovCompactness in
private theorem residualLaunch_zero :
    CurvatureJetTerm.zero.launchDeriv = CurvatureJetTerm.zero := rfl

open DifferentialGeometry.CheegerGromovCompactness in
private theorem residualLaunch_add (x y : CurvatureJetTerm) :
    (CurvatureJetTerm.add x y).launchDeriv =
      CurvatureJetTerm.add x.launchDeriv y.launchDeriv := rfl

open DifferentialGeometry.CheegerGromovCompactness in
private theorem residualLaunch_scale (c : ℝ) (x : CurvatureJetTerm) :
    (CurvatureJetTerm.scale c x).launchDeriv =
      CurvatureJetTerm.scale c x.launchDeriv := rfl

open DifferentialGeometry.CheegerGromovCompactness in
private theorem residualLaunch_pathT :
    (CurvatureJetTerm.atom IntrinsicJacobiJetAtom.pathT).launchDeriv =
      CurvatureJetTerm.atom (IntrinsicJacobiJetAtom.aTime 0) := rfl

open DifferentialGeometry.CheegerGromovCompactness in
private theorem residualLaunch_pathDt :
    (CurvatureJetTerm.atom IntrinsicJacobiJetAtom.pathDt).launchDeriv =
      CurvatureJetTerm.zero := rfl

open DifferentialGeometry.CheegerGromovCompactness in
private theorem residualLaunch_aJet (n : ℕ) :
    (CurvatureJetTerm.atom (IntrinsicJacobiJetAtom.aJet n)).launchDeriv =
      CurvatureJetTerm.atom (IntrinsicJacobiJetAtom.aJet (n + 1)) := rfl

open DifferentialGeometry.CheegerGromovCompactness in
private theorem residualLaunch_aTime (n : ℕ) :
    (CurvatureJetTerm.atom (IntrinsicJacobiJetAtom.aTime n)).launchDeriv =
      CurvatureJetTerm.add
        (CurvatureJetTerm.atom (IntrinsicJacobiJetAtom.aTime (n + 1)))
        (CurvatureJetTerm.curv 0
          (residualSlots3
            (CurvatureJetTerm.atom (IntrinsicJacobiJetAtom.aJet 0))
            (CurvatureJetTerm.atom IntrinsicJacobiJetAtom.pathT)
            (CurvatureJetTerm.atom (IntrinsicJacobiJetAtom.aJet n)))) := rfl

open DifferentialGeometry.CheegerGromovCompactness in
private theorem residualLaunch_bJet (n : ℕ) :
    (CurvatureJetTerm.atom (IntrinsicJacobiJetAtom.bJet n)).launchDeriv =
      CurvatureJetTerm.atom (IntrinsicJacobiJetAtom.bJet (n + 1)) := rfl

open DifferentialGeometry.CheegerGromovCompactness in
private theorem residualLaunch_bTime (n : ℕ) :
    (CurvatureJetTerm.atom (IntrinsicJacobiJetAtom.bTime n)).launchDeriv =
      CurvatureJetTerm.add
        (CurvatureJetTerm.atom (IntrinsicJacobiJetAtom.bTime (n + 1)))
        (CurvatureJetTerm.curv 0
          (residualSlots3
            (CurvatureJetTerm.atom (IntrinsicJacobiJetAtom.aJet 0))
            (CurvatureJetTerm.atom IntrinsicJacobiJetAtom.pathT)
            (CurvatureJetTerm.atom (IntrinsicJacobiJetAtom.bJet n)))) := rfl

open DifferentialGeometry.CheegerGromovCompactness in
private theorem residualLaunch_curv (k : ℕ)
    (slots : Fin (k + 3) → CurvatureJetTerm) :
    (CurvatureJetTerm.curv k slots).launchDeriv =
      CurvatureJetTerm.add
        (CurvatureJetTerm.curv (k + 1)
          (Fin.cons (CurvatureJetTerm.atom (IntrinsicJacobiJetAtom.aJet 0)) slots))
        (CurvatureJetTerm.finSum (fun i ↦
          CurvatureJetTerm.curv k
            (Function.update slots i (slots i).launchDeriv))) := rfl

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
private theorem residualFinSum_eval
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u a b : E) {n : ℕ}
    (terms : Fin n → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
    (q : ℝ × ℝ) :
    (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.finSum terms).eval
        (I := I) g hEnorm p u a b q =
      ∑ i, (terms i).eval (I := I) g hEnorm p u a b q := by
  induction n with
  | zero =>
      rw [DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.finSum]
      change (0 : TangentSpace I
        (intrinsicLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))) =
          ∑ i : Fin 0, (terms i).eval (I := I) g hEnorm p u a b q
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
  | succ n ih =>
      rw [DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.finSum]
      change
        (terms 0).eval (I := I) g hEnorm p u a b q +
            (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.finSum
              (fun i ↦ terms i.succ)).eval (I := I) g hEnorm p u a b q =
          ∑ i, (terms i).eval (I := I) g hEnorm p u a b q
      rw [Fin.sum_univ_succ, ih]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrJetResidual_two_zero_eq_curvature
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (a b : E) :
    (intrinsicJetResidual (I := I) g hEnorm p 0 a b 2 (0, 1) : E) =
      (-2 : ℝ) •
        (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p)
          (show TangentSpace I p from b)
          (show TangentSpace I p from a)
          (show TangentSpace I p from a) := by
  let R : E := show E from
    (DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) p)
      (show TangentSpace I p from b)
      (show TangentSpace I p from a)
      (show TangentSpace I p from a)
  change (intrinsicJetResidual (I := I) g hEnorm p 0 a b 2 (0, 1) : E) =
    (-2 : ℝ) • R
  have hres0 := congrFun
    (congrFun
      (DifferentialGeometry.CheegerGromovCompactness.intrinsic_jacobi_residual_term_eval
        (I := I) g hEnorm p (0 : E) a b 2)
      (0 : ℝ))
    (1 : ℝ)
  have hcorr (n : ℕ) :
      DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiCorrectionTerm n =
        residualCorrTerm n := by
    rfl
  have hterm :
      DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiResidualTerm 2 =
        ((DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiResidualTerm 0).launchDeriv +
          (-1 : ℝ) • DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiCorrectionTerm 0).launchDeriv +
        (-1 : ℝ) • DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiCorrectionTerm 1 := by
    rfl
  let term2 : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm :=
    DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.add
      (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.scale (-1)
        (residualCorrTerm 0).launchDeriv)
      (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.scale (-1)
        (residualCorrTerm 1))
  have htermEval :
      DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.eval
          (I := I) g hEnorm p (0 : E) a b
          (DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiResidualTerm 2) (0, 1) =
        DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.eval
          (I := I) g hEnorm p (0 : E) a b term2 (0, 1) := by
    rw [hterm, hcorr 0, hcorr 1]
    dsimp only [term2,
      DifferentialGeometry.CheegerGromovCompactness.instZeroCurvatureJetTerm,
      DifferentialGeometry.CheegerGromovCompactness.instAddCurvatureJetTerm,
      DifferentialGeometry.CheegerGromovCompactness.instSMulRealCurvatureJetTerm,
      DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.launchDeriv,
      DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.eval]
    rw [show
      (DifferentialGeometry.CheegerGromovCompactness.intrinsicJacobiResidualTerm 0).launchDeriv.launchDeriv =
        DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.zero by rfl]
    rw [show
      ((-1 : ℝ) • residualCorrTerm 0).launchDeriv =
        DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.scale (-1)
          (residualCorrTerm 0).launchDeriv by rfl]
    rw [show
      (-1 : ℝ) • residualCorrTerm 1 =
        DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.scale (-1)
          (residualCorrTerm 1) by rfl]
    simp only [DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.eval,
      zero_add]
  have hpoint :
      intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1) = p := by
    dsimp only [intrinsicLaunch3]
    simp only [zero_smul, add_zero]
    change expMapIntrinsic (I := I) g hEnorm p (0 : TangentSpace I p) = p
    exact expMapIntrinsic_zero (I := I) g hEnorm p
  have hT :
      (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT.eval
        (I := I) g hEnorm p 0 a b (0, 1) : E) = 0 :=
    intrAtom_pathT_base_zero (I := I) g hEnorm p a b 1
  have hdT :
      (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathDt.eval
        (I := I) g hEnorm p 0 a b (0, 1) : E) = 0 := by
    exact congrArg (fun z ↦ (z : E))
      (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.path_dt_zero
        (I := I) g hEnorm p 0 a b 0 1)
  have hB :
      id (α := E)
        ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 0).eval
          (I := I) g hEnorm p 0 a b (0, 1)) = b := by
    change id (α := E) (intrinsicLaunchJ (I := I) g hEnorm p 0 a b (0, 1)) = b
    exact intrinsicLaunchJ_zero_base_one (I := I) g hEnorm p a b
  have hA :
      id (α := E)
        ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aJet 0).eval
          (I := I) g hEnorm p 0 a b (0, 1)) = a := by
    have heq := congrArg (fun z ↦ id (α := E) z)
      (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.a_jet_eq_self
        (I := I) g hEnorm p 0 a b 0 0 1)
    exact heq.trans (by
      change id (α := E) (intrinsicLaunchJ (I := I) g hEnorm p 0 a a (0, 1)) = a
      exact intrinsicLaunchJ_zero_base_one (I := I) g hEnorm p a a)
  have hTime (a' b' : E) :
      ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bTime 0).eval
        (I := I) g hEnorm p 0 a' b' (0, 1) : E) = b' := by
    let f : ℝ → ℝ → M := fun r t ↦
      intrinsicLaunch3 (I := I) g hEnorm p 0 a' b' ((r, 0), t)
    let V : ∀ r t : ℝ, TangentSpace I (f r t) := fun r t ↦
      intrinsicLaunchJ (I := I) g hEnorm p 0 a' b' (r, t)
    have hcurve : (fun t : ℝ ↦ f 0 t) = fun _ : ℝ ↦ p := by
      funext t
      have hs := intrinsicGeodesic_smul (I := I) g hEnorm p
        (0 : TangentSpace I p) t
      rw [smul_zero] at hs
      have hzero : intrinsicGeodesic (I := I) g hEnorm p
          (0 : TangentSpace I p) 1 = p := by
        change expMapIntrinsic (I := I) g hEnorm p (0 : TangentSpace I p) = p
        exact expMapIntrinsic_zero (I := I) g hEnorm p
      dsimp only [f, intrinsicLaunch3]
      simp only [zero_smul, add_zero]
      exact hs.symm.trans hzero
    have hfield : ∀ t : ℝ, (V 0 t : E) = t • b' := by
      intro t
      exact intrinsicLaunchJ_base_zero (I := I) g hEnorm p a' b' t
    have hcongr := covDerivAlong_congr_curve (I := I) g (t := (1 : ℝ))
      (fun t : ℝ ↦ V 0 t)
      (fun t : ℝ ↦ (show TangentSpace I p from t • b'))
      (Filter.Eventually.of_forall (fun t ↦ congrFun hcurve t))
      (Filter.Eventually.of_forall hfield)
    have hcongrE := congrArg (fun z ↦ (z : E)) hcongr
    change (Variation.covSnd (I := I) g f V 0 1 : E) = b'
    exact hcongrE.trans
      (covDerivAlong_const_linear (I := I) g p
        (show TangentSpace I p from b') 1)
  have hdB :
      ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bTime 0).eval
        (I := I) g hEnorm p 0 a b (0, 1) : E) = b := hTime a b
  have hdA :
      ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0).eval
        (I := I) g hEnorm p 0 a b (0, 1) : E) = a := by
    have heq := congrArg (fun z ↦ (z : E))
      (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.a_time_eq_self
        (I := I) g hEnorm p 0 a b 0 0 1)
    exact heq.trans (hTime a a)
  have hA1 :
      ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aJet 1).eval
        (I := I) g hEnorm p 0 a b (0, 1) : E) = 0 :=
    intrJetAtom_aJet_one_pole (I := I) g hEnorm p a b
  have hB1 :
      ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 1).eval
        (I := I) g hEnorm p 0 a b (0, 1) : E) = 0 :=
    intrJetAtom_bJet_one_pole (I := I) g hEnorm p a b
  have hdA1 :
      ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 1).eval
        (I := I) g hEnorm p 0 a b (0, 1) : E) = 0 :=
    intrJetAtom_aTime_one_pole (I := I) g hEnorm p a b
  have hdB1 :
      ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bTime 1).eval
        (I := I) g hEnorm p 0 a b (0, 1) : E) = 0 :=
    intrJetAtom_bTime_one_pole (I := I) g hEnorm p a b
  have hcalc :
      DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.eval
          (I := I) g hEnorm p (0 : E) a b term2 (0, 1) =
        (tangentSpaceModelContinuousLinearEquiv (I := I)
          (intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1))).symm
          ((-2 : ℝ) • R) := by
    dsimp only [term2,
      DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.launchDeriv,
      residualCorrTerm, residualSlots3, residualSlots4]
    have hevalAdd
        (x y : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.add x y).eval
            (I := I) g hEnorm p 0 a b (0, 1) =
          x.eval (I := I) g hEnorm p 0 a b (0, 1) +
            y.eval (I := I) g hEnorm p 0 a b (0, 1) := rfl
    have hevalScale (c : ℝ)
        (x : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.scale c x).eval
            (I := I) g hEnorm p 0 a b (0, 1) =
          c • x.eval (I := I) g hEnorm p 0 a b (0, 1) := rfl
    have hevalAtom (atom : DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom atom).eval
            (I := I) g hEnorm p 0 a b (0, 1) =
          atom.eval (I := I) g hEnorm p 0 a b (0, 1) := rfl
    have hevalAdd' (x y : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
        (x + y).eval (I := I) g hEnorm p 0 a b (0, 1) =
          x.eval (I := I) g hEnorm p 0 a b (0, 1) +
            y.eval (I := I) g hEnorm p 0 a b (0, 1) := rfl
    have hevalScale' (c : ℝ)
        (x : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
        (c • x).eval (I := I) g hEnorm p 0 a b (0, 1) =
          c • x.eval (I := I) g hEnorm p 0 a b (0, 1) := rfl
    have hlaunchScale' (c : ℝ)
        (z : DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm) :
        (c • z).launchDeriv =
          DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.scale c
            z.launchDeriv := rfl
    have hz00
        (slots : Fin 3 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
        (hi : (slots 0).eval (I := I) g hEnorm p 0 a b (0, 1) = 0) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 slots).eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      exact DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero_at
        (I := I) g 0 _ _ 0 hi
    have hz01
        (slots : Fin 3 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
        (hi : (slots 1).eval (I := I) g hEnorm p 0 a b (0, 1) = 0) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 slots).eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      exact DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero_at
        (I := I) g 0 _ _ 1 hi
    have hz02
        (slots : Fin 3 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
        (hi : (slots 2).eval (I := I) g hEnorm p 0 a b (0, 1) = 0) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 slots).eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      exact DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero_at
        (I := I) g 0 _ _ 2 hi
    have hz10
        (slots : Fin 4 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
        (hi : (slots 0).eval (I := I) g hEnorm p 0 a b (0, 1) = 0) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1 slots).eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      exact DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero_at
        (I := I) g 1 _ _ 0 hi
    have hz11
        (slots : Fin 4 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
        (hi : (slots 1).eval (I := I) g hEnorm p 0 a b (0, 1) = 0) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1 slots).eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      exact DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero_at
        (I := I) g 1 _ _ 1 hi
    have hz12
        (slots : Fin 4 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
        (hi : (slots 2).eval (I := I) g hEnorm p 0 a b (0, 1) = 0) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1 slots).eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      exact DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero_at
        (I := I) g 1 _ _ 2 hi
    have hz13
        (slots : Fin 4 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
        (hi : (slots 3).eval (I := I) g hEnorm p 0 a b (0, 1) = 0) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 1 slots).eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      exact DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero_at
        (I := I) g 1 _ _ 3 hi
    have hz20
        (slots : Fin 5 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
        (hi : (slots 0).eval (I := I) g hEnorm p 0 a b (0, 1) = 0) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 2 slots).eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      exact DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero_at
        (I := I) g 2 _ _ 0 hi
    have hz21
        (slots : Fin 5 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
        (hi : (slots 1).eval (I := I) g hEnorm p 0 a b (0, 1) = 0) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 2 slots).eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      exact DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero_at
        (I := I) g 2 _ _ 1 hi
    have hz22
        (slots : Fin 5 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
        (hi : (slots 2).eval (I := I) g hEnorm p 0 a b (0, 1) = 0) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 2 slots).eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      exact DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero_at
        (I := I) g 2 _ _ 2 hi
    have hz23
        (slots : Fin 5 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
        (hi : (slots 3).eval (I := I) g hEnorm p 0 a b (0, 1) = 0) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 2 slots).eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      exact DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero_at
        (I := I) g 2 _ _ 3 hi
    have hz24
        (slots : Fin 5 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
        (hi : (slots 4).eval (I := I) g hEnorm p 0 a b (0, 1) = 0) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 2 slots).eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      exact DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero_at
        (I := I) g 2 _ _ 4 hi
    have hdiag
        (slots : Fin 3 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
        (h01 : (slots 0).eval (I := I) g hEnorm p 0 a b (0, 1) =
          (slots 1).eval (I := I) g hEnorm p 0 a b (0, 1)) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 slots).eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      let x := intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1)
      let X : TangentSpace I x :=
        (slots 0).eval (I := I) g hEnorm p 0 a b (0, 1)
      let Z : TangentSpace I x :=
        (slots 2).eval (I := I) g hEnorm p 0 a b (0, 1)
      change DifferentialGeometry.CheegerGromovCompactness.curvOpN
        (I := I) g 0 x
          (fun i ↦ (slots i).eval (I := I) g hEnorm p 0 a b (0, 1)) = 0
      rw [show (fun i ↦ (slots i).eval
            (I := I) g hEnorm p 0 a b (0, 1)) =
          DifferentialGeometry.Geometry.Curvature.vec3 (I := I) X X Z by
        funext i
        fin_cases i
        · rfl
        · exact h01.symm
        · rfl]
      rw [DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero]
      have hswap := DifferentialGeometry.Geometry.Curvature.riemannOp_swap
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
        x X X Z
      linear_combination (norm := module) (1 / 2 : ℝ) • hswap
    let x := intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1)
    let e := tangentSpaceModelContinuousLinearEquiv (I := I) x
    have hBe :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
          (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 0)).eval
            (I := I) g hEnorm p 0 a b (0, 1) = e.symm b := by
      rw [hevalAtom]
      dsimp only [e]
      change id (α := E)
          ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 0).eval
            (I := I) g hEnorm p 0 a b (0, 1)) = b
      exact hB
    have hAe :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
          (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aJet 0)).eval
            (I := I) g hEnorm p 0 a b (0, 1) = e.symm a := by
      rw [hevalAtom]
      dsimp only [e]
      change id (α := E)
          ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aJet 0).eval
            (I := I) g hEnorm p 0 a b (0, 1)) = a
      exact hA
    have hdAe :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
          (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0)).eval
            (I := I) g hEnorm p 0 a b (0, 1) = e.symm a := by
      rw [hevalAtom]
      dsimp only [e]
      change id (α := E)
          ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0).eval
            (I := I) g hEnorm p 0 a b (0, 1)) = a
      exact hdA
    have hcurvBAA
        (slots : Fin 3 → DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm)
        (h0 : (slots 0).eval (I := I) g hEnorm p 0 a b (0, 1) = e.symm b)
        (h1 : (slots 1).eval (I := I) g hEnorm p 0 a b (0, 1) = e.symm a)
        (h2 : (slots 2).eval (I := I) g hEnorm p 0 a b (0, 1) = e.symm a) :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.curv 0 slots).eval
            (I := I) g hEnorm p 0 a b (0, 1) = e.symm R := by
      change DifferentialGeometry.CheegerGromovCompactness.curvOpN
        (I := I) g 0 x
          (fun i ↦ (slots i).eval (I := I) g hEnorm p 0 a b (0, 1)) =
        e.symm R
      rw [show (fun i ↦ (slots i).eval
            (I := I) g hEnorm p 0 a b (0, 1)) =
          DifferentialGeometry.Geometry.Curvature.vec3 (I := I)
            (e.symm b) (e.symm a) (e.symm a) by
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2]
      rw [DifferentialGeometry.CheegerGromovCompactness.curvOpN_zero]
      dsimp only [x, e]
      rw [hpoint]
      rfl
    have hbJetLaunchZero :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
          (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 0)).launchDeriv.eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      rw [residualLaunch_bJet, show 0 + 1 = 1 by rfl, hevalAtom]
      exact hB1
    have haTimeLaunchZero :
        (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
          (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0)).launchDeriv.eval
            (I := I) g hEnorm p 0 a b (0, 1) = 0 := by
      rw [residualLaunch_aTime, hevalAdd, show 0 + 1 = 1 by rfl]
      conv_lhs =>
        lhs
        rw [hevalAtom]
      rw [hdA1, hz01 _ (by exact hT), zero_add]
    repeat' first
      | rw [hevalAdd]
      | rw [hevalScale]
      | rw [hevalAdd']
      | rw [hevalScale']
      | rw [residualFinSum_eval]
    repeat' first
      | rw [Fin.sum_univ_succ]
      | rw [Finset.univ_eq_empty]
      | rw [Finset.sum_empty]
    simp only [Fin.cons_zero, Fin.cons_succ, residualLaunch_pathT,
      residualLaunch_pathDt, residualLaunch_aJet, residualLaunch_aTime,
      residualLaunch_bJet]
    rw [hz21 _ (by exact hT)]
    rw [hz23 _ (by exact hT)]
    rw [hz12 _ (by
      rw [Function.update_of_ne (by decide)]
      rw [show (2 : Fin 4) = (1 : Fin 3).succ by rfl, Fin.cons_succ]
      rw [show (1 : Fin 3) = (0 : Fin 2).succ by rfl, Fin.cons_succ,
        Fin.cons_zero]
      exact hT)]
    rw [hz10 _ (by
      simpa [Function.update, Fin.cons,
        DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.eval] using hT)]
    rw [hz10 _ (by
      simpa [Function.update, Fin.cons,
        DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.eval] using hT)]
    rw [hz10 _ (by
      simpa [Function.update, Fin.cons,
        DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.eval] using hT)]
    rw [hz12 _ (by exact hT)]
    rw [hz12 _ (by exact hdT)]
    rw [hz12 _ (by exact hT)]
    rw [hz12 _ (by
      rw [Function.update_of_ne (by decide)]
      rw [show (2 : Fin 4) = (1 : Fin 3).succ by rfl, Fin.cons_succ]
      rw [show (1 : Fin 3) = (0 : Fin 2).succ by rfl, Fin.cons_succ,
        Fin.cons_zero]
      exact hT)]
    rw [hz13 _ (by
      rw [Function.update_of_ne (by decide)]
      rw [show (3 : Fin 4) = (2 : Fin 3).succ by rfl, Fin.cons_succ]
      rw [show (2 : Fin 3) = (1 : Fin 2).succ by rfl, Fin.cons_succ]
      change (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
        DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.pathT).eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hT)]
    rw [hz12 _ (by
      rw [Function.update_of_ne (by decide)]
      rw [show (2 : Fin 4) = (1 : Fin 3).succ by rfl, Fin.cons_succ]
      rw [show (1 : Fin 3) = (0 : Fin 2).succ by rfl, Fin.cons_succ,
        Fin.cons_zero]
      exact hT)]
    rw [hz13 _ (by exact hT)]
    rw [hz12 _ (by exact hT)]
    rw [hz01 _ (by
      rw [Function.update_of_ne (by decide)]
      rw [show (1 : Fin 3) = (0 : Fin 2).succ by rfl, Fin.cons_succ,
        Fin.cons_zero]
      exact hT)]
    rw [hdiag _ (by
      simp [Function.update, Fin.cons])]
    rw [hz01 _ (by
      rw [Function.update_of_ne (by decide)]
      rw [show (1 : Fin 3) = (0 : Fin 2).succ by rfl, Fin.cons_succ,
        Fin.cons_zero]
      exact hT)]
    rw [hz01 _ (by
      rw [Function.update_of_ne (by decide)]
      rw [show (1 : Fin 3) = (0 : Fin 2).succ by rfl, Fin.cons_succ,
        Fin.cons_zero]
      exact hdT)]
    rw [hz01 _ (by
      simp [Function.update,
        DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.eval])]
    rw [hz01 _ (by
      rw [Function.update_of_ne (by decide)]
      rw [show (1 : Fin 3) = (0 : Fin 2).succ by rfl, Fin.cons_succ,
        Fin.cons_zero]
      exact hdT)]
    rw [hlaunchScale', hevalScale, residualLaunch_curv, hevalAdd]
    rw [hz12 _ (by exact hT)]
    rw [residualFinSum_eval]
    repeat' first
      | rw [Fin.sum_univ_succ]
      | rw [Finset.univ_eq_empty]
      | rw [Finset.sum_empty]
    rw [hz00 _ (by
      rw [Function.update_apply]
      exact hA1)]
    rw [hdiag _ (by
      rw [show (1 : Fin 3) = (0 : Fin 2).succ by rfl]
      rw [Function.update_self, Function.update_of_ne (by decide),
        Fin.cons_zero, Fin.cons_succ, Fin.cons_zero, residualLaunch_pathT]
      change id (α := E)
          ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aJet 0).eval
            (I := I) g hEnorm p 0 a b (0, 1)) =
        id (α := E)
          ((DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0).eval
            (I := I) g hEnorm p 0 a b (0, 1))
      exact hA.trans hdA.symm)]
    rw [hz02 _ (by
      rw [Function.update_apply]
      rw [ite_eq_left (show (2 : Fin 3) = (Fin.succ 0).succ by rfl)]
      change ((DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
        (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bTime 0)).launchDeriv).eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
      rw [residualLaunch_bTime]
      rw [hevalAdd]
      rw [show 0 + 1 = 1 by rfl]
      conv_lhs =>
        lhs
        rw [hevalAtom]
      rw [hdB1]
      rw [hz01 _ (by exact hT)]
      simp only [zero_add])]
    rw [hz00 _ (by
      rw [Function.update_self]
      change (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
        (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 0)).launchDeriv.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hbJetLaunchZero)]
    rw [hz01 _ (by
      rw [show (1 : Fin 3) = (0 : Fin 2).succ by rfl]
      rw [Function.update_self]
      change (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
        (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0)).launchDeriv.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact haTimeLaunchZero)]
    rw [hcurvBAA _
      (by simpa [Function.update_apply, Fin.cons] using hBe)
      (by
        rw [Function.update_of_ne (by decide)]
        rw [show (1 : Fin 3) = (0 : Fin 2).succ by rfl,
          Fin.cons_succ, Fin.cons_zero]
        exact hdAe)
      (by simpa [Function.update_apply, Fin.cons, residualLaunch_pathT] using hdAe)]
    rw [hz00 _ (by
      rw [Function.update_self]
      change (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
        (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.bJet 0)).launchDeriv.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact hbJetLaunchZero)]
    rw [hcurvBAA _
      (by simpa [Function.update_apply, Fin.cons] using hBe)
      (by simpa [Function.update_apply, Fin.cons, residualLaunch_pathT] using hdAe)
      (by
        rw [Function.update_of_ne (by decide)]
        rw [show (2 : Fin 3) = (1 : Fin 2).succ by rfl,
          Fin.cons_succ]
        rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl,
          Fin.cons_succ]
        exact hdAe)]
    rw [hz02 _ (by
      rw [show (2 : Fin 3) = (Fin.succ 0).succ by rfl]
      rw [Function.update_self]
      change (DifferentialGeometry.CheegerGromovCompactness.CurvatureJetTerm.atom
        (DifferentialGeometry.CheegerGromovCompactness.IntrinsicJacobiJetAtom.aTime 0)).launchDeriv.eval
          (I := I) g hEnorm p 0 a b (0, 1) = 0
      exact haTimeLaunchZero)]
    rw [hz10 _ (by exact hT)]
    rw [hz01 _ (by exact hT)]
    rw [hz01 _ (by exact hdT)]
    rw [hz01 _ (by exact hT)]
    rw [hz12 _ (by exact hT)]
    rw [hz02 _ (by exact hT)]
    rw [hz01 _ (by exact hT)]
    change _ = e.symm ((-2 : ℝ) • R)
    rw [map_smul]
    module
  have hfinal0 := hres0.trans (htermEval.trans hcalc)
  exact hfinal0.trans
    (tangentSpaceModelContinuousLinearEquiv_symm_apply (I := I)
      (intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((0, 0), 1)) ((-2 : ℝ) • R))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
