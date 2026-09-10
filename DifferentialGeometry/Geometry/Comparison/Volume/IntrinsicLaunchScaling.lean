import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.JacobiJets

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

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
theorem intrinsicLaunchJ_scale
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (u a b : E) (r t : ℝ) :
    (intrinsicLaunchJ (I := I) g hEnorm p u a b (r, t) : E) =
      t • (intrinsicLaunchJ (I := I) g hEnorm p
        (t • u) (t • a) b (r, 1) : E) := by
  have hJL :
      (intrinsicLaunchJ (I := I) g hEnorm p u a b (r, t) : E) =
        (intrinsicJacobi (I := I) g hEnorm p
          (show TangentSpace I p from u + r • a) b t : E) :=
    congrArg (fun z ↦ (z : E))
      (intrinsicLaunchJ_at (I := I) g hEnorm p u a b r t)
  have hJR :
      (intrinsicLaunchJ (I := I) g hEnorm p
        (t • u) (t • a) b (r, 1) : E) =
        (intrinsicJacobi (I := I) g hEnorm p
          (show TangentSpace I p from t • u + r • (t • a)) b 1 : E) :=
    congrArg (fun z ↦ (z : E))
      (intrinsicLaunchJ_at (I := I) g hEnorm p (t • u) (t • a) b r 1)
  have hleft := intrinsic_jacobi_at (I := I) g hEnorm p
    (u + r • a) b t
  have hright := intrinsic_jacobi_one (I := I) g hEnorm p
    (t • u + r • (t • a)) b
  have hleftE :
      (intrinsicJacobi (I := I) g hEnorm p
          (show TangentSpace I p from u + r • a) b t : E) =
        (mfderiv (modelWithCornersSelf ℝ E) I
          (fun z : E ↦ expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from z))
          (t • (u + r • a)) (t • b) : E) :=
    congrArg (fun z ↦ (z : E)) hleft
  have hrightE :
      (intrinsicJacobi (I := I) g hEnorm p
          (show TangentSpace I p from t • u + r • (t • a)) b 1 : E) =
        (mfderiv (modelWithCornersSelf ℝ E) I
          (fun z : E ↦ expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from z))
          (t • u + r • (t • a)) b : E) :=
    congrArg (fun z ↦ (z : E)) hright
  have hbase : t • (u + r • a) = t • u + r • (t • a) := by
    module
  let D := mfderiv (modelWithCornersSelf ℝ E) I
    (fun z : E ↦ expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from z)) (t • u + r • (t • a))
  have hDbase :
      (mfderiv (modelWithCornersSelf ℝ E) I
          (fun z : E ↦ expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from z))
          (t • (u + r • a)) (t • b) : E) = D (t • b) := by
    rw [hbase]
  have hDlin : D (t • b) = t • D b := D.map_smul t b
  have hR : D b =
      (intrinsicJacobi (I := I) g hEnorm p
        (show TangentSpace I p from t • u + r • (t • a)) b 1 : E) := by
    exact (show D b = D b from rfl).trans hrightE.symm
  have hRsmul := congrArg (fun z : E ↦ t • z) hR
  have hJRsmul := congrArg (fun z : E ↦ t • z) hJR.symm
  exact hJL.trans (hleftE.trans
    (hDbase.trans (hDlin.trans (hRsmul.trans hJRsmul))))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicLaunchJ_zero_scale
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) (r t : ℝ) :
    (intrinsicLaunchJ (I := I) g hEnorm p 0 a b (r, t) : E) =
      t • (intrinsicLaunchJ (I := I) g hEnorm p 0 a b (t * r, 1) : E) := by
  have hscale := intrinsicLaunchJ_scale (I := I) g hEnorm p 0 a b r t
  have hleft := congrArg (fun z ↦ (z : E))
    (intrinsicLaunchJ_at (I := I) g hEnorm p (t • (0 : E)) (t • a) b r 1)
  have hright := congrArg (fun z ↦ (z : E))
    (intrinsicLaunchJ_at (I := I) g hEnorm p 0 a b (t * r) 1)
  have hbase : t • (0 : E) + r • (t • a) = (0 : E) + (t * r) • a := by
    module
  have hJac :
      (intrinsicJacobi (I := I) g hEnorm p
          (show TangentSpace I p from t • (0 : E) + r • (t • a)) b 1 : E) =
        (intrinsicJacobi (I := I) g hEnorm p
          (show TangentSpace I p from (0 : E) + (t * r) • a) b 1 : E) :=
    congrArg
      (fun x : E ↦ (intrinsicJacobi (I := I) g hEnorm p
        (show TangentSpace I p from x) b 1 : E)) hbase
  have hlaunch :
      (intrinsicLaunchJ (I := I) g hEnorm p
          (t • (0 : E)) (t • a) b (r, 1) : E) =
        (intrinsicLaunchJ (I := I) g hEnorm p 0 a b (t * r, 1) : E) :=
    hleft.trans (hJac.trans hright.symm)
  exact hscale.trans (congrArg (fun z : E ↦ t • z) hlaunch)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicLaunchJ_zero_base_one
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) :
    id (α := E) (intrinsicLaunchJ (I := I) g hEnorm p 0 a b (0, 1)) = b := by
  have hJ := congrArg (fun z ↦ id (α := E) z)
    (intrinsicLaunchJ_zero (I := I) g hEnorm p 0 a b 1)
  have hOne := congrArg (fun z ↦ id (α := E) z)
    (intrinsic_jacobi_one (I := I) g hEnorm p
      (show TangentSpace I p from (0 : E))
      (show TangentSpace I p from b))
  have hD := mfderiv_expMapIntrinsic_at_zero (I := I) g hEnorm p
  have happ := congrArg
    (fun D ↦ id (α := E)
      (D (show TangentSpace (modelWithCornersSelf ℝ E) (0 : E)
        from b))) hD
  calc
    id (α := E) (intrinsicLaunchJ (I := I) g hEnorm p 0 a b (0, 1)) =
        id (α := E) (intrinsicJacobi (I := I) g hEnorm p
          (show TangentSpace I p from (0 : E))
          (show TangentSpace I p from b) 1) := hJ
    _ = id (α := E)
        ((mfderiv (modelWithCornersSelf ℝ E) I
          (fun z : E ↦ expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from z)) (0 : E))
          (show TangentSpace (modelWithCornersSelf ℝ E) (0 : E)
            from b)) := hOne
    _ = b := happ.trans (by rfl)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicLaunchJet_zero_scale
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    (a b : E) (n : ℕ) (r t : ℝ) :
    (intrinsicLaunchJet (I := I) g hEnorm p 0 a b n (r, t) : E) =
      t ^ (n + 1) •
        (intrinsicLaunchJet (I := I) g hEnorm p 0 a b n (t * r, 1) : E) := by
  induction n generalizing r with
  | zero =>
      simpa only [intrinsicLaunchJet_zero, Nat.zero_add, pow_one] using
        intrinsicLaunchJ_zero_scale (I := I) g hEnorm p a b r t
  | succ n ih =>
      let f : ℝ → ℝ → M := fun s v ↦
        intrinsicLaunch3 (I := I) g hEnorm p 0 a b ((s, 0), v)
      let W : ∀ s v : ℝ, TangentSpace I (f s v) := fun s v ↦
        intrinsicLaunchJet (I := I) g hEnorm p 0 a b n (s, v)
      let γ : ℝ → M := fun s ↦ f s t
      let γ1 : ℝ → M := fun s ↦ f s 1
      let Wt : ∀ s : ℝ, TangentSpace I (γ s) := fun s ↦ W s t
      let W1 : ∀ s : ℝ, TangentSpace I (γ1 s) := fun s ↦ W s 1
      have hcurveEq : γ = fun s : ℝ ↦ γ1 (t * s) := by
        funext s
        dsimp only [γ, γ1, f, intrinsicLaunch3]
        have hgeo := intrinsicGeodesic_smul (I := I) g hEnorm p
          (show TangentSpace I p from s • a) t
        have hvec :
            t • (show TangentSpace I p from s • a) =
              (show TangentSpace I p from (t * s) • a) := by
          apply (tangentSpaceModelContinuousLinearEquiv (I := I) p).injective
          change t • (s • a) = (t * s) • a
          rw [smul_smul]
        have hzeroL :
            (show TangentSpace I p from (0 : E) + s • a + (0 : ℝ) • b) =
              (show TangentSpace I p from s • a) := by
          apply (tangentSpaceModelContinuousLinearEquiv (I := I) p).injective
          change (0 : E) + s • a + (0 : ℝ) • b = s • a
          module
        have hzeroR :
            (show TangentSpace I p from (0 : E) + (t * s) • a + (0 : ℝ) • b) =
              (show TangentSpace I p from (t * s) • a) := by
          apply (tangentSpaceModelContinuousLinearEquiv (I := I) p).injective
          change (0 : E) + (t * s) • a + (0 : ℝ) • b = (t * s) • a
          module
        convert hgeo.symm.trans (congrArg
          (fun v : TangentSpace I p ↦ intrinsicGeodesic (I := I) g hEnorm p v 1) hvec) using 1
        · exact congrArg
            (fun v : TangentSpace I p ↦ intrinsicGeodesic (I := I) g hEnorm p v t) hzeroL
        · exact congrArg
            (fun v : TangentSpace I p ↦ intrinsicGeodesic (I := I) g hEnorm p v 1) hzeroR
      have hfield : ∀ s : ℝ,
          (Wt s : E) = t ^ (n + 1) • (W1 (t * s) : E) := by
        intro s
        exact ih s
      have hcongr := covDerivAlong_congr_curve (I := I) g (t := r)
        Wt (fun s : ℝ ↦ t ^ (n + 1) • W1 (t * s))
        (Filter.Eventually.of_forall (fun s ↦ congrFun hcurveEq s))
        (Filter.Eventually.of_forall hfield)
      have hsmul := covDerivAlong_smul (I := I) g
        (fun s : ℝ ↦ γ1 (t * s)) (t ^ (n + 1))
        (fun s : ℝ ↦ W1 (t * s)) r
      have hcomp := covDeriv_comp_mul (I := I) g γ1 W1 t r
      have hcongrE := congrArg (fun z ↦ (z : E)) hcongr
      have hsmulE := congrArg (fun z ↦ (z : E)) hsmul
      have hcompE := congrArg (fun z ↦ (z : E)) hcomp
      rw [intrinsicLaunchJet_succ]
      change (covDerivAlong (I := I) g γ Wt r : E) = _
      rw [hcongrE, hsmulE, hcompE]
      change t ^ (n + 1) • (t • (covDerivAlong (I := I) g γ1 W1 (t * r) : E)) = _
      rw [smul_smul]
      congr 1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem covDerivAlong_const_linear
    (g : SmoothRiemannianMetric I M) (p : M) (X : TangentSpace I p) (t : ℝ) :
    (covDerivAlong (I := I) g (fun _ : ℝ ↦ p)
        (fun s : ℝ ↦ (show TangentSpace I p from s • (X : E))) t : E) =
      (X : E) := by
  have hdiff : DifferentiableAt ℝ (fun s : ℝ ↦ s • (X : E)) t := by
    fun_prop
  rw [covDerivAlong_const (I := I) g p
    (fun s : ℝ ↦ (show TangentSpace I p from s • (X : E))) t hdiff]
  simpa using ((hasDerivAt_id t).smul_const (X : E)).deriv

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem covDerivAlong_const_cubic
    (g : SmoothRiemannianMetric I M) (p : M) (X : TangentSpace I p) (t : ℝ) :
    (covDerivAlong (I := I) g (fun _ : ℝ ↦ p)
        (fun s : ℝ ↦ (show TangentSpace I p from s ^ 3 • (X : E))) t : E) =
      (3 * t ^ 2) • (X : E) := by
  have hdiff : DifferentiableAt ℝ (fun s : ℝ ↦ s ^ 3 • (X : E)) t := by
    fun_prop
  rw [covDerivAlong_const (I := I) g p
    (fun s : ℝ ↦ (show TangentSpace I p from s ^ 3 • (X : E))) t hdiff]
  have hpow := (hasDerivAt_id t).pow 3
  have hsmul := hpow.smul_const (X : E)
  convert hsmul.deriv using 1 <;> norm_num

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem covDerivAlong_const_cubic_first
    (g : SmoothRiemannianMetric I M) (p : M) (X : TangentSpace I p) (t : ℝ) :
    (covDerivAlong (I := I) g (fun _ : ℝ ↦ p)
        (fun s : ℝ ↦
          (show TangentSpace I p from (3 * s ^ 2) • (X : E))) t : E) =
      (6 * t) • (X : E) := by
  have hdiff : DifferentiableAt ℝ (fun s : ℝ ↦ (3 * s ^ 2) • (X : E)) t := by
    fun_prop
  rw [covDerivAlong_const (I := I) g p
    (fun s : ℝ ↦
      (show TangentSpace I p from (3 * s ^ 2) • (X : E))) t hdiff]
  have hscalar : HasDerivAt (fun s : ℝ ↦ 3 * s ^ 2) (6 * t) t := by
    have hraw := ((hasDerivAt_id t).pow 2).const_mul 3
    have hraw' : HasDerivAt (fun s : ℝ ↦ (3 : ℝ) * s ^ 2)
        ((3 : ℝ) * (2 * t)) t := by
      simpa only [Pi.mul_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
        Nat.reduceSub, pow_one, mul_one] using hraw
    have hcoef : (3 : ℝ) * (2 * t) = 6 * t := by ring
    rw [← hcoef]
    exact hraw'
  exact (hscalar.smul_const (X : E)).deriv

end Poincare.Geometry.Riemannian.VolumeComparison
