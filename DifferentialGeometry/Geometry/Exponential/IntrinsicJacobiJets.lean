import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation
import DifferentialGeometry.Geometry.Comparison.Variation.CovariantJet
import DifferentialGeometry.Geometry.Comparison.Variation.GeneralCurvatureCommutation
import DifferentialGeometry.Geometry.Exponential.EndpointShape
import DifferentialGeometry.Geometry.Exponential.IntrinsicVelocity

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
noncomputable def intrLaunch3
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (q : (Real × Real) × Real) : M :=
  intrinsicGeodesic (I := I) g hEnorm p
    (show TangentSpace I p from u + q.1.1 • a + q.1.2 • b) q.2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunch3_smooth
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) :
    ContMDiff
      (((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real)).prod
          (modelWithCornersSelf Real Real))
      I ∞
      (intrLaunch3 (I := I) g hEnorm p u a b) := by
  let launch : (Real × Real) × Real → E := fun q =>
    q.2 • (u + q.1.1 • a + q.1.2 • b)
  have hbase : ContMDiff
      (((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real)).prod
          (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real E) ∞
      (fun q : (Real × Real) × Real =>
        u + q.1.1 • a + q.1.2 • b) :=
    (contMDiff_const.add (contMDiff_fst.fst.smul contMDiff_const)).add
      (contMDiff_fst.snd.smul contMDiff_const)
  have hlaunch : ContMDiff
      (((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real)).prod
          (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real E) ∞ launch :=
    contMDiff_snd.smul hbase
  have hcomp :=
    (intrinsicFiber_smooth (I := I) g hEnorm p).comp hlaunch
  have heq :
      ((fun v : E => expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from v)) ∘ launch) =
        intrLaunch3 (I := I) g hEnorm p u a b := by
    funext q
    change intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from launch q) 1 =
      intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u + q.1.1 • a + q.1.2 • b) q.2
    simpa only [launch] using
      intrinsicGeodesic_smul (I := I) g hEnorm p
        (show TangentSpace I p from
          u + q.1.1 • a + q.1.2 • b) q.2
  rw [heq] at hcomp
  exact hcomp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
noncomputable def intrLaunchJ
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (q : Real × Real) :
    TangentSpace I
      (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2)) :=
  mfderiv
    (modelWithCornersSelf Real ((Real × Real) × Real))
    I (intrLaunch3 (I := I) g hEnorm p u a b)
    ((q.1, 0), q.2) ((0, 1), 0)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchJ_smooth
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) :
    ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      (I.prod (modelWithCornersSelf Real E)) ∞
      (fun q : Real × Real =>
        TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _))
          (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))
          (intrLaunchJ (I := I) g hEnorm p u a b q)) := by
  let D := modelWithCornersSelf Real ((Real × Real) × Real)
  let Q := modelWithCornersSelf Real (Real × Real)
  let F := intrLaunch3 (I := I) g hEnorm p u a b
  let ι : Real × Real → (Real × Real) × Real := fun q => ((q.1, 0), q.2)
  let v : (Real × Real) × Real := ((0, 1), 0)
  have hF : ContMDiff D I ∞ F := by
    dsimp only [D, F]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
      modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact intrLaunch3_smooth (I := I) g hEnorm p u a b
  have hconst :
      ContMDiff D D.tangent ∞
        (fun z : (Real × Real) × Real =>
          (TotalSpace.mk' ((Real × Real) × Real) z v :
            TangentBundle D ((Real × Real) × Real))) := by
    exact
      (contMDiff_vectorSpace_iff_contDiff (V := fun _ => v)).mpr
        contDiff_const
  have hι :
      ContMDiff Q D ∞ ι := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hsection :
      ContMDiff Q D.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' ((Real × Real) × Real) (ι q) v :
            TangentBundle D ((Real × Real) × Real))) :=
    hconst.comp hι
  have htan :
      ContMDiff D.tangent I.tangent ∞ (tangentMap D I F) :=
    hF.contMDiff_tangentMap (le_refl _)
  have hcomp := htan.comp hsection
  dsimp only [Q] at hcomp
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hcomp
  simpa only [D, F, ι, v, tangentMap, intrLaunchJ] using hcomp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
noncomputable def intrLaunchJet
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) (q : Real × Real) :
    TangentSpace I
      (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2)) :=
  let f : Real -> Real -> M := fun r t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
  let V : forall r t : Real, TangentSpace I (f r t) := fun r t =>
    intrLaunchJ (I := I) g hEnorm p u a b (r, t)
  Variation.covFstIter (I := I) g f n V q.1 q.2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
@[simp]
theorem intrLaunchJet_zero
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (q : Real × Real) :
    intrLaunchJet (I := I) g hEnorm p u a b 0 q =
      intrLaunchJ (I := I) g hEnorm p u a b q :=
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
@[simp]
theorem intrLaunchJet_succ
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) (r t : Real) :
    intrLaunchJet (I := I) g hEnorm p u a b (Nat.succ n) (r, t) =
      Variation.covFst (I := I) g
        (fun s v =>
          intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), v))
        (fun s v =>
          intrLaunchJet (I := I) g hEnorm p u a b n (s, v))
        r t :=
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchJet_smooth
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) :
    ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))
          (intrLaunchJet (I := I) g hEnorm p u a b n q) :
            TangentBundle I M)) := by
  let f : Real -> Real -> M := fun r t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
  let V : forall r t : Real, TangentSpace I (f r t) := fun r t =>
    intrLaunchJ (I := I) g hEnorm p u a b (r, t)
  have hV :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)) := by
    simpa only [f, V] using
      intrLaunchJ_smooth (I := I) g hEnorm p u a b
  have hjet :=
    Variation.covFstIter_smooth (I := I) g f V hV n
  simpa only [f, V, intrLaunchJet] using hjet

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchMix_smooth
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) :
    let f : Real → Real → M := fun r t =>
      intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
    let V : ∀ r t : Real, TangentSpace I (f r t) := fun r t =>
      intrLaunchJ (I := I) g hEnorm p u a b (r, t)
    ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2)
          (Variation.covFst (I := I) g f V q.1 q.2) :
            TangentBundle I M)) := by
  dsimp only
  let f : Real → Real → M := fun r t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
  let V : ∀ r t : Real, TangentSpace I (f r t) := fun r t =>
    intrLaunchJ (I := I) g hEnorm p u a b (r, t)
  have hV :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)) := by
    simpa only [f, V] using
      intrLaunchJ_smooth (I := I) g hEnorm p u a b
  exact Variation.cov_fst_smooth (I := I) g f V hV

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrMixDeriv_smooth
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) :
    let f : Real → Real → M := fun r t =>
      intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
    let V : ∀ r t : Real, TangentSpace I (f r t) := fun r t =>
      intrLaunchJ (I := I) g hEnorm p u a b (r, t)
    let W : ∀ r t : Real, TangentSpace I (f r t) := fun r t =>
      Variation.covFst (I := I) g f V r t
    ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2)
          (Variation.covSnd (I := I) g f W q.1 q.2) :
            TangentBundle I M)) := by
  dsimp only
  let f : Real → Real → M := fun r t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
  let V : ∀ r t : Real, TangentSpace I (f r t) := fun r t =>
    intrLaunchJ (I := I) g hEnorm p u a b (r, t)
  let W : ∀ r t : Real, TangentSpace I (f r t) := fun r t =>
    Variation.covFst (I := I) g f V r t
  have hW :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (f q.1 q.2) (W q.1 q.2) : TangentBundle I M)) := by
    simpa only [f, V, W] using
      intrLaunchMix_smooth (I := I) g hEnorm p u a b
  exact Variation.cov_snd_smooth (I := I) g f W hW

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchDir_smooth
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (v : (Real × Real) × Real) :
    ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      (I.prod (modelWithCornersSelf Real E)) ∞
      (fun q : Real × Real =>
        TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _))
          (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))
          (mfderiv
            (modelWithCornersSelf Real ((Real × Real) × Real))
            I (intrLaunch3 (I := I) g hEnorm p u a b)
            ((q.1, 0), q.2) v)) := by
  let D := modelWithCornersSelf Real ((Real × Real) × Real)
  let Q := modelWithCornersSelf Real (Real × Real)
  let F := intrLaunch3 (I := I) g hEnorm p u a b
  let ι : Real × Real → (Real × Real) × Real := fun q => ((q.1, 0), q.2)
  have hF : ContMDiff D I ∞ F := by
    dsimp only [D, F]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
      modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact intrLaunch3_smooth (I := I) g hEnorm p u a b
  have hconst :
      ContMDiff D D.tangent ∞
        (fun z : (Real × Real) × Real =>
          (TotalSpace.mk' ((Real × Real) × Real) z v :
            TangentBundle D ((Real × Real) × Real))) := by
    exact
      (contMDiff_vectorSpace_iff_contDiff (V := fun _ => v)).mpr
        contDiff_const
  have hι : ContMDiff Q D ∞ ι := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hsection :
      ContMDiff Q D.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' ((Real × Real) × Real) (ι q) v :
            TangentBundle D ((Real × Real) × Real))) :=
    hconst.comp hι
  have htan :
      ContMDiff D.tangent I.tangent ∞ (tangentMap D I F) :=
    hF.contMDiff_tangentMap (le_refl _)
  have hcomp := htan.comp hsection
  dsimp only [Q] at hcomp
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hcomp
  simpa only [D, F, ι, tangentMap] using hcomp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchA_eq
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (q : Real × Real) :
    mfderiv
        (modelWithCornersSelf Real ((Real × Real) × Real))
        I (intrLaunch3 (I := I) g hEnorm p u a b)
        ((q.1, 0), q.2) ((1, 0), 0) =
      Variation.varFst (I := I)
        (fun s t : Real =>
          intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), t))
        q.1 q.2 := by
  let D := modelWithCornersSelf Real ((Real × Real) × Real)
  let F := intrLaunch3 (I := I) g hEnorm p u a b
  let ι : Real → (Real × Real) × Real := fun s => ((s, 0), q.2)
  have hFsmooth : ContMDiff D I ∞ F := by
    dsimp only [D, F]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
      modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact intrLaunch3_smooth (I := I) g hEnorm p u a b
  have hF : MDifferentiableAt D I F (ι q.1) :=
    hFsmooth.mdifferentiableAt (by simp)
  have hι :
      MDifferentiableAt (modelWithCornersSelf Real Real) D ι q.1 :=
    mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
  have hιHas :
      HasFDerivAt ι
        (((ContinuousLinearMap.id Real Real).prod
          (0 : Real →L[Real] Real)).prod
            (0 : Real →L[Real] Real)) q.1 :=
    ((hasFDerivAt_id q.1).prodMk
      (hasFDerivAt_const (x := q.1) (c := (0 : Real)))).prodMk
        (hasFDerivAt_const (x := q.1) (c := q.2))
  have hι' :
      mfderiv (modelWithCornersSelf Real Real) D ι q.1 (1 : Real) =
        ((1, 0), 0) := by
    rw [mfderiv_eq_fderiv, hιHas.fderiv]
    rfl
  have hcomp :=
    mfderiv_comp_apply (I := modelWithCornersSelf Real Real)
      (I' := D) (I'' := I) (f := ι) (g := F) q.1
        hF hι (1 : Real)
  rw [hι'] at hcomp
  simpa only [D, F, ι, Function.comp_apply, Variation.varFst] using hcomp.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchA_zero
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (t : Real) :
    Variation.varFst (I := I)
        (fun s v : Real =>
          intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), v)) 0 t =
      intrinsicJacobi (I := I) g hEnorm p u a t := by
  unfold Variation.varFst intrinsicJacobi
  have hfun :
      (fun r : Real =>
        intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u + r • a + (0 : Real) • b) t) =
        fun r : Real =>
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u + r • a) t := by
    funext r
    simp
  simpa only [intrLaunch3] using congrArg
    (fun F : Real → M => mfderiv (modelWithCornersSelf Real Real) I F 0 1) hfun

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchT_eq
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (q : Real × Real) :
    mfderiv
        (modelWithCornersSelf Real ((Real × Real) × Real))
        I (intrLaunch3 (I := I) g hEnorm p u a b)
        ((q.1, 0), q.2) ((0, 0), 1) =
      Variation.varSnd (I := I)
        (fun s t : Real =>
          intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), t))
        q.1 q.2 := by
  let D := modelWithCornersSelf Real ((Real × Real) × Real)
  let F := intrLaunch3 (I := I) g hEnorm p u a b
  let ι : Real → (Real × Real) × Real := fun t => ((q.1, 0), t)
  have hFsmooth : ContMDiff D I ∞ F := by
    dsimp only [D, F]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
      modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact intrLaunch3_smooth (I := I) g hEnorm p u a b
  have hF : MDifferentiableAt D I F (ι q.2) :=
    hFsmooth.mdifferentiableAt (by simp)
  have hι :
      MDifferentiableAt (modelWithCornersSelf Real Real) D ι q.2 :=
    mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
  have hιHas :
      HasFDerivAt ι
        (((0 : Real →L[Real] Real).prod
          (0 : Real →L[Real] Real)).prod
            (ContinuousLinearMap.id Real Real)) q.2 :=
    ((hasFDerivAt_const (x := q.2) (c := q.1)).prodMk
      (hasFDerivAt_const (x := q.2) (c := (0 : Real)))).prodMk
        (hasFDerivAt_id q.2)
  have hι' :
      mfderiv (modelWithCornersSelf Real Real) D ι q.2 (1 : Real) =
        ((0, 0), 1) := by
    rw [mfderiv_eq_fderiv, hιHas.fderiv]
    rfl
  have hcomp :=
    mfderiv_comp_apply (I := modelWithCornersSelf Real Real)
      (I' := D) (I'' := I) (f := ι) (g := F) q.2
        hF hι (1 : Real)
  rw [hι'] at hcomp
  simpa only [D, F, ι, Function.comp_apply, Variation.varSnd] using hcomp.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchJ_eq
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (q : Real × Real) :
    intrLaunchJ (I := I) g hEnorm p u a b q =
      mfderiv (modelWithCornersSelf Real Real) I
        (fun s : Real =>
          intrLaunch3 (I := I) g hEnorm p u a b ((q.1, s), q.2))
        0 (1 : Real) := by
  let D := modelWithCornersSelf Real ((Real × Real) × Real)
  let F := intrLaunch3 (I := I) g hEnorm p u a b
  let ι : Real → (Real × Real) × Real := fun s => ((q.1, s), q.2)
  have hFsmooth : ContMDiff D I ∞ F := by
    dsimp only [D, F]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
      modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact intrLaunch3_smooth (I := I) g hEnorm p u a b
  have hF : MDifferentiableAt D I F (ι 0) :=
    hFsmooth.mdifferentiableAt (by simp)
  have hι : MDifferentiableAt (modelWithCornersSelf Real Real) D ι 0 :=
    mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
  have hιHas :
      HasFDerivAt ι
        (((0 : Real →L[Real] Real).prod
          (ContinuousLinearMap.id Real Real)).prod
            (0 : Real →L[Real] Real)) 0 :=
    ((hasFDerivAt_const (x := (0 : Real)) (c := q.1)).prodMk
      (hasFDerivAt_id (0 : Real))).prodMk
        (hasFDerivAt_const (x := (0 : Real)) (c := q.2))
  have hι' :
      mfderiv (modelWithCornersSelf Real Real) D ι 0 (1 : Real) =
        ((0, 1), 0) := by
    rw [mfderiv_eq_fderiv, hιHas.fderiv]
    rfl
  have hcomp :=
    mfderiv_comp_apply (I := modelWithCornersSelf Real Real)
      (I' := D) (I'' := I) (f := ι) (g := F) (0 : Real)
        hF hι (1 : Real)
  rw [hι'] at hcomp
  simpa only [D, F, ι, Function.comp_apply, intrLaunchJ] using hcomp.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchA_self
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a : E) (r t : Real) :
    let f : Real → Real → M := fun s v =>
      intrLaunch3 (I := I) g hEnorm p u a a ((s, 0), v)
    Variation.varFst (I := I) f r t =
      intrLaunchJ (I := I) g hEnorm p u a a (r, t) := by
  dsimp only
  let f : Real → Real → M := fun s v =>
    intrLaunch3 (I := I) g hEnorm p u a a ((s, 0), v)
  have hfSmooth :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I ∞ (fun q : Real × Real => f q.1 q.2) := by
    have hincl :
        ContMDiff
          ((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real))
          (((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real)).prod
              (modelWithCornersSelf Real Real))
          ∞ (fun q : Real × Real => ((q.1, (0 : Real)), q.2)) :=
      (contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd
    exact (intrLaunch3_smooth (I := I) g hEnorm p u a a).comp hincl
  have hf : Variation.IsSmoothVariation (I := I) f :=
    hfSmooth.of_le ENat.LEInfty.out
  have hshift :=
    Variation.varFst_shift (I := I) f hf r t
  have hfamily :
      (fun s v : Real => f (r + s) v) =
        fun s v : Real =>
          intrLaunch3 (I := I) g hEnorm p u a a ((r, s), v) := by
    funext s v
    simp only [f, intrLaunch3, zero_smul, add_zero, add_smul]
    rw [add_assoc]
  rw [hfamily] at hshift
  calc
    Variation.varFst (I := I) f r t =
        Variation.varFst (I := I)
          (fun s v : Real =>
            intrLaunch3 (I := I) g hEnorm p u a a ((r, s), v))
          0 t := hshift.symm
    _ = mfderiv (modelWithCornersSelf Real Real) I
          (fun s : Real =>
            intrLaunch3 (I := I) g hEnorm p u a a ((r, s), t))
          0 (1 : Real) := rfl
    _ = intrLaunchJ (I := I) g hEnorm p u a a (r, t) :=
      (intrLaunchJ_eq (I := I) g hEnorm p u a a (r, t)).symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrAJet_self
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a : E) (n : Nat) (q : Real × Real) :
    let f : Real → Real → M := fun r t =>
      intrLaunch3 (I := I) g hEnorm p u a a ((r, 0), t)
    let A : ∀ r t : Real, TangentSpace I (f r t) := fun r t =>
      Variation.varFst (I := I) f r t
    Variation.covFstIter (I := I) g f n A q.1 q.2 =
      intrLaunchJet (I := I) g hEnorm p u a a n q := by
  dsimp only
  let f : Real → Real → M := fun r t =>
    intrLaunch3 (I := I) g hEnorm p u a a ((r, 0), t)
  let A : ∀ r t : Real, TangentSpace I (f r t) := fun r t =>
    Variation.varFst (I := I) f r t
  let B : ∀ r t : Real, TangentSpace I (f r t) := fun r t =>
    intrLaunchJ (I := I) g hEnorm p u a a (r, t)
  have hAB : A = B := by
    funext r t
    exact intrLaunchA_self (I := I) g hEnorm p u a r t
  change Variation.covFstIter (I := I) g f n A q.1 q.2 =
    Variation.covFstIter (I := I) g f n B q.1 q.2
  rw [hAB]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchJ_time0
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (r : Real) :
    intrLaunchJ (I := I) g hEnorm p u a b (r, 0) = 0 := by
  rw [intrLaunchJ_eq]
  have hconst :
      (fun s : Real =>
        intrLaunch3 (I := I) g hEnorm p u a b ((r, s), 0)) =
        fun _ : Real => p := by
    funext s
    exact intrinsicGeodesic_zero (I := I) g hEnorm p _
  rw [hconst, mfderiv_const]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchJet_time0
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) (r : Real) :
    intrLaunchJet (I := I) g hEnorm p u a b n (r, 0) = 0 := by
  let f : Real → Real → M := fun s t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), t)
  let V : ∀ s t : Real, TangentSpace I (f s t) := fun s t =>
    intrLaunchJ (I := I) g hEnorm p u a b (s, t)
  change Variation.covFstIter (I := I) g f n V r 0 = 0
  exact Variation.covFstIter_zero_of (I := I) g f V 0
    (fun s => intrLaunchJ_time0 (I := I) g hEnorm p u a b s) n r

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchDJ_time0
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (r : Real) :
    let f : Real → Real → M := fun s t =>
      intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), t)
    let V : ∀ s t : Real, TangentSpace I (f s t) := fun s t =>
      intrLaunchJ (I := I) g hEnorm p u a b (s, t)
    Variation.covSnd (I := I) g f V r 0 = b := by
  dsimp only
  let f : Real → Real → M := fun s t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), t)
  let V : ∀ s t : Real, TangentSpace I (f s t) := fun s t =>
    intrLaunchJ (I := I) g hEnorm p u a b (s, t)
  let γ : Real → M := fun t => f r t
  let γ' : Real → M := fun t =>
    intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from u + r • a) t
  let J' : ∀ t : Real, TangentSpace I (γ' t) := fun t =>
    mfderiv (modelWithCornersSelf Real Real) I
      (fun s : Real =>
        intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u + r • a + s • b) t)
      0 (1 : Real)
  have hcurve : γ =ᶠ[𝓝 (0 : Real)] γ' := by
    filter_upwards with t
    simp only [γ, γ', f, intrLaunch3, zero_smul, add_zero]
  have hfield : ∀ᶠ t in 𝓝 (0 : Real), (V r t : E) = (J' t : E) := by
    filter_upwards with t
    simpa only [V, J', f, intrLaunch3, zero_smul, add_zero] using
      intrLaunchJ_eq (I := I) g hEnorm p u a b (r, t)
  have hcongr :=
    covDerivAlong_congr_curve (I := I) g
      (γ := γ) (γ' := γ') (fun t => V r t) J' hcurve hfield
  have hd0 :=
    intrinsic_jacobi_d0 (I := I) g hEnorm p (u + r • a) b
  simpa only [Variation.covSnd, f, V, γ, γ', J'] using hcongr.trans hd0

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchJ_at
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (r t : Real) :
    intrLaunchJ (I := I) g hEnorm p u a b (r, t) =
      intrinsicJacobi (I := I) g hEnorm p (u + r • a) b t := by
  rw [intrLaunchJ_eq]
  unfold intrinsicJacobi
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchJ_zero
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (t : Real) :
    intrLaunchJ (I := I) g hEnorm p u a b (0, t) =
      intrinsicJacobi (I := I) g hEnorm p u b t := by
  rw [intrLaunchJ_eq]
  unfold intrinsicJacobi
  have hfun :
      (fun s : Real =>
        intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u + (0 : Real) • a + s • b) t) =
        fun s : Real =>
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u + s • b) t := by
    funext s
    simp
  simpa only [intrLaunch3] using congrArg
    (fun F : Real → M => mfderiv (modelWithCornersSelf Real Real) I F 0 1) hfun

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchDA_zero
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (t : Real) :
    let f : Real → Real → M := fun r s =>
      intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), s)
    Variation.covSnd (I := I) g f
        (fun r s => Variation.varFst (I := I) f r s) 0 t =
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
        (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p u)
        (intrinsicJacobi (I := I) g hEnorm p u a) t := by
  dsimp only
  let f : Real → Real → M := fun r s =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), s)
  let A : ∀ s : Real, TangentSpace I (f 0 s) := fun s =>
    Variation.varFst (I := I) f 0 s
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  let J : ∀ s : Real, TangentSpace I (γ s) :=
    intrinsicJacobi (I := I) g hEnorm p u a
  have hγ : (fun s : Real => f 0 s) =ᶠ[𝓝 t] γ := by
    filter_upwards with s
    simp [f, γ, intrLaunch3]
  have hA : ∀ᶠ s in 𝓝 t, (A s : E) = (J s : E) := by
    filter_upwards with s
    simpa only [A, J, f] using congrArg (fun z => (z : E))
      (intrLaunchA_zero (I := I) g hEnorm p u a b s)
  simpa only [Variation.covSnd, f, A, γ, J] using
    covDerivAlong_congr_curve (I := I) g A J hγ hA

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunchDJ_zero
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (t : Real) :
    let f : Real → Real → M := fun r s =>
      intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), s)
    let V : ∀ r s : Real, TangentSpace I (f r s) := fun r s =>
      intrLaunchJ (I := I) g hEnorm p u a b (r, s)
    Variation.covSnd (I := I) g f V 0 t =
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
        (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p u)
        (intrinsicJacobi (I := I) g hEnorm p u b) t := by
  dsimp only
  let f : Real → Real → M := fun r s =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), s)
  let V : ∀ r s : Real, TangentSpace I (f r s) := fun r s =>
    intrLaunchJ (I := I) g hEnorm p u a b (r, s)
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  let J : ∀ s : Real, TangentSpace I (γ s) :=
    intrinsicJacobi (I := I) g hEnorm p u b
  have hγ : (fun s : Real => f 0 s) =ᶠ[𝓝 t] γ := by
    filter_upwards with s
    simp [f, γ, intrLaunch3]
  have hV : ∀ᶠ s in 𝓝 t, (V 0 s : E) = (J s : E) := by
    filter_upwards with s
    simpa only [V, J, f] using congrArg (fun z => (z : E))
      (intrLaunchJ_zero (I := I) g hEnorm p u a b s)
  simpa only [Variation.covSnd, f, V, γ, J] using
    covDerivAlong_congr_curve (I := I) g (fun s => V 0 s) J hγ hV

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunch_jacobi
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (r : Real) :
    let γ : Real → M := fun t =>
      intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
    let J : ∀ t : Real, TangentSpace I (γ t) := fun t =>
      mfderiv (modelWithCornersSelf Real Real) I
        (fun s : Real =>
          intrLaunch3 (I := I) g hEnorm p u a b ((r, s), t))
        0 (1 : Real)
    DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAlong
      (I := I) g γ J := by
  dsimp only
  let x : E := u + r • a
  have hγ :
      (fun t : Real =>
        intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)) =
        fun t : Real =>
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from x) t := by
    funext t
    simp [intrLaunch3, x]
  rw [hγ]
  simpa [intrLaunch3, x] using
    (intrinsic_jacobi (I := I) g hEnorm p x b)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunch_mix_zero
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) :
    let γ : Real → M := fun r =>
      intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), 0)
    let J : ∀ r : Real, TangentSpace I (γ r) := fun r =>
      mfderiv (modelWithCornersSelf Real Real) I
        (fun s : Real =>
          intrLaunch3 (I := I) g hEnorm p u a b ((r, s), 0))
        0 (1 : Real)
    DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
      (I := I) g γ J 0 = 0 := by
  dsimp only
  let γ : Real → M := fun r =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), 0)
  let J : ∀ r : Real, TangentSpace I (γ r) := fun r =>
    mfderiv (modelWithCornersSelf Real Real) I
      (fun s : Real =>
        intrLaunch3 (I := I) g hEnorm p u a b ((r, s), 0))
      0 (1 : Real)
  change
    DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
      (I := I) g γ J 0 = 0
  have hJ : J = fun r : Real => (0 : TangentSpace I (γ r)) := by
    funext r
    have hconst :
        (fun s : Real =>
          intrLaunch3 (I := I) g hEnorm p u a b ((r, s), 0)) =
          fun _ : Real => p := by
      funext s
      exact intrinsicGeodesic_zero (I := I) g hEnorm p _
    change
      mfderiv (modelWithCornersSelf Real Real) I
        (fun s : Real =>
          intrLaunch3 (I := I) g hEnorm p u a b ((r, s), 0))
        0 (1 : Real) = 0
    rw [hconst, mfderiv_const]
    rfl
  rw [hJ]
  exact
    DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong_zero
      (I := I) g γ 0

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunch_commute
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (t : Real) :
    let f : Real → Real → M := fun r s =>
      intrLaunch3 (I := I) g hEnorm p u a b ((r, s), t)
    DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
        (I := I) g (fun r : Real => f r 0)
        (fun r : Real =>
          mfderiv (modelWithCornersSelf Real Real) I
            (fun s : Real => f r s) 0 1) 0 =
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
        (I := I) g (fun s : Real => f 0 s)
        (fun s : Real =>
          mfderiv (modelWithCornersSelf Real Real) I
            (fun r : Real => f r s) 0 1) 0 := by
  let f : Real → Real → M := fun r s =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, s), t)
  have hfSmooth :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I ∞ (fun q : Real × Real => f q.1 q.2) := by
    have hincl : ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        (((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real)).prod
            (modelWithCornersSelf Real Real))
        ∞ (fun q : Real × Real => ((q.1, q.2), t)) :=
      (contMDiff_fst.prodMk contMDiff_snd).prodMk contMDiff_const
    exact (intrLaunch3_smooth (I := I) g hEnorm p u a b).comp hincl
  have hf :
      DifferentialGeometry.Geometry.Riemannian.Variation.IsSmoothVariation
        (I := I) f := by
    exact hfSmooth.of_le ENat.LEInfty.out
  exact
    DifferentialGeometry.Geometry.Riemannian.Variation.commute_ds_dt_intrinsic
      (I := I) g f hf 0

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunch_dmix0
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) :
    let f : Real → Real → M := fun r t =>
      intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
    let V : ∀ r t : Real, TangentSpace I (f r t) := fun r t =>
      intrLaunchJ (I := I) g hEnorm p u a b (r, t)
    Variation.covSnd (I := I) g f
      (fun r t => Variation.covFst (I := I) g f V r t) 0 0 = 0 := by
  dsimp only
  let f : Real → Real → M := fun r t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
  let V : ∀ r t : Real, TangentSpace I (f r t) := fun r t =>
    intrLaunchJ (I := I) g hEnorm p u a b (r, t)
  change Variation.covSnd (I := I) g f
    (fun r t => Variation.covFst (I := I) g f V r t) 0 0 = 0
  have hfSmooth :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I ∞ (fun q : Real × Real => f q.1 q.2) := by
    have hincl :
        ContMDiff
          ((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real))
          (((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real)).prod
              (modelWithCornersSelf Real Real))
          ∞ (fun q : Real × Real => ((q.1, (0 : Real)), q.2)) :=
      (contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd
    exact (intrLaunch3_smooth (I := I) g hEnorm p u a b).comp hincl
  have hf : Variation.IsSmoothVariation (I := I) f :=
    hfSmooth.of_le ENat.LEInfty.out
  have hV :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)) := by
    simpa only [f, V] using
      intrLaunchJ_smooth (I := I) g hEnorm p u a b
  have hcomm :=
    Variation.cov_commute_smooth (I := I) g f hf V 0 hV
  let A : ∀ r : Real, TangentSpace I (f r 0) := fun r =>
    Variation.covSnd (I := I) g f V r 0
  have hf0 : (fun r : Real => f r 0) =ᶠ[𝓝 (0 : Real)]
      (fun _ : Real => p) := by
    filter_upwards with r
    exact intrinsicGeodesic_zero (I := I) g hEnorm p _
  have hA0 : ∀ᶠ r in 𝓝 (0 : Real), (A r : E) = b := by
    filter_upwards with r
    let gamma : Real → M := fun t =>
      intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
    let gamma' : Real → M := fun t =>
      intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u + r • a) t
    let J' : ∀ t : Real, TangentSpace I (gamma' t) := fun t =>
      mfderiv (modelWithCornersSelf Real Real) I
        (fun s : Real =>
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u + r • a + s • b) t)
        0 (1 : Real)
    have hcurve : gamma =ᶠ[𝓝 (0 : Real)] gamma' := by
      filter_upwards with t
      simp only [gamma, gamma', intrLaunch3, zero_smul, add_zero]
    have hfield : ∀ᶠ t in 𝓝 (0 : Real),
        (intrLaunchJ (I := I) g hEnorm p u a b (r, t) : E) =
          (J' t : E) := by
      filter_upwards with t
      simpa only [gamma, gamma', J', intrLaunch3, zero_smul, add_zero] using
        intrLaunchJ_eq (I := I) g hEnorm p u a b (r, t)
    have hcongr :=
      covDerivAlong_congr_curve (I := I) g
        (γ := gamma) (γ' := gamma')
        (fun t => intrLaunchJ (I := I) g hEnorm p u a b (r, t))
        J' hcurve hfield
    have hd0 :=
      intrinsic_jacobi_d0 (I := I) g hEnorm p (u + r • a) b
    simpa only [A, Variation.covSnd, f, V, gamma, gamma', J'] using
      hcongr.trans hd0
  have hleftCongr :=
    covDerivAlong_congr_curve (I := I) g A
      (fun _ : Real => (show TangentSpace I p from b)) hf0 hA0
  have hconst :=
    covDerivAlong_const (I := I) g p
      (fun _ : Real => (show TangentSpace I p from b)) 0 (by fun_prop)
  have hleft :
      (Variation.covFst (I := I) g f
        (fun r t => Variation.covSnd (I := I) g f V r t) 0 0 : E) = 0 := by
    change
      (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
        (I := I) g (fun r : Real => f r 0) A 0 : E) = 0
    calc
      _ = (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (I := I) g (fun _ : Real => p)
          (fun _ : Real => (show TangentSpace I p from b)) 0 : E) :=
        hleftCongr
      _ = deriv (fun _ : Real => (b : E)) 0 := hconst
      _ = 0 := deriv_const _ _
  have hV00 : V 0 0 = 0 := by
    change intrLaunchJ (I := I) g hEnorm p u a b (0, 0) = 0
    rw [intrLaunchJ_eq]
    have hconst :
        (fun s : Real =>
          intrLaunch3 (I := I) g hEnorm p u a b ((0, s), 0)) =
          fun _ : Real => p := by
      funext s
      exact intrinsicGeodesic_zero (I := I) g hEnorm p _
    rw [hconst, mfderiv_const]
    rfl
  have hcurv :
      ((DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
        (f 0 0))
        (mfderiv (modelWithCornersSelf Real Real) I
          (fun r : Real => f r 0) 0 (1 : Real))
        (mfderiv (modelWithCornersSelf Real Real) I
          (fun t : Real => f 0 t) 0 (1 : Real))
        (V 0 0) : E) = 0 := by
    rw [hV00]
    exact map_zero _
  change
    (Variation.covFst (I := I) g f
        (fun r t => Variation.covSnd (I := I) g f V r t) 0 0 : E) -
      (Variation.covSnd (I := I) g f
        (fun r t => Variation.covFst (I := I) g f V r t) 0 0 : E) =
      _ at hcomm
  rw [hleft, hcurv] at hcomm
  simpa only [zero_sub, neg_eq_zero] using hcomm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrLaunch_var_eq
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (t : Real) :
    let f : Real → Real → M := fun r v =>
      intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), v)
    let V : ∀ r v : Real, TangentSpace I (f r v) := fun r v =>
      intrLaunchJ (I := I) g hEnorm p u a b (r, v)
    Variation.covSnd2 (I := I) g f
          (fun r v => Variation.covFst (I := I) g f V r v) 0 t +
        Variation.jacCurv (I := I) g f
          (fun r v => Variation.covFst (I := I) g f V r v) 0 t =
      Variation.jacVarForce (I := I) g f V t := by
  let f : Real → Real → M := fun r v =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), v)
  let V : ∀ r v : Real, TangentSpace I (f r v) := fun r v =>
    intrLaunchJ (I := I) g hEnorm p u a b (r, v)
  change
    Variation.covSnd2 (I := I) g f
          (fun r v => Variation.covFst (I := I) g f V r v) 0 t +
        Variation.jacCurv (I := I) g f
          (fun r v => Variation.covFst (I := I) g f V r v) 0 t =
      Variation.jacVarForce (I := I) g f V t
  have hfSmooth :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I ∞ (fun q : Real × Real => f q.1 q.2) := by
    have hincl :
        ContMDiff
          ((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real))
          (((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real)).prod
              (modelWithCornersSelf Real Real))
          ∞ (fun q : Real × Real => ((q.1, (0 : Real)), q.2)) :=
      (contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd
    exact (intrLaunch3_smooth (I := I) g hEnorm p u a b).comp hincl
  have hf : Variation.IsSmoothVariation (I := I) f :=
    hfSmooth.of_le ENat.LEInfty.out
  have hV :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)) := by
    simpa only [f, V] using
      intrLaunchJ_smooth (I := I) g hEnorm p u a b
  have hJac : ∀ r : Real,
      Variation.IsJacobiAlong (I := I) g (fun v : Real => f r v)
        (fun v : Real => V r v) := by
    intro r
    simpa only [f, V, intrLaunchJ_eq] using
      intrLaunch_jacobi (I := I) g hEnorm p u a b r
  have hGeo : ∀ r : Real,
      DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
        (I := I) g (fun v : Real => f r v) := by
    intro r
    simpa only [f, intrLaunch3, zero_smul, add_zero] using
      intrinsicGeodesic_isGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u + r • a)
  exact Variation.jacobi_var_eq (I := I) g f hf V hV hJac hGeo t

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
noncomputable def intrJetResidual
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) (q : Real × Real) :
    TangentSpace I
      (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2)) :=
  let f : Real -> Real -> M := fun r t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
  let V : ∀ r t : Real, TangentSpace I (f r t) := fun r t =>
    intrLaunchJ (I := I) g hEnorm p u a b (r, t)
  Variation.jacJetResidual (I := I) g f V n q.1 q.2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
noncomputable def intrJetCorr
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) (q : Real × Real) :
    TangentSpace I
      (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2)) :=
  let f : Real -> Real -> M := fun r t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
  let V : ∀ r t : Real, TangentSpace I (f r t) := fun r t =>
    intrLaunchJ (I := I) g hEnorm p u a b (r, t)
  Variation.jacJetCorr (I := I) g f V n q.1 q.2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
@[simp]
theorem intrJetResidual_zero
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (r t : Real) :
    intrJetResidual (I := I) g hEnorm p u a b 0 (r, t) = 0 := by
  let γ : Real -> M := fun v =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), v)
  let J : ∀ v : Real, TangentSpace I (γ v) := fun v =>
    mfderiv (modelWithCornersSelf Real Real) I
      (fun s : Real =>
        intrLaunch3 (I := I) g hEnorm p u a b ((r, s), v))
      0 (1 : Real)
  have hfield :
      (fun v : Real => intrLaunchJ (I := I) g hEnorm p u a b (r, v)) =
        J := by
    funext v
    exact intrLaunchJ_eq (I := I) g hEnorm p u a b (r, v)
  change Variation.IsJacobiAt (I := I) g γ
    (fun v : Real => intrLaunchJ (I := I) g hEnorm p u a b (r, v)) t
  rw [hfield]
  exact intrLaunch_jacobi (I := I) g hEnorm p u a b r t

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrJetCurv_smooth
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) :
    let f : Real -> Real -> M := fun r t =>
      intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
    ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2)
          (Variation.jacCurv (I := I) g f
            (fun r t =>
              intrLaunchJet (I := I) g hEnorm p u a b n (r, t))
            q.1 q.2) : TangentBundle I M)) := by
  dsimp only
  let f : Real -> Real -> M := fun r t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
  let W : ∀ r t : Real, TangentSpace I (f r t) := fun r t =>
    intrLaunchJet (I := I) g hEnorm p u a b n (r, t)
  have hW :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (W q.1 q.2) : TangentBundle I M)) := by
    simpa only [f, W] using
      intrLaunchJet_smooth (I := I) g hEnorm p u a b n
  have hT :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2)
            (Variation.varSnd (I := I) f q.1 q.2) :
              TangentBundle I M)) := by
    have hdir :=
      intrLaunchDir_smooth (I := I) g hEnorm p u a b
        (((0 : Real), (0 : Real)), (1 : Real))
    simpa only [f, intrLaunchT_eq] using hdir
  have hcurv :=
    Variation.jacCurv_smooth (I := I) g f W hW hT
  simpa only [f, W] using hcurv

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace ℝ E] in
theorem intrJetResidual_succ
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) (r t : Real) :
    let f : Real -> Real -> M := fun s v =>
      intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), v)
    intrJetResidual (I := I) g hEnorm p u a b (Nat.succ n) (r, t) =
      Variation.covFst (I := I) g f
          (fun s v =>
            intrJetResidual (I := I) g hEnorm p u a b n (s, v))
          r t -
        intrJetCorr (I := I) g hEnorm p u a b n (r, t) := by
  dsimp only
  let f : Real -> Real -> M := fun s v =>
    intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), v)
  let V : ∀ s v : Real, TangentSpace I (f s v) := fun s v =>
    intrLaunchJ (I := I) g hEnorm p u a b (s, v)
  have hfSmooth :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I ∞ (fun q : Real × Real => f q.1 q.2) := by
    have hincl :
        ContMDiff
          ((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real))
          (((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real)).prod
              (modelWithCornersSelf Real Real))
          ∞ (fun q : Real × Real => ((q.1, (0 : Real)), q.2)) :=
      (contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd
    exact (intrLaunch3_smooth (I := I) g hEnorm p u a b).comp hincl
  have hf : Variation.IsSmoothVariation (I := I) f :=
    hfSmooth.of_le ENat.LEInfty.out
  have hV :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)) := by
    simpa only [f, V] using
      intrLaunchJ_smooth (I := I) g hEnorm p u a b
  have hJn := intrJetCurv_smooth (I := I) g hEnorm p u a b n
  have hrec :=
    Variation.jacJetResidual_succ (I := I) g f hf V hV n hJn r t
  simpa only [intrJetResidual, intrJetCorr, f, V] using hrec

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
