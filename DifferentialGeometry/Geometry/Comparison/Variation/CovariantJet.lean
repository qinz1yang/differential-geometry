import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation
import DifferentialGeometry.Geometry.Comparison.Variation.GeneralCurvatureCommutation

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem covFst_shift
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (V : forall s t : Real, TangentSpace I (f s t))
    (c t : Real) :
    covFst (I := I) g
        (fun a v => f (c + a) v) (fun a v => V (c + a) v) 0 t =
      covFst (I := I) g f V c t := by
  simpa only [covFst] using
    (covDerivAlong_const_add_shift
      (I := I) g (fun s : Real => f s t) (fun s : Real => V s t) c)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem varFst_shift
    (f : Real -> Real -> M) (hf : IsSmoothVariation (I := I) f)
    (c t : Real) :
    varFst (I := I) (fun a v => f (c + a) v) 0 t =
      varFst (I := I) f c t := by
  have hslice :
      ContMDiff (modelWithCornersSelf Real Real) I 8
        (fun s : Real => f s t) := by
    have hincl :
        ContMDiff (modelWithCornersSelf Real Real)
          ((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real))
          8 (fun s : Real => (s, t)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hcomp :
      (fun a : Real => f (c + a) t) =
        (fun s : Real => f s t) ∘ (fun a : Real => c + a) := rfl
  have hshift :
      MDifferentiableAt (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real) (fun a : Real => c + a) 0 := by
    have hcd :
        ContMDiffAt (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real) ∞
          (fun a : Real => c + a) 0 := by
      rw [contMDiffAt_iff_contDiffAt]
      exact contDiffAt_const.add contDiffAt_id
    exact hcd.mdifferentiableAt (by simp)
  have hslice_at :
      MDifferentiableAt (modelWithCornersSelf Real Real) I
        (fun s : Real => f s t) ((fun a : Real => c + a) 0) := by
    simpa using hslice.contMDiffAt.mdifferentiableAt (by simp)
  rw [varFst, varFst, hcomp, mfderiv_comp 0 hslice_at hshift]
  have hderiv : HasDerivAt (fun a : Real => c + a) (1 : Real) 0 := by
    simpa using (hasDerivAt_id (0 : Real)).const_add c
  have hshift_mf :
      (mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real) (fun a : Real => c + a) 0)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real Real) 0).symm 1) =
        (tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real Real) (c + 0)).symm 1 := by
    have heq :
        mfderiv (modelWithCornersSelf Real Real)
            (modelWithCornersSelf Real Real) (fun a : Real => c + a) 0 =
          fderiv Real (fun a : Real => c + a) 0 :=
      mfderiv_eq_fderiv (𝕜 := Real) (f := fun a : Real => c + a) (x := 0)
    rw [heq]
    change deriv (fun a : Real => c + a) 0 = (1 : Real)
    exact hderiv.deriv
  change
    ((mfderiv (modelWithCornersSelf Real Real) I
        (fun s : Real => f s t) (c + 0)).comp
      (mfderiv (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real) (fun a : Real => c + a) 0))
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real Real) 0).symm 1) =
      mfderiv (modelWithCornersSelf Real Real) I
        (fun s : Real => f s t) c
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real Real) c).symm 1)
  rw [ContinuousLinearMap.comp_apply]
  rw [hshift_mf]
  rw [add_zero]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem covSnd_shift
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (V : forall s t : Real, TangentSpace I (f s t))
    (c a t : Real) :
    covSnd (I := I) g
        (fun r v => f (c + r) v) (fun r v => V (c + r) v) a t =
      covSnd (I := I) g f V (c + a) t :=
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem covSnd2_shift
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (V : forall s t : Real, TangentSpace I (f s t))
    (c a t : Real) :
    covSnd2 (I := I) g
        (fun r v => f (c + r) v) (fun r v => V (c + r) v) a t =
      covSnd2 (I := I) g f V (c + a) t :=
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in
private theorem varSnd_shift
    (f : Real -> Real -> M) (c t : Real) :
    varSnd (I := I) (fun r v => f (c + r) v) 0 t =
      varSnd (I := I) f c t := by
  have hcurve :
      (fun v : Real => f (c + 0) v) = fun v : Real => f c v := by
    funext v
    rw [add_zero]
  rw [varSnd, varSnd, hcurve]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartRep_fst_diff
    (f : Real -> Real -> M)
    (V : forall s t : Real, TangentSpace I (f s t))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)))
    (s t : Real) :
    DifferentiableAt Real
      (chartRepAt (I := I) (fun r : Real => f r t)
        (fun r : Real => V r t) s) s := by
  let swap : Real × Real -> Real × Real := fun q => (q.2, q.1)
  have hswap :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        ∞ swap :=
    contMDiff_snd.prodMk contMDiff_fst
  have hVswap :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.2 q.1) (V q.2 q.1) : TangentBundle I M)) := by
    change ContMDiff _ _ ∞
      ((fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)) ∘ swap)
    exact hV.comp hswap
  simpa only using
    chartRep_snd_diff (I := I) (fun a b => f b a)
      (fun a b => V b a) hVswap t s

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem covFst_add
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (V W : forall s t : Real, TangentSpace I (f s t))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)))
    (hW : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2) (W q.1 q.2) : TangentBundle I M)))
    (s t : Real) :
    covFst (I := I) g f (fun r v => V r v + W r v) s t =
      covFst (I := I) g f V s t + covFst (I := I) g f W s t := by
  simpa only [covFst] using
    covDerivAlong_add (I := I) g (fun r : Real => f r t)
      (fun r : Real => V r t) (fun r : Real => W r t) s
      (chartRep_fst_diff (I := I) f V hV s t)
      (chartRep_fst_diff (I := I) f W hW s t)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem cov_commute_global
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (hf : IsSmoothVariation (I := I) f)
    (V : forall s t : Real, TangentSpace I (f s t))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)))
    (s t : Real) :
    covFst (I := I) g f
          (fun r v => covSnd (I := I) g f V r v) s t -
        covSnd (I := I) g f
          (fun r v => covFst (I := I) g f V r v) s t =
      varCurv (I := I) g f V s t := by
  let fs : Real -> Real -> M := fun a v => f (s + a) v
  let Vs : forall a v : Real, TangentSpace I (fs a v) :=
    fun a v => V (s + a) v
  have hshift :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        ∞ (fun q : Real × Real => (s + q.1, q.2)) :=
    (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
  have hshift8 :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        8 (fun q : Real × Real => (s + q.1, q.2)) :=
    (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
  have hfs : IsSmoothVariation (I := I) fs :=
    (hf : ContMDiff _ _ _ _).comp hshift8
  have hVs :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (fs q.1 q.2) (Vs q.1 q.2) : TangentBundle I M)) := by
    change ContMDiff _ _ ∞
      ((fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)) ∘
        fun q : Real × Real => (s + q.1, q.2))
    exact hV.comp hshift
  have hraw :
      covFst (I := I) g fs
            (fun a v => covSnd (I := I) g fs Vs a v) 0 t -
          covSnd (I := I) g fs
            (fun a v => covFst (I := I) g fs Vs a v) 0 t =
        varCurv (I := I) g fs Vs 0 t := by
    simpa only [covFst, covSnd, varCurv, curvAlong, varFst, varSnd] using
      cov_commute_smooth (I := I) g fs hfs Vs t hVs
  have hleft :
      covFst (I := I) g fs
          (fun a v => covSnd (I := I) g fs Vs a v) 0 t =
        covFst (I := I) g f
          (fun r v => covSnd (I := I) g f V r v) s t := by
    have hfield :
        (fun a v => covSnd (I := I) g fs Vs a v) =
          fun a v => covSnd (I := I) g f V (s + a) v := by
      funext a v
      exact covSnd_shift (I := I) g f V s a v
    rw [hfield]
    exact covFst_shift (I := I) g f
      (fun r v => covSnd (I := I) g f V r v) s t
  have hright :
      covSnd (I := I) g fs
          (fun a v => covFst (I := I) g fs Vs a v) 0 t =
        covSnd (I := I) g f
          (fun r v => covFst (I := I) g f V r v) s t := by
    simp only [covSnd, fs, Vs, covFst_shift]
    rw [add_zero]
  have hcurv :
      varCurv (I := I) g fs Vs 0 t =
        varCurv (I := I) g f V s t := by
    simp only [varCurv, fs, Vs, varFst_shift (I := I) f hf s,
      varSnd_shift (I := I) f s]
    rw [add_zero]
  rw [hleft, hright, hcurv] at hraw
  exact hraw

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem cov_snd2_expand_at
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (hf : IsSmoothVariation (I := I) f)
    (V : forall s t : Real, TangentSpace I (f s t))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)))
    (s t : Real) :
    covFst (I := I) g f (fun r v => covSnd2 (I := I) g f V r v) s t =
      covSnd2 (I := I) g f
          (fun r v => covFst (I := I) g f V r v) s t +
        curvDerivAlong (I := I) g (fun v : Real => f s v)
          (fun v : Real => varFst (I := I) f s v)
          (fun v : Real => varSnd (I := I) f s v)
          (fun v : Real => V s v) t +
        curvAlong (I := I) g (fun v : Real => f s v)
          (fun v : Real =>
            covSnd (I := I) g f
              (fun r w => varFst (I := I) f r w) s v)
          (fun v : Real => varSnd (I := I) f s v)
          (fun v : Real => V s v) t +
        curvAlong (I := I) g (fun v : Real => f s v)
          (fun v : Real => varFst (I := I) f s v)
          (fun v : Real =>
            covSnd (I := I) g f
              (fun r w => varSnd (I := I) f r w) s v)
          (fun v : Real => V s v) t +
        (2 : Real) •
          varCurv (I := I) g f
            (fun r v => covSnd (I := I) g f V r v) s t := by
  let fs : Real -> Real -> M := fun a v => f (s + a) v
  let Vs : forall a v : Real, TangentSpace I (fs a v) :=
    fun a v => V (s + a) v
  have hshift :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        ∞ (fun q : Real × Real => (s + q.1, q.2)) :=
    (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
  have hshift8 :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        8 (fun q : Real × Real => (s + q.1, q.2)) :=
    (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
  have hfs : IsSmoothVariation (I := I) fs := by
    exact (hf : ContMDiff _ _ _ _).comp hshift8
  have hVs :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (fs q.1 q.2) (Vs q.1 q.2) : TangentBundle I M)) := by
    change ContMDiff _ _ ∞
      ((fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)) ∘
        fun q : Real × Real => (s + q.1, q.2))
    exact hV.comp hshift
  have hraw := cov_snd2_expand (I := I) g fs hfs Vs hVs t
  dsimp only [fs, Vs] at hraw
  have hleft :
      covFst (I := I) g (fun a v => f (s + a) v)
          (fun r v =>
            covSnd2 (I := I) g (fun a w => f (s + a) w)
              (fun a w => V (s + a) w) r v) 0 t =
        covFst (I := I) g f
          (fun r v => covSnd2 (I := I) g f V r v) s t := by
    have hfield :
        (fun r v =>
          covSnd2 (I := I) g (fun a w => f (s + a) w)
            (fun a w => V (s + a) w) r v) =
          (fun r v => covSnd2 (I := I) g f V (s + r) v) := by
      funext r v
      exact covSnd2_shift (I := I) g f V s r v
    rw [hfield]
    exact covFst_shift (I := I) g f
      (fun r v => covSnd2 (I := I) g f V r v) s t
  have hlead :
      covSnd2 (I := I) g (fun a v => f (s + a) v)
          (fun r v =>
            covFst (I := I) g (fun a w => f (s + a) w)
              (fun a w => V (s + a) w) r v) 0 t =
        covSnd2 (I := I) g f
          (fun r v => covFst (I := I) g f V r v) s t := by
    simp only [covSnd2, covSnd, covFst_shift]
    have hbase : (fun v : Real => f (s + 0) v) = fun v : Real => f s v := by
      simp only [add_zero]
    rw [hbase]
  have hcurvD :
      curvDerivAlong (I := I) g (fun v : Real => f (s + 0) v)
          (fun v : Real => varFst (I := I) (fun a w => f (s + a) w) 0 v)
          (fun v : Real => varSnd (I := I) (fun a w => f (s + a) w) 0 v)
          (fun v : Real => V (s + 0) v) t =
        curvDerivAlong (I := I) g (fun v : Real => f s v)
          (fun v : Real => varFst (I := I) f s v)
          (fun v : Real => varSnd (I := I) f s v)
          (fun v : Real => V s v) t := by
    simp_rw [varFst_shift (I := I) f hf s]
    simp_rw [varSnd_shift (I := I) f s]
    rw [add_zero s]
  have hcurv1 :
      curvAlong (I := I) g (fun v : Real => f (s + 0) v)
          (fun v : Real =>
            covSnd (I := I) g (fun a w => f (s + a) w)
              (fun r w =>
                varFst (I := I) (fun a u => f (s + a) u) r w) 0 v)
          (fun v : Real =>
            varSnd (I := I) (fun a w => f (s + a) w) 0 v)
          (fun v : Real => V (s + 0) v) t =
        curvAlong (I := I) g (fun v : Real => f s v)
          (fun v : Real =>
            covSnd (I := I) g f
              (fun r w => varFst (I := I) f r w) s v)
          (fun v : Real => varSnd (I := I) f s v)
          (fun v : Real => V s v) t := by
    simp only [covSnd]
    simp_rw [varFst_shift (I := I) f hf s]
    simp_rw [varSnd_shift (I := I) f s]
    rw [add_zero s]
  have hcurv2 :
      curvAlong (I := I) g (fun v : Real => f (s + 0) v)
          (fun v : Real =>
            varFst (I := I) (fun a w => f (s + a) w) 0 v)
          (fun v : Real =>
            covSnd (I := I) g (fun a w => f (s + a) w)
              (fun r w =>
                varSnd (I := I) (fun a u => f (s + a) u) r w) 0 v)
          (fun v : Real => V (s + 0) v) t =
        curvAlong (I := I) g (fun v : Real => f s v)
          (fun v : Real => varFst (I := I) f s v)
          (fun v : Real =>
            covSnd (I := I) g f
              (fun r w => varSnd (I := I) f r w) s v)
          (fun v : Real => V s v) t := by
    simp only [covSnd]
    simp_rw [varFst_shift (I := I) f hf s]
    simp_rw [varSnd_shift (I := I) f s]
    rw [add_zero s]
  have hvar :
      varCurv (I := I) g (fun a v => f (s + a) v)
          (fun r v =>
            covSnd (I := I) g (fun a w => f (s + a) w)
              (fun a w => V (s + a) w) r v) 0 t =
        varCurv (I := I) g f
          (fun r v => covSnd (I := I) g f V r v) s t := by
    simp only [varCurv]
    simp_rw [varFst_shift (I := I) f hf s]
    simp_rw [varSnd_shift (I := I) f s]
    simp_rw [covSnd_shift (I := I) g f V s]
    rw [add_zero s]
  rw [hleft, hlead, hcurvD, hcurv1, hcurv2, hvar] at hraw
  exact hraw

noncomputable def jacResidual
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (V : forall s t : Real, TangentSpace I (f s t)) (s t : Real) :
    TangentSpace I (f s t) :=
  covSnd2 (I := I) g f V s t + jacCurv (I := I) g f V s t

noncomputable def jacStepCorr
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (V : forall s t : Real, TangentSpace I (f s t)) (s t : Real) :
    TangentSpace I (f s t) :=
  curvDerivAlong (I := I) g (fun v : Real => f s v)
      (fun v : Real => varFst (I := I) f s v)
      (fun v : Real => varSnd (I := I) f s v)
      (fun v : Real => V s v) t +
    curvAlong (I := I) g (fun v : Real => f s v)
      (fun v : Real =>
        covSnd (I := I) g f
          (fun r w => varFst (I := I) f r w) s v)
      (fun v : Real => varSnd (I := I) f s v)
      (fun v : Real => V s v) t +
    curvAlong (I := I) g (fun v : Real => f s v)
      (fun v : Real => varFst (I := I) f s v)
      (fun v : Real =>
        covSnd (I := I) g f
          (fun r w => varSnd (I := I) f r w) s v)
      (fun v : Real => V s v) t +
    (2 : Real) •
      varCurv (I := I) g f
        (fun r v => covSnd (I := I) g f V r v) s t +
    curvDerivAlong (I := I) g (fun r : Real => f r t)
      (fun r : Real => V r t)
      (fun r : Real => varSnd (I := I) f r t)
      (fun r : Real => varSnd (I := I) f r t) s +
    curvAlong (I := I) g (fun r : Real => f r t)
      (fun r : Real => V r t)
      (fun r : Real =>
        covFst (I := I) g f
          (fun a v => varSnd (I := I) f a v) r t)
      (fun r : Real => varSnd (I := I) f r t) s +
    curvAlong (I := I) g (fun r : Real => f r t)
      (fun r : Real => V r t)
      (fun r : Real => varSnd (I := I) f r t)
      (fun r : Real =>
        covFst (I := I) g f
          (fun a v => varSnd (I := I) f a v) r t) s

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem jacResidual_step
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (hf : IsSmoothVariation (I := I) f)
    (V : forall s t : Real, TangentSpace I (f s t))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)))
    (hJ : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2) (jacCurv (I := I) g f V q.1 q.2) :
            TangentBundle I M)))
    (s t : Real) :
    jacResidual (I := I) g f
        (fun r v => covFst (I := I) g f V r v) s t =
      covFst (I := I) g f
          (fun r v => jacResidual (I := I) g f V r v) s t -
        jacStepCorr (I := I) g f V s t := by
  have hDt := cov_snd_smooth (I := I) g f V hV
  have hD2 :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (covSnd2 (I := I) g f V q.1 q.2) :
              TangentBundle I M)) := by
    change ContMDiff _ _ ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2)
          (covSnd (I := I) g f
            (fun r v => covSnd (I := I) g f V r v) q.1 q.2) :
            TangentBundle I M))
    exact cov_snd_smooth (I := I) g f
      (fun r v => covSnd (I := I) g f V r v) hDt
  have hadd :=
    covFst_add (I := I) g f
      (fun r v => covSnd2 (I := I) g f V r v)
      (fun r v => jacCurv (I := I) g f V r v) hD2 hJ s t
  have hD2comm := cov_snd2_expand_at (I := I) g f hf V hV s t
  have hRcomm := cov_jacCurv (I := I) g f V s t
  have hJlead :
      curvAlong (I := I) g (fun r : Real => f r t)
          (fun r : Real => covFst (I := I) g f V r t)
          (fun r : Real => varSnd (I := I) f r t)
          (fun r : Real => varSnd (I := I) f r t) s =
        jacCurv (I := I) g f
          (fun r v => covFst (I := I) g f V r v) s t :=
    rfl
  rw [hJlead] at hRcomm
  unfold jacResidual jacStepCorr
  rw [hadd]
  linear_combination (norm := module) - hD2comm - hRcomm

noncomputable def covFstIter
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M) :
    Nat -> (forall s t : Real, TangentSpace I (f s t)) ->
      forall s t : Real, TangentSpace I (f s t)
  | 0, V => V
  | Nat.succ n, V => fun s t =>
      covFst (I := I) g f
        (fun r v => covFstIter g f n V r v) s t

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp]
theorem covFstIter_zero
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (V : forall s t : Real, TangentSpace I (f s t)) :
    covFstIter (I := I) g f 0 V = V :=
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp]
theorem covFstIter_succ
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (V : forall s t : Real, TangentSpace I (f s t))
    (n : Nat) (s t : Real) :
    covFstIter (I := I) g f (Nat.succ n) V s t =
      covFst (I := I) g f
        (fun r v => covFstIter (I := I) g f n V r v) s t :=
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem covFstIter_zero_of
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (V : forall s t : Real, TangentSpace I (f s t))
    (t : Real) (hzero : forall s, V s t = 0) :
    forall n s, covFstIter (I := I) g f n V s t = 0 := by
  intro n
  induction n with
  | zero =>
      intro s
      simpa only [covFstIter_zero] using hzero s
  | succ n ih =>
      intro s
      rw [covFstIter_succ]
      change covDerivAlong (I := I) g (fun r : Real => f r t)
          (fun r : Real => covFstIter (I := I) g f n V r t) s = 0
      have hfield :
          (fun r : Real => covFstIter (I := I) g f n V r t) =
            fun r : Real => (0 : TangentSpace I (f r t)) := by
        funext r
        exact ih r
      rw [hfield]
      exact covDerivAlong_zero (I := I) g (fun r : Real => f r t) s

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem covFstIter_smooth
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (V : forall s t : Real, TangentSpace I (f s t))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M))) :
    forall n : Nat,
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2)
            (covFstIter (I := I) g f n V q.1 q.2) :
              TangentBundle I M)) := by
  intro n
  induction n with
  | zero =>
      simpa only [covFstIter_zero] using hV
  | succ n ih =>
      have hnext :=
        cov_fst_smooth (I := I) g f
          (fun s t => covFstIter (I := I) g f n V s t) ih
      simpa only [covFstIter_succ, covFst] using hnext

noncomputable def jacJetResidual
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (V : forall s t : Real, TangentSpace I (f s t))
    (n : Nat) (s t : Real) : TangentSpace I (f s t) :=
  jacResidual (I := I) g f (covFstIter (I := I) g f n V) s t

noncomputable def jacJetCorr
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (V : forall s t : Real, TangentSpace I (f s t))
    (n : Nat) (s t : Real) : TangentSpace I (f s t) :=
  jacStepCorr (I := I) g f (covFstIter (I := I) g f n V) s t

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem jacJetResidual_succ
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (hf : IsSmoothVariation (I := I) f)
    (V : forall s t : Real, TangentSpace I (f s t))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)))
    (n : Nat)
    (hJn : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2)
          (jacCurv (I := I) g f
            (covFstIter (I := I) g f n V) q.1 q.2) :
              TangentBundle I M)))
    (s t : Real) :
    jacJetResidual (I := I) g f V (Nat.succ n) s t =
      covFst (I := I) g f
          (fun r v => jacJetResidual (I := I) g f V n r v) s t -
        jacJetCorr (I := I) g f V n s t := by
  have hstep :=
    jacResidual_step (I := I) g f hf
      (covFstIter (I := I) g f n V)
      (covFstIter_smooth (I := I) g f V hV n) hJn s t
  change
    jacResidual (I := I) g f
        (fun r v => covFst (I := I) g f
          (covFstIter (I := I) g f n V) r v) s t =
      covFst (I := I) g f
          (fun r v => jacResidual (I := I) g f
            (covFstIter (I := I) g f n V) r v) s t -
        jacStepCorr (I := I) g f (covFstIter (I := I) g f n V) s t
  exact hstep

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem innerJet_deriv
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (V W : forall s t : Real, TangentSpace I (f s t))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)))
    (hW : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2) (W q.1 q.2) : TangentBundle I M)))
    (i j : Nat) (s t : Real) :
    HasDerivAt
      (fun r : Real =>
        g.inner (f r t)
          (covFstIter (I := I) g f i V r t)
          (covFstIter (I := I) g f j W r t))
      (g.inner (f s t)
          (covFstIter (I := I) g f (Nat.succ i) V s t)
          (covFstIter (I := I) g f j W s t) +
        g.inner (f s t)
          (covFstIter (I := I) g f i V s t)
          (covFstIter (I := I) g f (Nat.succ j) W s t))
      s := by
  let γ : Real -> M := fun r => f r t
  let Vi : forall r : Real, TangentSpace I (γ r) := fun r =>
    covFstIter (I := I) g f i V r t
  let Wj : forall r : Real, TangentSpace I (γ r) := fun r =>
    covFstIter (I := I) g f j W r t
  let incl : Real -> Real × Real := fun r => (r, t)
  have hincl : ContMDiff
      (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      ∞ incl := by
    change ContMDiff _ _ ∞ (fun r : Real => (id r, t))
    exact contMDiff_id.prodMk contMDiff_const
  have hViJoint := covFstIter_smooth (I := I) g f V hV i
  have hWjJoint := covFstIter_smooth (I := I) g f W hW j
  have hVi :
      ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
        (fun r : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (γ r) (Vi r) : TangentBundle I M)) := by
    change ContMDiff _ _ ∞
      ((fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (covFstIter (I := I) g f i V q.1 q.2) :
              TangentBundle I M)) ∘ incl)
    exact hViJoint.comp hincl
  have hWj :
      ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
        (fun r : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (γ r) (Wj r) : TangentBundle I M)) := by
    change ContMDiff _ _ ∞
      ((fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (covFstIter (I := I) g f j W q.1 q.2) :
              TangentBundle I M)) ∘ incl)
    exact hWjJoint.comp hincl
  have hγ : ContMDiff (modelWithCornersSelf Real Real) I ∞ γ := by
    intro r
    exact (Bundle.contMDiffAt_totalSpace.mp hVi.contMDiffAt).1
  have hVidiff := CovariantDerivativeAlong.chartRep_diff
    (I := I) γ Vi hVi s
  have hWjdiff := CovariantDerivativeAlong.chartRep_diff
    (I := I) γ Wj hWj s
  have hinner :=
    metric_compat_hasDerivAt_inner (I := I) (n := (∞ : WithTop ENat))
      (by simp) g γ Vi Wj s hγ hVidiff hWjdiff
  simpa only [γ, Vi, Wj, covFstIter_succ, covFst] using hinner

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
