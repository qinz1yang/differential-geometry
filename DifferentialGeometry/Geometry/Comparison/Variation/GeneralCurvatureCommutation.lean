import DifferentialGeometry.Geometry.Comparison.Variation.CovariantCommutationCurvature
import DifferentialGeometry.Geometry.Comparison.Variation.JacobiField

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

noncomputable def covFst
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (V : ∀ s t : Real, TangentSpace I (f s t)) (s t : Real) :
    TangentSpace I (f s t) :=
  covDerivAlong (I := I) g (fun r : Real => f r t)
    (fun r : Real => V r t) s

noncomputable def covSnd
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (V : ∀ s t : Real, TangentSpace I (f s t)) (s t : Real) :
    TangentSpace I (f s t) :=
  covDerivAlong (I := I) g (fun v : Real => f s v)
    (fun v : Real => V s v) t

noncomputable def varFst (f : Real → Real → M) (s t : Real) :
    TangentSpace I (f s t) :=
  mfderiv (modelWithCornersSelf Real Real) I (fun r : Real => f r t) s
    (1 : Real)

noncomputable def varSnd (f : Real → Real → M) (s t : Real) :
    TangentSpace I (f s t) :=
  mfderiv (modelWithCornersSelf Real Real) I (fun v : Real => f s v) t
    (1 : Real)

noncomputable def covSnd2
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (V : ∀ s t : Real, TangentSpace I (f s t)) (s t : Real) :
    TangentSpace I (f s t) :=
  covSnd (I := I) g f (fun r v => covSnd (I := I) g f V r v) s t

noncomputable def covFstSnd
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (V : ∀ s t : Real, TangentSpace I (f s t)) (s t : Real) :
    TangentSpace I (f s t) :=
  covFst (I := I) g f (fun r v => covSnd (I := I) g f V r v) s t

noncomputable def covSndFst
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (V : ∀ s t : Real, TangentSpace I (f s t)) (s t : Real) :
    TangentSpace I (f s t) :=
  covSnd (I := I) g f (fun r v => covFst (I := I) g f V r v) s t

noncomputable def curvAlong
    (g : SmoothRiemannianMetric I M) (γ : Real → M)
    (X Y Z : ∀ s : Real, TangentSpace I (γ s)) (t : Real) :
    TangentSpace I (γ t) :=
  (DifferentialGeometry.Geometry.Curvature.riemannOp
    (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
    (X t) (Y t) (Z t)

noncomputable def varCurv
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (V : ∀ s t : Real, TangentSpace I (f s t)) (s t : Real) :
    TangentSpace I (f s t) :=
  curvAlong (I := I) g (fun v : Real => f s v)
    (fun v : Real => varFst (I := I) f s v)
    (fun v : Real => varSnd (I := I) f s v)
    (fun v : Real => V s v) t

noncomputable def jacCurv
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (V : ∀ s t : Real, TangentSpace I (f s t)) (s t : Real) :
    TangentSpace I (f s t) :=
  curvAlong (I := I) g (fun r : Real => f r t)
    (fun r : Real => V r t)
    (fun r : Real => varSnd (I := I) f r t)
    (fun r : Real => varSnd (I := I) f r t) s

noncomputable def curvDerivAlong
    (g : SmoothRiemannianMetric I M) (γ : Real → M)
    (X Y Z : ∀ s : Real, TangentSpace I (γ s)) (t : Real) :
    TangentSpace I (γ t) :=
  covDerivAlong (I := I) g γ
      (fun s : Real => curvAlong (I := I) g γ X Y Z s) t -
    curvAlong (I := I) g γ
      (fun s : Real => covDerivAlong (I := I) g γ X s) Y Z t -
    curvAlong (I := I) g γ X
      (fun s : Real => covDerivAlong (I := I) g γ Y s) Z t -
    curvAlong (I := I) g γ X Y
      (fun s : Real => covDerivAlong (I := I) g γ Z s) t

noncomputable def jacVarForce
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (V : ∀ s t : Real, TangentSpace I (f s t)) (t : Real) :
    TangentSpace I (f 0 t) :=
  - (curvDerivAlong (I := I) g (fun v : Real => f 0 v)
        (fun v : Real => varFst (I := I) f 0 v)
        (fun v : Real => varSnd (I := I) f 0 v)
        (fun v : Real => V 0 v) t +
      curvAlong (I := I) g (fun v : Real => f 0 v)
        (fun v : Real =>
          covSnd (I := I) g f
            (fun s w => varFst (I := I) f s w) 0 v)
        (fun v : Real => varSnd (I := I) f 0 v)
        (fun v : Real => V 0 v) t +
      (2 : Real) •
        varCurv (I := I) g f
          (fun s v => covSnd (I := I) g f V s v) 0 t +
      curvDerivAlong (I := I) g (fun s : Real => f s t)
        (fun s : Real => V s t)
        (fun s : Real => varSnd (I := I) f s t)
        (fun s : Real => varSnd (I := I) f s t) 0 +
      curvAlong (I := I) g (fun v : Real => f 0 v)
        (fun v : Real => V 0 v)
        (fun v : Real =>
          covSnd (I := I) g f
            (fun s w => varFst (I := I) f s w) 0 v)
        (fun v : Real => varSnd (I := I) f 0 v) t +
      curvAlong (I := I) g (fun v : Real => f 0 v)
        (fun v : Real => V 0 v)
        (fun v : Real => varSnd (I := I) f 0 v)
        (fun v : Real =>
          covSnd (I := I) g f
            (fun s w => varFst (I := I) f s w) 0 v) t)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem cov_curvAlong
    (g : SmoothRiemannianMetric I M) (γ : Real → M)
    (X Y Z : ∀ s : Real, TangentSpace I (γ s)) (t : Real) :
    covDerivAlong (I := I) g γ
        (fun s : Real => curvAlong (I := I) g γ X Y Z s) t =
      curvDerivAlong (I := I) g γ X Y Z t +
        curvAlong (I := I) g γ
          (fun s : Real => covDerivAlong (I := I) g γ X s) Y Z t +
        curvAlong (I := I) g γ X
          (fun s : Real => covDerivAlong (I := I) g γ Y s) Z t +
        curvAlong (I := I) g γ X Y
          (fun s : Real => covDerivAlong (I := I) g γ Z s) t := by
  unfold curvDerivAlong
  abel

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem curvAlong_smooth
    (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (X Y Z : ∀ s, TangentSpace I (γ s))
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hX : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (X s) : TangentBundle I M)))
    (hY : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Y s) : TangentBundle I M)))
    (hZ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Z s) : TangentBundle I M))) :
    ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (curvAlong (I := I) g γ X Y Z s) : TangentBundle I M)) := by
  letI : NormedAddCommGroup (E →L[Real] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] E) :=
    ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (E →L[Real] E →L[Real] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] E →L[Real] E) :=
    ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (E →L[Real] E →L[Real] E →L[Real] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] E →L[Real] E →L[Real] E) :=
    ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (E × (E →L[Real] E)) :=
    Prod.normedAddCommGroup
  letI : NormedSpace Real (E × (E →L[Real] E)) :=
    Prod.normedSpace
  letI : NormedAddCommGroup (E × (E →L[Real] E →L[Real] E)) :=
    Prod.normedAddCommGroup
  letI : NormedSpace Real (E × (E →L[Real] E →L[Real] E)) :=
    Prod.normedSpace
  letI : NormedAddCommGroup
      (E × (E →L[Real] E →L[Real] E →L[Real] E)) :=
    Prod.normedAddCommGroup
  letI : NormedSpace Real
      (E × (E →L[Real] E →L[Real] E →L[Real] E)) :=
    Prod.normedSpace
  have hR0 :=
    (riemannOp_section_contMDiff (I := I) (M := M) g).comp hγ
  have hR1 :=
    ContMDiff.clm_bundle_apply
      (F₁ := E) (F₂ := E →L[Real] E →L[Real] E)
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M =>
        TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
      (b := γ)
      (ϕ := fun s =>
        riemannOp (LeviCivita (I := I) g) (γ s))
      (v := X) hR0 hX
  have hR2 :=
    ContMDiff.clm_bundle_apply
      (F₁ := E) (F₂ := E →L[Real] E)
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[Real] TangentSpace I x)
      (b := γ)
      (ϕ := fun s => (riemannOp (LeviCivita (I := I) g) (γ s)) (X s))
      (v := Y) hR1 hY
  have hR3 :=
    ContMDiff.clm_bundle_apply
      (F₁ := E) (F₂ := E)
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x)
      (b := γ)
      (ϕ := fun s =>
        (riemannOp (LeviCivita (I := I) g) (γ s)) (X s) (Y s))
      (v := Z) hR2 hZ
  simpa only [curvAlong] using hR3

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem jacCurv_smooth
    (g : SmoothRiemannianMetric I M) (f : Real -> Real -> M)
    (V : ∀ s t : Real, TangentSpace I (f s t))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)))
    (hT : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2) (varSnd (I := I) f q.1 q.2) : TangentBundle I M))) :
    ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f q.1 q.2) (jacCurv (I := I) g f V q.1 q.2) :
            TangentBundle I M)) := by
  letI : NormedAddCommGroup (E →L[Real] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] E) :=
    ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (E →L[Real] E →L[Real] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] E →L[Real] E) :=
    ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (E →L[Real] E →L[Real] E →L[Real] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] E →L[Real] E →L[Real] E) :=
    ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (E × (E →L[Real] E)) :=
    Prod.normedAddCommGroup
  letI : NormedSpace Real (E × (E →L[Real] E)) :=
    Prod.normedSpace
  letI : NormedAddCommGroup (E × (E →L[Real] E →L[Real] E)) :=
    Prod.normedAddCommGroup
  letI : NormedSpace Real (E × (E →L[Real] E →L[Real] E)) :=
    Prod.normedSpace
  letI : NormedAddCommGroup
      (E × (E →L[Real] E →L[Real] E →L[Real] E)) :=
    Prod.normedAddCommGroup
  letI : NormedSpace Real
      (E × (E →L[Real] E →L[Real] E →L[Real] E)) :=
    Prod.normedSpace
  let F : Real × Real -> M := fun q => f q.1 q.2
  let T : ∀ q : Real × Real, TangentSpace I (F q) :=
    fun q => varSnd (I := I) f q.1 q.2
  have hF :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I ∞ F := by
    intro q
    exact (Bundle.contMDiffAt_totalSpace.mp hV.contMDiffAt).1
  have hR0 :=
    (riemannOp_section_contMDiff (I := I) (M := M) g).comp hF
  have hR1 :=
    ContMDiff.clm_bundle_apply
      (F₁ := E) (F₂ := E →L[Real] E →L[Real] E)
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M =>
        TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
      (b := F)
      (ϕ := fun q =>
        riemannOp (LeviCivita (I := I) g) (F q))
      (v := fun q => V q.1 q.2) hR0 hV
  have hR2 :=
    ContMDiff.clm_bundle_apply
      (F₁ := E) (F₂ := E →L[Real] E)
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[Real] TangentSpace I x)
      (b := F)
      (ϕ := fun q =>
        (riemannOp (LeviCivita (I := I) g) (F q)) (V q.1 q.2))
      (v := T) hR1 hT
  have hR3 :=
    ContMDiff.clm_bundle_apply
      (F₁ := E) (F₂ := E)
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x)
      (b := F)
      (ϕ := fun q =>
        (riemannOp (LeviCivita (I := I) g) (F q))
          (V q.1 q.2) (T q))
      (v := T) hR2 hT
  simpa only [F, T, jacCurv, curvAlong] using hR3

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem curvDeriv_smul_left
    (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (f : Real -> Real) (X Y Z : ∀ s, TangentSpace I (γ s)) (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hf : DifferentiableAt Real f t)
    (hX : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (X s) : TangentBundle I M)))
    (hY : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Y s) : TangentBundle I M)))
    (hZ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Z s) : TangentBundle I M))) :
    curvDerivAlong (I := I) g γ (fun s => f s • X s) Y Z t =
      f t • curvDerivAlong (I := I) g γ X Y Z t := by
  have hXdiff := chartRep_diff (I := I) γ X hX t
  have hRsm := curvAlong_smooth (I := I) g γ X Y Z hγ hX hY hZ
  have hRdiff :=
    chartRep_diff (I := I) γ
      (fun s => curvAlong (I := I) g γ X Y Z s) hRsm t
  have hlead :
      (fun s : Real =>
        curvAlong (I := I) g γ (fun r => f r • X r) Y Z s) =
        fun s : Real => f s • curvAlong (I := I) g γ X Y Z s := by
    funext s
    simp only [curvAlong, map_smul, ContinuousLinearMap.smul_apply]
  unfold curvDerivAlong
  rw [hlead]
  rw [covDerivAlong_smulFun (I := I) g γ f
    (fun s => curvAlong (I := I) g γ X Y Z s) t
    hf hRdiff]
  unfold curvAlong
  simp only
  rw [covDerivAlong_smulFun (I := I) g γ f X t
    hf hXdiff]
  simp only [map_add, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  module

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem curvDeriv_smul_mid
    (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (f : Real -> Real) (X Y Z : ∀ s, TangentSpace I (γ s)) (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hf : DifferentiableAt Real f t)
    (hX : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (X s) : TangentBundle I M)))
    (hY : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Y s) : TangentBundle I M)))
    (hZ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Z s) : TangentBundle I M))) :
    curvDerivAlong (I := I) g γ X (fun s => f s • Y s) Z t =
      f t • curvDerivAlong (I := I) g γ X Y Z t := by
  have hYdiff := chartRep_diff (I := I) γ Y hY t
  have hRsm := curvAlong_smooth (I := I) g γ X Y Z hγ hX hY hZ
  have hRdiff :=
    chartRep_diff (I := I) γ
      (fun s => curvAlong (I := I) g γ X Y Z s) hRsm t
  have hlead :
      (fun s : Real =>
        curvAlong (I := I) g γ X (fun r => f r • Y r) Z s) =
        fun s : Real => f s • curvAlong (I := I) g γ X Y Z s := by
    funext s
    simp only [curvAlong, map_smul, ContinuousLinearMap.smul_apply]
  unfold curvDerivAlong
  rw [hlead]
  rw [covDerivAlong_smulFun (I := I) g γ f
    (fun s => curvAlong (I := I) g γ X Y Z s) t
    hf hRdiff]
  unfold curvAlong
  simp only
  rw [covDerivAlong_smulFun (I := I) g γ f Y t
    hf hYdiff]
  simp only [map_add, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  module

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem curvDeriv_smul_right
    (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (f : Real -> Real) (X Y Z : ∀ s, TangentSpace I (γ s)) (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hf : DifferentiableAt Real f t)
    (hX : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (X s) : TangentBundle I M)))
    (hY : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Y s) : TangentBundle I M)))
    (hZ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Z s) : TangentBundle I M))) :
    curvDerivAlong (I := I) g γ X Y (fun s => f s • Z s) t =
      f t • curvDerivAlong (I := I) g γ X Y Z t := by
  have hZdiff := chartRep_diff (I := I) γ Z hZ t
  have hRsm := curvAlong_smooth (I := I) g γ X Y Z hγ hX hY hZ
  have hRdiff :=
    chartRep_diff (I := I) γ
      (fun s => curvAlong (I := I) g γ X Y Z s) hRsm t
  have hlead :
      (fun s : Real =>
        curvAlong (I := I) g γ X Y (fun r => f r • Z r) s) =
        fun s : Real => f s • curvAlong (I := I) g γ X Y Z s := by
    funext s
    simp only [curvAlong, map_smul]
  unfold curvDerivAlong
  rw [hlead]
  rw [covDerivAlong_smulFun (I := I) g γ f
    (fun s => curvAlong (I := I) g γ X Y Z s) t
    hf hRdiff]
  unfold curvAlong
  simp only
  rw [covDerivAlong_smulFun (I := I) g γ f Z t
    hf hZdiff]
  simp only [map_add, map_smul]
  module

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem curvDeriv_add_left
    (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (X X' Y Z : ∀ s, TangentSpace I (γ s)) (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hX : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (X s) : TangentBundle I M)))
    (hX' : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (X' s) : TangentBundle I M)))
    (hY : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Y s) : TangentBundle I M)))
    (hZ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Z s) : TangentBundle I M))) :
    curvDerivAlong (I := I) g γ (fun s => X s + X' s) Y Z t =
      curvDerivAlong (I := I) g γ X Y Z t +
        curvDerivAlong (I := I) g γ X' Y Z t := by
  have hXdiff := chartRep_diff (I := I) γ X hX t
  have hX'diff := chartRep_diff (I := I) γ X' hX' t
  have hRsm := curvAlong_smooth (I := I) g γ X Y Z hγ hX hY hZ
  have hRsm' := curvAlong_smooth (I := I) g γ X' Y Z hγ hX' hY hZ
  have hRdiff :=
    chartRep_diff (I := I) γ
      (fun s => curvAlong (I := I) g γ X Y Z s) hRsm t
  have hRdiff' :=
    chartRep_diff (I := I) γ
      (fun s => curvAlong (I := I) g γ X' Y Z s) hRsm' t
  have hlead :
      (fun s : Real =>
        curvAlong (I := I) g γ (fun r => X r + X' r) Y Z s) =
        fun s : Real =>
          curvAlong (I := I) g γ X Y Z s +
            curvAlong (I := I) g γ X' Y Z s := by
    funext s
    simp only [curvAlong, map_add, ContinuousLinearMap.add_apply]
  unfold curvDerivAlong
  rw [hlead]
  rw [covDerivAlong_add (I := I) g γ
    (fun s => curvAlong (I := I) g γ X Y Z s)
    (fun s => curvAlong (I := I) g γ X' Y Z s) t hRdiff hRdiff']
  unfold curvAlong
  simp only
  rw [covDerivAlong_add (I := I) g γ X X' t hXdiff hX'diff]
  simp only [map_add, ContinuousLinearMap.add_apply]
  abel

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem curvDeriv_add_mid
    (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (X Y Y' Z : ∀ s, TangentSpace I (γ s)) (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hX : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (X s) : TangentBundle I M)))
    (hY : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Y s) : TangentBundle I M)))
    (hY' : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Y' s) : TangentBundle I M)))
    (hZ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Z s) : TangentBundle I M))) :
    curvDerivAlong (I := I) g γ X (fun s => Y s + Y' s) Z t =
      curvDerivAlong (I := I) g γ X Y Z t +
        curvDerivAlong (I := I) g γ X Y' Z t := by
  have hYdiff := chartRep_diff (I := I) γ Y hY t
  have hY'diff := chartRep_diff (I := I) γ Y' hY' t
  have hRsm := curvAlong_smooth (I := I) g γ X Y Z hγ hX hY hZ
  have hRsm' := curvAlong_smooth (I := I) g γ X Y' Z hγ hX hY' hZ
  have hRdiff :=
    chartRep_diff (I := I) γ
      (fun s => curvAlong (I := I) g γ X Y Z s) hRsm t
  have hRdiff' :=
    chartRep_diff (I := I) γ
      (fun s => curvAlong (I := I) g γ X Y' Z s) hRsm' t
  have hlead :
      (fun s : Real =>
        curvAlong (I := I) g γ X (fun r => Y r + Y' r) Z s) =
        fun s : Real =>
          curvAlong (I := I) g γ X Y Z s +
            curvAlong (I := I) g γ X Y' Z s := by
    funext s
    simp only [curvAlong, map_add, ContinuousLinearMap.add_apply]
  unfold curvDerivAlong
  rw [hlead]
  rw [covDerivAlong_add (I := I) g γ
    (fun s => curvAlong (I := I) g γ X Y Z s)
    (fun s => curvAlong (I := I) g γ X Y' Z s) t hRdiff hRdiff']
  unfold curvAlong
  simp only
  rw [covDerivAlong_add (I := I) g γ Y Y' t hYdiff hY'diff]
  simp only [map_add, ContinuousLinearMap.add_apply]
  abel

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem curvDeriv_add_right
    (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (X Y Z Z' : ∀ s, TangentSpace I (γ s)) (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hX : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (X s) : TangentBundle I M)))
    (hY : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Y s) : TangentBundle I M)))
    (hZ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Z s) : TangentBundle I M)))
    (hZ' : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Z' s) : TangentBundle I M))) :
    curvDerivAlong (I := I) g γ X Y (fun s => Z s + Z' s) t =
      curvDerivAlong (I := I) g γ X Y Z t +
        curvDerivAlong (I := I) g γ X Y Z' t := by
  have hZdiff := chartRep_diff (I := I) γ Z hZ t
  have hZ'diff := chartRep_diff (I := I) γ Z' hZ' t
  have hRsm := curvAlong_smooth (I := I) g γ X Y Z hγ hX hY hZ
  have hRsm' := curvAlong_smooth (I := I) g γ X Y Z' hγ hX hY hZ'
  have hRdiff :=
    chartRep_diff (I := I) γ
      (fun s => curvAlong (I := I) g γ X Y Z s) hRsm t
  have hRdiff' :=
    chartRep_diff (I := I) γ
      (fun s => curvAlong (I := I) g γ X Y Z' s) hRsm' t
  have hlead :
      (fun s : Real =>
        curvAlong (I := I) g γ X Y (fun r => Z r + Z' r) s) =
        fun s : Real =>
          curvAlong (I := I) g γ X Y Z s +
            curvAlong (I := I) g γ X Y Z' s := by
    funext s
    simp only [curvAlong, map_add]
  unfold curvDerivAlong
  rw [hlead]
  rw [covDerivAlong_add (I := I) g γ
    (fun s => curvAlong (I := I) g γ X Y Z s)
    (fun s => curvAlong (I := I) g γ X Y Z' s) t hRdiff hRdiff']
  unfold curvAlong
  simp only
  rw [covDerivAlong_add (I := I) g γ Z Z' t hZdiff hZ'diff]
  simp only [map_add]
  abel

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem curvDeriv_congr
    (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    {X X' Y Y' Z Z' : ∀ s, TangentSpace I (γ s)} {t : Real}
    (hX : X =ᶠ[𝓝 t] X') (hY : Y =ᶠ[𝓝 t] Y') (hZ : Z =ᶠ[𝓝 t] Z') :
    curvDerivAlong (I := I) g γ X Y Z t =
      curvDerivAlong (I := I) g γ X' Y' Z' t := by
  have hR :
      (fun s => curvAlong (I := I) g γ X Y Z s) =ᶠ[𝓝 t]
        fun s => curvAlong (I := I) g γ X' Y' Z' s := by
    filter_upwards [hX, hY, hZ] with s hXs hYs hZs
    simp only [curvAlong]
    rw [hXs, hYs, hZs]
  have hDX :=
    covDerivAlong_congr_of_eventuallyEq (I := I) g γ hX
  have hDY :=
    covDerivAlong_congr_of_eventuallyEq (I := I) g γ hY
  have hDZ :=
    covDerivAlong_congr_of_eventuallyEq (I := I) g γ hZ
  have hXt : X t = X' t := hX.self_of_nhds
  have hYt : Y t = Y' t := hY.self_of_nhds
  have hZt : Z t = Z' t := hZ.self_of_nhds
  unfold curvDerivAlong
  rw [covDerivAlong_congr_of_eventuallyEq (I := I) g γ hR]
  unfold curvAlong
  simp only
  rw [hDX, hDY, hDZ, hXt, hYt, hZt]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem curvDeriv_sum_left
    {ι : Type*} (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (s : Finset ι) (X : ι -> ∀ u, TangentSpace I (γ u))
    (Y Z : ∀ u, TangentSpace I (γ u)) (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hX : ∀ i ∈ s, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun u : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ u) (X i u) : TangentBundle I M)))
    (hY : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun u : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ u) (Y u) : TangentBundle I M)))
    (hZ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun u : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ u) (Z u) : TangentBundle I M))) :
    curvDerivAlong (I := I) g γ (fun u => ∑ i ∈ s, X i u) Y Z t =
      ∑ i ∈ s, curvDerivAlong (I := I) g γ (X i) Y Z t := by
  classical
  letI (u : Real) : NormedAddCommGroup
      (TangentSpace I (γ u) →L[Real] TangentSpace I (γ u)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI (u : Real) : NormedSpace Real
      (TangentSpace I (γ u) →L[Real] TangentSpace I (γ u)) :=
    ContinuousLinearMap.toNormedSpace
  letI (u : Real) : NormedAddCommGroup
      (TangentSpace I (γ u) →L[Real]
        TangentSpace I (γ u) →L[Real] TangentSpace I (γ u)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI (u : Real) : NormedSpace Real
      (TangentSpace I (γ u) →L[Real]
        TangentSpace I (γ u) →L[Real] TangentSpace I (γ u)) :=
    ContinuousLinearMap.toNormedSpace
  have hXdiff :
      ∀ i ∈ s, DifferentiableAt Real (chartRepAt (I := I) γ (X i) t) t :=
    fun i hi => chartRep_diff (I := I) γ (X i) (hX i hi) t
  have hRdiff :
      ∀ i ∈ s, DifferentiableAt Real
        (chartRepAt (I := I) γ
          (fun u => curvAlong (I := I) g γ (X i) Y Z u) t) t := by
    intro i hi
    exact chartRep_diff (I := I) γ
      (fun u => curvAlong (I := I) g γ (X i) Y Z u)
      (curvAlong_smooth (I := I) g γ (X i) Y Z hγ (hX i hi) hY hZ) t
  have hlead :
      (fun u : Real =>
        curvAlong (I := I) g γ (fun v => ∑ i ∈ s, X i v) Y Z u) =
        fun u : Real => ∑ i ∈ s, curvAlong (I := I) g γ (X i) Y Z u := by
    funext u
    simp only [curvAlong, map_sum, ContinuousLinearMap.sum_apply]
  unfold curvDerivAlong
  rw [hlead]
  rw [covDerivAlong_sum (I := I) g γ s
    (fun i u => curvAlong (I := I) g γ (X i) Y Z u) t hRdiff]
  unfold curvAlong
  simp only
  rw [covDerivAlong_sum (I := I) g γ s X t hXdiff]
  simp only [map_sum, ContinuousLinearMap.sum_apply,
    Finset.sum_sub_distrib]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem curvDeriv_sum_mid
    {ι : Type*} (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (s : Finset ι) (X : ∀ u, TangentSpace I (γ u))
    (Y : ι -> ∀ u, TangentSpace I (γ u))
    (Z : ∀ u, TangentSpace I (γ u)) (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hX : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun u : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ u) (X u) : TangentBundle I M)))
    (hY : ∀ i ∈ s, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun u : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ u) (Y i u) : TangentBundle I M)))
    (hZ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun u : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ u) (Z u) : TangentBundle I M))) :
    curvDerivAlong (I := I) g γ X (fun u => ∑ i ∈ s, Y i u) Z t =
      ∑ i ∈ s, curvDerivAlong (I := I) g γ X (Y i) Z t := by
  classical
  letI (u : Real) : NormedAddCommGroup
      (TangentSpace I (γ u) →L[Real] TangentSpace I (γ u)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI (u : Real) : NormedSpace Real
      (TangentSpace I (γ u) →L[Real] TangentSpace I (γ u)) :=
    ContinuousLinearMap.toNormedSpace
  have hYdiff :
      ∀ i ∈ s, DifferentiableAt Real (chartRepAt (I := I) γ (Y i) t) t :=
    fun i hi => chartRep_diff (I := I) γ (Y i) (hY i hi) t
  have hRdiff :
      ∀ i ∈ s, DifferentiableAt Real
        (chartRepAt (I := I) γ
          (fun u => curvAlong (I := I) g γ X (Y i) Z u) t) t := by
    intro i hi
    exact chartRep_diff (I := I) γ
      (fun u => curvAlong (I := I) g γ X (Y i) Z u)
      (curvAlong_smooth (I := I) g γ X (Y i) Z hγ hX (hY i hi) hZ) t
  have hlead :
      (fun u : Real =>
        curvAlong (I := I) g γ X (fun v => ∑ i ∈ s, Y i v) Z u) =
        fun u : Real => ∑ i ∈ s, curvAlong (I := I) g γ X (Y i) Z u := by
    funext u
    simp only [curvAlong, map_sum, ContinuousLinearMap.sum_apply]
  unfold curvDerivAlong
  rw [hlead]
  rw [covDerivAlong_sum (I := I) g γ s
    (fun i u => curvAlong (I := I) g γ X (Y i) Z u) t hRdiff]
  unfold curvAlong
  simp only
  rw [covDerivAlong_sum (I := I) g γ s Y t hYdiff]
  simp only [map_sum, ContinuousLinearMap.sum_apply,
    Finset.sum_sub_distrib]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem curvDeriv_sum_right
    {ι : Type*} (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (s : Finset ι) (X Y : ∀ u, TangentSpace I (γ u))
    (Z : ι -> ∀ u, TangentSpace I (γ u)) (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hX : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun u : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ u) (X u) : TangentBundle I M)))
    (hY : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun u : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ u) (Y u) : TangentBundle I M)))
    (hZ : ∀ i ∈ s, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun u : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ u) (Z i u) : TangentBundle I M))) :
    curvDerivAlong (I := I) g γ X Y (fun u => ∑ i ∈ s, Z i u) t =
      ∑ i ∈ s, curvDerivAlong (I := I) g γ X Y (Z i) t := by
  classical
  have hZdiff :
      ∀ i ∈ s, DifferentiableAt Real (chartRepAt (I := I) γ (Z i) t) t :=
    fun i hi => chartRep_diff (I := I) γ (Z i) (hZ i hi) t
  have hRdiff :
      ∀ i ∈ s, DifferentiableAt Real
        (chartRepAt (I := I) γ
          (fun u => curvAlong (I := I) g γ X Y (Z i) u) t) t := by
    intro i hi
    exact chartRep_diff (I := I) γ
      (fun u => curvAlong (I := I) g γ X Y (Z i) u)
      (curvAlong_smooth (I := I) g γ X Y (Z i) hγ hX hY (hZ i hi)) t
  have hlead :
      (fun u : Real =>
        curvAlong (I := I) g γ X Y (fun v => ∑ i ∈ s, Z i v) u) =
        fun u : Real => ∑ i ∈ s, curvAlong (I := I) g γ X Y (Z i) u := by
    funext u
    simp only [curvAlong, map_sum]
  unfold curvDerivAlong
  rw [hlead]
  rw [covDerivAlong_sum (I := I) g γ s
    (fun i u => curvAlong (I := I) g γ X Y (Z i) u) t hRdiff]
  unfold curvAlong
  simp only
  rw [covDerivAlong_sum (I := I) g γ s Z t hZdiff]
  simp only [map_sum, Finset.sum_sub_distrib]

omit [InnerProductSpace ℝ E] [T2Space M] [SigmaCompactSpace M] in
private lemma covDeriv_coord
    {n : WithTop ℕ∞} [ENat.LEInfty n] (hn : n ≠ 0)
    (g : SmoothRiemannianMetric I M) (γ : Real → M)
    (V : ∀ s, TangentSpace I (γ s)) (t : Real) (β : M)
    (hγ : ContMDiff (modelWithCornersSelf Real Real) I n γ)
    (hβ : γ t ∈ (chartAt H β).source)
    (hV : DifferentiableAt Real (chartRepAt (I := I) γ V t) t) :
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt Real (γ t)
        (covDerivAlong (I := I) g γ V t) =
      chartCovDerivAlong (I := I) g β γ
        (chartRepAtBase (I := I) β γ V) t := by
  have hinv :=
    covDerivAlong_chart_foot_invariance
      (I := I) hn g γ V t β hγ hβ hV
  rw [← hinv]
  have hmem :
      γ t ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hβ
  exact
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt_symmL
      (R := Real) hmem _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma fieldCoord_contDiffAt
    (f : Real × Real → M)
    (V : ∀ q : Real × Real, TangentSpace I (f q))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q) (V q) : TangentBundle I M)))
    (q₀ : Real × Real) :
    ContDiffAt Real ∞
      (fun q : Real × Real =>
        (trivializationAt E (TangentSpace I) (f q₀)).continuousLinearMapAt
          Real (f q) (V q))
      q₀ := by
  let S : Real × Real → TangentBundle I M := fun q =>
    TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (f q) (V q)
  have hAt :
      ContMDiffAt
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞ S q₀ := by
    simpa only [S] using hV.contMDiffAt
  rw [Bundle.contMDiffAt_totalSpace] at hAt
  have hbase := hAt.1
  have hfiber := hAt.2
  have hmem :
      f q₀ ∈ (trivializationAt E (TangentSpace I) (f q₀)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (f q₀)
  have hpre :
      f ⁻¹' (trivializationAt E (TangentSpace I) (f q₀)).baseSet ∈ 𝓝 q₀ :=
    hbase.continuousAt.preimage_mem_nhds
      ((trivializationAt E (TangentSpace I) (f q₀)).open_baseSet.mem_nhds hmem)
  have heq :
      (fun q : Real × Real =>
        ((trivializationAt E (TangentSpace I) (f q₀)) (S q)).2)
        =ᶠ[𝓝 q₀]
      fun q : Real × Real =>
        (trivializationAt E (TangentSpace I) (f q₀)).continuousLinearMapAt
          Real (f q) (V q) := by
    filter_upwards [hpre] with q hq
    simp only [S, TotalSpace.mk']
    rw [(trivializationAt E (TangentSpace I) (f q₀)).continuousLinearMapAt_apply
      (R := Real)]
    rw [(trivializationAt E (TangentSpace I) (f q₀)).coe_linearMapAt_of_mem hq]
  have hfiber' := hfiber.congr_of_eventuallyEq heq.symm
  rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
    ← chartedSpaceSelf_prod]
  exact hfiber'

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartRep_snd_diff
    (f : Real → Real → M)
    (V : ∀ s t : Real, TangentSpace I (f s t))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)))
    (s t : Real) :
    DifferentiableAt Real
      (chartRepAt (I := I) (fun v : Real => f s v)
        (fun v : Real => V s v) t) t := by
  have hcoord :=
    fieldCoord_contDiffAt (I := I)
      (fun q : Real × Real => f q.1 q.2)
      (fun q : Real × Real => V q.1 q.2) hV (s, t)
  have hincl : ContDiffAt Real ∞ (fun v : Real => (s, v)) t :=
    (contDiff_const.prodMk contDiff_id).contDiffAt
  have hs := hcoord.comp t hincl
  simpa only [chartRepAt] using hs.differentiableAt (by simp)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma gammaContr_contDiffAt
    {n : Nat}
    (g : SmoothRiemannianMetric I M) (α : M)
    (P Q R : Real × Real → E) (q₀ : Real × Real)
    (hP : ContDiffAt Real (n : WithTop ℕ∞) P q₀)
    (hQ : ContDiffAt Real (n : WithTop ℕ∞) Q q₀)
    (hR : ContDiffAt Real (n : WithTop ℕ∞) R q₀)
    (hRint : R q₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt Real (n : WithTop ℕ∞)
      (fun q : Real × Real =>
        chartChristoffelContraction (I := I) g α (P q) (Q q) (R q))
      q₀ := by
  classical
  unfold chartChristoffelContraction
  refine ContDiffAt.sum (fun k _ => ?_)
  refine (ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => ?_))).smul
    contDiffAt_const
  have hΓbase :
      ContDiffAt Real ∞
        (DifferentialGeometry.Geometry.Operator.chartChristoffel
          (I := I) g α i j k)
        (R q₀) :=
    (DifferentialGeometry.Geometry.Operator.chartChristoffel_contDiffOn_interior
      (I := I) g α i j k).contDiffAt
        (isOpen_interior.mem_nhds hRint)
  have hΓ :
      ContDiffAt Real (n : WithTop ℕ∞)
        (fun q : Real × Real =>
          DifferentialGeometry.Geometry.Operator.chartChristoffel
            (I := I) g α i j k (R q))
        q₀ :=
    (hΓbase.of_le
      (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞)).comp q₀ hR
  have hPi :
      ContDiffAt Real (n : WithTop ℕ∞)
        (fun q : Real × Real => chartCoord (E := E) i (P q)) q₀ := by
    simpa only [Function.comp_apply, chartCoordCLM_apply] using
      (chartCoordCLM (E := E) i).contDiff.contDiffAt.comp q₀ hP
  have hQj :
      ContDiffAt Real (n : WithTop ℕ∞)
        (fun q : Real × Real => chartCoord (E := E) j (Q q)) q₀ := by
    simpa only [Function.comp_apply, chartCoordCLM_apply] using
      (chartCoordCLM (E := E) j).contDiff.contDiffAt.comp q₀ hQ
  exact (hΓ.mul hPi).mul hQj

omit [InnerProductSpace ℝ E] [SigmaCompactSpace M] in
theorem cov_commute_curv
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (hf : IsSmoothVariation (I := I) f)
    (V : ∀ s t : Real, TangentSpace I (f s t)) (t : Real)
    (hV2 : ContDiffAt Real 2
      (fun q : Real × Real =>
        (trivializationAt E (TangentSpace I) (f 0 t)).continuousLinearMapAt
          Real (f q.1 q.2) (V q.1 q.2))
      (0, t))
    (hinnerL : ∀ s : Real, DifferentiableAt Real
      (chartRepAt (I := I) (fun v : Real => f s v)
        (fun v : Real => V s v) t) t)
    (hinnerR : ∀ v : Real, DifferentiableAt Real
      (chartRepAt (I := I) (fun s : Real => f s v)
        (fun s : Real => V s v) 0) 0)
    (houterL : DifferentiableAt Real
      (chartRepAt (I := I) (fun s : Real => f s t)
        (fun s : Real =>
          covDerivAlong (I := I) g (fun v : Real => f s v)
            (fun v : Real => V s v) t) 0) 0)
    (houterR : DifferentiableAt Real
      (chartRepAt (I := I) (fun v : Real => f 0 v)
        (fun v : Real =>
          covDerivAlong (I := I) g (fun s : Real => f s v)
            (fun s : Real => V s v) 0) t) t) :
    covDerivAlong (I := I) g (fun s : Real => f s t)
        (fun s : Real =>
          covDerivAlong (I := I) g (fun v : Real => f s v)
            (fun v : Real => V s v) t) 0 -
      covDerivAlong (I := I) g (fun v : Real => f 0 v)
        (fun v : Real =>
          covDerivAlong (I := I) g (fun s : Real => f s v)
            (fun s : Real => V s v) 0) t =
      (DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
        (f 0 t))
        (mfderiv (modelWithCornersSelf Real Real) I
          (fun s : Real => f s t) 0 (1 : Real))
        (mfderiv (modelWithCornersSelf Real Real) I
          (fun v : Real => f 0 v) t (1 : Real))
        (V 0 t) := by
  classical
  set β : M := f 0 t with hβ
  set Y : Real → Real → E := fun s v =>
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt
      Real (f s v) (V s v) with hY
  have hY2 :
      ContDiffAt Real 2 (fun q : Real × Real => Y q.1 q.2) (0, t) := by
    simpa only [Y, β] using hV2
  have hfixed :=
    chartCovDerivAlong_commutator_eq_riemannOp_on_variation
      (I := I) g f hf Y 0 t hY2
  have hsliceL : ∀ s : Real,
      ContMDiff (modelWithCornersSelf Real Real) I (8 : Nat)
        (fun v : Real => f s v) := by
    intro s
    have hincl : ContMDiff
        (modelWithCornersSelf Real Real)
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        (8 : Nat) (fun v : Real => (s, v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hsliceR : ∀ v : Real,
      ContMDiff (modelWithCornersSelf Real Real) I (8 : Nat)
        (fun s : Real => f s v) := by
    intro v
    have hincl : ContMDiff
        (modelWithCornersSelf Real Real)
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        (8 : Nat) (fun s : Real => (s, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have htransverse : ContMDiff
      (modelWithCornersSelf Real Real) I (8 : Nat)
      (fun s : Real => f s t) :=
    hsliceR t
  have hcentral : ContMDiff
      (modelWithCornersSelf Real Real) I (8 : Nat)
      (fun v : Real => f 0 v) :=
    hsliceL 0
  have hsrcβ : f 0 t ∈ (chartAt H β).source := by
    rw [hβ]
    exact mem_chart_source H (f 0 t)
  have hrepL : ∀ s : Real,
      chartRepAtBase (I := I) β (fun v : Real => f s v)
          (fun v : Real => V s v) =
        fun v : Real => Y s v := by
    intro s
    funext v
    rw [chartRepAtBase_apply, hY]
  have hrepR : ∀ v : Real,
      chartRepAtBase (I := I) β (fun s : Real => f s v)
          (fun s : Real => V s v) =
        fun s : Real => Y s v := by
    intro v
    funext s
    rw [chartRepAtBase_apply, hY]
  have hinnerCoordL : ∀ s : Real,
      f s t ∈ (chartAt H β).source →
        (trivializationAt E (TangentSpace I) β).continuousLinearMapAt
            Real (f s t)
            (covDerivAlong (I := I) g (fun v : Real => f s v)
              (fun v : Real => V s v) t) =
          chartCovDerivAlong (I := I) g β (fun v : Real => f s v)
            (fun v : Real => Y s v) t := by
    intro s hs
    have hcoord :=
      covDeriv_coord (I := I) (n := (8 : Nat)) (by norm_num)
        g (fun v : Real => f s v) (fun v : Real => V s v)
        t β (hsliceL s) hs (hinnerL s)
    rw [hrepL s] at hcoord
    exact hcoord
  have hinnerCoordR : ∀ v : Real,
      f 0 v ∈ (chartAt H β).source →
        (trivializationAt E (TangentSpace I) β).continuousLinearMapAt
            Real (f 0 v)
            (covDerivAlong (I := I) g (fun s : Real => f s v)
              (fun s : Real => V s v) 0) =
          chartCovDerivAlong (I := I) g β (fun s : Real => f s v)
            (fun s : Real => Y s v) 0 := by
    intro v hv
    have hcoord :=
      covDeriv_coord (I := I) (n := (8 : Nat)) (by norm_num)
        g (fun s : Real => f s v) (fun s : Real => V s v)
        0 β (hsliceR v) hv (hinnerR v)
    rw [hrepR v] at hcoord
    exact hcoord
  let innerL : ∀ s : Real, TangentSpace I (f s t) := fun s =>
    covDerivAlong (I := I) g (fun v : Real => f s v)
      (fun v : Real => V s v) t
  let innerR : ∀ v : Real, TangentSpace I (f 0 v) := fun v =>
    covDerivAlong (I := I) g (fun s : Real => f s v)
      (fun s : Real => V s v) 0
  have hopenL : IsOpen {s : Real | f s t ∈ (chartAt H β).source} :=
    htransverse.continuous.isOpen_preimage _
      (chartAt H β).open_source
  have hopenR : IsOpen {v : Real | f 0 v ∈ (chartAt H β).source} :=
    hcentral.continuous.isOpen_preimage _ (chartAt H β).open_source
  have hrepOuterL :
      chartRepAt (I := I) (fun s : Real => f s t) innerL 0
        =ᶠ[nhds (0 : Real)]
          fun s : Real =>
            chartCovDerivAlong (I := I) g β (fun v : Real => f s v)
              (fun v : Real => Y s v) t := by
    filter_upwards [hopenL.mem_nhds hsrcβ] with s hs
    rw [chartRepAt_apply]
    rw [← hβ]
    exact hinnerCoordL s hs
  have hrepOuterR :
      chartRepAt (I := I) (fun v : Real => f 0 v) innerR t
        =ᶠ[nhds t]
          fun v : Real =>
            chartCovDerivAlong (I := I) g β (fun s : Real => f s v)
              (fun s : Real => Y s v) 0 := by
    filter_upwards [hopenR.mem_nhds hsrcβ] with v hv
    rw [chartRepAt_apply]
    rw [← hβ]
    exact hinnerCoordR v hv
  have hbaseL :
      chartRepAtBase (I := I) β (fun s : Real => f s t) innerL =
        chartRepAt (I := I) (fun s : Real => f s t) innerL 0 := by
    rw [hβ]
    exact chartRepAtBase_foot (I := I)
      (fun s : Real => f s t) innerL 0
  have hbaseR :
      chartRepAtBase (I := I) β (fun v : Real => f 0 v) innerR =
        chartRepAt (I := I) (fun v : Real => f 0 v) innerR t := by
    rw [hβ]
    exact chartRepAtBase_foot (I := I)
      (fun v : Real => f 0 v) innerR t
  have houterCoordL :
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt
          Real (f 0 t)
          (covDerivAlong (I := I) g (fun s : Real => f s t)
            innerL 0) =
        chartCovDerivAlong (I := I) g β (fun s : Real => f s t)
          (fun s : Real =>
            chartCovDerivAlong (I := I) g β (fun v : Real => f s v)
              (fun v : Real => Y s v) t) 0 := by
    have hcoord :=
      covDeriv_coord (I := I) (n := (8 : Nat)) (by norm_num)
        g (fun s : Real => f s t) innerL 0 β htransverse hsrcβ
        houterL
    rw [hbaseL, chartCovDerivAlong_def, hrepOuterL.deriv_eq,
      hrepOuterL.eq_of_nhds] at hcoord
    exact hcoord
  have houterCoordR :
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt
          Real (f 0 t)
          (covDerivAlong (I := I) g (fun v : Real => f 0 v)
            innerR t) =
        chartCovDerivAlong (I := I) g β (fun v : Real => f 0 v)
          (fun v : Real =>
            chartCovDerivAlong (I := I) g β (fun s : Real => f s v)
              (fun s : Real => Y s v) 0) t := by
    have hcoord :=
      covDeriv_coord (I := I) (n := (8 : Nat)) (by norm_num)
        g (fun v : Real => f 0 v) innerR t β hcentral hsrcβ
        houterR
    rw [hbaseR, chartCovDerivAlong_def, hrepOuterR.deriv_eq,
      hrepOuterR.eq_of_nhds] at hcoord
    exact hcoord
  have hfootCLM : ∀ x : TangentSpace I (f 0 t),
      (trivializationAt E (TangentSpace I) (f 0 t)).continuousLinearMapAt
          Real (f 0 t) x = x := by
    intro x
    have hsrc : f 0 t ∈ (chartAt H (f 0 t)).source :=
      mem_chart_source H (f 0 t)
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (I := I) hsrc]
    exact (tangentBundleCore I M).coordChange_self
      (achart H (f 0 t)) (f 0 t) (mem_achart_source H (f 0 t)) x
  rw [hβ, hfootCLM] at houterCoordL houterCoordR
  have hslotL :
      fderiv Real (fun s : Real => extChartAt I (f 0 t) (f s t))
          0 (1 : Real) =
        (mfderiv (modelWithCornersSelf Real Real) I
          (fun s : Real => f s t) 0 (1 : Real) : E) := by
    have hbridge :=
      MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := I) (M := M) (γ := fun s : Real => f s t)
        (htransverse.mdifferentiableAt (by norm_num))
        (f 0 t) (mem_chart_source H (f 0 t))
    have hcomp :
        (extChartAt I (f 0 t) ∘ fun s : Real => f s t) =
          fun s : Real => extChartAt I (f 0 t) (f s t) :=
      rfl
    rw [hcomp, hfootCLM] at hbridge
    exact hbridge.symm
  have hslotR :
      fderiv Real (fun v : Real => extChartAt I (f 0 t) (f 0 v))
          t (1 : Real) =
        (mfderiv (modelWithCornersSelf Real Real) I
          (fun v : Real => f 0 v) t (1 : Real) : E) := by
    have hbridge :=
      MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := I) (M := M) (γ := fun v : Real => f 0 v)
        (hcentral.mdifferentiableAt (by norm_num))
        (f 0 t) (mem_chart_source H (f 0 t))
    have hcomp :
        (extChartAt I (f 0 t) ∘ fun v : Real => f 0 v) =
          fun v : Real => extChartAt I (f 0 t) (f 0 v) :=
      rfl
    rw [hcomp, hfootCLM] at hbridge
    exact hbridge.symm
  have hYft : Y 0 t = V 0 t := by
    rw [hY]
    change
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt
          Real (f 0 t) (V 0 t) = V 0 t
    rw [hβ]
    exact hfootCLM (V 0 t)
  rw [hslotL, hslotR, hYft] at hfixed
  change
    covDerivAlong (I := I) g (fun s : Real => f s t) innerL 0 -
      covDerivAlong (I := I) g (fun v : Real => f 0 v) innerR t = _
  rw [houterCoordL, houterCoordR]
  exact hfixed

omit [InnerProductSpace ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem cov_snd_smooth
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (V : ∀ s t : Real, TangentSpace I (f s t))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M))) :
    ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2)
          (covDerivAlong (I := I) g (fun v : Real => f q.1 v)
            (fun v : Real => V q.1 v) q.2) : TangentBundle I M)) := by
  classical
  let F : Real × Real → M := fun q => f q.1 q.2
  let W : ∀ q : Real × Real, TangentSpace I (F q) :=
    fun q => V q.1 q.2
  have hW :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (F q) (W q) : TangentBundle I M)) := by
    simpa only [F, W] using hV
  have hF :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I ∞ F := by
    intro q
    exact (Bundle.contMDiffAt_totalSpace.mp hW.contMDiffAt).1
  rw [contMDiff_infty]
  intro n q₀
  set β : M := F q₀ with hβ
  let Y : Real × Real → E := fun q =>
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt
      Real (F q) (W q)
  let U : Real × Real → E := fun q => extChartAt I β (F q)
  let dY : Real × Real → E := fun q =>
    fderiv Real (fun v : Real => Y (q.1, v)) q.2 (1 : Real)
  let dU : Real × Real → E := fun q =>
    fderiv Real (fun v : Real => U (q.1, v)) q.2 (1 : Real)
  let Z : Real × Real → E := fun q =>
    chartCovDerivAlong (I := I) g β (fun v : Real => f q.1 v)
      (fun v : Real => Y (q.1, v)) q.2
  have hYinf : ContDiffAt Real ∞ Y q₀ := by
    simpa only [Y, β] using fieldCoord_contDiffAt (I := I) F W hW q₀
  have hsrcβ : F q₀ ∈ (chartAt H β).source := by
    rw [hβ]
    exact mem_chart_source H (F q₀)
  have hUinf : ContDiffAt Real ∞ U q₀ := by
    have hext :
        ContMDiffAt I (modelWithCornersSelf Real E) ∞
          (extChartAt I β) (F q₀) :=
      contMDiffAt_extChartAt' (I := I) (n := ∞) (x := β) hsrcβ
    have hcomp := hext.comp q₀ hF.contMDiffAt
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    simpa only [U] using hcomp
  have hY3 :
      ContDiffAt Real ((n : WithTop ℕ∞) + 1)
        (Function.uncurry (fun q : Real × Real => fun v : Real => Y (q.1, v)))
        (q₀, q₀.2) := by
    have hproj :
        ContDiffAt Real ∞
          (fun z : (Real × Real) × Real => (z.1.1, z.2))
          (q₀, q₀.2) := by
      fun_prop
    have hcomp := hYinf.comp (q₀, q₀.2) hproj
    exact hcomp.of_le
      (by exact_mod_cast le_top :
        ((n : WithTop ℕ∞) + 1) ≤ ∞)
  have hU3 :
      ContDiffAt Real ((n : WithTop ℕ∞) + 1)
        (Function.uncurry (fun q : Real × Real => fun v : Real => U (q.1, v)))
        (q₀, q₀.2) := by
    have hproj :
        ContDiffAt Real ∞
          (fun z : (Real × Real) × Real => (z.1.1, z.2))
          (q₀, q₀.2) := by
      fun_prop
    have hcomp := hUinf.comp (q₀, q₀.2) hproj
    exact hcomp.of_le
      (by exact_mod_cast le_top :
        ((n : WithTop ℕ∞) + 1) ≤ ∞)
  have htime :
      ContDiffAt Real (n : WithTop ℕ∞) (fun q : Real × Real => q.2) q₀ :=
    contDiffAt_snd
  have hpartialY :
      ContDiffAt Real (n : WithTop ℕ∞)
        (fun q : Real × Real =>
          fderiv Real (fun v : Real => Y (q.1, v)) q.2)
        q₀ :=
    ContDiffAt.fderiv (𝕜 := Real)
      (f := fun q : Real × Real => fun v : Real => Y (q.1, v))
      (g := fun q : Real × Real => q.2) hY3 htime le_rfl
  have hpartialU :
      ContDiffAt Real (n : WithTop ℕ∞)
        (fun q : Real × Real =>
          fderiv Real (fun v : Real => U (q.1, v)) q.2)
        q₀ :=
    ContDiffAt.fderiv (𝕜 := Real)
      (f := fun q : Real × Real => fun v : Real => U (q.1, v))
      (g := fun q : Real × Real => q.2) hU3 htime le_rfl
  have hdY : ContDiffAt Real (n : WithTop ℕ∞) dY q₀ := by
    have heval :=
      (ContinuousLinearMap.apply Real E (1 : Real)).contDiff.contDiffAt.comp
        q₀ hpartialY
    simpa only [dY, Function.comp_apply] using heval
  have hdU : ContDiffAt Real (n : WithTop ℕ∞) dU q₀ := by
    have heval :=
      (ContinuousLinearMap.apply Real E (1 : Real)).contDiff.contDiffAt.comp
        q₀ hpartialU
    simpa only [dU, Function.comp_apply] using heval
  have hUint : U q₀ ∈ interior (extChartAt I β).target := by
    have htarget :
        extChartAt I β (F q₀) ∈ (extChartAt I β).target :=
      (extChartAt I β).map_source
        (by
          rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
            (I := I)]
          exact hsrcβ)
    rw [(isOpen_extChartAt_target (I := I) β).interior_eq]
    simpa only [U] using htarget
  have hGamma :
      ContDiffAt Real (n : WithTop ℕ∞)
        (fun q : Real × Real =>
          chartChristoffelContraction (I := I) g β
            (dU q) (Y q) (U q))
        q₀ :=
    gammaContr_contDiffAt (I := I) (n := n) g β dU Y U q₀ hdU
      (hYinf.of_le
        (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞))
      (hUinf.of_le
        (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞))
      hUint
  have hZ : ContDiffAt Real (n : WithTop ℕ∞) Z q₀ := by
    have hadd := hdY.add hGamma
    simpa only [Z, dY, dU, chartCovDerivAlong_def, chartCurve_def,
      fderiv_apply_one_eq_deriv] using hadd
  have hslice : ∀ s : Real,
      ContMDiff (modelWithCornersSelf Real Real) I (8 : Nat)
        (fun v : Real => f s v) := by
    intro s
    have hincl : ContMDiff
        (modelWithCornersSelf Real Real)
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        ∞ (fun v : Real => (s, v)) :=
      contMDiff_const.prodMk contMDiff_id
    have h8le : ((8 : Nat) : WithTop ℕ∞) ≤ ∞ := by
      show ((8 : Nat) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr (le_top : ((8 : Nat) : ℕ∞) ≤ ⊤)
    exact (hF.comp hincl).of_le h8le
  have hinner : ∀ q : Real × Real, DifferentiableAt Real
      (chartRepAt (I := I) (fun v : Real => f q.1 v)
        (fun v : Real => V q.1 v) q.2) q.2 := by
    intro q
    have hcoord := fieldCoord_contDiffAt (I := I) F W hW q
    have hincl : ContDiffAt Real ∞ (fun v : Real => (q.1, v)) q.2 :=
      (contDiff_const.prodMk contDiff_id).contDiffAt
    have hs := hcoord.comp q.2 hincl
    simpa only [F, W, chartRepAt] using hs.differentiableAt (by simp)
  have hopen : IsOpen {q : Real × Real | F q ∈ (chartAt H β).source} :=
    hF.continuous.isOpen_preimage _ (chartAt H β).open_source
  have heq :
      (fun q : Real × Real =>
        ((trivializationAt E (TangentSpace I) β)
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (F q)
            (covDerivAlong (I := I) g (fun v : Real => f q.1 v)
              (fun v : Real => V q.1 v) q.2))).2)
        =ᶠ[𝓝 q₀] Z := by
    filter_upwards [hopen.mem_nhds hsrcβ] with q hq
    have hcoord :=
      covDeriv_coord (I := I) (n := (8 : Nat)) (by norm_num)
        g (fun v : Real => f q.1 v) (fun v : Real => V q.1 v)
        q.2 β (hslice q.1) hq (hinner q)
    have hrep :
        chartRepAtBase (I := I) β (fun v : Real => f q.1 v)
            (fun v : Real => V q.1 v) =
          fun v : Real => Y (q.1, v) := by
      funext v
      rw [chartRepAtBase_apply]
    rw [hrep] at hcoord
    have hbase :
        F q ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hq
    dsimp only [Z]
    rw [← hcoord]
    simp only [TotalSpace.mk']
    rw [(trivializationAt E (TangentSpace I) β).continuousLinearMapAt_apply
      (R := Real)]
    rw [(trivializationAt E (TangentSpace I) β).coe_linearMapAt_of_mem hbase]
  rw [Bundle.contMDiffAt_totalSpace]
  constructor
  · simpa only [F] using
      (hF.contMDiffAt.of_le
        (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞))
  · have hfiberCD := hZ.congr_of_eventuallyEq heq
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod] at hfiberCD
    simpa only [F, β] using hfiberCD

omit [InnerProductSpace ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem cov_fst_smooth
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (V : ∀ s t : Real, TangentSpace I (f s t))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M))) :
    ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2)
          (covDerivAlong (I := I) g (fun s : Real => f s q.2)
            (fun s : Real => V s q.2) q.1) : TangentBundle I M)) := by
  let swap : Real × Real → Real × Real := fun q => (q.2, q.1)
  have hswap : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      ∞ swap := by
    simpa only [swap] using contMDiff_snd.prodMk contMDiff_fst
  have hVswap :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (f q.2 q.1) (V q.2 q.1) : TangentBundle I M)) := by
    simpa only [swap, Function.comp_apply] using hV.comp hswap
  have hsnd :=
    cov_snd_smooth (I := I) g (fun s t : Real => f t s)
      (fun s t : Real => V t s) hVswap
  have hcomp := hsnd.comp hswap
  simpa only [swap, Function.comp_apply] using hcomp

omit [InnerProductSpace ℝ E] [SigmaCompactSpace M] in
theorem cov_commute_smooth
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (hf : IsSmoothVariation (I := I) f)
    (V : ∀ s t : Real, TangentSpace I (f s t)) (t : Real)
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M))) :
    covDerivAlong (I := I) g (fun s : Real => f s t)
        (fun s : Real =>
          covDerivAlong (I := I) g (fun v : Real => f s v)
            (fun v : Real => V s v) t) 0 -
      covDerivAlong (I := I) g (fun v : Real => f 0 v)
        (fun v : Real =>
          covDerivAlong (I := I) g (fun s : Real => f s v)
            (fun s : Real => V s v) 0) t =
      (DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
        (f 0 t))
        (mfderiv (modelWithCornersSelf Real Real) I
          (fun s : Real => f s t) 0 (1 : Real))
        (mfderiv (modelWithCornersSelf Real Real) I
          (fun v : Real => f 0 v) t (1 : Real))
        (V 0 t) := by
  classical
  let F : Real × Real → M := fun q => f q.1 q.2
  let W : ∀ q : Real × Real, TangentSpace I (F q) :=
    fun q => V q.1 q.2
  have hW :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (F q) (W q) : TangentBundle I M)) := by
    simpa only [F, W] using hV
  have hV2 : ContDiffAt Real 2
      (fun q : Real × Real =>
        (trivializationAt E (TangentSpace I) (f 0 t)).continuousLinearMapAt
          Real (f q.1 q.2) (V q.1 q.2))
      (0, t) := by
    simpa only [F, W] using
      (fieldCoord_contDiffAt (I := I) F W hW (0, t)).of_le
        (by norm_cast)
  have hinnerL : ∀ s : Real, DifferentiableAt Real
      (chartRepAt (I := I) (fun v : Real => f s v)
        (fun v : Real => V s v) t) t := by
    intro s
    have hcoord := fieldCoord_contDiffAt (I := I) F W hW (s, t)
    have hincl : ContDiffAt Real ∞ (fun v : Real => (s, v)) t :=
      (contDiff_const.prodMk contDiff_id).contDiffAt
    have hslice := hcoord.comp t hincl
    simpa only [F, W, chartRepAt] using
      hslice.differentiableAt (by simp)
  have hinnerR : ∀ v : Real, DifferentiableAt Real
      (chartRepAt (I := I) (fun s : Real => f s v)
        (fun s : Real => V s v) 0) 0 := by
    intro v
    have hcoord := fieldCoord_contDiffAt (I := I) F W hW (0, v)
    have hincl : ContDiffAt Real ∞ (fun s : Real => (s, v)) 0 :=
      (contDiff_id.prodMk contDiff_const).contDiffAt
    have hslice := hcoord.comp 0 hincl
    simpa only [F, W, chartRepAt] using
      hslice.differentiableAt (by simp)
  set β : M := f 0 t with hβ
  set Y : Real → Real → E := fun s v =>
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt
      Real (f s v) (V s v) with hY
  have hY2 :
      ContDiffAt Real 2 (fun q : Real × Real => Y q.1 q.2) (0, t) := by
    simpa only [Y, β] using hV2
  have hsliceL : ∀ s : Real,
      ContMDiff (modelWithCornersSelf Real Real) I (8 : Nat)
        (fun v : Real => f s v) := by
    intro s
    have hincl : ContMDiff
        (modelWithCornersSelf Real Real)
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        (8 : Nat) (fun v : Real => (s, v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hsliceR : ∀ v : Real,
      ContMDiff (modelWithCornersSelf Real Real) I (8 : Nat)
        (fun s : Real => f s v) := by
    intro v
    have hincl : ContMDiff
        (modelWithCornersSelf Real Real)
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        (8 : Nat) (fun s : Real => (s, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have htransverse : ContMDiff
      (modelWithCornersSelf Real Real) I (8 : Nat)
      (fun s : Real => f s t) :=
    hsliceR t
  have hcentral : ContMDiff
      (modelWithCornersSelf Real Real) I (8 : Nat)
      (fun v : Real => f 0 v) :=
    hsliceL 0
  have hsrcβ : f 0 t ∈ (chartAt H β).source := by
    rw [hβ]
    exact mem_chart_source H (f 0 t)
  have hrepL : ∀ s : Real,
      chartRepAtBase (I := I) β (fun v : Real => f s v)
          (fun v : Real => V s v) =
        fun v : Real => Y s v := by
    intro s
    funext v
    rw [chartRepAtBase_apply, hY]
  have hrepR : ∀ v : Real,
      chartRepAtBase (I := I) β (fun s : Real => f s v)
          (fun s : Real => V s v) =
        fun s : Real => Y s v := by
    intro v
    funext s
    rw [chartRepAtBase_apply, hY]
  have hinnerCoordL : ∀ s : Real,
      f s t ∈ (chartAt H β).source →
        (trivializationAt E (TangentSpace I) β).continuousLinearMapAt
            Real (f s t)
            (covDerivAlong (I := I) g (fun v : Real => f s v)
              (fun v : Real => V s v) t) =
          chartCovDerivAlong (I := I) g β (fun v : Real => f s v)
            (fun v : Real => Y s v) t := by
    intro s hs
    have hcoord :=
      covDeriv_coord (I := I) (n := (8 : Nat)) (by norm_num)
        g (fun v : Real => f s v) (fun v : Real => V s v)
        t β (hsliceL s) hs (hinnerL s)
    rw [hrepL s] at hcoord
    exact hcoord
  have hinnerCoordR : ∀ v : Real,
      f 0 v ∈ (chartAt H β).source →
        (trivializationAt E (TangentSpace I) β).continuousLinearMapAt
            Real (f 0 v)
            (covDerivAlong (I := I) g (fun s : Real => f s v)
              (fun s : Real => V s v) 0) =
          chartCovDerivAlong (I := I) g β (fun s : Real => f s v)
            (fun s : Real => Y s v) 0 := by
    intro v hv
    have hcoord :=
      covDeriv_coord (I := I) (n := (8 : Nat)) (by norm_num)
        g (fun s : Real => f s v) (fun s : Real => V s v)
        0 β (hsliceR v) hv (hinnerR v)
    rw [hrepR v] at hcoord
    exact hcoord
  let innerL : ∀ s : Real, TangentSpace I (f s t) := fun s =>
    covDerivAlong (I := I) g (fun v : Real => f s v)
      (fun v : Real => V s v) t
  let innerR : ∀ v : Real, TangentSpace I (f 0 v) := fun v =>
    covDerivAlong (I := I) g (fun s : Real => f s v)
      (fun s : Real => V s v) 0
  have hopenL : IsOpen {s : Real | f s t ∈ (chartAt H β).source} :=
    htransverse.continuous.isOpen_preimage _ (chartAt H β).open_source
  have hopenR : IsOpen {v : Real | f 0 v ∈ (chartAt H β).source} :=
    hcentral.continuous.isOpen_preimage _ (chartAt H β).open_source
  have hrepOuterL :
      chartRepAt (I := I) (fun s : Real => f s t) innerL 0
        =ᶠ[𝓝 (0 : Real)]
          fun s : Real =>
            chartCovDerivAlong (I := I) g β (fun v : Real => f s v)
              (fun v : Real => Y s v) t := by
    filter_upwards [hopenL.mem_nhds hsrcβ] with s hs
    rw [chartRepAt_apply]
    rw [← hβ]
    exact hinnerCoordL s hs
  have hrepOuterR :
      chartRepAt (I := I) (fun v : Real => f 0 v) innerR t
        =ᶠ[𝓝 t]
          fun v : Real =>
            chartCovDerivAlong (I := I) g β (fun s : Real => f s v)
              (fun s : Real => Y s v) 0 := by
    filter_upwards [hopenR.mem_nhds hsrcβ] with v hv
    rw [chartRepAt_apply]
    rw [← hβ]
    exact hinnerCoordR v hv
  have hF2 :
      ContDiffAt Real 2
        (fun q : Real × Real => extChartAt I β (f q.1 q.2)) (0, t) :=
    (chartPulled_contDiffAt_infty (I := I) f hf β 0 t hsrcβ).of_le
      (by norm_cast)
  have hΓ : ∀ i j k : Fin (Module.finrank Real E),
      DifferentiableAt Real
        (DifferentialGeometry.Geometry.Operator.chartChristoffel
          (I := I) g β i j k)
        (extChartAt I β (f 0 t)) := by
    intro i j k
    rw [hβ]
    exact Aux3.chartChristoffel_differentiableAt_self (I := I) g β i j k
  have houterL : DifferentiableAt Real
      (chartRepAt (I := I) (fun s : Real => f s t) innerL 0) 0 := by
    refine hrepOuterL.differentiableAt_iff.mpr ?_
    exact
      (Aux4.hasDerivAt_innerW (I := I) g β f Y 0 t hF2 hY2 hΓ).differentiableAt
  have houterR : DifferentiableAt Real
      (chartRepAt (I := I) (fun v : Real => f 0 v) innerR t) t := by
    refine hrepOuterR.differentiableAt_iff.mpr ?_
    exact
      (Aux4.hasDerivAt_innerW_snd (I := I) g β f Y 0 t hF2 hY2 hΓ).differentiableAt
  exact
    cov_commute_curv (I := I) g f hf V t hV2 hinnerL hinnerR
      houterL houterR

omit [InnerProductSpace ℝ E] [SigmaCompactSpace M] in
theorem cov_snd2_commute
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (hf : IsSmoothVariation (I := I) f)
    (V : ∀ s t : Real, TangentSpace I (f s t))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)))
    (t : Real) :
    covFst (I := I) g f (fun s v => covSnd2 (I := I) g f V s v) 0 t =
      covSnd (I := I) g f
          (fun s v =>
            covSndFst (I := I) g f V s v +
              varCurv (I := I) g f V s v) 0 t +
        varCurv (I := I) g f
          (fun s v => covSnd (I := I) g f V s v) 0 t := by
  have hDt :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (f q.1 q.2)
            (covSnd (I := I) g f V q.1 q.2) : TangentBundle I M)) := by
    simpa only [covSnd] using cov_snd_smooth (I := I) g f V hV
  have hcomm1 : ∀ v : Real,
      covFstSnd (I := I) g f V 0 v -
        covSndFst (I := I) g f V 0 v =
      varCurv (I := I) g f V 0 v := by
    intro v
    simpa only [covFstSnd, covSndFst, varCurv, covFst, covSnd,
      varFst, varSnd, curvAlong] using
      cov_commute_smooth (I := I) g f hf V v hV
  have hfield :
      (fun v : Real => covFstSnd (I := I) g f V 0 v) =
      fun v : Real =>
        covSndFst (I := I) g f V 0 v +
          varCurv (I := I) g f V 0 v := by
    funext v
    have hv := hcomm1 v
    linear_combination (norm := module) hv
  have hcomm2 :
      covFstSnd (I := I) g f
          (fun s v => covSnd (I := I) g f V s v) 0 t -
        covSndFst (I := I) g f
          (fun s v => covSnd (I := I) g f V s v) 0 t =
      varCurv (I := I) g f
        (fun s v => covSnd (I := I) g f V s v) 0 t := by
    simpa only [covFstSnd, covSndFst, varCurv, covFst, covSnd,
      varFst, varSnd, curvAlong] using
      cov_commute_smooth (I := I) g f hf
        (fun s v => covSnd (I := I) g f V s v) t hDt
  have houter :
      covSndFst (I := I) g f
          (fun s v => covSnd (I := I) g f V s v) 0 t =
        covSnd (I := I) g f
          (fun s v =>
            covSndFst (I := I) g f V s v +
              varCurv (I := I) g f V s v) 0 t := by
    change
      covDerivAlong (I := I) g (fun v : Real => f 0 v)
          (fun v : Real => covFstSnd (I := I) g f V 0 v) t =
        covDerivAlong (I := I) g (fun v : Real => f 0 v)
          (fun v : Real =>
            covSndFst (I := I) g f V 0 v +
              varCurv (I := I) g f V 0 v) t
    rw [hfield]
  rw [houter] at hcomm2
  change
    covFstSnd (I := I) g f
        (fun s v => covSnd (I := I) g f V s v) 0 t =
      covSnd (I := I) g f
          (fun s v =>
            covSndFst (I := I) g f V s v +
              varCurv (I := I) g f V s v) 0 t +
        varCurv (I := I) g f
          (fun s v => covSnd (I := I) g f V s v) 0 t
  linear_combination (norm := module) hcomm2

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem cov_varCurv
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (V : ∀ s t : Real, TangentSpace I (f s t)) (s t : Real) :
    covSnd (I := I) g f
        (fun r v => varCurv (I := I) g f V r v) s t =
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
        curvAlong (I := I) g (fun v : Real => f s v)
          (fun v : Real => varFst (I := I) f s v)
          (fun v : Real => varSnd (I := I) f s v)
          (fun v : Real => covSnd (I := I) g f V s v) t := by
  simpa only [covSnd, varCurv] using
    cov_curvAlong (I := I) g (fun v : Real => f s v)
      (fun v : Real => varFst (I := I) f s v)
      (fun v : Real => varSnd (I := I) f s v)
      (fun v : Real => V s v) t

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem cov_jacCurv
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (V : ∀ s t : Real, TangentSpace I (f s t)) (s t : Real) :
    covFst (I := I) g f
        (fun r v => jacCurv (I := I) g f V r v) s t =
      curvDerivAlong (I := I) g (fun r : Real => f r t)
          (fun r : Real => V r t)
          (fun r : Real => varSnd (I := I) f r t)
          (fun r : Real => varSnd (I := I) f r t) s +
        curvAlong (I := I) g (fun r : Real => f r t)
          (fun r : Real => covFst (I := I) g f V r t)
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
              (fun a v => varSnd (I := I) f a v) r t) s := by
  simpa only [covFst, jacCurv] using
    cov_curvAlong (I := I) g (fun r : Real => f r t)
      (fun r : Real => V r t)
      (fun r : Real => varSnd (I := I) f r t)
      (fun r : Real => varSnd (I := I) f r t) s

omit [InnerProductSpace ℝ E] [SigmaCompactSpace M] in
theorem cov_snd2_expand
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (hf : IsSmoothVariation (I := I) f)
    (V : ∀ s t : Real, TangentSpace I (f s t))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)))
    (t : Real) :
    covFst (I := I) g f (fun s v => covSnd2 (I := I) g f V s v) 0 t =
      covSnd2 (I := I) g f
          (fun s v => covFst (I := I) g f V s v) 0 t +
        curvDerivAlong (I := I) g (fun v : Real => f 0 v)
          (fun v : Real => varFst (I := I) f 0 v)
          (fun v : Real => varSnd (I := I) f 0 v)
          (fun v : Real => V 0 v) t +
        curvAlong (I := I) g (fun v : Real => f 0 v)
          (fun v : Real =>
            covSnd (I := I) g f
              (fun s w => varFst (I := I) f s w) 0 v)
          (fun v : Real => varSnd (I := I) f 0 v)
          (fun v : Real => V 0 v) t +
        curvAlong (I := I) g (fun v : Real => f 0 v)
          (fun v : Real => varFst (I := I) f 0 v)
          (fun v : Real =>
            covSnd (I := I) g f
              (fun s w => varSnd (I := I) f s w) 0 v)
          (fun v : Real => V 0 v) t +
        (2 : Real) •
          varCurv (I := I) g f
            (fun s v => covSnd (I := I) g f V s v) 0 t := by
  have hDt :=
    cov_snd_smooth (I := I) g f V hV
  have hDr :=
    cov_fst_smooth (I := I) g f V hV
  have hFstSnd :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (f q.1 q.2)
            (covFstSnd (I := I) g f V q.1 q.2) :
              TangentBundle I M)) := by
    simpa only [covFstSnd] using
      cov_fst_smooth (I := I) g f
        (fun s v => covSnd (I := I) g f V s v) hDt
  have hSndFst :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (f q.1 q.2)
            (covSndFst (I := I) g f V q.1 q.2) :
              TangentBundle I M)) := by
    simpa only [covSndFst] using
      cov_snd_smooth (I := I) g f
        (fun s v => covFst (I := I) g f V s v) hDr
  have hFSdiff :
      DifferentiableAt Real
        (chartRepAt (I := I) (fun v : Real => f 0 v)
          (fun v : Real => covFstSnd (I := I) g f V 0 v) t) t :=
    chartRep_snd_diff (I := I) f
      (fun s v => covFstSnd (I := I) g f V s v) hFstSnd 0 t
  have hSFdiff :
      DifferentiableAt Real
        (chartRepAt (I := I) (fun v : Real => f 0 v)
          (fun v : Real => covSndFst (I := I) g f V 0 v) t) t :=
    chartRep_snd_diff (I := I) f
      (fun s v => covSndFst (I := I) g f V s v) hSndFst 0 t
  have hcomm1 : ∀ v : Real,
      covFstSnd (I := I) g f V 0 v -
        covSndFst (I := I) g f V 0 v =
      varCurv (I := I) g f V 0 v := by
    intro v
    simpa only [covFstSnd, covSndFst, varCurv, covFst, covSnd,
      varFst, varSnd, curvAlong] using
      cov_commute_smooth (I := I) g f hf V v hV
  have hRfield :
      (fun v : Real => varCurv (I := I) g f V 0 v) =
        fun v : Real =>
          covFstSnd (I := I) g f V 0 v -
            covSndFst (I := I) g f V 0 v := by
    funext v
    exact (hcomm1 v).symm
  have hRdiff :
      DifferentiableAt Real
        (chartRepAt (I := I) (fun v : Real => f 0 v)
          (fun v : Real => varCurv (I := I) g f V 0 v) t) t := by
    rw [hRfield]
    have hrepSub :
        chartRepAt (I := I) (fun v : Real => f 0 v)
            (fun v : Real =>
              covFstSnd (I := I) g f V 0 v -
                covSndFst (I := I) g f V 0 v) t =
          fun v : Real =>
            chartRepAt (I := I) (fun w : Real => f 0 w)
                (fun w : Real => covFstSnd (I := I) g f V 0 w) t v -
              chartRepAt (I := I) (fun w : Real => f 0 w)
                (fun w : Real => covSndFst (I := I) g f V 0 w) t v := by
      funext v
      rw [chartRepAt_apply, chartRepAt_apply, chartRepAt_apply, map_sub]
    rw [hrepSub]
    exact hFSdiff.sub hSFdiff
  have hsplit :
      covSnd (I := I) g f
          (fun s v =>
            covSndFst (I := I) g f V s v +
              varCurv (I := I) g f V s v) 0 t =
        covSnd (I := I) g f
            (fun s v => covSndFst (I := I) g f V s v) 0 t +
          covSnd (I := I) g f
            (fun s v => varCurv (I := I) g f V s v) 0 t := by
    simpa only [covSnd] using
      covDerivAlong_add (I := I) g (fun v : Real => f 0 v)
        (fun v : Real => covSndFst (I := I) g f V 0 v)
        (fun v : Real => varCurv (I := I) g f V 0 v)
        t hSFdiff hRdiff
  have hraw := cov_snd2_commute (I := I) g f hf V hV t
  rw [hsplit, cov_varCurv (I := I) g f V 0 t] at hraw
  have hlead :
      covSnd (I := I) g f
          (fun s v => covSndFst (I := I) g f V s v) 0 t =
        covSnd2 (I := I) g f
          (fun s v => covFst (I := I) g f V s v) 0 t := rfl
  have hlast :
      curvAlong (I := I) g (fun v : Real => f 0 v)
          (fun v : Real => varFst (I := I) f 0 v)
          (fun v : Real => varSnd (I := I) f 0 v)
          (fun v : Real => covSnd (I := I) g f V 0 v) t =
        varCurv (I := I) g f
          (fun s v => covSnd (I := I) g f V s v) 0 t := rfl
  rw [hlead, hlast] at hraw
  linear_combination (norm := module) hraw

omit [InnerProductSpace ℝ E] [SigmaCompactSpace M] in
theorem jacobi_var_eq
    (g : SmoothRiemannianMetric I M) (f : Real → Real → M)
    (hf : IsSmoothVariation (I := I) f)
    (V : ∀ s t : Real, TangentSpace I (f s t))
    (hV : ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2) (V q.1 q.2) : TangentBundle I M)))
    (hJac : ∀ s : Real,
      IsJacobiAlong (I := I) g (fun v : Real => f s v)
        (fun v : Real => V s v))
    (hGeo : ∀ s : Real, IsGeodesic (I := I) g (fun v : Real => f s v))
    (t : Real) :
    covSnd2 (I := I) g f
          (fun s v => covFst (I := I) g f V s v) 0 t +
        jacCurv (I := I) g f
          (fun s v => covFst (I := I) g f V s v) 0 t =
      jacVarForce (I := I) g f V t := by
  have hJacEq : ∀ s : Real,
      covSnd2 (I := I) g f V s t =
        - jacCurv (I := I) g f V s t := by
    intro s
    have hj :=
      jacobi_d2_eq (I := I) g (fun v : Real => f s v)
        (fun v : Real => V s v) ((hJac s) t)
    simpa only [covSnd2, covSnd, jacCurv, curvAlong, varSnd,
      curveVelocity] using hj
  have hJacField :
      (fun s : Real => covSnd2 (I := I) g f V s t) =
        fun s : Real => - jacCurv (I := I) g f V s t := by
    funext s
    exact hJacEq s
  have hJacDeriv :
      covFst (I := I) g f
          (fun s v => covSnd2 (I := I) g f V s v) 0 t =
        - covFst (I := I) g f
          (fun s v => jacCurv (I := I) g f V s v) 0 t := by
    change
      covDerivAlong (I := I) g (fun s : Real => f s t)
          (fun s : Real => covSnd2 (I := I) g f V s t) 0 =
        - covDerivAlong (I := I) g (fun s : Real => f s t)
          (fun s : Real => jacCurv (I := I) g f V s t) 0
    rw [hJacField]
    have hneg :=
      covDerivAlong_smul (I := I) g (fun s : Real => f s t)
        (-1 : Real) (fun s : Real => jacCurv (I := I) g f V s t) 0
    simpa only [neg_one_smul] using hneg
  have hAcomm :
      covFst (I := I) g f
          (fun s v => varSnd (I := I) f s v) 0 t =
        covSnd (I := I) g f
          (fun s v => varFst (I := I) f s v) 0 t := by
    simpa only [covFst, covSnd, varFst, varSnd] using
      commute_ds_dt_intrinsic (I := I) g f hf t
  have hcentral2 :
      ContMDiffAt (modelWithCornersSelf Real Real) I 2
        (fun v : Real => f 0 v) t := by
    have hincl : ContMDiff
        (modelWithCornersSelf Real Real)
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        (8 : Nat) (fun v : Real => ((0 : Real), v)) :=
      contMDiff_const.prodMk contMDiff_id
    have hjoint : ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I (8 : Nat) (fun q : Real × Real => f q.1 q.2) :=
      hf
    exact (hjoint.comp hincl).contMDiffAt.of_le (by norm_num)
  have hTzero :
      covSnd (I := I) g f
          (fun s v => varSnd (I := I) f s v) 0 t = 0 := by
    simpa only [covSnd, varSnd] using
      covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
        (I := I) g (fun v : Real => f 0 v) t hcentral2
          ((hGeo 0).hasGeodesicEquationAt t)
  have hExp := cov_snd2_expand (I := I) g f hf V hV t
  have hzeroTerm :
      curvAlong (I := I) g (fun v : Real => f 0 v)
          (fun v : Real => varFst (I := I) f 0 v)
          (fun v : Real =>
            covSnd (I := I) g f
              (fun s w => varSnd (I := I) f s w) 0 v)
          (fun v : Real => V 0 v) t = 0 := by
    unfold curvAlong
    change
      (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
          (f 0 t))
          (varFst (I := I) f 0 t)
          (covSnd (I := I) g f
            (fun s v => varSnd (I := I) f s v) 0 t)
          (V 0 t) = 0
    rw [hTzero, map_zero]
    rfl
  rw [hzeroTerm] at hExp
  simp only [add_zero] at hExp
  have hJcurv := cov_jacCurv (I := I) g f V 0 t
  have hKterm :
      curvAlong (I := I) g (fun r : Real => f r t)
          (fun r : Real => covFst (I := I) g f V r t)
          (fun r : Real => varSnd (I := I) f r t)
          (fun r : Real => varSnd (I := I) f r t) 0 =
        jacCurv (I := I) g f
          (fun s v => covFst (I := I) g f V s v) 0 t := rfl
  have hslot2 :
      curvAlong (I := I) g (fun r : Real => f r t)
          (fun r : Real => V r t)
          (fun r : Real =>
            covFst (I := I) g f
              (fun a v => varSnd (I := I) f a v) r t)
          (fun r : Real => varSnd (I := I) f r t) 0 =
        curvAlong (I := I) g (fun v : Real => f 0 v)
          (fun v : Real => V 0 v)
          (fun v : Real =>
            covSnd (I := I) g f
              (fun s w => varFst (I := I) f s w) 0 v)
          (fun v : Real => varSnd (I := I) f 0 v) t := by
    unfold curvAlong
    change
      (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
          (f 0 t))
          (V 0 t)
          (covFst (I := I) g f
            (fun a v => varSnd (I := I) f a v) 0 t)
          (varSnd (I := I) f 0 t) =
        (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
          (f 0 t))
          (V 0 t)
          (covSnd (I := I) g f
            (fun s w => varFst (I := I) f s w) 0 t)
          (varSnd (I := I) f 0 t)
    rw [hAcomm]
  have hslot3 :
      curvAlong (I := I) g (fun r : Real => f r t)
          (fun r : Real => V r t)
          (fun r : Real => varSnd (I := I) f r t)
          (fun r : Real =>
            covFst (I := I) g f
              (fun a v => varSnd (I := I) f a v) r t) 0 =
        curvAlong (I := I) g (fun v : Real => f 0 v)
          (fun v : Real => V 0 v)
          (fun v : Real => varSnd (I := I) f 0 v)
          (fun v : Real =>
            covSnd (I := I) g f
              (fun s w => varFst (I := I) f s w) 0 v) t := by
    unfold curvAlong
    change
      (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
          (f 0 t))
          (V 0 t)
          (varSnd (I := I) f 0 t)
          (covFst (I := I) g f
            (fun a v => varSnd (I := I) f a v) 0 t) =
        (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
          (f 0 t))
          (V 0 t)
          (varSnd (I := I) f 0 t)
          (covSnd (I := I) g f
            (fun s w => varFst (I := I) f s w) 0 t)
    rw [hAcomm]
  rw [hKterm, hslot2, hslot3] at hJcurv
  rw [hExp, hJcurv] at hJacDeriv
  unfold jacVarForce
  linear_combination (norm := module) hJacDeriv

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
