import DifferentialGeometry.Geometry.Connection.ChartBridge.Gradient
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Geometry.Curvature.OpenSubtypeNaturality
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityCross
import DifferentialGeometry.Geometry.Metric.LocalPullback
import DifferentialGeometry.Geometry.Metric.PullbackCross
import DifferentialGeometry.Geometry.Operator.NormGradSq
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphOpens
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
variable [T2Space M]

theorem gradientFun_pullbackCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (f : N → Real) (x : M)
    (hf : MDifferentiableAt J 𝓘(Real, Real) f (Φ x)) :
    gradientFun (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ)
        (f ∘ (Φ : M → N)) x =
      (Φ.mfderivToContinuousLinearEquiv (by simp) x).symm
        (gradientFun (I := J) g f (Φ x)) := by
  have he : mfderiv I J (Φ : M → N) x =
      (Φ.mfderivToContinuousLinearEquiv (by simp) x :
        TangentSpace I x →L[Real] TangentSpace J (Φ x)) :=
    (Φ.mfderivToContinuousLinearEquiv_coe (by simp) (x := x)).symm
  apply (metricFlatEquiv (I := I)
    (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ) x).injective
  ext w
  rw [metricFlatEquiv_apply, metricFlatEquiv_apply, gradientFun_eq,
    inner_metricSharp, Diffeomorph.pullbackMetricCross_inner, he,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    gradientFun_eq, inner_metricSharp]
  change mvfderiv (I := I) (f ∘ (Φ : M → N)) x w =
    mvfderiv (I := J) f (Φ x)
      ((Φ.mfderivToContinuousLinearEquiv (by simp) x) w)
  rw [mvfderiv_comp_apply x hf (Φ.contMDiff.mdifferentiableAt (by simp)) w]
  simp only [he]
  rfl

theorem gradientFun_localPull
    (g : SmoothRiemannianMetric J N) (Phi : M → N)
    (hPhi : IsLocalDiffeomorph I J ∞ Phi)
    (f : N → Real) (x : M)
    (hf : MDifferentiableAt J (modelWithCornersSelf Real Real) f (Phi x)) :
    gradientFun (I := I)
        (localPullMetric (I := I) (J := J) g Phi hPhi)
        (f ∘ Phi) x =
      (hPhi.mfderivToContinuousLinearEquiv (by simp) x).symm
        (gradientFun (I := J) g f (Phi x)) := by
  have he : mfderiv I J Phi x =
      (hPhi.mfderivToContinuousLinearEquiv (by simp) x :
        TangentSpace I x →L[Real] TangentSpace J (Phi x)) :=
    (hPhi.mfderivToContinuousLinearEquiv_coe (by simp) (x := x)).symm
  apply (metricFlatEquiv (I := I)
    (localPullMetric (I := I) (J := J) g Phi hPhi) x).injective
  ext w
  rw [metricFlatEquiv_apply, metricFlatEquiv_apply, gradientFun_eq,
    inner_metricSharp, localPullMetric_inner, he,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    gradientFun_eq, inner_metricSharp]
  change mvfderiv (I := I) (f ∘ Phi) x w =
    mvfderiv (I := J) f (Phi x)
      ((hPhi.mfderivToContinuousLinearEquiv (by simp) x) w)
  rw [mvfderiv_comp_apply x hf
    (hPhi.contMDiff.mdifferentiableAt (by simp)) w]
  simp only [he]
  rfl

theorem normGradSqFun_localPull
    (g : SmoothRiemannianMetric J N) (Phi : M → N)
    (hPhi : IsLocalDiffeomorph I J ∞ Phi)
    (f : N → Real) (x : M)
    (hf : MDifferentiableAt J (modelWithCornersSelf Real Real) f (Phi x)) :
    normGradSqFun (I := I)
        (localPullMetric (I := I) (J := J) g Phi hPhi)
        (f ∘ Phi) x =
      normGradSqFun (I := J) g f (Phi x) := by
  rw [normGradSqFun_def, normGradSqFun_def]
  have hgrad :
      gradFun (I := I) (localPullMetric (I := I) (J := J) g Phi hPhi)
          (f ∘ Phi) x =
        (hPhi.mfderivToContinuousLinearEquiv (by simp) x).symm
          (gradFun (I := J) g f (Phi x)) := by
    simpa only [Connection.gradient_eq_gradFun] using
      gradientFun_localPull (I := I) (J := J) g Phi hPhi f x hf
  rw [hgrad, localPullMetric_inner]
  rw [← hPhi.mfderivToContinuousLinearEquiv_coe (by simp)]
  simp

omit [T2Space M] in
theorem gradientFun_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U] (f : M → Real) (x : U)
    (hf : MDifferentiableAt I (modelWithCornersSelf Real Real) f (x : M)) :
    gradientFun (I := I) (g.restrictOpen (I := I) U)
        (fun y : U ↦ f (y : M)) x =
      Curvature.restrictOpenTangentField (I := I) U
        (fun y : M ↦ gradientFun (I := I) g f y) x := by
  change gradFun (I := I) (g.restrictOpen (I := I) U)
      (fun y : U ↦ f (y : M)) x =
    Curvature.restrictOpenTangentField (I := I) U
      (fun y : M ↦ gradFun (I := I) g f y) x
  refine (Connection.gradFun_unique (I := I)
    (g.restrictOpen (I := I) U) (fun y : U ↦ f (y : M)) ?_).symm
  intro v
  let vM : TangentSpace I (x : M) :=
    mfderiv I I (Subtype.val : U → M) x v
  have hinner :
      (g.restrictOpen (I := I) U).inner x
          (Curvature.restrictOpenTangentField (I := I) U
            (fun y : M ↦ gradFun (I := I) g f y) x) v =
        g.inner (x : M) (gradFun (I := I) g f (x : M)) vM := by
    simpa only [vM, Curvature.restrictOpenTangentField_apply,
      mfderiv_subtype_val_apply] using!
        SmoothRiemannianMetric.restrictOpen_inner g U x
          (Curvature.restrictOpenTangentField (I := I) U
            (fun y : M ↦ gradFun (I := I) g f y) x) v
  rw [hinner, Connection.gradFun_metricDual_mvfderiv]
  simpa only [vM, mfderiv_subtype_val_apply] using!
    (Curvature.mvfderiv_restrictOpen (I := I) U f x v hf).symm

end DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
variable [SigmaCompactSpace N] [T2Space N] [J.Boundaryless]

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
theorem hessFun_pullbackCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (f : C^∞⟮J, N; Real⟯) (x : M) (v w : TangentSpace I x) :
    hessFun (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ)
        (f.comp Φ.toContMDiffMap) x v w =
      hessFun (I := J) g f (Φ x)
        (mfderiv I J (Φ : M → N) x v)
        (mfderiv I J (Φ : M → N) x w) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let _ : CompleteSpace F := FiniteDimensional.complete Real F
  let gΦ := Diffeomorph.pullbackMetricCross (I := I) (J := J) g Φ
  let fΦ : C^∞⟮I, M; Real⟯ := f.comp Φ.toContMDiffMap
  let Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun y => gradientFun (I := I) gΦ fΦ y,
      gradFun_contMDiff_total_section (I := I) gΦ fΦ.contMDiff⟩
  let Z : ContMDiffSection J F (∞ : WithTop ℕ∞)
      (TangentSpace J : N → Type _) :=
    ⟨fun q => gradientFun (I := J) g f q,
      gradFun_contMDiff_total_section (I := J) g f.contMDiff⟩
  have hpush :
      (fun q : N => pushFwdSectionCross (I := I) (J := J) Φ Y q) =
        fun q : N => Z q := by
    funext q
    rw [show q = Φ (Φ.symm q) from (Φ.apply_symm_apply q).symm]
    rw [pushFwdSectionCross_apply_at_image]
    have hgrad := gradientFun_pullbackCross
      (I := I) (J := J) g Φ f (Φ.symm q)
      (f.contMDiff.mdifferentiableAt (by simp))
    have hY : Y (Φ.symm q) =
        (Φ.mfderivToContinuousLinearEquiv (by simp) (Φ.symm q)).symm
          (Z (Φ (Φ.symm q))) := by
      change gradientFun (I := I) gΦ (fun y => fΦ y) (Φ.symm q) = _
      rw [show (fun y => fΦ y) = f ∘ (Φ : M → N) by rfl]
      simpa [Z, gΦ] using hgrad
    rw [hY, ← Φ.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (Φ.mfderivToContinuousLinearEquiv (by simp) (Φ.symm q)).apply_symm_apply _
  rw [hessFun_eq_cov_grad (I := I) gΦ fΦ.contMDiff x v w]
  rw [hessFun_eq_cov_grad (I := J) g f.contMDiff (Φ x)
    (mfderiv I J (Φ : M → N) x v) (mfderiv I J (Φ : M → N) x w)]
  change gΦ.inner x
      ((metricCov (I := I) (M := M) gΦ).toFun (fun y => Y y) x v) w = _
  rw [Diffeomorph.pullbackMetricCross_inner]
  rw [metricCov_pullbackCross (I := I) (J := J) g Φ Y x v]
  rw [hpush]
  rfl

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
theorem hessFun_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U]
    (f : C^∞⟮I, M; Real⟯) (x : U) (v w : TangentSpace I x) :
    hessFun (I := I) (g.restrictOpen (I := I) U)
        (fun y : U ↦ f (y : M)) x v w =
      hessFun (I := I) g f (x : M)
        (mfderiv I I (Subtype.val : U → M) x v)
        (mfderiv I I (Subtype.val : U → M) x w) := by
  let fU : U → Real := fun y ↦ f (y : M)
  have hfU : ContMDiff I (modelWithCornersSelf Real Real) ∞ fU :=
    f.contMDiff.comp (contMDiff_subtype_val (I := I) (U := U))
  let Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun y ↦ gradFun (I := I) g f y,
      Connection.gradFun_contMDiff_total_section (I := I) g f.contMDiff⟩
  have hgrad :
      (fun y : U ↦ gradFun (I := I) (g.restrictOpen (I := I) U) fU y) =
        Curvature.restrictOpenTangentField (I := I) U (fun y : M ↦ Y y) := by
    funext y
    exact gradientFun_restrictOpen (I := I) g U f y
      (f.contMDiff.mdifferentiableAt (by simp))
  rw [hessFun_eq_cov_grad (I := I) (g.restrictOpen (I := I) U) hfU x v w,
    hessFun_eq_cov_grad (I := I) g f.contMDiff (x : M)
      (mfderiv I I (Subtype.val : U → M) x v)
      (mfderiv I I (Subtype.val : U → M) x w),
    hgrad]
  let vM : TangentSpace I (x : M) :=
    mfderiv I I (Subtype.val : U → M) x v
  let wM : TangentSpace I (x : M) :=
    mfderiv I I (Subtype.val : U → M) x w
  let aU : TangentSpace I x :=
    (Curvature.metricCov (I := I) (M := U) (g.restrictOpen (I := I) U)
      (Curvature.restrictOpenTangentField (I := I) U (fun y : M ↦ Y y)) x) v
  let aM : TangentSpace I (x : M) :=
    (Curvature.metricCov (I := I) (M := M) g (fun y : M ↦ Y y) (x : M)) vM
  have ha : aU = aM := by
    simpa only [aU, aM, vM, mfderiv_subtype_val_apply] using!
      Curvature.metricCov_restrictOpen_globalSection (I := I) g U Y x v
  have hinner :
      (g.restrictOpen (I := I) U).inner x aU w =
        g.inner (x : M) aM wM := by
    simpa only [ha, wM, mfderiv_subtype_val_apply] using!
      SmoothRiemannianMetric.restrictOpen_inner g U x aU w
  exact hinner

theorem hessFun_localPull
    (g : SmoothRiemannianMetric J N) (Phi : M → N)
    (hPhi : IsLocalDiffeomorph I J ∞ Phi)
    (f : C^∞⟮J, N; Real⟯) (x : M) (v w : TangentSpace I x) :
    hessFun (I := I)
        (localPullMetric (I := I) (J := J) g Phi hPhi)
        (f ∘ Phi) x v w =
      hessFun (I := J) g f (Phi x)
        (mfderiv I J Phi x v) (mfderiv I J Phi x w) := by
  let PhiLocal : PartialDiffeomorph I J M N ∞ := Classical.choose (hPhi x)
  have hxLocal : x ∈ PhiLocal.source := (hPhi x).choose_spec.1
  have hEq : Set.EqOn Phi (PhiLocal : M → N) PhiLocal.source :=
    (hPhi x).choose_spec.2
  let U : TopologicalSpace.Opens M := ⟨PhiLocal.source, PhiLocal.open_source⟩
  have hU : (U : Set M) ⊆ PhiLocal.source := Set.Subset.rfl
  let V : TopologicalSpace.Opens N :=
    ⟨(PhiLocal : M → N) '' (U : Set M),
      image_opens_isOpen PhiLocal hU⟩
  let Psi : Diffeomorph I J U V ∞ :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeoCross PhiLocal hU
  let xu : U := ⟨x, hxLocal⟩
  let toU (z : TangentSpace I x) : TangentSpace I xu :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) xu).symm
      (tangentSpaceModelContinuousLinearEquiv (I := I) x z)
  have htoU (z : TangentSpace I x) :
      mfderiv I I (Subtype.val : U → M) xu (toU z) = z := by
    rw [mfderiv_subtype_val_apply]
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) x).injective
    change (tangentSpaceModelContinuousLinearEquiv (I := I) x)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) xu).symm
          (tangentSpaceModelContinuousLinearEquiv (I := I) x z)) =
      tangentSpaceModelContinuousLinearEquiv (I := I) x z
    rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
    exact tangentSpaceModelContinuousLinearEquiv_apply (I := I) x z
  let _ : SigmaCompactSpace U :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let _ : SigmaCompactSpace V :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen J V.isOpen)
  have hEqNhds : Phi =ᶠ[nhds x] (PhiLocal : M → N) :=
    Filter.eventuallyEq_of_mem (PhiLocal.open_source.mem_nhds hxLocal) hEq
  have hDPhi : mfderiv I J Phi x = mfderiv I J (PhiLocal : M → N) x :=
    hEqNhds.mfderiv_eq
  have hPsiD (y : U) (z : TangentSpace I y) :
      mfderiv I J (Psi : U → V) y z =
        mfderiv I J (PhiLocal : M → N) (y : M) z := by
    simpa only [Psi] using
      DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeoCross
        PhiLocal hU y z
  have hPsiDAmbient (y : U) (z : TangentSpace I y) :
      mfderiv J J (Subtype.val : V → N) (Psi y)
          (mfderiv I J (Psi : U → V) y z) =
        mfderiv I J (PhiLocal : M → N) (y : M)
          (mfderiv I I (Subtype.val : U → M) y z) := by
    rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
    exact hPsiD y z
  have hPsiVal (y : U) : ((Psi y : V) : N) = (PhiLocal : M → N) (y : M) := by
    rfl
  have hmetric :
      (localPullMetric (I := I) (J := J) g Phi hPhi).restrictOpen (I := I) U =
        Diffeomorph.pullbackMetricCross (I := I) (J := J)
          (g.restrictOpen (I := J) V) Psi := by
    apply SmoothRiemannianMetric.ext_inner
    intro y a b
    have hyLocal : (y : M) ∈ PhiLocal.source := hU y.2
    have hEqYNhds : Phi =ᶠ[nhds (y : M)] (PhiLocal : M → N) :=
      Filter.eventuallyEq_of_mem (PhiLocal.open_source.mem_nhds hyLocal) hEq
    have hDPhiY : mfderiv I J Phi (y : M) =
        mfderiv I J (PhiLocal : M → N) (y : M) :=
      hEqYNhds.mfderiv_eq
    calc
      ((localPullMetric (I := I) (J := J) g Phi hPhi).restrictOpen
          (I := I) U).inner y a b =
          (localPullMetric (I := I) (J := J) g Phi hPhi).inner (y : M)
            (mfderiv I I (Subtype.val : U → M) y a)
            (mfderiv I I (Subtype.val : U → M) y b) := by
              rw [SmoothRiemannianMetric.restrictOpen_inner,
                mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
      _ = g.inner (Phi (y : M))
            (mfderiv I J Phi (y : M)
              (mfderiv I I (Subtype.val : U → M) y a))
            (mfderiv I J Phi (y : M)
              (mfderiv I I (Subtype.val : U → M) y b)) :=
        localPullMetric_inner (I := I) (J := J) g Phi hPhi (y : M)
          (mfderiv I I (Subtype.val : U → M) y a)
          (mfderiv I I (Subtype.val : U → M) y b)
      _ = g.inner ((PhiLocal : M → N) (y : M))
            (mfderiv I J (PhiLocal : M → N) (y : M)
              (mfderiv I I (Subtype.val : U → M) y a))
            (mfderiv I J (PhiLocal : M → N) (y : M)
              (mfderiv I I (Subtype.val : U → M) y b)) := by
        rw [hEq hyLocal, hDPhiY]
      _ = (g.restrictOpen (I := J) V).inner (Psi y)
            (mfderiv I J (Psi : U → V) y a)
            (mfderiv I J (Psi : U → V) y b) := by
        rw [SmoothRiemannianMetric.restrictOpen_inner,
          mfderiv_subtype_val_apply, mfderiv_subtype_val_apply,
          hPsiD, hPsiD, hPsiVal]
      _ = (Diffeomorph.pullbackMetricCross (I := I) (J := J)
            (g.restrictOpen (I := J) V) Psi).inner y a b :=
        (Diffeomorph.pullbackMetricCross_inner
          (I := I) (J := J) (g.restrictOpen (I := J) V) Psi y a b).symm
  let PhiMap : C^∞⟮I, M; J, N⟯ := ⟨Phi, hPhi.contMDiff⟩
  let fPhi : C^∞⟮I, M; Real⟯ := f.comp PhiMap
  let fV : C^∞⟮J, V; Real⟯ :=
    ⟨fun y : V ↦ f (y : N),
      f.contMDiff.comp (contMDiff_subtype_val (I := J) (U := V))⟩
  have hfun : (fun y : U ↦ f (Phi (y : M))) =
      fun y : U ↦ (fV.comp Psi.toContMDiffMap) y := by
    funext y
    change f (Phi (y : M)) = f ((Psi y : V) : N)
    rw [hPsiVal, hEq (hU y.2)]
  have hpoint : ((Psi xu : V) : N) = Phi x := by
    rw [hPsiVal]
    exact (hEq hxLocal).symm
  have htargetD (z : TangentSpace I x) :
      mfderiv J J (Subtype.val : V → N) (Psi xu)
          (mfderiv I J (Psi : U → V) xu (toU z)) =
        mfderiv I J Phi x z := by
    rw [hPsiDAmbient, htoU, ← hDPhi]
    rfl
  have htargetDF (z : TangentSpace I x) :
      (mfderiv J J (Subtype.val : V → N) (Psi xu) : F →L[Real] F)
          ((mfderiv I J (Psi : U → V) xu : E →L[Real] F) (toU z)) =
        (mfderiv I J Phi x : E →L[Real] F) z := by
    simpa only using! htargetD z
  calc
    hessFun (I := I) (localPullMetric (I := I) (J := J) g Phi hPhi)
        (f ∘ Phi) x v w =
        hessFun (I := I)
          ((localPullMetric (I := I) (J := J) g Phi hPhi).restrictOpen
            (I := I) U)
          (fun y : U ↦ fPhi y) xu (toU v) (toU w) := by
            rw [hessFun_restrictOpen, htoU, htoU]
            rfl
    _ = hessFun (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J)
            (g.restrictOpen (I := J) V) Psi)
          (fV.comp Psi.toContMDiffMap) xu (toU v) (toU w) := by
            rw [hmetric]
            have hpot : (fun y : U ↦ fPhi y) =ᶠ[nhds xu]
                fun y : U ↦ (fV.comp Psi.toContMDiffMap) y := by
              rw [show (fun y : U ↦ fPhi y) =
                fun y : U ↦ f (Phi (y : M)) by rfl]
              exact Filter.Eventually.of_forall (congrFun hfun)
            have hh := hessFun_congr (I := I)
              (Diffeomorph.pullbackMetricCross (I := I) (J := J)
                (g.restrictOpen (I := J) V) Psi) hpot
            exact congrArg (fun B ↦ B (toU v) (toU w)) hh
    _ = hessFun (I := J) (g.restrictOpen (I := J) V) fV (Psi xu)
          (mfderiv I J (Psi : U → V) xu (toU v))
          (mfderiv I J (Psi : U → V) xu (toU w)) :=
      hessFun_pullbackCross (I := I) (J := J)
        (g.restrictOpen (I := J) V) Psi fV xu (toU v) (toU w)
    _ = hessFun (I := J) g f (((Psi xu : V) : N))
          (mfderiv J J (Subtype.val : V → N) (Psi xu)
            (mfderiv I J (Psi : U → V) xu (toU v)))
          (mfderiv J J (Subtype.val : V → N) (Psi xu)
            (mfderiv I J (Psi : U → V) xu (toU w))) :=
      hessFun_restrictOpen (I := J) g V f (Psi xu)
        (mfderiv I J (Psi : U → V) xu (toU v))
        (mfderiv I J (Psi : U → V) xu (toU w))
    _ = hessFun (I := J) g f (Phi x)
          (mfderiv I J Phi x v) (mfderiv I J Phi x w) := by
      rw [htargetDF, htargetDF]
      rw [hpoint]

end DifferentialGeometry.Geometry.Operator
