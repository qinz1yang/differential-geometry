import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativePullback

import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNormRestriction
import DifferentialGeometry.Geometry.Curvature.RestrictOpenRm04
import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic


open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.Auxiliary
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow (SolutionOn IsSolutionOn MetricVariationEquationOn
  ricciNorm SolutionFamily RicciAtFamily)

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]
  [IsManifold I 1 M] [IsManifold I 2 M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [IsManifold I 1 M] [IsManifold I 2 M] in
private theorem mfderiv_subtype_val_eq_modelLift
    (U : TopologicalSpace.Opens M) (x : U) (v : TangentSpace I x) :
    mfderiv I I (Subtype.val : U → M) x v =
      (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).symm
        (tangentSpaceModelContinuousLinearEquiv (I := I) x v) := by
  apply (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).injective
  rw [mfderiv_subtype_val_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact (tangentSpaceModelContinuousLinearEquiv_apply (I := I) (x : M) v).trans
    (tangentSpaceModelContinuousLinearEquiv_apply (I := I) x v).symm

omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ricciTensor_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] (x : U) (v w : TangentSpace I x) :
    ricciTensor (I := I) (M := U) (g.restrictOpen (I := I) U) x v w
      = ricciTensor (I := I) (M := M) g (x : M)
          (mfderiv I I (Subtype.val : U → M) x v)
          (mfderiv I I (Subtype.val : U → M) x w) := by
  classical
  obtain ⟨B, hB⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) (M := M) g (x : M)
  let hdim : Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I (x : M)) := by
    rfl
  let Bf : Fin (Module.finrank ℝ E) → TangentSpace I (x : M) :=
    fun i => B (Fin.cast hdim i)
  have hBf : ∀ i j, g.inner (x : M) (Bf i) (Bf j) =
      if i = j then (1 : ℝ) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa only [Bf, if_pos] using hB (Fin.cast hdim i) (Fin.cast hdim i)
    · have hcast : Fin.cast hdim i ≠ Fin.cast hdim j := by
        intro h
        apply hij
        apply Fin.ext
        exact congrArg Fin.val h
      simpa only [Bf, if_neg hij, if_neg hcast] using
        hB (Fin.cast hdim i) (Fin.cast hdim j)
  let eU : TangentSpace I (x : M) ≃ₗ[ℝ] TangentSpace I x :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).toLinearEquiv.trans
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.toLinearEquiv
  let BU : Fin (Module.finrank ℝ E) → TangentSpace I x := fun i => eU (Bf i)
  have hBU_apply (i) :
      mfderiv I I (Subtype.val : U → M) x (BU i) = Bf i := by
    rw [mfderiv_subtype_val_apply]
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).injective
    change tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M) (Bf i))) =
      tangentSpaceModelContinuousLinearEquiv (I := I) (x : M) (Bf i)
    rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
    exact tangentSpaceModelContinuousLinearEquiv_apply (I := I) (x : M) (Bf i)
  have hBU : ∀ i j,
      (g.restrictOpen (I := I) U).inner x (BU i) (BU j) =
        if i = j then (1 : ℝ) else 0 := by
    intro i j
    calc
      _ = g.inner (x : M)
          (mfderiv I I (Subtype.val : U → M) x (BU i))
          (mfderiv I I (Subtype.val : U → M) x (BU j)) := by
        rw [SmoothRiemannianMetric.restrictOpen_inner,
          mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
      _ = _ := by rw [hBU_apply, hBU_apply]; exact hBf i j
  rw [ricciTensor_eq_orthonormal_trace (I := I) (M := U)
      (g.restrictOpen (I := I) U) x v w BU hBU,
    ricciTensor_eq_orthonormal_trace (I := I) (M := M) g (x : M)
      (mfderiv I I (Subtype.val : U → M) x v)
      (mfderiv I I (Subtype.val : U → M) x w) Bf hBf]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [(g.restrictOpen (I := I) U).symm x
        (riemannOp (LeviCivita (I := I) (g.restrictOpen (I := I) U)) x (BU i) v w) (BU i),
    ← metricRm04StdAt_eq_inner_riemannOp (I := I) (M := U) (g.restrictOpen (I := I) U)
        x (BU i) v w (BU i),
    metricRm04StdAt_restrictOpen (I := I) g U x (BU i) v w (BU i),
    hBU_apply,
    metricRm04StdAt_eq_inner_riemannOp (I := I) (M := M) g (x : M)
      (Bf i) (mfderiv I I (Subtype.val : U → M) x v)
      (mfderiv I I (Subtype.val : U → M) x w) (Bf i),
    g.symm (x : M) (Bf i)
      (riemannOp (LeviCivita (I := I) g) (x : M) (Bf i)
        (mfderiv I I (Subtype.val : U → M) x v)
        (mfderiv I I (Subtype.val : U → M) x w))]

omit [I.Boundaryless] [IsManifold I 2 M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricRicci_restrictOpen_eval
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] (x : U) (slots : Fin 2 → TangentSpace I x) :
    metricRicci (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
      = metricRicci (I := I) (M := M) g (x : M)
          (fun q => mfderiv I I (Subtype.val : U → M) x (slots q)) := by
  have hLHS : metricRicci (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
      = ricciTensor (I := I) (M := U) (g.restrictOpen (I := I) U) x (slots 0) (slots 1) := by
    have hcmm : metricRicciAt (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
        = metricRicciAt (I := I) (M := U) (g.restrictOpen (I := I) U) x
          (vec2 (slots 0) (slots 1)) :=
      congrArg _ (by funext i; fin_cases i <;> rfl)
    rw [metricRicci_apply, hcmm]
    exact metricRicciAt_apply_eq_ricciTensor (I := I) (g.restrictOpen (I := I) U) x (slots 0)
      (slots 1)
  have hRHS : metricRicci (I := I) (M := M) g (x : M)
        (fun q => mfderiv I I (Subtype.val : U → M) x (slots q)) =
      ricciTensor (I := I) (M := M) g (x : M)
        (mfderiv I I (Subtype.val : U → M) x (slots 0))
        (mfderiv I I (Subtype.val : U → M) x (slots 1)) := by
    have hcmm : metricRicciAt (I := I) (M := M) g (x : M)
          (fun q => mfderiv I I (Subtype.val : U → M) x (slots q))
        = metricRicciAt (I := I) (M := M) g (x : M)
          (vec2 (mfderiv I I (Subtype.val : U → M) x (slots 0))
            (mfderiv I I (Subtype.val : U → M) x (slots 1))) :=
      congrArg _ (by
        funext i
        fin_cases i <;> rfl)
    rw [metricRicci_apply, hcmm]
    exact metricRicciAt_apply_eq_ricciTensor (I := I) g (x : M)
      (mfderiv I I (Subtype.val : U → M) x (slots 0))
      (mfderiv I I (Subtype.val : U → M) x (slots 1))
  rw [hLHS, hRHS]
  exact ricciTensor_restrictOpen (I := I) g U x (slots 0) (slots 1)

omit [I.Boundaryless] [IsManifold I 2 M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricScalarAt_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] (x : U) :
    metricScalarAt (I := I) (M := U) (g.restrictOpen (I := I) U) x
      = metricScalarAt (I := I) (M := M) g (x : M) := by
  classical
  obtain ⟨basisU, hONU⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) (M := U)
    (g.restrictOpen (I := I) U) x
  let eM : TangentSpace I x ≃ₗ[ℝ] TangentSpace I (x : M) :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).toLinearEquiv.trans
      (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).symm.toLinearEquiv
  let basisM := basisU.map eM
  have hbasisM_apply (i) : basisM i =
      mfderiv I I (Subtype.val : U → M) x (basisU i) := by
    rw [Module.Basis.map_apply]
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).injective
    change tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).symm
          (tangentSpaceModelContinuousLinearEquiv (I := I) x (basisU i))) =
      tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)
        (mfderiv I I (Subtype.val : U → M) x (basisU i))
    rw [ContinuousLinearEquiv.apply_symm_apply, mfderiv_subtype_val_apply]
    exact (tangentSpaceModelContinuousLinearEquiv_apply (I := I) x (basisU i)).trans
      (tangentSpaceModelContinuousLinearEquiv_apply (I := I) (x : M) (basisU i)).symm
  have hONM : ∀ i j, g.inner (x : M) (basisM i) (basisM j) =
      if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hbasisM_apply, hbasisM_apply]
    calc
      _ = (g.restrictOpen (I := I) U).inner x (basisU i) (basisU j) := by
        rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
        exact (SmoothRiemannianMetric.restrictOpen_inner g U x
          (basisU i) (basisU j)).symm
      _ = _ := hONU i j
  have hinvU : MetricInverseInBasisGen (I := I) (M := U)
      (g.restrictOpen (I := I) U) x basisU
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    change MetricInverseInBasisGen (I := I) (M := U)
      (g.restrictOpen (I := I) U) x basisU (fun a k => if a = k then 1 else 0)
    exact DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) (M := U)
      (g.restrictOpen (I := I) U) basisU hONU
  have hinvM : MetricInverseInBasisGen (I := I) (M := M) g (x : M) basisM
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    change MetricInverseInBasisGen (I := I) (M := M) g (x : M) basisM
      (fun a k => if a = k then 1 else 0)
    exact DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) (M := M) g basisM hONM
  rw [metricScalarAt_def, metricScalarAt_def,
    metricTracePair0SAt_eq_sum_basis (I := I) (M := U)
      (g.restrictOpen (I := I) U) basisU
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) hinvU
      (metricRicciAt (I := I) (M := U) (g.restrictOpen (I := I) U) x),
    metricTracePair0SAt_eq_sum_basis (I := I) (M := M) g basisM
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) hinvM
      (metricRicciAt (I := I) (M := M) g (x : M))]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have e1 : metricRicciAt (I := I) (M := U) (g.restrictOpen (I := I) U) x
        (vec2 (basisU i) (basisU j)) =
      ricciTensor (I := I) (M := U) (g.restrictOpen (I := I) U) x
        (basisU i) (basisU j) :=
    metricRicciAt_apply_eq_ricciTensor (I := I) (g.restrictOpen (I := I) U) x
      (basisU i) (basisU j)
  have e2 : metricRicciAt (I := I) (M := M) g (x : M)
        (vec2 (basisM i) (basisM j)) =
      ricciTensor (I := I) (M := M) g (x : M) (basisM i) (basisM j) :=
    metricRicciAt_apply_eq_ricciTensor (I := I) g (x : M) (basisM i) (basisM j)
  have hric : metricRicciAt (I := I) (M := U) (g.restrictOpen (I := I) U) x
        (vec2 (basisU i) (basisU j)) =
      metricRicciAt (I := I) (M := M) g (x : M) (vec2 (basisM i) (basisM j)) := by
    rw [e1, e2]
    rw [hbasisM_apply, hbasisM_apply]
    exact ricciTensor_restrictOpen (I := I) g U x (basisU i) (basisU j)
  exact congrArg (fun r => identityInvMetric i j * r) hric

omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metricRm04_restrictOpen_eval
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [IsManifold I 1 U] (x : U) (slots : Fin 4 → TangentSpace I x) :
    metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
      = metricRm04 (I := I) (M := M) g (x : M)
          (fun q => mfderiv I I (Subtype.val : U → M) x (slots q)) := by
  have hLHS : metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
      = metricRm04StdAt (I := I) (M := U) (g.restrictOpen (I := I) U) x
          (slots 0) (slots 1) (slots 2) (slots 3) := by
    have hcmm : metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
        = metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x
            (vec4 (slots 0) (slots 1) (slots 2) (slots 3)) :=
      congrArg _ (by funext i; fin_cases i <;> rfl)
    rw [hcmm, metricRm04_apply]
    exact (metricRm04StdAt_apply (I := I) (M := U) (g.restrictOpen (I := I) U) x
      (slots 0) (slots 1) (slots 2) (slots 3)).symm
  have hRHS : metricRm04 (I := I) (M := M) g (x : M)
        (fun q => mfderiv I I (Subtype.val : U → M) x (slots q))
      = metricRm04StdAt (I := I) (M := M) g (x : M)
          (mfderiv I I (Subtype.val : U → M) x (slots 0))
          (mfderiv I I (Subtype.val : U → M) x (slots 1))
          (mfderiv I I (Subtype.val : U → M) x (slots 2))
          (mfderiv I I (Subtype.val : U → M) x (slots 3)) := by
    have hcmm : metricRm04 (I := I) (M := M) g (x : M)
          (fun q => mfderiv I I (Subtype.val : U → M) x (slots q))
        = metricRm04 (I := I) (M := M) g (x : M)
            (vec4 (mfderiv I I (Subtype.val : U → M) x (slots 0))
              (mfderiv I I (Subtype.val : U → M) x (slots 1))
              (mfderiv I I (Subtype.val : U → M) x (slots 2))
              (mfderiv I I (Subtype.val : U → M) x (slots 3))) :=
      congrArg _ (by funext i; fin_cases i <;> rfl)
    rw [hcmm, metricRm04_apply]
    exact (metricRm04StdAt_apply (I := I) (M := M) g (x : M)
      (mfderiv I I (Subtype.val : U → M) x (slots 0))
      (mfderiv I I (Subtype.val : U → M) x (slots 1))
      (mfderiv I I (Subtype.val : U → M) x (slots 2))
      (mfderiv I I (Subtype.val : U → M) x (slots 3))).symm
  rw [hLHS, hRHS]
  exact metricRm04StdAt_restrictOpen (I := I) g U x (slots 0) (slots 1) (slots 2) (slots 3)

variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

def solutionOnRestrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : TopologicalSpace.Opens M)
    [hSigma : SigmaCompactSpace U] [T2Space U] :
    SolutionOn (I := I) (M := U) D := by
  let _ := hSigma
  exact { base := { metric := fun t => (S.base.metric t).restrictOpen (I := I) U } }

open Classical in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [IsManifold I 2 M] in
theorem restrictOpenPush_contMDiffWithinAt
    {Idx : Type} (U : TopologicalSpace.Opens M)
    [IsManifold I 1 U] {frame : Idx → (x : U) → TangentSpace I x} {u : Set U}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (i : Idx) (x : U) (hxu : x ∈ u) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        (if h : y ∈ U then
          (tangentSpaceModelContinuousLinearEquiv (I := I) y).symm
            (tangentSpaceModelContinuousLinearEquiv (I := I) (⟨y, h⟩ : U)
              (frame i ⟨y, h⟩))
        else 0)) (Subtype.val '' u) (x : M) := by
  set cor : M → U := fun y => if h : y ∈ U then ⟨y, h⟩ else x with hcor_def
  have hcorval : ∀ z : U, cor (z : M) = z := by
    intro z; rw [hcor_def]; simp only [dif_pos z.2, Subtype.coe_eta]
  have hcor : ContMDiffAt I I (∞ : WithTop ℕ∞) cor (x : M) := by
    rw [← contMDiffAt_subtype_iff (I := I) (I' := I) (U := U) (n := ∞) (x := x)]
    have hid : (fun z : U => cor (z : M)) = id := by funext z; simpa using hcorval z
    rw [hid]
    exact contMDiffAt_id
  have hpush : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (fun z : U => tangentMap I I (Subtype.val : U → M)
        (TotalSpace.mk' E (E := fun w : U => TangentSpace I w) z (frame i z))) u x :=
    ((contMDiff_subtype_val (I := I) (U := U) (n := ∞)).contMDiff_tangentMap
      (by simp)).contMDiffAt.comp_contMDiffWithinAt x (hframe.contMDiffOn i x hxu)
  have hmaps : Set.MapsTo cor (Subtype.val '' u) u := by
    rintro y ⟨z, hz, rfl⟩
    rw [hcorval z]; exact hz
  have hpush' : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (fun z : U => tangentMap I I (Subtype.val : U → M)
        (TotalSpace.mk' E (E := fun w : U => TangentSpace I w) z (frame i z))) u (cor (x : M)) := by
    rw [hcorval x]; exact hpush
  have hgcor : ∀ z : M, (hz : z ∈ U) →
      (fun z : U => tangentMap I I (Subtype.val : U → M)
        (TotalSpace.mk' E (E := fun w : U => TangentSpace I w) z (frame i z))) (cor z)
        = TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
            (if h : z ∈ U then
              (tangentSpaceModelContinuousLinearEquiv (I := I) z).symm
                (tangentSpaceModelContinuousLinearEquiv (I := I) (⟨z, h⟩ : U)
                  (frame i ⟨z, h⟩))
            else 0) := by
    intro z hz
    have hcz : cor z = ⟨z, hz⟩ := by simp only [hcor_def, dif_pos hz]
    rw [dif_pos hz, hcz]
    change TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
        (mfderiv I I (Subtype.val : U → M) (⟨z, hz⟩ : U) (frame i ⟨z, hz⟩)) =
      TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
        ((tangentSpaceModelContinuousLinearEquiv (I := I) z).symm
          (tangentSpaceModelContinuousLinearEquiv (I := I) (⟨z, hz⟩ : U)
            (frame i ⟨z, hz⟩)))
    congr 1
    exact mfderiv_subtype_val_eq_modelLift (I := I) U (⟨z, hz⟩ : U)
      (frame i ⟨z, hz⟩)
  refine (hpush'.comp (x : M) hcor.contMDiffWithinAt hmaps).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds ((U.isOpen).mem_nhds x.2)] with z hz
    exact (hgcor z hz).symm
  · exact (hgcor (x : M) x.2).symm

open Classical in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [IsManifold I 2 M] in
theorem isLocalFrameOn_restrictOpenPush
    {Idx : Type} (U : TopologicalSpace.Opens M)
    [IsManifold I 1 U] {frame : Idx → (x : U) → TangentSpace I x} {u : Set U}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) :
    IsLocalFrameOn (V := (TangentSpace I : M → Type _)) I E (∞ : WithTop ℕ∞)
      (fun i (y : M) => if h : y ∈ U then
        (tangentSpaceModelContinuousLinearEquiv (I := I) y).symm
          (tangentSpaceModelContinuousLinearEquiv (I := I) (⟨y, h⟩ : U)
            (frame i ⟨y, h⟩))
      else 0) (Subtype.val '' u) where
  linearIndependent {y} hy := by
    obtain ⟨x, hxu, rfl⟩ := hy
    have hxU : (x : M) ∈ U := x.2
    let eM : TangentSpace I x ≃ₗ[ℝ] TangentSpace I (x : M) :=
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).toLinearEquiv.trans
        (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).symm.toLinearEquiv
    let basisM := (hframe.toBasisAt hxu).map eM
    have hval :
        (fun i => if h : (x : M) ∈ U then
          (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).symm
            (tangentSpaceModelContinuousLinearEquiv (I := I) (⟨(x : M), h⟩ : U)
              (frame i ⟨(x : M), h⟩))
        else 0) = fun i => basisM i := by
      funext i
      rw [dif_pos hxU, Module.Basis.map_apply, IsLocalFrameOn.toBasisAt_coe]
      rfl
    exact hval.symm ▸ basisM.linearIndependent
  generating {y} hy := by
    obtain ⟨x, hxu, rfl⟩ := hy
    have hxU : (x : M) ∈ U := x.2
    let eM : TangentSpace I x ≃ₗ[ℝ] TangentSpace I (x : M) :=
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).toLinearEquiv.trans
        (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).symm.toLinearEquiv
    let basisM := (hframe.toBasisAt hxu).map eM
    have hval :
        (fun i => if h : (x : M) ∈ U then
          (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).symm
            (tangentSpaceModelContinuousLinearEquiv (I := I) (⟨(x : M), h⟩ : U)
              (frame i ⟨(x : M), h⟩))
        else 0) = fun i => basisM i := by
      funext i
      rw [dif_pos hxU, Module.Basis.map_apply, IsLocalFrameOn.toBasisAt_coe]
      rfl
    exact hval.symm ▸ (Module.Basis.span_eq basisM).ge
  contMDiffOn i := by
    intro y hy
    obtain ⟨x, hxu, rfl⟩ := hy
    exact restrictOpenPush_contMDiffWithinAt (I := I) U hframe i x hxu

omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem frameCompSmooth_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U]
    [IsManifold I 1 U] [hManifoldTop : IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    {Idx : Type} [Finite Idx] (frame : Idx → (x : U) → TangentSpace I x) {u : Set U}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (i j : Idx) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × U =>
        ((solutionOnRestrictOpen (I := I) S U).family.metric p.1).inner p.2
          (frame i p.2) (frame j p.2))
      (D.regular ×ˢ u) := by
  let _ := hManifoldTop
  classical
  let _ := Fintype.ofFinite Idx
  set frameM : Idx → (y : M) → TangentSpace I y :=
    fun k (y : M) => if h : y ∈ U then
      (tangentSpaceModelContinuousLinearEquiv (I := I) y).symm
        (tangentSpaceModelContinuousLinearEquiv (I := I) (⟨y, h⟩ : U)
          (frame k ⟨y, h⟩))
    else 0 with hframeM_def
  have hframeM : IsLocalFrameOn (V := (TangentSpace I : M → Type _)) I E (∞ : WithTop ℕ∞)
      frameM (Subtype.val '' u) := isLocalFrameOn_restrictOpenPush (I := I) U hframe
  have hpf := hS.smoothMetric.frameCompSmooth frameM hframeM i j
  have hmap : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (∞ : WithTop ℕ∞)
      (fun p : ℝ × U => (p.1, (p.2 : M))) :=
    contMDiff_fst.prodMk ((contMDiff_subtype_val (I := I) (U := U)).comp contMDiff_snd)
  have hmaps : Set.MapsTo (fun p : ℝ × U => (p.1, (p.2 : M)))
      (D.regular ×ˢ u) (D.regular ×ˢ (Subtype.val '' u)) :=
    fun p hp => ⟨hp.1, Set.mem_image_of_mem _ hp.2⟩
  have hcomp := hpf.comp hmap.contMDiffOn hmaps
  refine hcomp.congr ?_
  intro p hp
  have hxU : (p.2 : M) ∈ U := p.2.2
  have hval : ∀ k, frameM k (p.2 : M) =
      mfderiv I I (Subtype.val : U → M) p.2 (frame k p.2) := by
    intro k
    rw [hframeM_def]
    change (if h : (p.2 : M) ∈ U then
      (tangentSpaceModelContinuousLinearEquiv (I := I) (p.2 : M)).symm
        (tangentSpaceModelContinuousLinearEquiv (I := I) (⟨(p.2 : M), h⟩ : U)
          (frame k ⟨(p.2 : M), h⟩))
    else 0) = mfderiv I I (Subtype.val : U → M) p.2 (frame k p.2)
    rw [dif_pos hxU]
    exact (mfderiv_subtype_val_eq_modelLift (I := I) U p.2 (frame k p.2)).symm
  simp only [Function.comp_apply, hval]
  change ((S.base.metric p.1).restrictOpen (I := I) U).inner p.2
      (frame i p.2) (frame j p.2) =
    (S.base.metric p.1).inner (p.2 : M)
      (mfderiv I I (Subtype.val : U → M) p.2 (frame i p.2))
      (mfderiv I I (Subtype.val : U → M) p.2 (frame j p.2))
  rw [SmoothRiemannianMetric.restrictOpen_inner,
    mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]

omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metricFamilySmoothOn_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [hBoundaryless : BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    MetricFamilySmoothOn (I := I) D (solutionOnRestrictOpen (I := I) S U).family.metric where
  coeff x X Y := hS.smoothMetric.coeff (x : M) X Y
  coeff_cont x X Y := hS.smoothMetric.coeff_cont (x : M) X Y
  metricTensor_cont := by
    let _ := hBoundaryless
    apply tensor0SFamilyContinuousOnSet.congr
      (tensor0SFamilyContinuousOnSet.restrictOpen (I := I)
        (fun t x => Tensor0SBundle.metricTensorField (I := I) (S.family.metric t) x)
        hS.smoothMetric.metricTensor_cont U)
    intro t _ht x
    ext slots
    change Tensor0SBundle.metricTensorField (I := I) (S.family.metric t) (x : M)
        (fun q => mfderiv I I (Subtype.val : U → M) x (slots q)) =
      Tensor0SBundle.metricTensorField (I := I)
        ((S.family.metric t).restrictOpen (I := I) U) x slots
    rw [Tensor0SBundle.metricTensorField_apply, Tensor0SBundle.metricTensorField_apply,
      SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply,
      mfderiv_subtype_val_apply]
  frameCompSmooth := by
    intro Idx _ frame u hframe i j
    exact frameCompSmooth_restrictOpen (I := I) S hS U frame hframe i j

omit [I.Boundaryless] [IsManifold I 2 M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricVariationEquation_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [hManifoldTop : IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    MetricVariationEquationOn (I := I) (solutionOnRestrictOpen (I := I) S U) := by
  let _ := hManifoldTop
  intro t x X Y
  have hric :
      RicciAtFamily.toTensorField (I := I)
          (solutionOnRestrictOpen (I := I) S U).ricciAt (t : ℝ) x X Y
        = RicciAtFamily.toTensorField (I := I) S.ricciAt (t : ℝ) (x : M)
          (mfderiv I I (Subtype.val : U → M) x X)
          (mfderiv I I (Subtype.val : U → M) x Y) := by
    simp only [RicciAtFamily.toTensorField_apply]
    change metricRicciAt (I := I)
          ((S.base.metric (t : ℝ)).restrictOpen (I := I) U) x (vec2 X Y)
        = metricRicciAt (I := I) (S.base.metric (t : ℝ)) (x : M)
          (vec2 (mfderiv I I (Subtype.val : U → M) x X)
            (mfderiv I I (Subtype.val : U → M) x Y))
    rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor]
    exact ricciTensor_restrictOpen (I := I) (S.base.metric (t : ℝ)) U x X Y
  rw [hric]
  convert hS.equation t (x : M)
      (mfderiv I I (Subtype.val : U → M) x X)
      (mfderiv I I (Subtype.val : U → M) x Y) using 1
  funext s
  calc
    _ = (S.family.metric s).inner (x : M) X Y :=
      SmoothRiemannianMetric.restrictOpen_inner (S.family.metric s) U x X Y
    _ = _ := by rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]

omit [I.Boundaryless] [IsManifold I 2 M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalar_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [hManifoldTop : IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (t : ℝ) (x : U) :
    (solutionOnRestrictOpen (I := I) S U).scalar t x = S.scalar t (x : M) := by
  let _ := hManifoldTop
  simp only [SolutionOn.scalar, SolutionFamily.scalar, solutionOnRestrictOpen]
  exact metricScalarAt_restrictOpen (I := I) (S.base.metric t) U x

omit [I.Boundaryless] [IsManifold I 2 M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalarCont_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [hManifoldTop : IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    ContinuousOn (fun q : ℝ × U => (solutionOnRestrictOpen (I := I) S U).scalar q.1 q.2)
      (D.carrier ×ˢ (Set.univ : Set U)) := by
  have heq : (fun q : ℝ × U => (solutionOnRestrictOpen (I := I) S U).scalar q.1 q.2)
      = (fun p : ℝ × M => S.scalar p.1 p.2)
          ∘ (fun q : ℝ × U => ((q.1, (q.2 : M)) : ℝ × M)) := by
    funext q; exact scalar_restrictOpen (I := I) S U q.1 q.2
  rw [heq]
  exact hS.scalarCont.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
    (fun q hq => ⟨hq.1, Set.mem_univ _⟩)

omit [I.Boundaryless] [IsManifold I 2 M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalarTime_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    {K : Set ℝ} {t : ℝ} (htK : t ∈ K) (hKsub : K ⊆ D.carrier) (x : U) :
    DifferentiableWithinAt ℝ
      (fun s : ℝ => (solutionOnRestrictOpen (I := I) S U).scalar s x) K t := by
  have heq : (fun s : ℝ => (solutionOnRestrictOpen (I := I) S U).scalar s x)
      = fun s : ℝ => S.scalar s (x : M) := by
    funext s; exact scalar_restrictOpen (I := I) S U s x
  rw [heq]
  exact hS.scalarTime htK hKsub (x : M)

omit [I.Boundaryless] [IsManifold I 2 M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciCont_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [hManifoldTop : IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    tensor0SFamilyContinuousOnSet (I := I) (M := U) 2 D.carrier
      (fun t x => (solutionOnRestrictOpen (I := I) S U).ricci t x) := by
  let _ := hManifoldTop
  apply tensor0SFamilyContinuousOnSet.congr
    (tensor0SFamilyContinuousOnSet.restrictOpen (I := I)
      (fun t x => S.ricci t x) hS.ricciCont U)
  intro t _ht x
  ext slots
  change metricRicci (I := I) (M := M) (S.base.metric t) (x : M)
      (fun q => mfderiv I I (Subtype.val : U → M) x (slots q)) =
    metricRicci (I := I) (M := U) ((S.base.metric t).restrictOpen (I := I) U) x slots
  exact (metricRicci_restrictOpen_eval (I := I) (S.base.metric t) U x slots).symm

omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem rm04Cont_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [hBoundaryless : BoundarylessManifold I U]
    [IsManifold I 1 U] [hManifoldTop : IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    tensor0SFamilyContinuousOnSet (I := I) (M := U) 4 D.carrier
      (fun t x => (solutionOnRestrictOpen (I := I) S U).base.rm04 t x) := by
  let _ := hBoundaryless
  let _ := hManifoldTop
  apply tensor0SFamilyContinuousOnSet.congr
    (tensor0SFamilyContinuousOnSet.restrictOpen (I := I)
      (fun t x => S.base.rm04 t x) hS.rm04Cont U)
  intro t _ht x
  ext slots
  change metricRm04 (I := I) (M := M) (S.base.metric t) (x : M)
      (fun q => mfderiv I I (Subtype.val : U → M) x (slots q)) =
    metricRm04 (I := I) (M := U) ((S.base.metric t).restrictOpen (I := I) U) x slots
  exact (metricRm04_restrictOpen_eval (I := I) (S.base.metric t) U x slots).symm

omit [I.Boundaryless] [IsManifold I 2 M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciNorm_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [hManifoldTop : IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (t : ℝ) (x : U) :
    ricciNorm (I := I) (solutionOnRestrictOpen (I := I) S U) t x
      = ricciNorm (I := I) S t (x : M) := by
  let _ := hManifoldTop
  have hsec : metricRicci (I := I) (M := U) ((S.base.metric t).restrictOpen (I := I) U) x
      = metricRicci (I := I) (M := M) (S.base.metric t) (x : M) := by
    ext slots
    change metricRicci (I := I) (M := U)
        ((S.base.metric t).restrictOpen (I := I) U) x slots =
      metricRicci (I := I) (M := M) (S.base.metric t) (x : M) slots
    convert metricRicci_restrictOpen_eval (I := I) (S.base.metric t) U x slots using 1
    congr 1
    funext q
    rw [mfderiv_subtype_val_apply]
  have hnorm := normSq0S_restrictOpen_apply (I := I) (S.base.metric t) U 2 x
    (metricRicci (I := I) (M := U) ((S.base.metric t).restrictOpen (I := I) U) x)
  simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family, SolutionFamily.ricci_apply,
    SolutionFamily.ricciAt, metricRicci_apply, solutionOnRestrictOpen] at *
  rw [hnorm, hsec]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem ricciNormSpace_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [IsManifold I 1 U]
    (t : ℝ) (x : U) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (ricciNorm (I := I) (solutionOnRestrictOpen (I := I) S U) t) x := by
  have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (ricciNorm (I := I) (solutionOnRestrictOpen (I := I) S U) t) := by
    refine (DifferentialGeometry.Tensor.RSTensor.normSq02_smooth (I := I) (M := U)
      ((solutionOnRestrictOpen (I := I) S U).family.metric t)
      (metricRicci (I := I) (M := U)
        ((solutionOnRestrictOpen (I := I) S U).family.metric t))).congr ?_
    intro y
    simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
      SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
  exact hsmooth.contMDiffAt.mdifferentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem smoothConnection_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [IsManifold I 1 U] :
    ConnectionFamilySmoothOn (I := I) (solutionOnRestrictOpen (I := I) S U).family := by
  intro t
  exact leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I)
    ((solutionOnRestrictOpen (I := I) S U).base.metric (t : ℝ))

omit [I.Boundaryless] [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem isSolutionOn_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    IsSolutionOn (I := I) (solutionOnRestrictOpen (I := I) S U) where
  smoothMetric := metricFamilySmoothOn_restrictOpen (I := I) S hS U
  smoothConnection := smoothConnection_restrictOpen (I := I) S U
  equation := metricVariationEquation_restrictOpen (I := I) S hS U
  scalarCont := scalarCont_restrictOpen (I := I) S hS U
  scalarTime := fun htK hKsub x => scalarTime_restrictOpen (I := I) S hS U htK hKsub x
  ricciCont := ricciCont_restrictOpen (I := I) S hS U
  rm04Cont := rm04Cont_restrictOpen (I := I) S hS U
  ricciNormSpace := fun t _ht x => ricciNormSpace_restrictOpen (I := I) S U t x
  ricciNormGrad := by
    intro t _ht x
    have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
        (ricciNorm (I := I) (solutionOnRestrictOpen (I := I) S U) t) := by
      refine (DifferentialGeometry.Tensor.RSTensor.normSq02_smooth (I := I) (M := U)
        ((solutionOnRestrictOpen (I := I) S U).family.metric t)
        (metricRicci (I := I) (M := U)
          ((solutionOnRestrictOpen (I := I) S U).family.metric t))).congr ?_
      intro y
      simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
        SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
    exact DifferentialGeometry.Geometry.Operator.gradientFun_mdiffAt (I := I)
      ((solutionOnRestrictOpen (I := I) S U).family.metric t) hsmooth x

end HCGCompactness
end DifferentialGeometry
