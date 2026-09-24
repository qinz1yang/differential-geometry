import DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.MetricData
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

private def inclusionTangentEquiv (U : TopologicalSpace.Opens M) (x : U) :
    TangentSpace I x ≃L[ℝ] TangentSpace I (x : M) := ContinuousLinearEquiv.refl ℝ E

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M] in
private theorem inclusionTangentEquiv_apply (U : TopologicalSpace.Opens M) (x : U)
    (v : TangentSpace I x) : inclusionTangentEquiv (I := I) U x v =
      mfderiv I I (Subtype.val : U → M) x v := by
  rw [mfderiv_subtype_val]
  rfl

omit [BoundarylessManifold I M] in
private theorem restrict_inner (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (x : U) (v w : TangentSpace I x) :
    (g.restrictOpen U).inner x v w = g.inner (x : M)
      (mfderiv I I (Subtype.val : U → M) x v) (mfderiv I I (Subtype.val : U → M) x w) := by
  rw [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]

theorem riemannOp_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (x : U) (u v w : TangentSpace I x) :
    mfderiv I I (Subtype.val : U → M) x (riemannOp (LeviCivita (g.restrictOpen U)) x u v w) =
      riemannOp (LeviCivita g) (x : M) (mfderiv I I (Subtype.val : U → M) x u)
        (mfderiv I I (Subtype.val : U → M) x v) (mfderiv I I (Subtype.val : U → M) x w) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply tangentFlatLinear_injective_gen (I := I) g (x : M)
  ext z
  simp only [tangentFlatLinear_apply_gen]
  obtain ⟨q, rfl⟩ := (inclusionTangentEquiv (I := I) U x).surjective z
  rw [inclusionTangentEquiv_apply]
  have h := metricRm04StandardAt_restrictOpen g U x u v w q
  rw [metricRm04StandardAt_eq_inner_riemannOp, metricRm04StandardAt_eq_inner_riemannOp, restrict_inner] at h
  exact (g.symm (x : M) _ _).trans (h.trans (g.symm (x : M) _ _))

theorem ricciTensor_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (x : U) (v w : TangentSpace I x) :
    ricciTensor (g.restrictOpen U) x v w = ricciTensor g (x : M)
      (mfderiv I I (Subtype.val : U → M) x v) (mfderiv I I (Subtype.val : U → M) x w) := by
  let e := inclusionTangentEquiv (I := I) U x
  have he := inclusionTangentEquiv_apply (I := I) U x
  let A := ricciEndo g (x : M) (mfderiv I I (Subtype.val : U → M) x v)
    (mfderiv I I (Subtype.val : U → M) x w)
  have hconj : ricciEndo (g.restrictOpen U) x v w = e.toLinearEquiv.symm.conj A := by
    apply LinearMap.ext
    intro z
    apply e.injective
    change e (riemannOp (LeviCivita (g.restrictOpen U)) x z v w) = e (e.symm (A (e z)))
    rw [e.apply_symm_apply]
    change inclusionTangentEquiv U x _ = A (inclusionTangentEquiv U x z)
    rw [he, he]
    exact riemannOp_restrictOpen g U x z v w
  rw [ricciTensor_apply, ricciTensor_apply, hconj]
  exact LinearMap.trace_conj' A e.toLinearEquiv.symm

theorem ricciSharp_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (x : U) (v : TangentSpace I x) :
    mfderiv I I (Subtype.val : U → M) x (ricciSharp (g.restrictOpen U) x v) =
      ricciSharp g (x : M) (mfderiv I I (Subtype.val : U → M) x v) := by
  apply tangentFlatLinear_injective_gen (I := I) g (x : M)
  ext z
  simp only [tangentFlatLinear_apply_gen]
  obtain ⟨w, rfl⟩ := (inclusionTangentEquiv (I := I) U x).surjective z
  rw [inclusionTangentEquiv_apply, ← restrict_inner, inner_ricciSharp, inner_ricciSharp]
  exact ricciTensor_restrictOpen g U x v w

end DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false
noncomputable section
open Set Function Filter Bundle Manifold DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RicciIdentity DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold Topology ContDiff ENNReal
namespace DifferentialGeometry.CheegerGromovCompactness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]
  [IsManifold I 1 M] [IsManifold I 2 M]


omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ricciTensor_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U] [BoundarylessManifold I U]
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
    ← metricRm04StandardAt_eq_inner_riemannOp (I := I) (M := U) (g.restrictOpen (I := I) U)
        x (BU i) v w (BU i),
    metricRm04StandardAt_restrictOpen (I := I) g U x (BU i) v w (BU i),
    hBU_apply,
    metricRm04StandardAt_eq_inner_riemannOp (I := I) (M := M) g (x : M)
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
    [T2Space U] [BoundarylessManifold I U]
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
    [T2Space U] [BoundarylessManifold I U]
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
  have hinvU : MetricInverseInBasis (I := I) (M := U)
      (g.restrictOpen (I := I) U) x basisU
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    change MetricInverseInBasis (I := I) (M := U)
      (g.restrictOpen (I := I) U) x basisU (fun a k => if a = k then 1 else 0)
    exact DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) (M := U)
      (g.restrictOpen (I := I) U) basisU hONU
  have hinvM : MetricInverseInBasis (I := I) (M := M) g (x : M) basisM
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    change MetricInverseInBasis (I := I) (M := M) g (x : M) basisM
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
    [T2Space U] [IsManifold I 1 U] (x : U) (slots : Fin 4 → TangentSpace I x) :
    metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
      = metricRm04 (I := I) (M := M) g (x : M)
          (fun q => mfderiv I I (Subtype.val : U → M) x (slots q)) := by
  have hLHS : metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
      = metricRm04StandardAt (I := I) (M := U) (g.restrictOpen (I := I) U) x
          (slots 0) (slots 1) (slots 2) (slots 3) := by
    have hcmm : metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
        = metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x
            (vec4 (slots 0) (slots 1) (slots 2) (slots 3)) :=
      congrArg _ (by funext i; fin_cases i <;> rfl)
    rw [hcmm, metricRm04_apply]
    exact (metricRm04StandardAt_apply (I := I) (M := U) (g.restrictOpen (I := I) U) x
      (slots 0) (slots 1) (slots 2) (slots 3)).symm
  have hRHS : metricRm04 (I := I) (M := M) g (x : M)
        (fun q => mfderiv I I (Subtype.val : U → M) x (slots q))
      = metricRm04StandardAt (I := I) (M := M) g (x : M)
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
    exact (metricRm04StandardAt_apply (I := I) (M := M) g (x : M)
      (mfderiv I I (Subtype.val : U → M) x (slots 0))
      (mfderiv I I (Subtype.val : U → M) x (slots 1))
      (mfderiv I I (Subtype.val : U → M) x (slots 2))
      (mfderiv I I (Subtype.val : U → M) x (slots 3))).symm
  rw [hLHS, hRHS]
  exact metricRm04StandardAt_restrictOpen (I := I) g U x (slots 0) (slots 1) (slots 2) (slots 3)


end DifferentialGeometry.CheegerGromovCompactness
end
