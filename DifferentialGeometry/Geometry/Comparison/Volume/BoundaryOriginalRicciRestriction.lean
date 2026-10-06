import DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import DifferentialGeometry.Geometry.Curvature.Components.Basic

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.CovariantDerivative
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
private theorem boundaryOriginal_metricRm13At_restrictOpen_component
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U] [IsManifold I 1 U] (x : U) {Idx : Type*}
    (BU : Module.Basis Idx ℝ (TangentSpace I x))
    (BM : Module.Basis Idx ℝ (TangentSpace I (x : M)))
    (hmap : ∀ j, mfderiv I I (Subtype.val : U → M) x (BU j) = BM j)
    (i : Idx) (hcoord : ∀ z : E, (BU.coord i) z = (BM.coord i) z)
    (v w : TangentSpace I x) :
    metricRm13At (g.restrictOpen (I := I) U) x
        (dualToCotangent (I := I) (BU.coord i)) (vec3 (BU i) v w) =
      metricRm13At (I := I) g (x : M)
        (dualToCotangent (I := I) (BM.coord i))
          (vec3 (BM i)
            (mfderiv I I (Subtype.val : U → M) x v)
            (mfderiv I I (Subtype.val : U → M) x w)) := by
  obtain ⟨Xs, hXs⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) (x : M) (BM i)
  obtain ⟨Ys, hYs⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) (x : M)
      (mfderiv I I (Subtype.val : U → M) x v)
  obtain ⟨Zs, hZs⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) (x : M)
      (mfderiv I I (Subtype.val : U → M) x w)
  let XU := restrictOpenTangentSection (I := I) U Xs
  let YU := restrictOpenTangentSection (I := I) U Ys
  let ZU := restrictOpenTangentSection (I := I) U Zs
  have hXsU : restrictOpenTangentField (I := I) U Xs x = BU i := by
    rw [restrictOpenTangentField_apply, hXs]
    exact (hmap i).symm.trans (mfderiv_subtype_val_apply U x (BU i))
  have hYsU : restrictOpenTangentField (I := I) U Ys x = v := by
    rw [restrictOpenTangentField_apply, hYs, mfderiv_subtype_val_apply]
  have hZsU : restrictOpenTangentField (I := I) U Zs x = w := by
    rw [restrictOpenTangentField_apply, hZs, mfderiv_subtype_val_apply]
  have hXUFun : (fun p : U => XU p) =
      restrictOpenTangentField (I := I) U (fun y : M => Xs y) := by
    funext p
    rfl
  have hYUFun : (fun p : U => YU p) =
      restrictOpenTangentField (I := I) U (fun y : M => Ys y) := by
    funext p
    rfl
  have hZUFun : (fun p : U => ZU p) =
      restrictOpenTangentField (I := I) U (fun y : M => Zs y) := by
    funext p
    rfl
  have hR :
      metricRm13At (g.restrictOpen (I := I) U) x
          (dualToCotangent (I := I) (BU.coord i))
          (vec3 (XU x) (YU x) (ZU x)) =
        metricRm13At (I := I) g (x : M)
          (dualToCotangent (I := I) (BM.coord i))
          (vec3 (Xs (x : M)) (Ys (x : M)) (Zs (x : M))) := by
    rw [metricRm13At, metricRm13At]
    rw [riemannCurvatureAt_apply_smooth (I := I)
      (cov := metricCov (g.restrictOpen (I := I) U))
      (hcov := metricCov_smooth (g.restrictOpen (I := I) U)) XU YU ZU]
    rw [riemannCurvatureAt_apply_smooth (I := I)
      (cov := metricCov g) (hcov := metricCov_smooth g) Xs Ys Zs]
    simp only [cotangentToDual_dualToCotangent]
    rw [hXUFun, hYUFun, hZUFun]
    rw [connectionRiemannCurvatureField_restrictOpen (I := I) g U Xs Ys Zs x]
    change (BU.coord i) _ = (BM.coord i) _
    exact hcoord _
  have hXUX : XU x = BU i := by
    change restrictOpenTangentField (I := I) U Xs x = BU i
    exact hXsU
  have hYUX : YU x = v := by
    change restrictOpenTangentField (I := I) U Ys x = v
    exact hYsU
  have hZUX : ZU x = w := by
    change restrictOpenTangentField (I := I) U Zs x = w
    exact hZsU
  simpa only [hXUX, hYUX, hZUX, hXs, hYs, hZs] using hR

omit [SigmaCompactSpace M] in
theorem boundaryOriginal_metricRicciAt_restrictOpen_apply
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U] [IsManifold I 1 U] (x : U)
    (v w : TangentSpace I x) :
    metricRicciAt (g.restrictOpen (I := I) U) x (vec2 v w) =
      metricRicciAt (I := I) g (x : M)
        (vec2 (mfderiv I I (Subtype.val : U → M) x v)
          (mfderiv I I (Subtype.val : U → M) x w)) := by
  let Idx := Fin (Module.finrank ℝ E)
  let BU : Module.Basis Idx ℝ (TangentSpace I x) :=
    Module.finBasis ℝ (TangentSpace I x)
  let BM : Module.Basis Idx ℝ (TangentSpace I (x : M)) :=
    Module.finBasis ℝ (TangentSpace I (x : M))
  have hmap (i : Idx) : mfderiv I I (Subtype.val : U → M) x (BU i) = BM i := by
    simp only [BU, BM, mfderiv_subtype_val_apply]
    rfl
  have hcoord (i : Idx) : ∀ z : E, (BU.coord i) z = (BM.coord i) z := by
    intro z
    simp only [BU, BM]
    rfl
  rw [metricRicciAt_eq_trace, metricRicciAt_eq_trace,
    ricciFromRm13At_apply_basis_trace BU,
    ricciFromRm13At_apply_basis_trace BM]
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact boundaryOriginal_metricRm13At_restrictOpen_component g U x BU BM hmap i
    (hcoord i) v w

omit [SigmaCompactSpace M] in
theorem boundaryOriginal_metricRicciAt_eq_restricted_ricciTensor
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U] [IsManifold I 1 U] [BoundarylessManifold I U] (x : U)
    (v w : TangentSpace I x) :
    metricRicciAt (I := I) g (x : M)
        (vec2 (mfderiv I I (Subtype.val : U → M) x v)
          (mfderiv I I (Subtype.val : U → M) x w)) =
      ricciTensor (g.restrictOpen (I := I) U) x v w := by
  calc
    metricRicciAt (I := I) g (x : M)
        (vec2 (mfderiv I I (Subtype.val : U → M) x v)
          (mfderiv I I (Subtype.val : U → M) x w)) =
      metricRicciAt (g.restrictOpen (I := I) U) x (vec2 v w) :=
        (boundaryOriginal_metricRicciAt_restrictOpen_apply g U x v w).symm
    _ = ricciTensor (g.restrictOpen (I := I) U) x v w :=
      metricRicciAt_apply_eq_ricciTensor (g.restrictOpen (I := I) U) x v w

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
