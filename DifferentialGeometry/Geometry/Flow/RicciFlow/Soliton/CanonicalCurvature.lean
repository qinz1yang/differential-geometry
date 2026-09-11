import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Canonical
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Curvature.Metric.Conditions
import DifferentialGeometry.Geometry.Curvature.Metric.SectionalCone
import Mathlib.Data.Sign.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

theorem canonicalMetric_metricRm04StdAt_sign
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M)
    (v w : TangentSpace I x) :
    SignType.sign (metricRm04StandardAt (I := I)
      (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x v w w v) =
      SignType.sign (metricRm04StandardAt (I := I) g
        (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x)
        (mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) : M → M) x v)
        (mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) : M → M) x w)
        (mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) : M → M) x w)
        (mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) : M → M) x v)) := by
  have hRm := canonicalMetric_metricRm04 g f sigma hcomplete hsol ht x (vec4 v w w v)
  change metricRm04StandardAt (I := I)
      (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x v w w v =
    (1 - sigma * t) * metricRm04StandardAt (I := I) g
      (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
        (canonicalFlowParameter sigma t) x)
      (mfderiv I I
        (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) : M → M) x v)
      (mfderiv I I
        (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) : M → M) x w)
      (mfderiv I I
        (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) : M → M) x w)
      (mfderiv I I
        (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) : M → M) x v) at hRm
  rw [hRm, sign_mul, sign_pos (mem_canonicalTimeDomain_iff.mp ht), one_mul]

theorem canonicalMetric_sectionalNonnegative_iff
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    metricRm04At (I := I)
        (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M) ↔
    metricRm04At (I := I) g
        (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x) ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M) := by
  let Φ := canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
    (canonicalFlowParameter sigma t)
  let e := Φ.mfderivToContinuousLinearEquiv (by decide) x
  rw [metricRm04At_mem_tensor04SectionalNonnegativeCone_iff,
    metricRm04At_mem_tensor04SectionalNonnegativeCone_iff]
  have hsign (v w : TangentSpace I x) :=
    canonicalMetric_metricRm04StdAt_sign g f sigma hcomplete hsol ht x v w
  constructor
  · intro h v w
    obtain ⟨v', rfl⟩ := e.surjective v
    obtain ⟨w', rfl⟩ := e.surjective w
    have hs := hsign v' w'
    exact (sign_nonneg_iff.mp ((congrArg (0 ≤ ·) hs).mp
      (sign_nonneg_iff.mpr (h v' w'))))
  · intro h v w
    exact sign_nonneg_iff.mp ((congrArg (0 ≤ ·) (hsign v w)).mpr
      (sign_nonneg_iff.mpr (h (e v) (e w))))

theorem canonicalMetric_ricciTensor_pos_iff
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    (∀ v : TangentSpace I x, v ≠ 0 →
      0 < ricciTensor (I := I)
        (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x v v) ↔
    ∀ v : TangentSpace I
        (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x), v ≠ 0 →
      0 < ricciTensor (I := I) g
        (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x) v v := by
  let Φ := canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
    (canonicalFlowParameter sigma t)
  let e := Φ.mfderivToContinuousLinearEquiv (by decide) x
  have hRic (v w : TangentSpace I x) :
      ricciTensor (I := I) (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x v w =
        ricciTensor (I := I) g (Φ x) (e v) (e w) := by
    have h := canonicalMetric_ricciTensor g f sigma hcomplete hsol ht x v w
    rw [← canonicalFlowDiffeomorph_apply] at h
    exact h
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ := e.surjective v
    have hw : w ≠ 0 := by intro hw; exact hv (hw ▸ e.map_zero)
    exact (hRic w w) ▸ h w hw
  · intro h v hv
    rw [hRic]
    exact h (e v) (e.toLinearEquiv.map_ne_zero_iff.mpr hv)

theorem canonicalMetric_ricciTensor_ker_map
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    (ricciTensor (I := I)
        (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x).ker.map
      (mfderiv I I
        (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) : M → M) x).toLinearMap =
    (ricciTensor (I := I) g
      (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
        (canonicalFlowParameter sigma t) x)).ker := by
  let Φ := canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
    (canonicalFlowParameter sigma t)
  let e := Φ.mfderivToContinuousLinearEquiv (by decide) x
  have hRic (v w : TangentSpace I x) :
      ricciTensor (I := I) (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x v w =
        ricciTensor (I := I) g (Φ x) (e v) (e w) := by
    have h := canonicalMetric_ricciTensor g f sigma hcomplete hsol ht x v w
    rw [← canonicalFlowDiffeomorph_apply] at h
    exact h
  change (ricciTensor (I := I)
      (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x).ker.map
    e.toLinearEquiv.toLinearMap = (ricciTensor (I := I) g (Φ x)).ker
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change ricciTensor (I := I)
      (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x w = 0 at hw
    change ricciTensor (I := I) g (Φ x) (e w) = 0
    ext z
    obtain ⟨y, rfl⟩ := e.surjective z
    have hy := congrArg (fun L : TangentSpace I x →L[Real] Real => L y) hw
    exact (hRic w y).symm.trans hy
  · intro hv
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    change ricciTensor (I := I) g (Φ x) v = 0 at hv
    change ricciTensor (I := I)
      (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x (e.symm v) = 0
    ext y
    rw [hRic, e.apply_symm_apply, hv]
    rfl

theorem canonicalMetric_ricciTensor_nullity
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    Module.finrank Real (ricciTensor (I := I)
      (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x).ker =
    Module.finrank Real (ricciTensor (I := I) g
      (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
        (canonicalFlowParameter sigma t) x)).ker := by
  let Φ := canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
    (canonicalFlowParameter sigma t)
  let e := Φ.mfderivToContinuousLinearEquiv (by decide) x
  rw [← canonicalMetric_ricciTensor_ker_map g f sigma hcomplete hsol ht x]
  exact (e.toLinearEquiv.finrank_map_eq _).symm

theorem canonicalMetric_ricciTensor_pos_everywhere_iff
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) :
    (∀ x : M, ∀ v : TangentSpace I x, v ≠ 0 →
      0 < ricciTensor (I := I)
        (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x v v) ↔
      ∀ x : M, ∀ v : TangentSpace I x, v ≠ 0 → 0 < ricciTensor (I := I) g x v v := by
  let Φ := canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
    (canonicalFlowParameter sigma t)
  constructor
  · intro h x
    obtain ⟨y, rfl⟩ := Φ.surjective x
    exact (canonicalMetric_ricciTensor_pos_iff g f sigma hcomplete hsol ht y).mp (h y)
  · intro h x
    exact (canonicalMetric_ricciTensor_pos_iff g f sigma hcomplete hsol ht x).mpr (h (Φ x))

theorem canonicalMetric_sectionalCurvature
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M)
    (v w : TangentSpace I x) :
    sectionalCurvature (I := I)
        (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x v w =
      (1 - sigma * t)⁻¹ * sectionalCurvature (I := I) g
        (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x)
        (mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) : M → M) x v)
        (mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) : M → M) x w) := by
  rw [canonicalMetric, sectionalCurvature_pullback, sectionalCurvature_scaleMetric]

theorem canonicalMetric_sectionalCurvature_sign
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M)
    (v w : TangentSpace I x) :
    SignType.sign (sectionalCurvature (I := I)
      (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x v w) =
      SignType.sign (sectionalCurvature (I := I) g
        (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x)
        (mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) : M → M) x v)
        (mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) : M → M) x w)) := by
  rw [canonicalMetric_sectionalCurvature, sign_mul,
    sign_pos (inv_pos.mpr (mem_canonicalTimeDomain_iff.mp ht)), one_mul]

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

theorem canonicalMetric_positiveRicciMetric_iff
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) :
    positiveRicciMetric (I := I)
        (canonicalMetric (I := I) g f sigma hcomplete hsol ht) ↔
      positiveRicciMetric (I := I) g := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  simp only [positiveRicciMetric, metricRicciAt_apply_eq_ricciTensor]
  exact canonicalMetric_ricciTensor_pos_everywhere_iff g f sigma hcomplete hsol ht

end InnerProduct

end DifferentialGeometry.PDE.RicciFlow.Soliton
