import DifferentialGeometry.Geometry.Geodesic.ParallelNormal
import DifferentialGeometry.Geometry.Metric.LinearAlgebra.NormalFixedVector

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open Poincare.Geometry

namespace Poincare.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_parallel_normal_field_of_return_det
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {L : ℝ} (hL : 0 < L)
    (hg : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (D : TangentSpace I (γ 0) ≃ₗ[ℝ] TangentSpace I (γ L))
    (hD : ∀ v w, g.inner (γ L) (D v) (D w) = g.inner (γ 0) v w)
    (hunit : g.inner (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 1)
    (hmatch : D (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = mfderiv 𝓘(ℝ, ℝ) I γ L (1 : ℝ))
    (hdet : (D.trans (parallelTransportLinearEquivOnIcc (I := I) g γ
      (hγ.of_le (by decide)) hL).symm).toLinearMap.det ≠
        (-1 : ℝ) ^ (Module.finrank ℝ E - 1)) :
    ∃ (δ : ℝ) (V : ∀ t, TangentSpace I (γ t)), 0 < δ ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)) (Ioo (-δ) (L + δ)) ∧
      (∀ t ∈ Icc (0 : ℝ) L, covDerivAlong (I := I) g γ V t = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) L, g.inner (γ t) (V t) (V t) = 1) ∧
      (∀ t ∈ Icc (0 : ℝ) L, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (V t) = 0) ∧
      V L = D (V 0) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let hγ2 : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ := hγ.of_le (by decide)
  let P := parallelTransportLinearEquivOnIcc (I := I) g γ hγ2 hL
  let A := D.trans P.symm
  have hinner (v w : TangentSpace I (γ 0)) : inner ℝ (A v) (A w) = inner ℝ v w := by
    change g.inner (γ 0) (A v) (A w) = g.inner (γ 0) v w
    rw [← parallelTransportLinearEquivOnIcc_inner g γ hγ2 hL (A v) (A w)]
    change g.inner (γ L) (P (A v)) (P (A w)) = g.inner (γ 0) v w
    simpa only [A, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using hD v w
  let B := A.isometryOfInner hinner
  let u := mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)
  have hu : u ≠ 0 := by
    intro h
    change g.inner (γ 0) u u = 1 at hunit
    simp only [h, map_zero] at hunit
    norm_num at hunit
  have hPu : P u = mfderiv 𝓘(ℝ, ℝ) I γ L (1 : ℝ) :=
    parallelTransportSection_velocity g γ hγ hL hg L ⟨hL.le, le_rfl⟩
  have hfix : B u = u := by
    change P.symm (D u) = u
    rw [hmatch, ← hPu, P.symm_apply_apply]
  have hd : B.toLinearMap.det ≠ (-1 : ℝ) ^ (Module.finrank ℝ (TangentSpace I (γ 0)) - 1) := hdet
  obtain ⟨v, hvnorm, hvorth, hvfix⟩ := exists_unit_normal_fixed_vector B hu hfix hd
  have hvunit : g.inner (γ 0) v v = 1 := by
    change inner ℝ v v = 1
    rw [real_inner_self_eq_norm_sq, hvnorm]
    norm_num
  obtain ⟨δ, V, hδ, hs, hV0, hp, hn, ho, heq⟩ :=
    exists_smooth_parallel_unit_normal_field g γ hγ hL hg v hvunit hvorth
  refine ⟨δ, V, hδ, hs, hp, hn, ho, ?_⟩
  have hVL : V L = P v := heq L ⟨hL.le, le_rfl⟩
  change P.symm (D v) = v at hvfix
  have hPv : P v = D v :=
    (congrArg P hvfix.symm).trans (P.apply_symm_apply (D v))
  rw [hV0, hVL, hPv]

end Poincare.Geometry.Riemannian.Geodesic
