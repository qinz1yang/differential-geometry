import DifferentialGeometry.Geometry.Connection.TensorNabla.Pullback
import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle

noncomputable section

open Bundle CovariantDerivative
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle ∞ F₂ V₂ I]

theorem rawBundleConnLap_multilinear_pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I F₂ V₂) [ContMDiffCovariantDerivative cov ∞] (k : ℕ)
    {T : ∀ x, Bundle.continuousMultilinearMap ℝ k F₂ V₂ x} {x : M}
    (hT : ContMDiffAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F₂) ℝ)) 2
      (fun y => (⟨y, T y⟩ : TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F₂) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F₂ V₂))) x) :
    rawBundleConnLap g
      (multilinear
        (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k)
      (fun y => (T y).compContinuousLinearMap (fun _ => (φ y).toContinuousLinearMap)) x =
      (rawBundleConnLap g (multilinear cov k) T x).compContinuousLinearMap
        (fun _ => (φ x).toContinuousLinearMap) := by
  let L := Bundle.continuousMultilinearMap.compContinuousLinearMapL
    (F₁ := F₁) (F₂ := F₂) x (fun _ : Fin k => (φ x).toContinuousLinearMap)
  change _ = L (rawBundleConnLap g (multilinear cov k) T x)
  simp only [rawBundleConnLap_def, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  let _ : NeZero (Module.finrank ℝ E) :=
    ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
  exact multilinear_secondCovDeriv_pullbackFiberwiseLinearEquiv φ hφ cov (LeviCivita g) k hT
    ((smoothOrthoFrame_smooth g x i).mdifferentiableAt (by simp)) (smoothOrthoFrame g x i x)

end DifferentialGeometry.Geometry.Connection
