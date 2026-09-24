import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : CompleteSpace F := FiniteDimensional.complete ℝ F
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
private local instance : IsManifold J 1 N := IsManifold.of_le (n := ∞) (by decide)

private def tensor02PullbackEquiv (Φ : M ≃ₘ⟮I, J⟯ N) (x : M) :
    Tensor0SSpace 2 J (Φ x) ≃L[ℝ] Tensor0SSpace 2 I x :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := J) 2 (Φ x)).trans
    ((ContinuousLinearEquiv.continuousMultilinearMapCongrLeft ℝ
      (fun _ : Fin 2 => Φ.mfderivToContinuousLinearEquiv (by decide) x)).trans
        (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x).symm)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [T2Space N] in
private theorem tensor02PullbackEquiv_apply (Φ : M ≃ₘ⟮I, J⟯ N) (x : M)
    (A : Tensor0SSpace 2 J (Φ x)) (v : Fin 2 → TangentSpace I x) :
    tensor02PullbackEquiv Φ x A v = A (fun j => mfderiv I J Φ x (v j)) := by
  change A (fun j => (Φ.mfderivToContinuousLinearEquiv (by decide) x) (v j)) = _
  apply congrArg A
  funext j
  exact DFunLike.congr_fun
    (Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ) (x := x) (by decide)) (v j)

omit [T2Space N] in
private theorem iteratedDerivWithin_pullbackTensor02FieldCross
    (Φ : M ≃ₘ⟮I, J⟯ N) (A : ℝ → Tensor0SField (I := J) (M := N) ∞ 2)
    (b : ℕ) (x : M) {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {t : ℝ} (ht : t ∈ s) :
    iteratedDerivWithin b (fun u => pullbackTensor02FieldCross Φ (A u) x) s t =
      tensor02PullbackEquiv Φ x (iteratedDerivWithin b (fun u => A u (Φ x)) s t) := by
  have hf : (fun u => pullbackTensor02FieldCross Φ (A u) x) =
      (tensor02PullbackEquiv Φ x) ∘ (fun u => A u (Φ x)) := by
    funext u
    ext v
    exact (pullbackTensor02FieldCross_apply Φ (A u) x v).trans
      (tensor02PullbackEquiv_apply Φ x (A u (Φ x)) v).symm
  rw [hf]
  exact congrArg (fun T => T (fun _ => (1 : ℝ)))
    ((tensor02PullbackEquiv Φ x).iteratedFDerivWithin_comp_left
      (fun u => A u (Φ x)) hs ht b)

omit [T2Space N] in
theorem pullbackTensor02FieldCross_eq_iteratedDerivWithin
    (Φ : M ≃ₘ⟮I, J⟯ N) (A : ℝ → Tensor0SField (I := J) (M := N) ∞ 2)
    (A' : Tensor0SField (I := J) (M := N) ∞ 2) (b : ℕ)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {t : ℝ} (ht : t ∈ s)
    (hA : ∀ y, A' y = iteratedDerivWithin b (fun u => A u y) s t) (x : M) :
    pullbackTensor02FieldCross Φ A' x =
      iteratedDerivWithin b (fun u => pullbackTensor02FieldCross Φ (A u) x) s t := by
  rw [iteratedDerivWithin_pullbackTensor02FieldCross Φ A b x hs ht]
  ext v
  rw [pullbackTensor02FieldCross_apply, tensor02PullbackEquiv_apply, hA]


end DifferentialGeometry.CheegerGromovCompactness
