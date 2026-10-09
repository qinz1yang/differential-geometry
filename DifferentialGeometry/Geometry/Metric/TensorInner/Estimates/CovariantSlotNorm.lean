import DifferentialGeometry.Geometry.Metric.TensorInner.Estimates.TensorProductNorm
import DifferentialGeometry.Tensor.RSTensor.Reindexing.CovariantSlot

noncomputable section

namespace DifferentialGeometry.Tensor0SBundle

open Bundle Manifold
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem normSq0S_covGradBundleEquiv_smulRight
    (g : SmoothRiemannianMetric I M) (x : M) {r s : ℕ}
    (α : TangentSpace I x →L[ℝ] ℝ)
    (T : TensorRSSpace r s I x) (D : Tensor0SSpace r I x) :
    normSq0S (I := I) g x (s + 1)
      ((covGradBundleEquiv (I := I) r s x
        (α.smulRight T))
        D) =
      normSq0S (I := I) g x 1 (dualToCotangent (I := I) α.toLinearMap) *
        normSq0S (I := I) g x s (T D) := by
  classical
  let A := dualToCotangent (I := I) α.toLinearMap
  let e : Fin (1 + s) ≃ Fin (s + 1) := finCongr (Nat.add_comm 1 s)
  have heq :
      (covGradBundleEquiv (I := I) r s x
        (α.smulRight T)) D =
      (Tensor0SSpace.product A (T D)).domDomCongr e := by
    apply tensor0SSpace_ext
    intro v
    change Tensor0SSpace.eval
      ((covGradBundleEquiv (I := I) r s x
        (α.smulRight T))
        D) v = _
    rw [covGradBundleEquiv_apply_eval, ContinuousLinearMap.smulRight_apply,
      TensorRSSpace.smul_apply]
    change α (v 0) * (T D) (Matrix.vecTail v) = _
    rw [Tensor0SSpace.domDomCongr_apply, Tensor0SSpace.product_apply]
    have hhead : (fun i : Fin 1 => v (e (Fin.castAdd s i))) = fun _ => v 0 := by
      funext i
      fin_cases i
      rfl
    have htail : (fun i : Fin s => v (e (Fin.natAdd 1 i))) = Matrix.vecTail v := by
      funext i
      change v (e (Fin.natAdd 1 i)) = v i.succ
      congr 1
      apply Fin.ext
      simp [e]
    change α (v 0) * (T D) (Matrix.vecTail v) =
      A (fun i => v (e (Fin.castAdd s i))) * (T D) (fun i => v (e (Fin.natAdd 1 i)))
    rw [hhead, htail]
    simp [A]
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis hON
  rw [heq, normSq0S_domDomCongr (I := I) g x basis hinv e,
    normSq0S_prod (I := I) g x basis hinv]

end DifferentialGeometry.Tensor0SBundle
