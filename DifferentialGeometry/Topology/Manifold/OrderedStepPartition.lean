import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

noncomputable section
open Set
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Topology.Manifold

private theorem sum_consecutive_sub {n : ℕ} (f : Fin (n + 2) → ℝ) :
    (∑ i : Fin (n + 1), (f i.castSucc - f i.succ)) = f 0 - f (Fin.last (n + 1)) := by
  rw [Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ f
  have hlast := Fin.sum_univ_castSucc f
  linarith only [hfirst, hlast]

variable {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

def orderedStepPartition (θ : Fin (n + 2) → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (horder : ∀ x, Antitone (fun i ↦ θ i x))
    (hfirst : ∀ x, θ 0 x = 1) (hlast : ∀ x, θ (Fin.last (n + 1)) x = 0) :
    SmoothPartitionOfUnity (Fin (n + 1)) I M where
  toFun i := ⟨fun x ↦ θ i.castSucc x - θ i.succ x,
    (θ i.castSucc).contMDiff.sub (θ i.succ).contMDiff⟩
  locallyFinite' := locallyFinite_of_finite _
  nonneg' i x := sub_nonneg.mpr (horder x (Fin.le_def.mpr (Nat.le_succ _)))
  sum_eq_one' x _ := by
    rw [finsum_eq_sum_of_fintype]
    exact (sum_consecutive_sub (fun i ↦ θ i x)).trans (by rw [hfirst, hlast, sub_zero])
  sum_le_one' x := by
    rw [finsum_eq_sum_of_fintype]
    exact le_of_eq ((sum_consecutive_sub (fun i ↦ θ i x)).trans (by rw [hfirst, hlast, sub_zero]))

@[simp] theorem orderedStepPartition_apply (θ : Fin (n + 2) → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (horder : ∀ x, Antitone (fun i ↦ θ i x))
    (hfirst : ∀ x, θ 0 x = 1) (hlast : ∀ x, θ (Fin.last (n + 1)) x = 0)
    (i : Fin (n + 1)) (x : M) :
    orderedStepPartition θ horder hfirst hlast i x = θ i.castSucc x - θ i.succ x := rfl

theorem sum_abs_mvfderiv_orderedStepPartition_le
    (θ : Fin (n + 2) → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (horder : ∀ x, Antitone (fun i ↦ θ i x))
    (hfirst : ∀ x, θ 0 x = 1) (hlast : ∀ x, θ (Fin.last (n + 1)) x = 0)
    (x : M) (v : TangentSpace I x) :
    (∑ i : Fin (n + 1), |mvfderiv I (orderedStepPartition θ horder hfirst hlast i) x v|) ≤
      2 * ∑ j : Fin (n + 2), |mvfderiv I (θ j) x v| := by
  have hlocal (i : Fin (n + 1)) :
      |mvfderiv I (orderedStepPartition θ horder hfirst hlast i) x v| ≤
        |mvfderiv I (θ i.castSucc) x v| + |mvfderiv I (θ i.succ) x v| := by
    change |mvfderiv I (fun y ↦ θ i.castSucc y - θ i.succ y) x v| ≤ _
    rw [mvfderiv_fun_sub ((θ i.castSucc).contMDiff.mdifferentiable (by decide) x)
      ((θ i.succ).contMDiff.mdifferentiable (by decide) x), sub_apply]
    exact abs_sub _ _
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hlocal i)
  rw [Finset.sum_add_distrib] at hsum
  have hfirstSum := Fin.sum_univ_succ (fun j : Fin (n + 2) ↦ |mvfderiv I (θ j) x v|)
  have hlastSum := Fin.sum_univ_castSucc (fun j : Fin (n + 2) ↦ |mvfderiv I (θ j) x v|)
  have ha := abs_nonneg (mvfderiv I (θ 0) x v)
  have hb := abs_nonneg (mvfderiv I (θ (Fin.last (n + 1))) x v)
  linarith only [hsum, hfirstSum, hlastSum, ha, hb]

end DifferentialGeometry.Topology.Manifold
