import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.Basic

open scoped ENNReal

namespace ContinuousLinearMap

section Topological

variable {𝕜 ι : Type*} [Semiring 𝕜]
  {E F : ι → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [∀ i, TopologicalSpace (E i)]
  [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)]
  [∀ i, TopologicalSpace (F i)]

def piLpMap (p : ℝ≥0∞) (L : ∀ i, E i →L[𝕜] F i) :
    PiLp p E →L[𝕜] PiLp p F :=
  (PiLp.continuousLinearEquiv p 𝕜 F).symm.toContinuousLinearMap.comp
    ((piMap L).comp (PiLp.continuousLinearEquiv p 𝕜 E).toContinuousLinearMap)

@[simp] theorem piLpMap_apply (p : ℝ≥0∞) (L : ∀ i, E i →L[𝕜] F i)
    (x : PiLp p E) (i : ι) : piLpMap p L x i = L i (x i) := rfl

@[simp] theorem piLpMap_id (p : ℝ≥0∞) :
    piLpMap p (fun i => ContinuousLinearMap.id 𝕜 (E i)) =
      ContinuousLinearMap.id 𝕜 (PiLp p E) := rfl

theorem piLpMap_comp {G : ι → Type*}
    [∀ i, AddCommGroup (G i)] [∀ i, Module 𝕜 (G i)]
    [∀ i, TopologicalSpace (G i)] (p : ℝ≥0∞)
    (K : ∀ i, F i →L[𝕜] G i) (L : ∀ i, E i →L[𝕜] F i) :
    (piLpMap p K).comp (piLpMap p L) = piLpMap p (fun i => (K i).comp (L i)) := rfl

end Topological

section Normed

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  {E F : ι → Type*}
  [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, SeminormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

theorem piLpMap_norm_le (L : ∀ i, E i →L[𝕜] F i)
    {C : ℝ} (hC : 0 ≤ C) (hL : ∀ i x, ‖L i x‖ ≤ C * ‖x‖)
    (x : PiLp 2 E) : ‖piLpMap 2 L x‖ ≤ C * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [piLpMap_apply]
  calc
    ‖L i (x i)‖ ^ 2 ≤ (C * ‖x i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hL i (x i)) 2
    _ = C ^ 2 * ‖x i‖ ^ 2 := mul_pow _ _ _

theorem norm_piLpMap_le (L : ∀ i, E i →L[𝕜] F i)
    {C : ℝ} (hC : 0 ≤ C) (hL : ∀ i, ‖L i‖ ≤ C) : ‖piLpMap 2 L‖ ≤ C := by
  apply opNorm_le_bound _ hC
  apply piLpMap_norm_le L hC
  intro i x
  exact (L i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hL i) (norm_nonneg x))

end Normed

end ContinuousLinearMap
