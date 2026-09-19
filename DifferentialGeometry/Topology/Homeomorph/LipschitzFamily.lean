/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Diffeomorph.Perturbation

/-! Joint continuity of inverses in uniformly controlled homeomorphism families. -/

open Filter Topology
open scoped ContDiff NNReal

namespace Homeomorph

theorem continuous_symm_of_uniform_antilipschitz
    {P X Y : Type*} [TopologicalSpace P] [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (e : P → X ≃ₜ Y) (he : Continuous (fun z : P × X => e z.1 z.2))
    (C : ℝ≥0) (hC : ∀ p, AntilipschitzWith C (e p)) :
    Continuous (fun z : P × Y => (e z.1).symm z.2) := by
  rw [continuous_iff_continuousAt]
  intro q
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hbound (p : P × Y) :
      dist ((e p.1).symm p.2) ((e q.1).symm q.2) ≤
        (C : ℝ) * dist p.2 (e p.1 ((e q.1).symm q.2)) := by
    simpa only [Homeomorph.apply_symm_apply] using
      (hC p.1).le_mul_dist ((e p.1).symm p.2) ((e q.1).symm q.2)
  refine squeeze_zero (fun _ => dist_nonneg) hbound ?_
  have h : Continuous (fun p : P × Y =>
      (C : ℝ) * dist p.2 (e p.1 ((e q.1).symm q.2))) :=
    continuous_const.mul
      (continuous_snd.dist (he.comp (continuous_fst.prodMk continuous_const)))
  simpa only [Homeomorph.apply_symm_apply, dist_self, mul_zero] using h.tendsto q

theorem exists_addLipschitz_family
    {P E : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : P × E → E} (hG : Continuous G) {C : ℝ≥0}
    (hLip : ∀ p, LipschitzWith C (fun y => G (p, y))) (hC : C < 1) :
    ∃ e : P → E ≃ₜ E, (∀ p y, e p y = y + G (p, y)) ∧
      Continuous (fun z : P × E => e z.1 z.2) ∧
      Continuous (fun z : P × E => (e z.1).symm z.2) := by
  let e : P → E ≃ₜ E := fun p =>
    (Diffeomorph.addLipschitz (𝕜 := ℝ) (n := 0)
      (contDiff_zero.mpr (hG.comp (continuous_const.prodMk continuous_id)))
      (hLip p) hC).toHomeomorph
  have he : Continuous (fun z : P × E => e z.1 z.2) := continuous_snd.add hG
  refine ⟨e, fun _ _ => rfl, he, continuous_symm_of_uniform_antilipschitz e he
    ((1 - C)⁻¹) ?_⟩
  intro p
  change AntilipschitzWith ((1 - C)⁻¹) (fun y : E => y + G (p, y))
  simpa only [inv_one, id_eq] using
    AntilipschitzWith.id.add_lipschitzWith (hLip p) (by simpa only [inv_one] using hC)

end Homeomorph
