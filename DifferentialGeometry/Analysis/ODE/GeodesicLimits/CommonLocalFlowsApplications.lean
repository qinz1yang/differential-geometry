import DifferentialGeometry.Analysis.ODE.GeodesicLimits.CommonLocalFlows

/-!
# Consumer of CM4.b: constant fields with vanishing perturbations

`exists_common_local_flows_const_add`: for constant fields `v + c i` with `c i → 0`, the frozen
theorem `exists_common_local_flows_C1_tendsto` (applied on `Ω = univ`) gives common local flows
converging in `C¹` to a local flow of the constant field `v`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

open DifferentialGeometry.Analysis.ODE.Flow
open DifferentialGeometry.CheegerGromovCompactness

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Constant fields `v + c i` converge in `C¹` on every set to `v` when `c i → 0`. -/
theorem mapCPConvergenceOn_const_add (v : F) {c : ℕ → F} (hc : Tendsto c atTop (𝓝 0))
    (C : Set F) : MapCPConvergenceOn C 1 (fun i (_ : F) => v + c i) (fun _ => v) := by
  refine mapCPConvergenceOn_one_of_forall_norm_sub_le
    (Eventually.of_forall fun i x _ => differentiableAt_const (v + c i))
    (fun x _ => differentiableAt_const v) ?_ ?_
  · intro ε hε
    have hball := (Metric.tendsto_nhds.mp hc) ε hε
    filter_upwards [hball] with i hi x _
    rw [add_sub_cancel_left, ← dist_zero_right]
    exact hi.le
  · intro ε hε
    refine Eventually.of_forall fun i x _ => ?_
    rw [fderiv_const_apply, fderiv_const_apply, sub_zero, norm_zero]
    exact hε.le

/-- **Consumer of CM4.b.** Constant fields `v + c i` with `c i → 0` have common local flows near
any point, converging in `C¹` to a local flow of `v`. -/
theorem exists_common_local_flows_const_add [FiniteDimensional ℝ F] (v : F) {c : ℕ → F}
    (hc : Tendsto c atTop (𝓝 0)) (z₀ : F) :
    ∃ (ρ : ℝ≥0) (T : ℝ) (Φ : ℕ → F × ℝ → F) (ΦInf : F × ℝ → F), 0 < (ρ : ℝ) ∧ 0 < T ∧
      IsLocalFlow (fun _ _ => v) 0 z₀ ρ (-T) T ΦInf ∧
      (∀ᶠ i in atTop, IsLocalFlow (fun _ _ => v + c i) 0 z₀ ρ (-T) T (Φ i)) ∧
      MapCPConvergenceOn (closedBall z₀ ρ ×ˢ Icc (-T) T) 1 Φ ΦInf := by
  obtain ⟨ρ, T, Φ, ΦInf, hρ, hT, hInf, hi, -, -, hconv⟩ :=
    exists_common_local_flows_C1_tendsto isOpen_univ (fun i (_ : F) => v + c i) (fun _ => v)
      (fun _ => contDiffOn_const) contDiffOn_const
      (fun C _ _ => mapCPConvergenceOn_const_add v hc C) (mem_univ z₀)
  exact ⟨ρ, T, Φ, ΦInf, hρ, hT, hInf, hi, hconv⟩

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
