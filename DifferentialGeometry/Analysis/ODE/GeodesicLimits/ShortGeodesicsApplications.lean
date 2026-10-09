import DifferentialGeometry.Analysis.ODE.GeodesicLimits.ShortGeodesics

/-!
# Consumer of the LFR09 chart kernel: constant Christoffel fields

`exists_short_geodesics_const_add`: for constant Christoffel fields `Γ₀ + c i` with `c i → 0`, any
two points of a compact set at distance `≤ τ` are joined, for a tail of `i`, by a geodesic on
`[0, 1]` with speed `O(‖y - x‖)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable local instance shortGeodAppBilinNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance shortGeodAppBilinNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

/-- **Consumer of LFR09 (chart kernel).** -/
theorem exists_short_geodesics_const_add (Γ₀ : E →L[ℝ] E →L[ℝ] E) {c : ℕ → E →L[ℝ] E →L[ℝ] E}
    (hc : Tendsto c atTop (𝓝 0)) {C : Set E} (hC : IsCompact C) :
    ∃ τ L : ℝ, 0 < τ ∧ 0 < L ∧ ∀ᶠ i in atTop, ∀ x ∈ C, ∀ y : E, ‖y - x‖ ≤ τ →
      ∃ γ γ' : ℝ → E, γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt γ (γ' t) (Icc 0 1) t ∧
        HasDerivWithinAt γ' (-((Γ₀ + c i) (γ' t) (γ' t))) (Icc 0 1) t ∧
        ‖γ' t‖ ≤ L * ‖y - x‖ := by
  have hconv : ∀ C' : Set E, MapCPConvergenceOn C' 1 (fun i (_ : E) => Γ₀ + c i) (fun _ => Γ₀) := by
    intro C'
    refine mapCPConvergenceOn_one_of_forall_norm_sub_le
      (Eventually.of_forall fun i x _ => differentiableAt_const (Γ₀ + c i))
      (fun x _ => differentiableAt_const Γ₀) ?_ ?_
    · intro ε hε
      filter_upwards [(Metric.tendsto_nhds.mp hc) ε hε] with i hi x _
      rw [add_sub_cancel_left, ← dist_zero_right]
      exact hi.le
    · intro ε hε
      refine Eventually.of_forall fun i x _ => ?_
      rw [fderiv_const_apply, fderiv_const_apply, sub_zero, norm_zero]
      exact hε.le
  obtain ⟨τ, L, hτ, hL, hev⟩ := exists_short_geodesics_of_isCompact isOpen_univ
    (Γ := fun i (_ : E) => Γ₀ + c i) (ΓInf := fun _ => Γ₀) (fun _ => contDiffOn_const)
    contDiffOn_const (fun C' _ _ => hconv C') hC (subset_univ C)
  refine ⟨τ, L, hτ, hL, ?_⟩
  filter_upwards [hev] with i hi x hx y hy
  obtain ⟨γ, γ', h0, h1, hγ⟩ := hi x hx y hy
  exact ⟨γ, γ', h0, h1, fun t ht => (hγ t ht).2⟩

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
