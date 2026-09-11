import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Complete

set_option autoImplicit false
noncomputable section
open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_curvatureOperatorImageAt_finrank_eq_on_past_interval
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {T : ℝ} (hreg : Iio T ⊆ D.regular)
    (hR : ∀ t < T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∃ t₀ < T, ∃ q : ℕ, (q = 0 ∨ q = 1 ∨ q = 3) ∧
      ∀ t ≤ t₀, ∀ x,
        Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
          ⟨metricRm04At (S.family.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q := by
  classical
  let rank (t : ℝ) (x : M) : ℕ :=
    Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩)
  let values : Set ℕ := {q | ∃ t < T, ∃ x, rank t x = q}
  let x₀ : M := Classical.choice inferInstance
  have hvalues : values.Nonempty := ⟨rank (T-1) x₀, T-1, by linarith, x₀, rfl⟩
  obtain ⟨s, hs, x, hx⟩ : sInf values ∈ values := Nat.sInf_mem hvalues
  let t₀ := s - 1
  have ht₀ : t₀ < T := by dsimp [t₀]; linarith
  have hconstant : ∀ t ≤ t₀, ∀ y, rank t y = sInf values := by
    intro t ht y
    have hts : t < s := by dsimp [t₀] at ht; linarith
    have htT : t < T := hts.trans hs
    apply le_antisymm
    · rw [← hx]
      exact curvatureOperatorImageAt_finrank_le_at_later_time S hS hdim hts
        (fun r hr => hreg (hr.2.trans_lt hs))
        (fun r hr => hR r (hr.2.trans_lt hs)) y x
    · exact Nat.sInf_le ⟨t, htT, y, rfl⟩
  refine ⟨t₀, ht₀, sInf values, ?_, hconstant⟩
  have htri := curvatureOperatorImageAt_finrank_trichotomy_at_later_time S hS hdim
    (s := t₀-1) (t := t₀) (by linarith)
    (fun r hr => hreg (hr.2.trans_lt ht₀))
    (fun r hr => hR r (hr.2.trans_lt ht₀)) x₀
  change rank t₀ x₀ = 0 ∨ rank t₀ x₀ = 1 ∨ rank t₀ x₀ = 3 at htri
  rwa [hconstant t₀ le_rfl x₀] at htri

theorem exists_curvatureOperatorImageAt_finrank_eq_on_past_interval_of_complete_ancient
    [ConnectedSpace M] [SigmaCompactSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {T : ℝ} (hreg : Iio T ⊆ D.regular)
    (hcomplete : ∀ t < T, RiemannianMetricComplete (I := I) (S.family.metric t)) :
    ∃ t₀ < T, ∃ q : ℕ, (q = 0 ∨ q = 1 ∨ q = 3) ∧
      ∀ t ≤ t₀, ∀ x,
        Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
          ⟨metricRm04At (S.family.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q := by
  apply exists_curvatureOperatorImageAt_finrank_eq_on_past_interval S hS hdim hreg
  intro t ht x
  exact curvatureOperator_nonnegative_of_complete_ancient S hS
    (fun r hr => D.regular_subset (hreg (hr.trans_lt ht)))
    (fun r hr => hreg (hr.trans ht))
    (fun r hr => hcomplete r (hr.trans_lt ht)) hdim x

end DifferentialGeometry.PDE.RicciFlow
