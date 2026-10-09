import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardUniformRestart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMaximalExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformLifetime

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1

theorem standard_solution_nonempty : Nonempty StandardSolution := by
  obtain ⟨τ, hτ, K, hK, hseeds⟩ := exists_uniform_partial_standard_solution
  let north : S3 := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨S, _⟩ := hseeds north
  obtain ⟨U, _⟩ := S.exists_maximal_extension
  exact ⟨U⟩

theorem standard_uniform_initial_window :
    ∃ α : ℝ, 0 < α ∧ ∃ K : ℝ, 0 < K ∧
      (∀ S : StandardSolution, ENNReal.ofReal α < S.val.lifetime) ∧
      ∀ S : StandardSolution, ∀ t ∈ Icc 0 α, ∀ x : E3,
        Real.sqrt (normSq0S (S.val.metric t) x 4 (metricRm04 (S.val.metric t) x)) ≤ K := by
  obtain ⟨a, ha, τ, hτ, KR, hKR, hrestart⟩ := standard_uniform_closed_restart_extension
  obtain ⟨b, hb, K, hK, hcurv⟩ := standard_uniform_initial_curvature_control
  let α := min a b
  have hα : 0 < α := lt_min ha hb
  have hlife (S : StandardSolution) : ENNReal.ofReal α < S.val.lifetime := by
    by_contra hn
    have hle : S.val.lifetime ≤ ENNReal.ofReal α := le_of_not_gt hn
    have htop : S.val.lifetime ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    let T := S.val.lifetime.toReal
    have hT : 0 < T := ENNReal.toReal_pos S.val.lifetime_pos.ne' htop
    have htime : S.val.lifetime = ENNReal.ofReal T := (ENNReal.ofReal_toReal htop).symm
    have hTa : T ≤ a := by
      rw [htime] at hle
      exact ((ENNReal.ofReal_le_ofReal_iff hα.le).mp hle).trans (min_le_left a b)
    obtain ⟨G, H, Q, _, _, _, _, hext, hstrict, _, _⟩ := hrestart S.val T hT hTa htime
    exact (not_le_of_gt hstrict) (S.property Q hext).1
  refine ⟨α, hα, K, hK, hlife, ?_⟩
  intro S t ht x
  exact hcurv S.val α hα.le (min_le_right a b) (hlife S) t ht x

theorem exists_uniform_standard_lifetime : ∃ α : ℝ, IsUniformStandardLifetime α := by
  obtain ⟨α, hα, K, hK, hlife, hcurv⟩ := standard_uniform_initial_window
  refine ⟨α, hα, ?_⟩
  intro θ hθ hθα
  refine ⟨fun S => (ENNReal.ofReal_le_ofReal hθα.le).trans_lt (hlife S), K, hK.le, ?_⟩
  intro S t ht x
  exact hcurv S t ⟨ht.1, ht.2.trans hθα.le⟩ x

theorem uniformStandardLifetime_pos : 0 < uniformStandardLifetime :=
  uniformStandardLifetime_pos_iff.mpr exists_uniform_standard_lifetime

theorem standard_solution_existence :
    Nonempty StandardSolution ∧ 0 < uniformStandardLifetime :=
  ⟨standard_solution_nonempty, uniformStandardLifetime_pos⟩
end DifferentialGeometry.PDE.RicciFlow
