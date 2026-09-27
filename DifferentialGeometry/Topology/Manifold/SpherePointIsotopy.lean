import DifferentialGeometry.Topology.Manifold.SpherePlanarChart
import DifferentialGeometry.Topology.Manifold.ChartSupportedExtension
import DifferentialGeometry.Analysis.ODE.Flow.Planar.CompactPointMotion

noncomputable section
open Set Metric Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem exists_smooth_planar_chart_containing_pair
    (a b : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ e : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ℂ,
      a ∈ e.source ∧ b ∈ e.source ∧ e.target = univ ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ e.symm e.target := by
  obtain ⟨e₀, _, het, _, _⟩ := exists_smooth_planar_chart_sphere a
  let : Infinite (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Infinite.of_surjective e₀ (e₀.surjective_of_target_eq_univ het)
  obtain ⟨v, hv⟩ := ((finite_singleton b).insert a).exists_notMem
  obtain ⟨e, hes, het, he, hei⟩ := exists_smooth_planar_chart_sphere v
  refine ⟨e, ?_, ?_, het, he, hei⟩
  · rw [hes]
    intro h
    exact hv (Or.inl (mem_singleton_iff.mp h).symm)
  · rw [hes]
    intro h
    exact hv (Or.inr (mem_singleton_iff.mpr (mem_singleton_iff.mp h).symm))

theorem exists_sphere_isotopy_moving_point
    (a b : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ J : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞,
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (J q.1).symm q.2) ∧
      J 0 = Diffeomorph.refl (𝓡 2) _ ∞ ∧ J 1 a = b := by
  obtain ⟨e, ha, hb, het, he, hei⟩ := exists_smooth_planar_chart_containing_pair a b
  obtain ⟨D, hD, hDi, hD0, hmove, K, hK, hfix⟩ :=
    DifferentialGeometry.Analysis.exists_compact_isotopy_moving_point (e a) (e b)
  obtain ⟨J, hJ, hJi, hJe, _, _, _⟩ :=
    exists_diffeomorph_extension_of_chart_family e het he hei D hD hDi hK hfix
  refine ⟨J, hJ, hJi, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro x
    rw [(hJe 0 x).1, hD0]
    change extendChartById e (id : ℂ → ℂ) x = x
    by_cases hx : x ∈ e.source
    · exact (show extendChartById e id x = e.symm (e x) from if_pos hx).trans (e.left_inv hx)
    · exact if_neg hx
  · rw [(hJe 1 a).1]
    have hx : extendChartById e (D 1) a = e.symm (D 1 (e a)) := if_pos ha
    rw [hx, hmove, e.left_inv hb]

end DifferentialGeometry.Topology.Manifold
