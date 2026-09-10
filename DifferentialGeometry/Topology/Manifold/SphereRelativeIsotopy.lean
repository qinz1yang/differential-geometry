import DifferentialGeometry.Topology.Manifold.SpherePlanarChart
import DifferentialGeometry.Topology.Manifold.ChartSupportedIsotopy

noncomputable section
open Set Metric Filter Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Manifold

theorem exists_sphere_isotopy_of_identity_near_point
    (f : Diffeomorph (𝓡 2) (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hfix : (f : _ → _) =ᶠ[𝓝 v] id) :
    ∃ J : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞,
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (J q.1).symm q.2) ∧
      J 0 = f ∧ J 1 = Diffeomorph.refl (𝓡 2) _ ∞ ∧
      ∃ U : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
        IsOpen U ∧ v ∈ U ∧ ∀ p x, x ∈ U → J p x = x ∧ (J p).symm x = x := by
  obtain ⟨N, hNfix, hN, hvN⟩ := _root_.mem_nhds_iff.mp hfix
  obtain ⟨e, hes, het, he, hei⟩ := exists_smooth_planar_chart_sphere v
  have hK : IsCompact Nᶜ := hN.isClosed_compl.isCompact
  have hKs : Nᶜ ⊆ e.source := by
    intro x hx
    rw [hes]
    intro h
    exact hx (mem_singleton_iff.mp h ▸ hvN)
  obtain ⟨J, hJ, hJi, hJ0, hJ1, C, hC, hCs, hJfix⟩ :=
    exists_isotopy_of_support_in_planar_chart e het he hei f hK hKs
      (fun x hx ↦ hNfix (not_not.mp hx))
  refine ⟨J, hJ, hJi, hJ0, hJ1, Cᶜ, hC.isClosed.isOpen_compl, ?_, hJfix⟩
  intro hvC
  have hvs := hCs hvC
  rw [hes] at hvs
  exact hvs (mem_singleton v)

end Poincare.Topology.Manifold
