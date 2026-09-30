import DifferentialGeometry.Topology.Homology.Spheres.SphereTopology

universe u

namespace DifferentialGeometry.Topology.SingularPair

open Metric
open scoped ContinuousMap unitInterval

theorem discreteTopology_of_chartedSpace_zero {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] : DiscreteTopology M := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  have hsub : ({x} : Set M) = (chartAt (EuclideanSpace ℝ (Fin 0)) x).source := by
    ext y
    constructor
    · rintro rfl
      exact mem_chart_source _ _
    · intro hy
      exact (chartAt (EuclideanSpace ℝ (Fin 0)) x).injOn hy (mem_chart_source _ x)
        (Subsingleton.elim _ _)
  rw [hsub]
  exact (chartAt _ x).open_source

theorem homotopy_apply_eq_of_discrete {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [DiscreteTopology Y] {f g : C(X, Y)} (H : f.Homotopy g) (x : X) : f x = g x := by
  have hc : Continuous fun t : I => H (t, x) :=
    H.continuous.comp (continuous_id.prodMk continuous_const)
  have := PreconnectedSpace.constant inferInstance hc (x := 0) (y := 1)
  simpa using this

theorem injective_homotopyEquiv_of_discrete {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [DiscreteTopology X] (e : X ≃ₕ Y) : Function.Injective e.toFun := by
  obtain ⟨H⟩ := e.left_inv
  intro a b hab
  have ha := homotopy_apply_eq_of_discrete H a
  have hb := homotopy_apply_eq_of_discrete H b
  simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply] at ha hb
  rw [← ha, ← hb, hab]

theorem compactSpace_of_homotopyEquiv_sphere_zero {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) : CompactSpace M := by
  have : DiscreteTopology M := discreteTopology_of_chartedSpace_zero
  have : Finite M := Finite.of_injective _ (injective_homotopyEquiv_of_discrete e)
  infer_instance

end DifferentialGeometry.Topology.SingularPair
