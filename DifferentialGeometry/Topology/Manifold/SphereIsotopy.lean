import DifferentialGeometry.Topology.Manifold.SphereDiffeomorphDegree
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

theorem exists_sphere_diffeomorph_isotopy_of_preservesOrientation
    (f : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      ≃ₘ⟮𝓡 2, 𝓡 2⟯ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (hf : f.preservesOrientation (sphereOrientation 2 (by norm_num))
      (sphereOrientation 2 (by norm_num))) :
    ∃ A : C(Set.Icc (0 : ℝ) 1 × (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)),
      (∀ y, A (⟨0, by constructor <;> norm_num⟩, y) = f y) ∧
      (∀ y, A (⟨1, by constructor <;> norm_num⟩, y) = y) ∧
      ∀ t, ∃ e : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
        ≃ₘ⟮𝓡 2, 𝓡 2⟯ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
        ∀ y, e y = A (t, y) := by
  obtain ⟨J, hJ, -, hJ0, hJ1⟩ :=
    (DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_eq_one_iff_isotopy f).mp
      (DifferentialGeometry.Topology.Manifold.sphereDiffeomorphDegree_eq_one_of_preservesOrientation
        f hf)
  have hcont : Continuous fun p :
      Set.Icc (0 : ℝ) 1 × (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) => J (p.1 : ℝ) p.2 :=
    hJ.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  refine ⟨⟨fun p => J (p.1 : ℝ) p.2, hcont⟩, ?_, ?_, ?_⟩
  · intro y
    change J (0 : ℝ) y = f y
    rw [hJ0]
  · intro y
    change J (1 : ℝ) y = y
    rw [hJ1]
    rfl
  · intro t
    exact ⟨J (t.1 : ℝ), fun y => rfl⟩

end DifferentialGeometry.Topology.Manifold
