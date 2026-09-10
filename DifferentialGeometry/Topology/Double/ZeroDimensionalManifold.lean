import DifferentialGeometry.Topology.Double.EmptyBoundary
import DifferentialGeometry.Topology.Manifold.ZeroDimensional
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology
open scoped ContDiff Topology
namespace Poincare.Topology

theorem exists_smoothAtlas_intrinsicDouble_of_subsingleton_model
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] :
    ∃ A : ChartedSpace H (Double (I.boundary M)), let _ := A
      IsManifold I ∞ (Double (I.boundary M)) ∧ BoundarylessManifold I (Double (I.boundary M)) ∧
      ContMDiff I I ∞ (doublePositive (I.boundary M)) ∧
      ContMDiff I I ∞ (doubleNegative (I.boundary M)) := by
  rw [DifferentialGeometry.boundary_eq_empty_of_subsingleton_model I]
  let _ : BoundarylessManifold I M :=
    DifferentialGeometry.boundaryless_manifold_of_subsingleton_model I
  let h : Double (∅ : Set M) ≃ₜ M ⊕ M := doubleEmptyHomeomorph
  let A := Poincare.Manifold.Homeomorph.pullbackChartedSpace (H := H) h
  let _ := A
  have hA : IsManifold I ∞ (Double (∅ : Set M)) :=
    Poincare.Manifold.Homeomorph.instIsManifoldPullback (I := I) (n := ∞) h
  have hs := Poincare.Manifold.Homeomorph.contMDiff_symm_pullback (I := I) (n := ∞) h
  have hB : BoundarylessManifold I (Double (∅ : Set M)) :=
    Poincare.Manifold.Homeomorph.boundaryless_manifold_pullback
      (I := I) (n := ∞) h (by simp)
  exact ⟨A, hA, hB, hs.comp ContMDiff.inl, hs.comp ContMDiff.inr⟩

end Poincare.Topology
