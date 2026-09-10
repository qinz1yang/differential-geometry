import DifferentialGeometry.Topology.VectorField.Index
import DifferentialGeometry.Topology.LocalDegree.Negation

set_option autoImplicit false
open scoped Manifold ContDiff Topology
noncomputable section
namespace Poincare.VectorField
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
  [IsManifold I 1 M] [I.Boundaryless]

theorem index_neg {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : HasContinuousIsolatedZero I V x) :
    index I (-V) x (hV.neg I) = (-1 : ℤ) ^ (d + 1) * index I V x hV := by
  let c := indexChart I x
  have hx : x ∈ c.source := by simp [c]
  have h := hV.in_coordinates I c le_rfl hx
  have hn := (hV.neg I).in_coordinates I c le_rfl hx
  rw [index_eq_in_coordinates I (hV.neg I) c hx, index_eq_in_coordinates I hV c hx]
  have he : _root_.VectorField.mpullback
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm (-V) =ᶠ[𝓝 (c x)]
        (fun y => -_root_.VectorField.mpullback
          𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V y) :=
    Filter.Eventually.of_forall (fun _ => _root_.VectorField.mpullback_neg_apply)
  exact (Poincare.LocalDegree.euclideanLocalDegree_congr hn
    (Poincare.LocalDegree.isolatedZero_neg h) he).trans
      (Poincare.LocalDegree.euclideanLocalDegree_neg h)

end Poincare.VectorField
