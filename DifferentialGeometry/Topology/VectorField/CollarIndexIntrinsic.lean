import DifferentialGeometry.Topology.VectorField.CollarIndex
import DifferentialGeometry.Topology.VectorField.IndexModel

set_option autoImplicit false
open scoped Manifold
noncomputable section
namespace Poincare.VectorField
variable {d : ℕ}

theorem HasContinuousIsolatedZero.euclideanCollarExtension
    {T : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {b : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {t : ℝ}
    (hT : HasContinuousIsolatedZero 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) T x)
    (hb : ContDiffAt ℝ 1 b x) (hb0 : b x ≠ 0)
    (hz : collarExtension (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))))
      T b collarTransition (x, t) = 0) :
    HasContinuousIsolatedZero 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2)))
      (euclideanCollarExtension T b collarTransition)
      (Poincare.LocalDegree.euclideanProductPoint d x t) :=
  hasContinuousIsolatedZero_model_iff.mpr
    (isolatedZero_euclideanCollarExtension (hasContinuousIsolatedZero_model_iff.mp hT) hb hb0 hz)

theorem index_euclideanCollarExtension
    {T : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {b : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {t : ℝ}
    (hT : HasContinuousIsolatedZero 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) T x)
    (hb : ContDiffAt ℝ 1 b x) (hb0 : b x ≠ 0)
    (hz : collarExtension (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))))
      T b collarTransition (x, t) = 0) :
    index 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2)))
        (euclideanCollarExtension T b collarTransition)
        (Poincare.LocalDegree.euclideanProductPoint d x t)
        (hT.euclideanCollarExtension hb hb0 hz) =
      index 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) T x hT := by
  rw [index_model_eq_localDegree, index_model_eq_localDegree]
  exact euclideanLocalDegree_collarExtension (hasContinuousIsolatedZero_model_iff.mp hT) hb hb0 hz

end Poincare.VectorField
