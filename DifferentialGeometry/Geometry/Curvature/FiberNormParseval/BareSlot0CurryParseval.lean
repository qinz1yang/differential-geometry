import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.BareSlot0CurryParseval

noncomputable section

open Bundle Manifold
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

abbrev tensor0SAsRS {s : ℕ} (x : M) (C : Tensor0SSpace s I x) :
    TensorRSSpace 0 s I x :=
  tensor0SToTensorRS (I := I) (M := M) x C

omit [CompleteSpace E] in
lemma slot0Curry_eq_tensor0SAsRS_curry_unitZeroSec
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (T : TensorRSSpace 0 (s + 1) I x) (a : Fin n) :
    slot0Curry (I := I) (M := M) g x s e K₀ T a =
      tensor0SAsRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) s x
          ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
            (unitZeroSec (I := I) (M := M) x)) (e a)) :=
  slot0Curry_eq_tensor0SToTensorRS_curry_unitZeroSec
    (I := I) (M := M) g x s e K₀ T a

end DifferentialGeometry.Integral.Connection

end
