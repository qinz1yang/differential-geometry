import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.ConnAddHessian

/-!
# Four-block split of the local-addition Hessian remainder

The second Fréchet derivative is linear in each of its two direction
arguments.  Splitting each direction into its horizontal and vertical parts
therefore gives four exact blocks.  This file records that elementary Banach
calculus identity and specializes it to `connAddD2Rem`.

No tension-field, PDE, or Jacobi-operator identification is asserted here.
-/

noncomputable section

namespace DifferentialGeometry
namespace Analysis

variable {P X Y : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The second Fréchet derivative on two product directions is the sum of its
horizontal-horizontal, horizontal-vertical, vertical-horizontal, and
vertical-vertical blocks.  No differentiability hypothesis is needed because
`fderiv (fderiv F)` is a continuous linear map in each displayed direction
even when the totalized derivative is zero. -/
theorem fderivD2_blocks
    (F : P × X → Y) (p : P) (x : X) (a b : P) (u v : X) :
    fderiv ℝ (fderiv ℝ F) (p, x) (a, u) (b, v) =
      fderiv ℝ (fderiv ℝ F) (p, x) (a, 0) (b, 0) +
        fderiv ℝ (fderiv ℝ F) (p, x) (a, 0) (0, v) +
        fderiv ℝ (fderiv ℝ F) (p, x) (0, u) (b, 0) +
        fderiv ℝ (fderiv ℝ F) (p, x) (0, u) (0, v) := by
  have ha : (a, u) = (a, 0) + (0, u) := by
    ext <;> simp
  have hb : (b, v) = (b, 0) + (0, v) := by
    ext <;> simp
  rw [ha, hb]
  simp only [map_add, ContinuousLinearMap.add_apply]
  abel

end Analysis

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace PDE.RicciFlow.Pullback

open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

/-- The first-jet local-addition remainder has the exact four-block split
obtained by separating each graph direction into its base direction and its
section-derivative direction. -/
theorem connAddD2_blocks
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z a b : E) :
    connAddD2Rem (I := I) g p v z a b =
      fderiv ℝ (fderiv ℝ (localAddTarget (I := I) g p)) (z, v z)
          (a, 0) (b, 0) +
        fderiv ℝ (fderiv ℝ (localAddTarget (I := I) g p)) (z, v z)
          (a, 0) (0, fderiv ℝ v z b) +
        fderiv ℝ (fderiv ℝ (localAddTarget (I := I) g p)) (z, v z)
          (0, fderiv ℝ v z a) (b, 0) +
        fderiv ℝ (fderiv ℝ (localAddTarget (I := I) g p)) (z, v z)
          (0, fderiv ℝ v z a) (0, fderiv ℝ v z b) := by
  simpa only [connAddD2Rem] using
    fderivD2_blocks (F := localAddTarget (I := I) g p)
      (p := z) (x := v z) (a := a) (b := b)
      (u := fderiv ℝ v z a) (v := fderiv ℝ v z b)

end PDE.RicciFlow.Pullback
end DifferentialGeometry

end
