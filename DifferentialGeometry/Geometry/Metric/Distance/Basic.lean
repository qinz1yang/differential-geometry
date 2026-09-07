import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

noncomputable def riemannianEDistOf
    (g : SmoothRiemannianMetric I M) (x y : M) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist I x y

theorem riemannianEDistOf_self
    (g : SmoothRiemannianMetric I M) (x : M) :
    riemannianEDistOf (I := I) g x x = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I x x = 0
  exact Manifold.riemannianEDist_self

theorem edistOf_iInf
    (g : SmoothRiemannianMetric I M) (x y : M) :
    riemannianEDistOf (I := I) g x y =
      ⨅ (γ : Path x y) (_ : CMDiff 1 γ),
        ∫⁻ t, ENNReal.ofReal (Real.sqrt
          (g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))) := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I x y = _
  rw [Manifold.riemannianEDist]
  refine iInf_congr fun γ => ?_
  refine iInf_congr fun hγ => ?_
  refine lintegral_congr fun t => ?_
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  congr 2

theorem riemannianEDistOf_comm
    (g : SmoothRiemannianMetric I M) (x y : M) :
    riemannianEDistOf (I := I) g x y = riemannianEDistOf (I := I) g y x := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_comm

theorem riemannianEDistOf_triangle
    (g : SmoothRiemannianMetric I M) (x y z : M) :
    riemannianEDistOf (I := I) g x z ≤
      riemannianEDistOf (I := I) g x y + riemannianEDistOf (I := I) g y z := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_triangle

end DifferentialGeometry

end
