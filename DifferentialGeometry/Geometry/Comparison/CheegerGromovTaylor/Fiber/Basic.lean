import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Fiber
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.Coordinates
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Agreement
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CheegerGromovTaylor

open Exponential NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

def intrinsicFiber
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p q : M) (r : Real) : Set E :=
  {u | u ∈ Metric.ball (0 : E) r ∧
    intrinsicFramedExp (I := I) g hEnorm p u = q}

theorem exists_fiber_inj
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {p q : M} {R r₀ s : Real}
    (hqs :
      riemannianEDist I p q < ENNReal.ofReal s)
    (hfit : r₀ + s < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    ∃ f :
        intrinsicFiber (I := I) g hEnorm p p r₀ →
          intrinsicFiber (I := I) g hEnorm p q (r₀ + s),
      Function.Injective f := by
  have hagree : framedExpMap (I := I) g p =
      intrinsicFramedExp (I := I) g hEnorm p := by
    funext z
    rw [framedExpMap_apply, intrinsicFrame_apply, expMap_eq_expMapIntrinsic g hEnorm p]
  have hdom : ∀ z ∈ Metric.ball (0 : E) R,
      normalFrame (I := I) g p z ∈ expDomain (I := I) g p := by
    intro z _
    rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
    exact mem_univ _
  have hloc' : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R) := by
    rw [hagree]
    exact hloc
  have hd : riemannianEDistOf g p q < ENNReal.ofReal s := by
    rw [riemannianEDistOf_eq_riemannianEDist g hEnorm]
    exact hqs
  obtain ⟨f⟩ := nonempty_embedding_fiber_framedExpMap g hd hfit hdom hloc'
  unfold intrinsicFiber
  rw [← hagree]
  exact ⟨f, f.injective⟩

theorem fiber_encard_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {p q : M} {R r₀ s : Real}
    (hqs :
      riemannianEDist I p q < ENNReal.ofReal s)
    (hfit : r₀ + s < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    (intrinsicFiber (I := I) g hEnorm p p r₀).encard ≤
      (intrinsicFiber (I := I) g hEnorm p q (r₀ + s)).encard := by
  obtain ⟨f, hf⟩ :=
    exists_fiber_inj (I := I) g hEnorm hqs hfit hloc
  exact (Function.Embedding.mk f hf).encard_le

end CheegerGromovTaylor
end Riemannian
end Geometry
end DifferentialGeometry
