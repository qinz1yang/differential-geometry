import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.ManifoldDerivative
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Framed
import DifferentialGeometry.Geometry.Exponential.Smoothness.Domain

noncomputable section

universe u uE uH

open Bundle Set
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

open Exponential

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

theorem contMDiffAt_framedExpMap
    (g : SmoothRiemannianMetric I M) (p : M) {z : E}
    (hz : normalFrame (I := I) g p z ∈ expDomain (I := I) g p) :
    ContMDiffAt 𝓘(Real, E) I ∞ (framedExpMap (I := I) g p) z := by
  let L : E →L[Real] E :=
    (normalFrame (I := I) g p).toContinuousLinearMap
  have hframe : ContMDiffAt 𝓘(Real, E) 𝓘(Real, E) ∞
      (L : E → E) z := L.contDiff.contMDiff.contMDiffAt
  have hexp := contMDiffAt_expMap (I := I) g p hz
  exact hexp.comp z hframe

theorem mfderiv_framedExpMap
    (g : SmoothRiemannianMetric I M) (p : M) {z : E}
    (hz : normalFrame (I := I) g p z ∈ expDomain (I := I) g p) :
    mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) z =
      (mfderiv 𝓘(Real, E) I
        (fun u : E => expMap (I := I) g p
          (show TangentSpace I p from u))
        (show E from normalFrame (I := I) g p z)).comp
          (show E →L[Real] E from (normalFrame (I := I) g p).toContinuousLinearMap) := by
  let L : E →L[Real] E :=
    (normalFrame (I := I) g p).toContinuousLinearMap
  let F : E → M := fun u =>
    expMap (I := I) g p (show TangentSpace I p from u)
  have hF : MDifferentiableAt 𝓘(Real, E) I F (L z) :=
    (contMDiffAt_expMap (I := I) g p hz).mdifferentiableAt (by decide)
  have hL : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, E)
      (fun w : E => L w) z :=
    L.contMDiff.mdifferentiableAt one_ne_zero
  have hchain := mfderiv_comp
    (I := 𝓘(Real, E)) (I' := 𝓘(Real, E)) (I'' := I)
    z hF hL
  have hLderiv :
      mfderiv 𝓘(Real, E) 𝓘(Real, E) (fun w : E => L w) z = L := by
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rw [hLderiv] at hchain
  change mfderiv 𝓘(Real, E) I (F ∘ fun w : E => L w) z =
    (mfderiv 𝓘(Real, E) I F (L z)).comp L
  exact hchain

theorem isLocalDiffeomorphOn_framedExpMap
    (g : SmoothRiemannianMetric I M) (p : M) {U : Set E}
    (hU : IsOpen U)
    (hdom : ∀ z ∈ U,
      normalFrame (I := I) g p z ∈ expDomain (I := I) g p)
    (hinj : ∀ z ∈ U, Function.Injective
      (mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) z)) :
    IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) U := by
  have hsmooth : ContMDiffOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) U := by
    intro z hz
    exact (contMDiffAt_framedExpMap (I := I) g p (hdom z hz)).contMDiffWithinAt
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  apply hsmooth.isLocalDiffeomorphOn_of_isInvertible_mfderiv hU (by simp)
  intro z hz
  have hDinj := hinj z hz
  have hDsurj : Function.Surjective
      (mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) z) :=
    LinearMap.surjective_of_injective hDinj
  let D : E ≃L[Real] E :=
    ContinuousLinearEquiv.ofBijective
      (mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) z)
      (LinearMap.ker_eq_bot.mpr hDinj)
      (LinearMap.range_eq_top.mpr hDsurj)
  have hDinv :
      (mfderiv 𝓘(Real, E) I
        (framedExpMap (I := I) g p) z).IsInvertible := by
    refine ⟨D, ?_⟩
    rfl
  exact hDinv

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
