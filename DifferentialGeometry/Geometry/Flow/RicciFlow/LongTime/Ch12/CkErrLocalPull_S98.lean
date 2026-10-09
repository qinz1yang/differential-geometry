import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrNaturality_O19
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrBridge_S57
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

set_option autoImplicit false

/-!
# CH12-S98 / G3a: `ckErr` of a local-isometry pull-back equals `ckErr` of the composite

`ckErr_S45 H (ψ^* m) c φ j p = ckErr_S45 H m c (ψ ∘ φ) j p` for `p` in an open set on which `φ` is smooth
(`ψ` a smooth local diffeomorphism, e.g. the survivor map).
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.TensorLieDeriv Bundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology.Manifold
open Set Filter TopologicalSpace Manifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.Ch12

theorem ckErr_localPull_S98 (H : FiniteVolumeHyperbolicModel.{u}) {N M' : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    [T2Space N] [TopologicalSpace M'] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M']
    [IsManifold (𝓡 3) ∞ M'] [T2Space M']
    (m : SmoothRiemannianMetric (𝓡 3) M') (ψ : N → M') (hψ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ ψ)
    (hψs : ContMDiff (𝓡 3) (𝓡 3) ∞ ψ) (φ : H.Carrier → N) (W : Opens H.Carrier)
    (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ W) (c : ℝ) (j : ℕ) (p : H.Carrier) (hp : p ∈ W) :
    ckErr_S45 H (localPullMetric (I := 𝓡 3) (J := 𝓡 3) m ψ hψ) c φ j p =
      ckErr_S45 H m c (fun z => ψ (φ z)) j p := by
  have hinf : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  change ckErr_O19 H _ c φ j p = ckErr_O19 H m c _ j p
  unfold ckErr_O19
  congr 1
  refine iteratedMetricCovariantDerivative_congr_open_O19 H.metric _ _ W.isOpen ?_ j p hp
  intro q hq
  have key : localPullInner (I := 𝓡 3) (localPullMetric (I := 𝓡 3) (J := 𝓡 3) m ψ hψ) φ q =
      localPullInner (I := 𝓡 3) m (fun z => ψ (φ z)) q := by
    ext v w
    rw [localPullInner_apply, localPullInner_apply, localPullMetric_inner]
    have hφq : MDifferentiableAt (𝓡 3) (𝓡 3) φ q :=
      (hφ.contMDiffAt (W.isOpen.mem_nhds hq)).mdifferentiableAt hinf
    have hcomp : ∀ a : TangentSpace (𝓡 3) q,
        mfderiv (𝓡 3) (𝓡 3) (fun z => ψ (φ z)) q a =
          mfderiv (𝓡 3) (𝓡 3) ψ (φ q) (mfderiv (𝓡 3) (𝓡 3) φ q a) := fun a =>
      mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) q
        ((hψs (φ q)).mdifferentiableAt hinf) hφq (v := a)
    rw [hcomp v, hcomp w]
  rw [key]

end GC.LongTime.Ch12
