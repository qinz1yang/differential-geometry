import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrDef_O19
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.FiniteJetCongruence

/-!
# CH12-O19 G1: isometry naturality of `ckErr_O19` (target side)

* `iteratedMetricCovariantDerivative_congr_open_O19`: germ locality of `∇^k` on an open set.
* `inner_mfderiv_symm_O19`: the inverse of a smooth isometric equivalence is isometric.
* `ckErr_comp_isometry_target_O19` (N1): composing the map with the inverse of an isometry
  `e : H ≃ H'` does not change the `C^k` pullback error.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.TensorLieDeriv Bundle
open Set Filter
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

/-- **Locality of `∇^k`.**  Two raw tensor fields agreeing on an open set have the same iterated
metric covariant derivatives there (`𝓡 3`, boundaryless). -/
theorem iteratedMetricCovariantDerivative_congr_open_O19 {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : SmoothRiemannianMetric (𝓡 3) M) {s : ℕ}
    (A B : (x : M) → Tensor0SSpace s (𝓡 3) x) {V : Set M} (hV : IsOpen V)
    (hAB : ∀ x ∈ V, A x = B x) (k : ℕ) :
    ∀ x ∈ V, iteratedMetricCovariantDerivative g s A k x =
      iteratedMetricCovariantDerivative g s B k x := by
  induction k with
  | zero => exact hAB
  | succ k ih =>
    intro x hx
    change metricCovariantDerivative g (s + k) (iteratedMetricCovariantDerivative g s A k) x =
      metricCovariantDerivative g (s + k) (iteratedMetricCovariantDerivative g s B k) x
    apply metricCovariantDerivative_eq_of_coordinate_one_jet
    · rw [ModelWithCorners.range_eq_univ]; exact univ_mem
    · intro j _
      have hev : tensor0SModelInChart (s + k) x (iteratedMetricCovariantDerivative g s A k)
          =ᶠ[𝓝 (extChartAt (𝓡 3) x x)]
          tensor0SModelInChart (s + k) x (iteratedMetricCovariantDerivative g s B k) := by
        have hc : ContinuousAt (extChartAt (𝓡 3) x).symm (extChartAt (𝓡 3) x x) :=
          continuousAt_extChartAt_symm x
        have hmem : V ∈ 𝓝 ((extChartAt (𝓡 3) x).symm (extChartAt (𝓡 3) x x)) := by
          rw [extChartAt_to_inv]; exact hV.mem_nhds hx
        filter_upwards [hc hmem] with y hy
        simp only [tensor0SModelInChart]
        rw [ih _ hy]
      exact hev.iteratedFDeriv ℝ j |>.eq_of_nhds

/-- The inverse of a smooth isometric equivalence is isometric. -/
theorem inner_mfderiv_symm_O19 (H H' : FiniteVolumeHyperbolicModel.{u})
    (e : H.Carrier ≃ H'.Carrier) (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e)
    (he' : ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm)
    (hiso : ∀ p, localPullInner H'.metric e p = H.metric.inner p)
    (y : H'.Carrier) (a b : TangentSpace (𝓡 3) y) :
    H.metric.inner (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y a)
      (mfderiv (𝓡 3) (𝓡 3) e.symm y b) = H'.metric.inner y a b := by
  have hinf : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hcomp : ∀ c : TangentSpace (𝓡 3) y,
      mfderiv (𝓡 3) (𝓡 3) e (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y c) = c := by
    intro c
    have h1 := mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) y
      ((he (e.symm y)).mdifferentiableAt hinf) ((he' y).mdifferentiableAt hinf) (v := c)
    have h2 : (e ∘ e.symm) = id := funext e.apply_symm_apply
    rw [← h1, h2, mfderiv_id]
    rfl
  have key := congrArg (fun L => L (mfderiv (𝓡 3) (𝓡 3) e.symm y a)
    (mfderiv (𝓡 3) (𝓡 3) e.symm y b)) (hiso (e.symm y))
  simp only [localPullInner_apply, hcomp] at key
  rw [← key]
  have hy : e (e.symm y) = y := e.apply_symm_apply y
  have hgen : ∀ z : H'.Carrier, z = y → H'.metric.inner z a b = H'.metric.inner y a b := by
    rintro z rfl; rfl
  exact hgen _ hy

/-- The pulled-back inner products agree on `U`. -/
theorem localPullInner_comp_isometry_target_O19 {Hs : FiniteVolumeHyperbolicModel.{u}}
    (H H' : FiniteVolumeHyperbolicModel.{u}) (e : H.Carrier ≃ H'.Carrier)
    (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e) (he' : ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm)
    (hiso : ∀ p, localPullInner H'.metric e p = H.metric.inner p)
    (U : TopologicalSpace.Opens Hs.Carrier) (f : Hs.Carrier → H'.Carrier)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) (q : Hs.Carrier) (hq : q ∈ U) :
    localPullInner (I := 𝓡 3) H.metric (fun z => e.symm (f z)) q =
      localPullInner (I := 𝓡 3) H'.metric f q := by
  have hinf : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  ext v w
  rw [localPullInner_apply, localPullInner_apply]
  have hfq : MDifferentiableAt (𝓡 3) (𝓡 3) f q :=
    (hf.contMDiffAt (U.isOpen.mem_nhds hq)).mdifferentiableAt hinf
  have hcomp : ∀ c : TangentSpace (𝓡 3) q,
      mfderiv (𝓡 3) (𝓡 3) (fun z => e.symm (f z)) q c =
        mfderiv (𝓡 3) (𝓡 3) e.symm (f q) (mfderiv (𝓡 3) (𝓡 3) f q c) := fun c =>
    mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) q
      ((he' (f q)).mdifferentiableAt hinf) hfq (v := c)
  rw [hcomp v, hcomp w]
  exact inner_mfderiv_symm_O19 H H' e he he' hiso (f q) _ _

/-- **N1 (target-side isometry naturality).** -/
theorem ckErr_comp_isometry_target_O19 (Hs H H' : FiniteVolumeHyperbolicModel.{u})
    (e : H.Carrier ≃ H'.Carrier) (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e)
    (he' : ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm)
    (hiso : ∀ p, localPullInner H'.metric e p = H.metric.inner p)
    (U : TopologicalSpace.Opens Hs.Carrier) (f : Hs.Carrier → H'.Carrier)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) (c : ℝ) (j : ℕ) (p : Hs.Carrier) (hp : p ∈ U) :
    ckErr_O19 Hs H.metric c (fun q => e.symm (f q)) j p = ckErr_O19 Hs H'.metric c f j p := by
  unfold ckErr_O19
  congr 1
  refine iteratedMetricCovariantDerivative_congr_open_O19 Hs.metric _ _ U.isOpen ?_ j p hp
  intro q hq
  rw [localPullInner_comp_isometry_target_O19 H H' e he he' hiso U f hf q hq]

end GC.LongTime.Ch12
