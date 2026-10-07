import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StepPieces_O40
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrBridge_S57
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Locality

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness
open Set TopologicalSpace Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.LongTime.Ch12

/-- CH12-O40 G2: a self-map of `H` that is the identity on an open set has vanishing
`ckErr_S45` (against `H.metric`, scale `1`) at every point of that set. -/
theorem ckErr_eq_zero_of_eq_id_O40 (H : FiniteVolumeHyperbolicModel.{u})
    (F : H.Carrier → H.Carrier) (U : Opens H.Carrier) (hFU : ∀ x ∈ U, F x = x) (j : ℕ)
    (p : H.Carrier) (hp : p ∈ U) : ckErr_S45 H H.metric 1 F j p = 0 := by
  have hev : ∀ y ∈ U, F =ᶠ[𝓝 y] id := fun y hy =>
    Filter.eventually_of_mem (U.isOpen.mem_nhds hy) fun x hx => hFU x hx
  have hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ F U :=
    contMDiffOn_id.congr fun x hx => hFU x hx
  have hd : ∀ y ∈ U, mfderiv (𝓡 3) (𝓡 3) F y = mfderiv (𝓡 3) (𝓡 3) id y := fun y hy =>
    (hev y hy).mfderiv_eq
  have hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) F y) := by
    intro y hy
    rw [hd y hy, mfderiv_id]
    exact fun a b h => h
  rw [ckErr_S45_eq_metricDerivNorm_S57 H H.metric 1 one_pos F U hF hinj j ⟨p, hp⟩]
  rw [metricDerivNorm_eq_of_metric_eventuallyEq j _ (H.metric.restrictOpen U)
    (H.metric.restrictOpen U) (H.metric.restrictOpen U) ⟨p, hp⟩ (Filter.Eventually.of_forall
      fun z v w => ?_)]
  · exact metricDerivNorm_self j _ _ _
  · simp only [pullbackRestrict_S57, SmoothRiemannianMetric.pullbackOfImmersion_inner,
      scaleMetric_inner, one_mul, SmoothRiemannianMetric.restrictOpen_inner]
    rw [mfderiv_comp_val_C4 F U hF z v, mfderiv_comp_val_C4 F U hF z w, hd z z.2, mfderiv_id,
      hFU z z.2]
    rfl

end GC.LongTime.Ch12
