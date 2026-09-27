import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.VariationPairing

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u v

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
variable {A : Type v} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem covDerivAlong_parameter_derivative_inner_of_regularCrossing
    (W : TopologicalSpace.Opens E.incoming.terminalRegularOpen)
    (F : PartialDiffeomorph ThreeModel ThreeModel
      E.incoming.terminalRegularOpen Q.Carrier ∞)
    (hsource : F.source = W)
    (hcross : ∀ x : W, E.RegularCrossing x.val.val (F x.val))
    {η : A × ℝ → W} {z : A} {t : ℝ}
    (hη : ContMDiffAt (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ η (z, t))
    (v w : A) :
    E.outputMetric.inner (F (η (z, t)).val)
      (covDerivAlong E.outputMetric (fun r => F (η (z, r)).val)
        (fun r => mfderiv 𝓘(ℝ, A) ThreeModel (fun q => F (η (q, r)).val) z v) t)
      (mfderiv 𝓘(ℝ, A) ThreeModel (fun q => F (η (q, t)).val) z w) =
      E.terminal.metric.inner (η (z, t)).val
        (covDerivAlong E.terminal.metric (fun r => (η (z, r)).val)
          (fun r => mfderiv 𝓘(ℝ, A) ThreeModel (fun q => (η (q, r)).val) z v) t)
        (mfderiv 𝓘(ℝ, A) ThreeModel (fun q => (η (q, t)).val) z w) := by
  let f : W → Q.Carrier := fun x => F x.val
  have hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f := by
    intro x
    have hFx : IsLocalDiffeomorphAt ThreeModel ThreeModel ∞ F x.val :=
      ⟨F, (hsource ▸ x.property), fun _ _ => rfl⟩
    exact (isLocalDiffeomorph_subtype_val W x).comp ThreeModel _ hFx
  have hinc : IsSmoothEmbedding ThreeModel ThreeModel ∞
      (Subtype.val : W → E.incoming.terminalRegularOpen) :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      (isLocalDiffeomorph_subtype_val W) Subtype.val_injective
  have hmetric (x : W) (v w : TangentSpace ThreeModel x) :
      (E.terminal.metric.restrictOpen W).inner x v w =
        E.outputMetric.inner (f x) (mfderiv ThreeModel ThreeModel f x v)
          (mfderiv ThreeModel ThreeModel f x w) := by
    have h := E.regularCrossing_chart_metric_inner
      (Subtype.val : W → E.incoming.terminalRegularOpen) f hinc rfl hcross x v w
    rw [mfderiv_subtype_val] at h
    exact h.symm
  have hnew := inner_covDerivAlong_parameter_derivative_map_of_local_isometry_on
    (E.terminal.metric.restrictOpen W) E.outputMetric isOpen_univ
    (fun x => hf x.val) (fun x _ v w => hmetric x v w) hη (mem_univ _) v w
  have hold := inner_covDerivAlong_parameter_derivative_map_of_local_isometry_on
    (E.terminal.metric.restrictOpen W) E.terminal.metric isOpen_univ
    (fun x => isLocalDiffeomorph_subtype_val W x.val)
    (fun x _ v w => by rw [mfderiv_subtype_val]; rfl) hη (mem_univ _) v w
  exact hnew.trans hold.symm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
