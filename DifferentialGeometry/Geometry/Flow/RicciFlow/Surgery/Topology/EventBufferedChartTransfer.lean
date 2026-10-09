import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventSurvivorMap
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u v

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ G H}
  {X : Type v} [TopologicalSpace X] [ChartedSpace H X]

theorem survivor_chart_metric_inner
    (F : PartialDiffeomorph ThreeModel ThreeModel
      E.incoming.terminalRegularOpen Q.Carrier ∞)
    (hmetric : ∀ x ∈ F.source, ∀ v w : TangentSpace ThreeModel x,
      E.outputMetric.inner (F x) (mfderiv ThreeModel ThreeModel (F : _ → _) x v)
        (mfderiv ThreeModel ThreeModel (F : _ → _) x w) = E.terminal.metric.inner x v w)
    (φ : X → E.incoming.terminalRegularOpen) (hφ : ContMDiff I ThreeModel ∞ φ)
    (himage : range φ ⊆ F.source) (x : X) (v w : TangentSpace I x) :
    E.outputMetric.inner ((F : _ → _) (φ x))
        (mfderiv I ThreeModel ((F : _ → _) ∘ φ) x v)
        (mfderiv I ThreeModel ((F : _ → _) ∘ φ) x w) =
      E.terminal.metric.inner (φ x) (mfderiv I ThreeModel φ x v)
        (mfderiv I ThreeModel φ x w) := by
  rw [mfderiv_comp x (F.mdifferentiableAt (by simp) (himage (mem_range_self x)))
    (hφ.mdifferentiableAt (by simp))]
  exact hmetric (φ x) (himage (mem_range_self x))
    (mfderiv I ThreeModel φ x v) (mfderiv I ThreeModel φ x w)

theorem exists_survivor_whole_chart_transfer
    (W : TopologicalSpace.Opens E.incoming.terminalRegularOpen) (p : W)
    (hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' E.old)) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel
        E.incoming.terminalRegularOpen Q.Carrier ∞,
      F.source = W ∧
      (∀ x ∈ W, E.RegularCrossing x.val (F x)) ∧
      (∀ z : E.old, E.oldTerminal z ∈ W → F (E.oldTerminal z) = E.oldOutput z) ∧
      ∀ (φ : X → E.incoming.terminalRegularOpen),
        IsSmoothEmbedding I ThreeModel ∞ φ → range φ ⊆ W →
        ∃ ψ : X → Q.Carrier, ψ = (F : _ → _) ∘ φ ∧
          IsSmoothEmbedding I ThreeModel ∞ ψ ∧
          (∀ x, E.RegularCrossing (φ x).val (ψ x)) ∧
          (∀ (x : X) (z : E.old), E.oldTerminal z = φ x → ψ x = E.oldOutput z) ∧
          (∀ A : Set X, ψ '' A = (F : _ → _) '' (φ '' A)) ∧
          ∀ (x : X) (v w : TangentSpace I x),
            E.outputMetric.inner (ψ x) (mfderiv I ThreeModel ψ x v)
              (mfderiv I ThreeModel ψ x w) =
              E.terminal.metric.inner (φ x) (mfderiv I ThreeModel φ x v)
                (mfderiv I ThreeModel φ x w) := by
  obtain ⟨F, hsource, hcross, hold, hmetric⟩ :=
    E.exists_survivor_partialDiffeomorph W p hW
  refine ⟨F, hsource, hcross, hold, ?_⟩
  intro φ hφ himage
  have hsrc : range φ ⊆ F.source := by rwa [hsource]
  refine ⟨(F : _ → _) ∘ φ, rfl,
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph F hφ hsrc,
    ?_, ?_, ?_, ?_⟩
  · intro x
    exact hcross (φ x) (himage (mem_range_self x))
  · intro x z hz
    change F (φ x) = E.oldOutput z
    rw [← hz]
    exact hold z (show E.oldTerminal z ∈ W from hz ▸ himage (mem_range_self x))
  · intro A
    exact (Set.image_image (F : _ → _) φ A).symm
  · intro x v w
    apply E.survivor_chart_metric_inner F ?_ φ hφ.contMDiff hsrc x v w
    intro y hy
    rw [hsource] at hy
    exact hmetric y hy

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end
