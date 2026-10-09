import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u v

variable {P : OrientedThreeStage.{u}} {Q : OrientedThreeStage.{v}} {a s : ℝ}

private theorem pullback_smoothUpTo
    (G : Q.IncomingSlab a s)
    (φ : P.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q.Carrier) :
    P.MetricSmoothUpTo
      (fun t => Diffeomorph.pullbackMetricCross (G.flow.base.metric t) φ) (Ico a s) := by
  let h : ℝ → SmoothRiemannianMetric ThreeModel P.Carrier :=
    fun t => Diffeomorph.pullbackMetricCross (G.flow.base.metric t) φ
  have hj : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × Q.Carrier => (⟨q.2, (G.flow.base.metric q.1).inner q.2⟩ :
        TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (Ico a s ×ˢ (Set.univ : Set Q.Carrier)) := G.smoothUpTo.jointContMDiffOn
  have hgram : ∀ (x₀ : P.Carrier) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
        (fun q : ℝ × P.Carrier =>
          chartGramMatrix (I := ThreeModel) (h q.1) x₀ q.2 i j)
        (Ico a s ×ˢ (trivializationAt ThreeSpace
          (TangentSpace ThreeModel) x₀).baseSet) := by
    intro x₀ i j
    exact chartGramMatrix_joint_contMDiffOn_of_pullback
      G.flow.base.metric (Ico a s) hj h (fun x => φ x) φ.contMDiff
      (fun t _ x v w => Diffeomorph.pullbackMetricCross_inner
        (G.flow.base.metric t) φ x v w) x₀ i j
  have hjoint := metricCLMSection_jointContMDiffOn_of_chartGram_on h (Ico a s) hgram
  intro p t ht
  obtain ⟨b, htb, hbs⟩ := exists_between ht.2
  have hab : a < b := ht.1.trans_lt htb
  obtain ⟨U, hU, hpU, hUbase, V, hV, htV, A, hA, hEq⟩ :=
    MetricSmoothUpTo.of_contMDiffOn_Ico P h hab hbs hjoint p t ⟨ht.1, htb.le⟩
  refine ⟨U, hU, hpU, hUbase, V ∩ Iio b, hV.inter isOpen_Iio,
    ⟨htV, htb⟩, A, ?_, ?_⟩
  · intro i j
    exact (hA i j).mono (Set.prod_mono inter_subset_left subset_rfl)
  · intro r hr x hx i j
    exact hEq r ⟨hr.1.1, hr.2.1, hr.1.2.le⟩ x hx i j

def IncomingSlab.pullback
    (G : Q.IncomingSlab a s)
    (φ : P.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q.Carrier) :
    P.IncomingSlab a s where
  lt := G.lt
  flow := G.flow.pullback φ
  equation := G.equation.pullback G.flow φ
  smoothUpTo := pullback_smoothUpTo G φ

@[simp] theorem IncomingSlab.pullback_flow
    (G : Q.IncomingSlab a s)
    (φ : P.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q.Carrier) :
    (G.pullback φ).flow = G.flow.pullback φ := rfl

theorem IncomingSlab.pullback_metric
    (G : Q.IncomingSlab a s)
    (φ : P.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q.Carrier) (t : ℝ) :
    (G.pullback φ).flow.base.metric t =
      Diffeomorph.pullbackMetricCross (G.flow.base.metric t) φ := rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
