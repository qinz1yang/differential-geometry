import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.TensorTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedNeckDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ShrinkingCylinderIsometries
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Metric.Family.CoefficientExtension
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {δ : ℝ} {k : ℕ}
    {N N' : NormalizedNeck (H.event i).terminal.metric δ k} {r : ℝ}

private theorem pullback_metric_smooth (B : IncomingBackwardNeck H i N r)
    (Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ neckBuffer δ) :
    ∀ p : neckBuffer δ, ∀ t ∈ Icc (-1 : ℝ) 0,
      ∃ U : Set (neckBuffer δ), IsOpen U ∧ p ∈ U ∧
        U ⊆ (trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
          (TangentSpace NeckCylinderModel) p).baseSet ∧
        ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
        ∃ A : ℝ × neckBuffer δ → (EuclideanSpace ℝ (Fin 2) × ℝ) →
          (EuclideanSpace ℝ (Fin 2) × ℝ) → ℝ,
          (∀ v w, ContMDiffOn (𝓘(ℝ, ℝ).prod NeckCylinderModel) 𝓘(ℝ) ∞
            (fun q => A q v w) (V ×ˢ U)) ∧
          ∀ s ∈ V ∩ Icc (-1 : ℝ) 0, ∀ x ∈ U, ∀ v w,
            A (s, x) v w = (Diffeomorph.pullbackMetricCross (B.metric s) Φ).inner x
              ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
                (TangentSpace NeckCylinderModel) p).symmL ℝ x v)
              ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
                (TangentSpace NeckCylinderModel) p).symmL ℝ x w) := by
  intro p t ht
  have hg := metricCLMSection_jointContMDiffOn_of_local_coefficients B.metric
    (Icc (-1 : ℝ) 0) B.metric_smooth
  have hg' := metricCLMSection_jointContMDiffOn_of_chartGram_on
    (fun t => Diffeomorph.pullbackMetricCross (B.metric t) Φ) (Icc (-1 : ℝ) 0)
    (chartGramMatrix_pullback_joint_contMDiffOn B.metric (Icc (-1 : ℝ) 0) hg
      (fun _ => Φ) (Φ.contMDiff.comp contMDiff_snd))
  obtain ⟨U, hU, hp, hUb, A, hA, heq⟩ :=
    Geometry.Metric.exists_local_metric_coefficient_extension
      (fun t => Diffeomorph.pullbackMetricCross (B.metric t) Φ)
      (by norm_num : (-1 : ℝ) < 0) hg' p
  exact ⟨U, hU, hp, hUb, univ, isOpen_univ, mem_univ t, A, hA,
    fun u hu x hx v w => heq u hu.2 x hx v w⟩


private theorem pullback_metric_on_slab (B : IncomingBackwardNeck H i N r)
    (Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ neckBuffer δ)
    (j : Fin H.eventCount) (hj : j.val ≤ i.val)
    (ha : H.time i.succ - r ^ 2 < H.time j.succ) (v : ℝ) (hv : v ∈ Ico (-1 : ℝ) 0)
    (htlo : H.time j.castSucc ≤ H.time i.succ + r ^ 2 * v)
    (hthi : H.time i.succ + r ^ 2 * v < H.time j.succ)
    (x : neckBuffer δ) (V W : TangentSpace NeckCylinderModel x) :
    (Diffeomorph.pullbackMetricCross (B.metric v) Φ).inner x V W = (r ^ 2)⁻¹ *
      ((H.event j).incoming.flow.base.metric (H.time i.succ + r ^ 2 * v)).inner
        (B.stageChart j hj ha (Φ x))
        (mfderiv NeckCylinderModel ThreeModel ((B.stageChart j hj ha) ∘ Φ) x V)
        (mfderiv NeckCylinderModel ThreeModel ((B.stageChart j hj ha) ∘ Φ) x W) := by
  rw [Diffeomorph.pullbackMetricCross_inner,
    B.metric_on_slab j hj ha v hv htlo hthi]
  have hmd := (B.stageChart_smooth j hj ha).contMDiff.mdifferentiableAt
    (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x := Φ x)
  have hmd' := Φ.contMDiff.mdifferentiableAt
    (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x := x)
  have hV := mfderiv_comp_apply x hmd hmd' V
  have hW := mfderiv_comp_apply x hmd hmd' W
  rw [hV, hW]


def IncomingBackwardNeck.pullback (B : IncomingBackwardNeck H i N r)
    (Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ neckBuffer δ)
    (hchart : ∀ x, N'.chart x = N.chart (Φ x))
    (hmetric : N'.normalizedMetric = Diffeomorph.pullbackMetricCross N.normalizedMetric Φ)
    (hmodel : ∀ t : Iio (1 : ℝ), Diffeomorph.pullbackMetricCross
      ((shrinkingCylinderMetric t).restrictOpen (neckBuffer δ)) Φ =
      (shrinkingCylinderMetric t).restrictOpen (neckBuffer δ))
    (htest : MapsTo Φ (neckClosedTest δ) (neckClosedTest δ)) :
    IncomingBackwardNeck H i N' r := by
  let : SigmaCompactSpace (neckBuffer δ) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer δ).isOpen)
  let A : ℝ → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2 :=
    fun t => metricTensorField (B.metric t) -
    metricTensorField ((shrinkingCylinderMetric
      ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ))
  have hA (t : ℝ) (x : neckBuffer δ) :
      pullbackTensor02FieldCross Φ (A t) x =
      metricTensorField (Diffeomorph.pullbackMetricCross (B.metric t) Φ) x -
        metricTensorField ((shrinkingCylinderMetric
          ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)) x := by
    have hbg := congrArg (fun g : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ) =>
      metricTensorField g x) (hmodel ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩)
    rw [← hbg]
    ext v
    rw [pullbackTensor02FieldCross_apply]
    rfl
  refine {
    radius_pos := B.radius_pos
    left_nonneg := B.left_nonneg
    stageChart := fun j hj ha => ⟨(B.stageChart j hj ha) ∘ Φ,
      (B.stageChart j hj ha).continuous.comp Φ.continuous⟩
    stageChart_smooth := ?_
    terminal_chart := fun ha x => (B.terminal_chart ha (Φ x)).trans (congrArg Subtype.val (hchart x)).symm
    crossing := fun j hj ha hn x => B.crossing j hj ha hn (Φ x)
    metric := fun t => Diffeomorph.pullbackMetricCross (B.metric t) Φ
    terminal_metric := (congrArg (fun g => Diffeomorph.pullbackMetricCross g Φ)
      B.terminal_metric).trans hmetric.symm
    metric_on_slab := pullback_metric_on_slab B Φ
    timeDifferenceJet := fun b v => pullbackTensor02FieldCross Φ (B.timeDifferenceJet b v)
    timeDifferenceJet_eq := ?_
    parabolic_closeness := ?_
    metric_smooth := pullback_metric_smooth B Φ }
  · intro j hj ha
    change IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ ((B.stageChart j hj ha) ∘ Φ)
    exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp
      (B.stageChart j hj ha) (B.stageChart_smooth j hj ha) Φ
  · intro b v x
    have hh := pullbackTensor02FieldCross_eq_iteratedDerivWithin Φ A
      (B.timeDifferenceJet b v) b (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0)) v.2
      (B.timeDifferenceJet_eq b v) x
    simp only [hA] at hh
    exact hh
  · obtain ⟨η, hη, hbound⟩ := B.parabolic_closeness
    refine ⟨η, hη, ?_⟩
    intro a b hab v x hx
    have hh := hbound a b hab v (Φ x) (htest hx)
    simp only [cylinderTensorCovDeriv_eq_tensor02CovDeriv] at hh ⊢
    change tensor02CovDerivNormWith a (pullbackTensor02FieldCross Φ (B.timeDifferenceJet b v))
      ((shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ))
      ((shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)) x ≤ η
    rw [← hmodel ⟨v.1, v.2.2.trans_lt zero_lt_one⟩,
      tensor02CovDerivNormWith_pullbackTensor02FieldCross]
    exact hh

section PullbackProjections

variable (B : IncomingBackwardNeck H i N r)
    (Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ neckBuffer δ)
    (hchart : ∀ x, N'.chart x = N.chart (Φ x))
    (hmetric : N'.normalizedMetric = Diffeomorph.pullbackMetricCross N.normalizedMetric Φ)
    (hmodel : ∀ t : Iio (1 : ℝ), Diffeomorph.pullbackMetricCross
      ((shrinkingCylinderMetric t).restrictOpen (neckBuffer δ)) Φ =
      (shrinkingCylinderMetric t).restrictOpen (neckBuffer δ))
    (htest : MapsTo Φ (neckClosedTest δ) (neckClosedTest δ))

@[simp] theorem IncomingBackwardNeck.pullback_stageChart
    (j : Fin H.eventCount) (hj : j.val ≤ i.val)
    (ha : H.time i.succ - r ^ 2 < H.time j.succ) (x : neckBuffer δ) :
    (B.pullback Φ hchart hmetric hmodel htest).stageChart j hj ha x =
      B.stageChart j hj ha (Φ x) := rfl

@[simp] theorem IncomingBackwardNeck.pullback_metric (t : ℝ) :
    (B.pullback Φ hchart hmetric hmodel htest).metric t =
      Diffeomorph.pullbackMetricCross (B.metric t) Φ := rfl

@[simp] theorem IncomingBackwardNeck.pullback_timeDifferenceJet
    (b : ℕ) (v : Icc (-1 : ℝ) 0) :
    (B.pullback Φ hchart hmetric hmodel htest).timeDifferenceJet b v =
      pullbackTensor02FieldCross Φ (B.timeDifferenceJet b v) := rfl

end PullbackProjections


private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

open DifferentialGeometry.Geometry.Neck

def IncomingBackwardNeck.rotatedDatum (B : IncomingBackwardNeck H i N r)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (he : Geometry.sphereDiffeo (n := 2) e spherePoint = N.sphereMark) (side : Bool) :
    IncomingBackwardNeck H i (N.rotatedDatum e he side).toNormalizedNeck r := by
  apply B.pullback (bufferedCylinderRotation δ e) (fun _ => rfl)
  · have hh := N.rotatedDatum_normalizedMetric e he side
    dsimp only at hh
    exact hh.trans (Diffeomorph.pullbackMetricCross_eq_pullbackMetric
      N.normalizedMetric (show neckBuffer δ ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ neckBuffer δ
        from bufferedCylinderRotation δ e)).symm
  · exact pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderRotation δ e
  · intro x hx
    rw [← image_bufferedCylinderRotation_neckClosedTest δ e]
    exact mem_image_of_mem _ hx


def IncomingBackwardNeck.oriented
    {x : (H.event i).incoming.terminalRegularOpen}
    (d : normalizedDatum (I := ThreeModel) (H.event i).terminal.metric x δ k)
    (B : IncomingBackwardNeck H i d.toNormalizedNeck r) :
    IncomingBackwardNeck H i
      (normalizedDatum.toNormalizedNeck (normalizedDatum.oriented (I := ThreeModel) d)) r := by
  apply B.pullback (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq)
    (fun _ => rfl)
  · exact d.oriented_normalizedMetric.trans
      (Diffeomorph.pullbackMetricCross_eq_pullbackMetric d.normalizedMetric
        (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq)).symm
  · exact pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderOrientation
      δ d.retainedSign d.retainedSign_sq
  · intro x hx
    rw [← image_bufferedCylinderOrientation_neckClosedTest δ d.retainedSign d.retainedSign_sq]
    exact mem_image_of_mem _ hx


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
