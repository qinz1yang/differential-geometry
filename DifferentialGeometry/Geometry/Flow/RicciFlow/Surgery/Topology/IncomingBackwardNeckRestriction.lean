import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.OpenTensorRestriction
import DifferentialGeometry.Geometry.Metric.Family.CoefficientExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffRemainingFields

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {δ δ' : ℝ} {k : ℕ}
    {N : NormalizedNeck (H.event i).terminal.metric δ k} {r : ℝ}

private theorem restricted_timeDifferenceJet_eq (B : IncomingBackwardNeck H i N r)
    (h : δ ≤ δ') (b : ℕ) (v : Icc (-1 : ℝ) 0) (x : neckBuffer δ') :
    restrictOpenTensor02FieldOfSubset (neckBuffer_le_of_le N.delta_pos h)
      (B.timeDifferenceJet b v) x =
      iteratedDerivWithin b (fun t =>
        metricTensorField ((B.metric t).restrictOpenOfSubset
          (neckBuffer_le_of_le N.delta_pos h)) x -
        metricTensorField ((shrinkingCylinderMetric
          ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
            (neckBuffer δ')) x) (Icc (-1 : ℝ) 0) v.1 := by
  let hle := neckBuffer_le_of_le N.delta_pos h
  let A := fun t => metricTensorField (B.metric t) -
    metricTensorField ((shrinkingCylinderMetric
      ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ))
  have hA : (fun t => metricTensorField ((B.metric t).restrictOpenOfSubset hle) x -
      metricTensorField ((shrinkingCylinderMetric
        ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ')) x) =
      fun t => restrictOpenTensor02FieldOfSubset hle (A t) x := by
    funext t
    rw [restrictOpenTensor02FieldOfSubset_eq]
    rfl
  rw [restrictOpenTensor02FieldOfSubset_eq, hA,
    iteratedDerivWithin_restrictOpenTensor02FieldOfSubset hle A b x
      (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0)) v.2]
  exact B.timeDifferenceJet_eq b v (TopologicalSpace.Opens.inclusion hle x)

private theorem restricted_parabolic_closeness (B : IncomingBackwardNeck H i N r)
    (h : δ ≤ δ') :
    ∃ η : ℝ, η < δ' ∧ ∀ a b : ℕ, a + 2*b ≤ k →
      ∀ v : Icc (-1 : ℝ) 0, ∀ x ∈ neckClosedTest δ',
      let g := (shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen
        (neckBuffer δ')
      Real.sqrt (normSq0S g x (a + 2)
        (cylinderTensorCovDeriv g
          (restrictOpenTensor02FieldOfSubset (neckBuffer_le_of_le N.delta_pos h)
            (B.timeDifferenceJet b v)) a x)) ≤ η := by
  obtain ⟨η, hη, hbound⟩ := B.parabolic_closeness
  refine ⟨η, hη.trans_le h, ?_⟩
  intro a b hab v x hx
  let hle := neckBuffer_le_of_le N.delta_pos h
  let : SigmaCompactSpace (neckBuffer δ) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer δ).isOpen)
  have hx' : TopologicalSpace.Opens.inclusion hle x ∈ neckClosedTest δ := by
    have hinv : δ'⁻¹ ≤ δ⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le N.delta_pos h
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hh := hbound a b hab v (TopologicalSpace.Opens.inclusion hle x) hx'
  simp only [cylinderTensorCovDeriv_eq_tensor02CovDeriv] at hh ⊢
  change tensor02CovDerivNormWith a (restrictOpenTensor02FieldOfSubset hle
    (B.timeDifferenceJet b v))
      ((shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ'))
      ((shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ')) x ≤ η
  rw [← SmoothRiemannianMetric.restrictOpen_flat _ hle,
    tensor02CovDerivNormWith_restrictOpenOfSubset hle]
  exact hh

private local instance : SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.event i).incoming.terminalRegularOpen.isOpen)

def IncomingBackwardNeck.monoDelta (B : IncomingBackwardNeck H i N r)
    (h : δ ≤ δ') (h' : δ' < 1) : IncomingBackwardNeck H i (N.monoDelta h h') r := by
  let hle := neckBuffer_le_of_le N.delta_pos h
  let incl := TopologicalSpace.Opens.inclusion hle
  have hincl : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ incl :=
    isSmoothEmbedding_opens_inclusion hle
  refine {
    radius_pos := B.radius_pos
    left_nonneg := B.left_nonneg
    stageChart := fun j hj ha => ⟨(B.stageChart j hj ha) ∘ incl,
      (B.stageChart j hj ha).continuous.comp hincl.contMDiff.continuous⟩
    stageChart_smooth := by
      intro j hj ha
      change IsSmoothEmbedding NeckCylinderModel ThreeModel ∞
        ((B.stageChart j hj ha) ∘ incl)
      exact IsSmoothEmbedding.comp (B.stageChart_smooth j hj ha) hincl (by decide)
    terminal_chart := fun ha x => B.terminal_chart ha (incl x)
    crossing := fun j hj ha hn x => B.crossing j hj ha hn (incl x)
    metric := fun t => (B.metric t).restrictOpenOfSubset hle
    terminal_metric := congrArg (fun g => g.restrictOpenOfSubset hle) B.terminal_metric
    metric_on_slab := ?_
    timeDifferenceJet := fun b v => restrictOpenTensor02FieldOfSubset hle (B.timeDifferenceJet b v)
    timeDifferenceJet_eq := restricted_timeDifferenceJet_eq B h
    parabolic_closeness := restricted_parabolic_closeness B h
    metric_smooth := ?_ }
  · intro j hj ha v hv htlo hthi x V W
    rw [SmoothRiemannianMetric.restrictSubset_inner,
      B.metric_on_slab j hj ha v hv htlo hthi (incl x) V W]
    have hmd := (B.stageChart_smooth j hj ha).contMDiff.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x := incl x)
    have hmd' := hincl.contMDiff.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x := x)
    change _ = _ * ((H.event j).incoming.flow.base.metric _).inner _
      (mfderiv NeckCylinderModel ThreeModel ((B.stageChart j hj ha) ∘ incl) x V)
      (mfderiv NeckCylinderModel ThreeModel ((B.stageChart j hj ha) ∘ incl) x W)
    rw [mfderiv_comp_apply x hmd hmd' V, mfderiv_comp_apply x hmd hmd' W]
    rw [show mfderiv NeckCylinderModel NeckCylinderModel incl x =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) from
        mfderiv_opens_incl (I := NeckCylinderModel) hle x]
    rfl
  · intro p t ht
    have hg := metricCLMSection_jointContMDiffOn_of_local_coefficients B.metric
      (Icc (-1 : ℝ) 0) B.metric_smooth
    have hg' := metricCLMSection_jointContMDiffOn_restrictOpenOfSubset hle B.metric
      (Icc (-1 : ℝ) 0) hg
    obtain ⟨U, hU, hp, hUb, A, hA, heq⟩ :=
      Geometry.Metric.exists_local_metric_coefficient_extension
        (fun t => (B.metric t).restrictOpenOfSubset hle)
        (by norm_num : (-1 : ℝ) < 0) hg' p
    exact ⟨U, hU, hp, hUb, univ, isOpen_univ, mem_univ t, A, hA,
      fun u hu x hx v w => heq u hu.2 x hx v w⟩

@[simp] theorem IncomingBackwardNeck.monoDelta_stageChart
    (B : IncomingBackwardNeck H i N r) (h : δ ≤ δ') (h' : δ' < 1)
    (j : Fin H.eventCount) (hj : j.val ≤ i.val)
    (ha : H.time i.succ - r ^ 2 < H.time j.succ) (x : neckBuffer δ') :
    (B.monoDelta h h').stageChart j hj ha x = B.stageChart j hj ha
      (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le N.delta_pos h) x) := rfl

@[simp] theorem IncomingBackwardNeck.monoDelta_metric
    (B : IncomingBackwardNeck H i N r) (h : δ ≤ δ') (h' : δ' < 1) (t : ℝ) :
    (B.monoDelta h h').metric t =
      (B.metric t).restrictOpenOfSubset (neckBuffer_le_of_le N.delta_pos h) := rfl

@[simp] theorem IncomingBackwardNeck.monoDelta_timeDifferenceJet
    (B : IncomingBackwardNeck H i N r) (h : δ ≤ δ') (h' : δ' < 1)
    (b : ℕ) (v : Icc (-1 : ℝ) 0) :
    (B.monoDelta h h').timeDifferenceJet b v =
      restrictOpenTensor02FieldOfSubset (neckBuffer_le_of_le N.delta_pos h)
        (B.timeDifferenceJet b v) := rfl


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
