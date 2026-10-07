import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowDeepC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardNeckIsometries
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardNeckRestriction

/-!
# Deep backward necks: neck-level transports (C12X, S16 round 3, O-C12X-S16K G1c)

The record necks of CT/PreparedHistoryCutoff and CT/HornCutoffRecord are obtained from the
selected neck by `monoDelta`, `rotatedDatum`, `oriented` and `lowerOrder`; the backward necks
follow by the corresponding operations on `IncomingBackwardNeck`
(ST/IncomingBackwardNeckIsometries, ST/IncomingBackwardNeckRestriction).  This file gives the deep
analogues for `IncomingBackwardNeckDeep_C12X` (depth factor `θ`), each extending the depth-one
operation (`toIncomingBackwardNeck` is the depth-one transport):

* `IncomingBackwardNeckDeep_C12X.pullback_C12X` (neck-buffer isometry fixing the model family),
  `rotatedDatum_C12X`, `oriented_C12X`;
* `IncomingBackwardNeckDeep_C12X.monoDelta_C12X` (restriction to a smaller buffer),
  `lowerOrder_C12X`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section Pullback

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {δ : ℝ} {k : ℕ}
    {N N' : NormalizedNeck (H.event i).terminal.metric δ k} {r θ : ℝ}

private theorem deep_pullback_metric_smooth_C12X (D : IncomingBackwardNeckDeep_C12X H i N r θ)
    (Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ neckBuffer δ) :
    ∀ p : neckBuffer δ, ∀ t ∈ Icc (-θ) 0,
      ∃ U : Set (neckBuffer δ), IsOpen U ∧ p ∈ U ∧
        U ⊆ (trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
          (TangentSpace NeckCylinderModel) p).baseSet ∧
        ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
        ∃ A : ℝ × neckBuffer δ → (EuclideanSpace ℝ (Fin 2) × ℝ) →
          (EuclideanSpace ℝ (Fin 2) × ℝ) → ℝ,
          (∀ v w, ContMDiffOn (𝓘(ℝ, ℝ).prod NeckCylinderModel) 𝓘(ℝ) ∞
            (fun q => A q v w) (V ×ˢ U)) ∧
          ∀ s ∈ V ∩ Icc (-θ) 0, ∀ x ∈ U, ∀ v w,
            A (s, x) v w = (Diffeomorph.pullbackMetricCross (D.metric s) Φ).inner x
              ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
                (TangentSpace NeckCylinderModel) p).symmL ℝ x v)
              ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
                (TangentSpace NeckCylinderModel) p).symmL ℝ x w) := by
  intro p t _
  have hθ : -θ < (0 : ℝ) := by linarith [D.one_le_depth]
  have hg := metricCLMSection_jointContMDiffOn_of_local_coefficients D.metric
    (Icc (-θ) 0) D.deep_metric_smooth
  have hg' := metricCLMSection_jointContMDiffOn_of_chartGram_on
    (fun t => Diffeomorph.pullbackMetricCross (D.metric t) Φ) (Icc (-θ) 0)
    (chartGramMatrix_pullback_joint_contMDiffOn D.metric (Icc (-θ) 0) hg
      (fun _ => Φ) (Φ.contMDiff.comp contMDiff_snd))
  obtain ⟨U, hU, hp, hUb, A, hA, heq⟩ :=
    Geometry.Metric.exists_local_metric_coefficient_extension
      (fun t => Diffeomorph.pullbackMetricCross (D.metric t) Φ) hθ hg' p
  exact ⟨U, hU, hp, hUb, univ, isOpen_univ, mem_univ t, A, hA,
    fun u hu x hx v w => heq u hu.2 x hx v w⟩

private theorem deep_pullback_metric_on_slab_C12X (D : IncomingBackwardNeckDeep_C12X H i N r θ)
    (Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ neckBuffer δ)
    (j : Fin H.eventCount) (hj : j.val ≤ i.val)
    (ha : H.time i.succ - θ * r ^ 2 < H.time j.succ) (v : ℝ) (hv : v ∈ Ico (-θ) 0)
    (htlo : H.time j.castSucc ≤ H.time i.succ + r ^ 2 * v)
    (hthi : H.time i.succ + r ^ 2 * v < H.time j.succ)
    (x : neckBuffer δ) (V W : TangentSpace NeckCylinderModel x) :
    (Diffeomorph.pullbackMetricCross (D.metric v) Φ).inner x V W = (r ^ 2)⁻¹ *
      ((H.event j).incoming.flow.base.metric (H.time i.succ + r ^ 2 * v)).inner
        (D.deepChart j hj ha (Φ x))
        (mfderiv NeckCylinderModel ThreeModel ((D.deepChart j hj ha) ∘ Φ) x V)
        (mfderiv NeckCylinderModel ThreeModel ((D.deepChart j hj ha) ∘ Φ) x W) := by
  rw [Diffeomorph.pullbackMetricCross_inner,
    D.deep_metric_on_slab j hj ha v hv htlo hthi]
  have hmd := (D.deepChart_smooth j hj ha).contMDiff.mdifferentiableAt
    (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x := Φ x)
  have hmd' := Φ.contMDiff.mdifferentiableAt
    (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x := x)
  have hV := mfderiv_comp_apply x hmd hmd' V
  have hW := mfderiv_comp_apply x hmd hmd' W
  rw [hV, hW]

/-- Deep analogue of `IncomingBackwardNeck.pullback`. -/
def IncomingBackwardNeckDeep_C12X.pullback_C12X (D : IncomingBackwardNeckDeep_C12X H i N r θ)
    (Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ neckBuffer δ)
    (hchart : ∀ x, N'.chart x = N.chart (Φ x))
    (hmetric : N'.normalizedMetric = Diffeomorph.pullbackMetricCross N.normalizedMetric Φ)
    (hmodel : ∀ t : Iio (1 : ℝ), Diffeomorph.pullbackMetricCross
      ((shrinkingCylinderMetric t).restrictOpen (neckBuffer δ)) Φ =
      (shrinkingCylinderMetric t).restrictOpen (neckBuffer δ))
    (htest : MapsTo Φ (neckClosedTest δ) (neckClosedTest δ)) :
    IncomingBackwardNeckDeep_C12X H i N' r θ := by
  let : SigmaCompactSpace (neckBuffer δ) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer δ).isOpen)
  have hθ : -θ < (0 : ℝ) := by linarith [D.one_le_depth]
  let A : ℝ → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2 :=
    fun t => metricTensorField (D.metric t) -
    metricTensorField ((shrinkingCylinderMetric
      ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ))
  have hA (t : ℝ) (x : neckBuffer δ) :
      pullbackTensor02FieldCross Φ (A t) x =
      metricTensorField (Diffeomorph.pullbackMetricCross (D.metric t) Φ) x -
        metricTensorField ((shrinkingCylinderMetric
          ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
            (neckBuffer δ)) x := by
    have hbg := congrArg (fun g : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ) =>
      metricTensorField g x) (hmodel ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩)
    rw [← hbg]
    ext v
    rw [pullbackTensor02FieldCross_apply]
    rfl
  refine {
    toIncomingBackwardNeck := D.toIncomingBackwardNeck.pullback Φ hchart hmetric hmodel htest
    one_le_depth := D.one_le_depth
    deep_left_nonneg := D.deep_left_nonneg
    deepChart := fun j hj ha => ⟨(D.deepChart j hj ha) ∘ Φ,
      (D.deepChart j hj ha).continuous.comp Φ.continuous⟩
    deepChart_smooth := ?_
    deepChart_eq := ?_
    deep_crossing := fun j hj ha hn x => D.deep_crossing j hj ha hn (Φ x)
    deep_metric_on_slab := deep_pullback_metric_on_slab_C12X D Φ
    deepJet := fun b v => pullbackTensor02FieldCross Φ (D.deepJet b v)
    deepJet_eq := ?_
    deep_closeness := ?_
    deep_metric_smooth := deep_pullback_metric_smooth_C12X D Φ }
  · intro j hj ha
    change IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ ((D.deepChart j hj ha) ∘ Φ)
    exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp
      (D.deepChart j hj ha) (D.deepChart_smooth j hj ha) Φ
  · intro j hj ha ha'
    ext x
    change D.deepChart j hj ha' (Φ x) = D.stageChart j hj ha (Φ x)
    rw [D.deepChart_eq j hj ha ha']
  · intro b v x
    have hh := pullbackTensor02FieldCross_eq_iteratedDerivWithin Φ A
      (D.deepJet b v) b (uniqueDiffOn_Icc hθ) v.2 (D.deepJet_eq b v) x
    simp only [hA] at hh
    exact hh
  · obtain ⟨η, hη, hbound⟩ := D.deep_closeness
    refine ⟨η, hη, ?_⟩
    intro a b hab v x hx
    have hh := hbound a b hab v (Φ x) (htest hx)
    simp only [cylinderTensorCovDeriv_eq_tensor02CovDeriv] at hh ⊢
    change tensor02CovDerivNormWith a (pullbackTensor02FieldCross Φ (D.deepJet b v))
      ((shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ))
      ((shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen
        (neckBuffer δ)) x ≤ η
    rw [← hmodel ⟨v.1, v.2.2.trans_lt zero_lt_one⟩,
      tensor02CovDerivNormWith_pullbackTensor02FieldCross]
    exact hh

private local instance deepTransportFinrank_C12X :
    Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

open DifferentialGeometry.Geometry.Neck

/-- Deep analogue of `IncomingBackwardNeck.rotatedDatum`. -/
def IncomingBackwardNeckDeep_C12X.rotatedDatum_C12X
    (D : IncomingBackwardNeckDeep_C12X H i N r θ)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (he : Geometry.sphereDiffeo (n := 2) e spherePoint = N.sphereMark) (side : Bool) :
    IncomingBackwardNeckDeep_C12X H i (N.rotatedDatum e he side).toNormalizedNeck r θ := by
  apply D.pullback_C12X (bufferedCylinderRotation δ e) (fun _ => rfl)
  · have hh := N.rotatedDatum_normalizedMetric e he side
    dsimp only at hh
    exact hh.trans (Diffeomorph.pullbackMetricCross_eq_pullbackMetric
      N.normalizedMetric (show neckBuffer δ ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ neckBuffer δ
        from bufferedCylinderRotation δ e)).symm
  · exact pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderRotation δ e
  · intro x hx
    rw [← image_bufferedCylinderRotation_neckClosedTest δ e]
    exact mem_image_of_mem _ hx

/-- Deep analogue of `IncomingBackwardNeck.oriented`. -/
def IncomingBackwardNeckDeep_C12X.oriented_C12X
    {x : (H.event i).incoming.terminalRegularOpen}
    (d : normalizedDatum (I := ThreeModel) (H.event i).terminal.metric x δ k)
    (D : IncomingBackwardNeckDeep_C12X H i d.toNormalizedNeck r θ) :
    IncomingBackwardNeckDeep_C12X H i
      (normalizedDatum.toNormalizedNeck (normalizedDatum.oriented (I := ThreeModel) d)) r θ := by
  apply D.pullback_C12X (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq)
    (fun _ => rfl)
  · exact d.oriented_normalizedMetric.trans
      (Diffeomorph.pullbackMetricCross_eq_pullbackMetric d.normalizedMetric
        (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq)).symm
  · exact pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderOrientation
      δ d.retainedSign d.retainedSign_sq
  · intro x hx
    rw [← image_bufferedCylinderOrientation_neckClosedTest δ d.retainedSign d.retainedSign_sq]
    exact mem_image_of_mem _ hx

end Pullback

section Restriction

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {δ δ' : ℝ} {k : ℕ}
    {N : NormalizedNeck (H.event i).terminal.metric δ k} {r θ : ℝ}

private theorem deep_restricted_jet_eq_C12X (D : IncomingBackwardNeckDeep_C12X H i N r θ)
    (h : δ ≤ δ') (b : ℕ) (v : Icc (-θ) 0) (x : neckBuffer δ') :
    restrictOpenTensor02FieldOfSubset (neckBuffer_le_of_le N.delta_pos h)
      (D.deepJet b v) x =
      iteratedDerivWithin b (fun t =>
        metricTensorField ((D.metric t).restrictOpenOfSubset
          (neckBuffer_le_of_le N.delta_pos h)) x -
        metricTensorField ((shrinkingCylinderMetric
          ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
            (neckBuffer δ')) x) (Icc (-θ) 0) v.1 := by
  have hθ : -θ < (0 : ℝ) := by linarith [D.one_le_depth]
  let hle := neckBuffer_le_of_le N.delta_pos h
  let A := fun t => metricTensorField (D.metric t) -
    metricTensorField ((shrinkingCylinderMetric
      ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ))
  have hA : (fun t => metricTensorField ((D.metric t).restrictOpenOfSubset hle) x -
      metricTensorField ((shrinkingCylinderMetric
        ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ')) x) =
      fun t => restrictOpenTensor02FieldOfSubset hle (A t) x := by
    funext t
    rw [restrictOpenTensor02FieldOfSubset_eq]
    rfl
  rw [restrictOpenTensor02FieldOfSubset_eq, hA,
    iteratedDerivWithin_restrictOpenTensor02FieldOfSubset hle A b x
      (uniqueDiffOn_Icc hθ) v.2]
  exact D.deepJet_eq b v (TopologicalSpace.Opens.inclusion hle x)

private theorem deep_restricted_closeness_C12X (D : IncomingBackwardNeckDeep_C12X H i N r θ)
    (h : δ ≤ δ') :
    ∃ η : ℝ, η < δ' ∧ ∀ a b : ℕ, a + 2 * b ≤ k →
      ∀ v : Icc (-θ) 0, ∀ x ∈ neckClosedTest δ',
      let g := (shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen
        (neckBuffer δ')
      Real.sqrt (normSq0S g x (a + 2)
        (cylinderTensorCovDeriv g
          (restrictOpenTensor02FieldOfSubset (neckBuffer_le_of_le N.delta_pos h)
            (D.deepJet b v)) a x)) ≤ η := by
  obtain ⟨η, hη, hbound⟩ := D.deep_closeness
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
    (D.deepJet b v))
      ((shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ'))
      ((shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen
        (neckBuffer δ')) x ≤ η
  rw [← SmoothRiemannianMetric.restrictOpen_flat _ hle,
    tensor02CovDerivNormWith_restrictOpenOfSubset hle]
  exact hh

/-- Deep analogue of `IncomingBackwardNeck.monoDelta`. -/
def IncomingBackwardNeckDeep_C12X.monoDelta_C12X (D : IncomingBackwardNeckDeep_C12X H i N r θ)
    (h : δ ≤ δ') (h' : δ' < 1) : IncomingBackwardNeckDeep_C12X H i (N.monoDelta h h') r θ := by
  have hθ : -θ < (0 : ℝ) := by linarith [D.one_le_depth]
  let hle := neckBuffer_le_of_le N.delta_pos h
  let incl := TopologicalSpace.Opens.inclusion hle
  have hincl : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ incl :=
    isSmoothEmbedding_opens_inclusion hle
  refine {
    toIncomingBackwardNeck := D.toIncomingBackwardNeck.monoDelta h h'
    one_le_depth := D.one_le_depth
    deep_left_nonneg := D.deep_left_nonneg
    deepChart := fun j hj ha => ⟨(D.deepChart j hj ha) ∘ incl,
      (D.deepChart j hj ha).continuous.comp hincl.contMDiff.continuous⟩
    deepChart_smooth := by
      intro j hj ha
      change IsSmoothEmbedding NeckCylinderModel ThreeModel ∞
        ((D.deepChart j hj ha) ∘ incl)
      exact IsSmoothEmbedding.comp (D.deepChart_smooth j hj ha) hincl (by decide)
    deepChart_eq := ?_
    deep_crossing := fun j hj ha hn x => D.deep_crossing j hj ha hn (incl x)
    deep_metric_on_slab := ?_
    deepJet := fun b v => restrictOpenTensor02FieldOfSubset hle (D.deepJet b v)
    deepJet_eq := deep_restricted_jet_eq_C12X D h
    deep_closeness := deep_restricted_closeness_C12X D h
    deep_metric_smooth := ?_ }
  · intro j hj ha ha'
    ext x
    change D.deepChart j hj ha' (incl x) = D.stageChart j hj ha (incl x)
    rw [D.deepChart_eq j hj ha ha']
  · intro j hj ha v hv htlo hthi x V W
    rw [IncomingBackwardNeck.monoDelta_metric, SmoothRiemannianMetric.restrictSubset_inner,
      D.deep_metric_on_slab j hj ha v hv htlo hthi (incl x) V W]
    have hmd := (D.deepChart_smooth j hj ha).contMDiff.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x := incl x)
    have hmd' := hincl.contMDiff.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x := x)
    change _ = _ * ((H.event j).incoming.flow.base.metric _).inner _
      (mfderiv NeckCylinderModel ThreeModel ((D.deepChart j hj ha) ∘ incl) x V)
      (mfderiv NeckCylinderModel ThreeModel ((D.deepChart j hj ha) ∘ incl) x W)
    rw [mfderiv_comp_apply x hmd hmd' V, mfderiv_comp_apply x hmd hmd' W]
    rw [show mfderiv NeckCylinderModel NeckCylinderModel incl x =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) from
        mfderiv_opens_incl (I := NeckCylinderModel) hle x]
    rfl
  · intro p t _
    have hg := metricCLMSection_jointContMDiffOn_of_local_coefficients D.metric
      (Icc (-θ) 0) D.deep_metric_smooth
    have hg' := metricCLMSection_jointContMDiffOn_restrictOpenOfSubset hle D.metric
      (Icc (-θ) 0) hg
    obtain ⟨U, hU, hp, hUb, A, hA, heq⟩ :=
      Geometry.Metric.exists_local_metric_coefficient_extension
        (fun t => (D.metric t).restrictOpenOfSubset hle) hθ hg' p
    exact ⟨U, hU, hp, hUb, univ, isOpen_univ, mem_univ t, A, hA,
      fun u hu x hx v w => heq u hu.2 x hx v w⟩

variable {j : ℕ}

/-- Deep analogue of `IncomingBackwardNeck.lowerOrder`. -/
def IncomingBackwardNeckDeep_C12X.lowerOrder_C12X (D : IncomingBackwardNeckDeep_C12X H i N r θ)
    (hjk : j ≤ k) : IncomingBackwardNeckDeep_C12X H i (N.lowerOrder hjk) r θ where
  toIncomingBackwardNeck := D.toIncomingBackwardNeck.lowerOrder hjk
  one_le_depth := D.one_le_depth
  deep_left_nonneg := D.deep_left_nonneg
  deepChart := D.deepChart
  deepChart_smooth := D.deepChart_smooth
  deepChart_eq := D.deepChart_eq
  deep_crossing := D.deep_crossing
  deep_metric_on_slab := D.deep_metric_on_slab
  deepJet := D.deepJet
  deepJet_eq := D.deepJet_eq
  deep_closeness := by
    obtain ⟨η, hη, hbound⟩ := D.deep_closeness
    exact ⟨η, hη, fun a b hab => hbound a b (hab.trans hjk)⟩
  deep_metric_smooth := D.deep_metric_smooth

end Restriction

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
