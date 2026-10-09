import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedRegularity
import DifferentialGeometry.Geometry.Metric.Family.CoefficientExtension
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Embedding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingAction

noncomputable section

open Set Manifold Bundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem event_heq_transport {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : MetricCutCapEvent P Q a s) : HEq (E.transport hP hQ ha hs) E := by
  cases hP
  cases hQ
  cases ha
  cases hs
  rfl

private theorem appendEvent_event_castSucc_heq
    (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (j : Fin H.eventCount) :
    HEq ((H.appendEvent E.incoming.lt E hinit).event j.castSucc) (H.event j) := by
  rw [H.appendEvent_event_apply, H.extendEventFamily_castSucc]
  exact event_heq_transport _ _ _ _ _

private theorem appendEvent_event_last_heq
    (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    HEq ((H.appendEvent E.incoming.lt E hinit).event (Fin.last H.eventCount)) E := by
  rw [H.appendEvent_event_last]
  exact event_heq_transport _ _ _ _ _

private theorem exists_neck_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (hE : HEq E F) {δ : ℝ} {k : ℕ} (N : NormalizedNeck E.terminal.metric δ k) :
    ∃ N' : NormalizedNeck F.terminal.metric δ k, HEq N' N := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact ⟨N, HEq.rfl⟩

private def castStageMap {P Q : OrientedThreeStage.{u}} (h : P = Q)
    {X : Type*} [TopologicalSpace X] (f : C(X, P.Carrier)) : C(X, Q.Carrier) := h ▸ f

private theorem castStageMap_smooth {P Q : OrientedThreeStage.{u}} (h : P = Q)
    {δ : ℝ} (f : C(neckBuffer δ, P.Carrier))
    (hf : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ f) :
    IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ (castStageMap h f) := by
  cases h
  exact hf

private theorem neck_normalizedMetric_eq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (hE : HEq E F) {δ : ℝ} {k : ℕ}
    {N : NormalizedNeck E.terminal.metric δ k} {N' : NormalizedNeck F.terminal.metric δ k}
    (hN : HEq N N') : N.normalizedMetric = N'.normalizedMetric := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  cases eq_of_heq hN
  rfl

private theorem neck_chart_transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (hE : HEq E F) {δ : ℝ} {k : ℕ}
    {N : NormalizedNeck E.terminal.metric δ k} {N' : NormalizedNeck F.terminal.metric δ k}
    (hN : HEq N N') (f : C(neckBuffer δ, P.Carrier))
    (hf : ∀ x, f x = (N.chart x).1) :
    ∀ x, castStageMap hP f x = (N'.chart x).1 := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  cases eq_of_heq hN
  exact hf

private theorem crossing_transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (hE : HEq E F) {δ : ℝ}
    (f : C(neckBuffer δ, P.Carrier)) (g : C(neckBuffer δ, Q.Carrier))
    (hf : ∀ x, E.RegularCrossing (f x) (g x)) :
    ∀ x, F.RegularCrossing (castStageMap hP f x) (castStageMap hQ g x) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact hf

private theorem metric_transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (hE : HEq E F) {δ : ℝ}
    (f : C(neckBuffer δ, P.Carrier)) (t : ℝ) (x : neckBuffer δ)
    (V W : TangentSpace NeckCylinderModel x) :
    (F.incoming.flow.base.metric t).inner (castStageMap hP f x)
      (mfderiv NeckCylinderModel ThreeModel (castStageMap hP f) x V)
      (mfderiv NeckCylinderModel ThreeModel (castStageMap hP f) x W) =
    (E.incoming.flow.base.metric t).inner (f x)
      (mfderiv NeckCylinderModel ThreeModel f x V)
      (mfderiv NeckCylinderModel ThreeModel f x W) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  rfl


namespace ObservedHistory

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace F] {I : ModelWithCorners ℝ E F}
  [TopologicalSpace M] [ChartedSpace F M] [IsManifold I ∞ M] [T2Space M]
  (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (J : (H.stage last).IncomingSlab (H.time last) s) (L : J.TerminalLimitMetric)
  (K : Set J.terminalRegularOpen)
  (G : ℝ → SmoothRiemannianMetric ThreeModel
    (H.backwardSurvivorIncomingFootprint first last hle J K))
  (Q : ℝ) (hQ : 0 < Q)
  (Phi : M → H.backwardSurvivorIncomingFootprint first last hle J K)
  (hPhi : IsLocalDiffeomorph I ThreeModel ∞ Phi)

private theorem prospective_slab_metric_inner
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
    {t : ℝ} (ht : t < H.time j.succ)
    (hGt : G t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
      (H.backwardSurvivorIncomingDomain first last hle J)).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle J K))
    (x : M) (v w : TangentSpace I x) :
    (localPullMetric (scaleMetric Q hQ (G t)) Phi hPhi).inner x v w =
      Q * ((H.event j).incoming.flow.base.metric t).inner
        (H.backwardSurvivorMap first last hle j.castSucc hf
          (j.castSucc_lt_succ.le.trans hl) (Phi x).val.val)
        (mfderiv I ThreeModel (fun y => H.backwardSurvivorMap first last hle
          j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Phi y).val.val) x v)
        (mfderiv I ThreeModel (fun y => H.backwardSurvivorMap first last hle
          j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Phi y).val.val) x w) := by
  erw [localPullMetric_inner, scaleMetric_inner, hGt,
    SmoothRiemannianMetric.restrictOpen_inner, SmoothRiemannianMetric.restrictOpen_inner,
    H.backwardSurvivorSlabMetric_before first last hle j hf hl ht,
    localPullMetric_inner]
  let psi : M → H.backwardSurvivorDomain first last hle := fun y => (Phi y).val.val
  have hpsi : MDifferentiable I ThreeModel psi :=
    ((contMDiff_subtype_val.comp contMDiff_subtype_val).comp hPhi.contMDiff).mdifferentiable
      (by decide)
  have hdp : mfderiv I ThreeModel psi x = mfderiv I ThreeModel Phi x := by
    exact (mfderiv_subtypeVal_comp (I := I) (J := ThreeModel)
      (fun y => (Phi y).val) x).trans
        (mfderiv_subtypeVal_comp (I := I) (J := ThreeModel) Phi x)
  have hd := mfderiv_comp x
    ((H.backwardSurvivorMap_isLocalDiffeomorph first last hle j.castSucc hf
      (j.castSucc_lt_succ.le.trans hl)).mdifferentiable (by decide) (psi x))
    (hpsi x)
  rw [hdp] at hd
  change mfderiv I ThreeModel (fun y => H.backwardSurvivorMap first last hle
    j.castSucc hf (j.castSucc_lt_succ.le.trans hl) (Phi y).val.val) x = _ at hd
  rw [hd]
  rfl

private theorem prospective_final_metric_inner
    {t : ℝ} (ht : t < s)
    (hGt : G t = (H.backwardSurvivorIncomingMetric first last hle J L t).restrictOpen
      (H.backwardSurvivorIncomingFootprint first last hle J K))
    (x : M) (v w : TangentSpace I x) :
    (localPullMetric (scaleMetric Q hQ (G t)) Phi hPhi).inner x v w =
      Q * (J.flow.base.metric t).inner
        (H.backwardSurvivorMap first last hle last hle le_rfl (Phi x).val.val)
        (mfderiv I ThreeModel (fun y => H.backwardSurvivorMap first last hle
          last hle le_rfl (Phi y).val.val) x v)
        (mfderiv I ThreeModel (fun y => H.backwardSurvivorMap first last hle
          last hle le_rfl (Phi y).val.val) x w) := by
  erw [localPullMetric_inner, scaleMetric_inner, hGt,
    H.backwardSurvivorIncomingMetric_before first last hle J L ht]
  erw [SmoothRiemannianMetric.restrictOpen_inner,
    SmoothRiemannianMetric.restrictOpen_inner, SmoothRiemannianMetric.restrictOpen_inner]
  have he : H.backwardSurvivorMap first last hle last hle le_rfl =
      Subtype.val := by
    funext z
    exact H.backwardSurvivorMap_last first last hle z
  rw [he]
  have hd : mfderiv I ThreeModel (fun y => (Phi y).val.val.val) x =
      mfderiv I ThreeModel Phi x := by
    exact (mfderiv_subtypeVal_comp (I := I) (J := ThreeModel)
      (fun y => (Phi y).val.val) x).trans
      ((mfderiv_subtypeVal_comp (I := I) (J := ThreeModel)
        (fun y => (Phi y).val) x).trans
          (mfderiv_subtypeVal_comp (I := I) (J := ThreeModel) Phi x))
  rw [hd]
  rfl


end ObservedHistory


private theorem first_le_stage_of_time_lt
    {H : ObservedHistory.{u}} {first : Fin (H.eventCount + 1)} {a : ℝ}
    (hstart : H.time first ≤ a) (j : Fin H.eventCount)
    (ha : a < H.time j.succ) : first ≤ j.castSucc := by
  by_contra hn
  have hj : j.succ ≤ first := by
    apply Fin.le_iff_val_le_val.mpr
    have hh := Fin.lt_def.mp (lt_of_not_ge hn)
    change j.val + 1 ≤ first.val
    exact hh
  exact (not_lt_of_ge ((H.time_strictMono.monotone hj).trans hstart)) ha

variable {δ θ : ℝ} (hθ : 1 < θ)

local instance : SigmaCompactSpace (neckBuffer δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer δ).isOpen)

private theorem solution_metric_smooth_on_neckBuffer
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-θ) 0 (by linarith))) (hS : IsSolutionOn S) :
    ∀ p : neckBuffer δ, ∀ t ∈ Icc (-1 : ℝ) 0,
      ∃ U : Set (neckBuffer δ), IsOpen U ∧ p ∈ U ∧
        U ⊆ (trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
          (TangentSpace NeckCylinderModel) p).baseSet ∧
      ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
      ∃ A : ℝ × neckBuffer δ → (EuclideanSpace ℝ (Fin 2) × ℝ) →
          (EuclideanSpace ℝ (Fin 2) × ℝ) → ℝ,
        (∀ v w, ContMDiffOn (𝓘(ℝ, ℝ).prod NeckCylinderModel) 𝓘(ℝ, ℝ) ∞
          (fun z => A z v w) (V ×ˢ U)) ∧
        ∀ s ∈ V ∩ Icc (-1 : ℝ) 0, ∀ x ∈ U, ∀ v w,
          A (s, x) v w = (S.base.metric s).inner x
            ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
              (TangentSpace NeckCylinderModel) p).symmL ℝ x v)
            ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
              (TangentSpace NeckCylinderModel) p).symmL ℝ x w) := by
  intro p t ht
  have hg := solution_metricCLMSection_contMDiffOn_closed S hS
    (show -θ < (-1 : ℝ) by linarith) (show (-1 : ℝ) < 0 by norm_num)
    (show Icc (-θ) 0 ⊆ (RealTimeInterval.closed (-θ) 0 (by linarith)).carrier from Subset.rfl)
    (show Ioo (-θ) 0 ⊆ (RealTimeInterval.closed (-θ) 0 (by linarith)).regular from Subset.rfl)
  obtain ⟨U, hU, hp, hUb, A, hA, hEq⟩ :=
    Geometry.Metric.exists_local_metric_coefficient_extension S.base.metric
      (by norm_num : (-1 : ℝ) < 0) hg p
  exact ⟨U, hU, hp, hUb, univ, isOpen_univ, mem_univ t, A, hA,
    fun s hs x hx v w => hEq s hs.2 x hx v w⟩


theorem NormalizedNeck.exists_incomingBackwardNeck_appendEvent
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
    (hle : first ≤ Fin.last H.eventCount) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck E.terminal.metric δ k)
    (K : Set E.incoming.terminalRegularOpen)
    (Φ : neckBuffer δ → H.backwardSurvivorIncomingFootprint first
      (Fin.last H.eventCount) hle E.incoming K)
    (hΦ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Φ)
    (hmap : H.backwardSurvivorIncomingFootprintMap first
      (Fin.last H.eventCount) hle E.incoming K ∘ Φ = N.chart)
    (G : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K))
    {θ : ℝ} (hθ : 1 < θ)
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-θ) 0 (by linarith))) (hS : IsSolutionOn S)
    (hterminal : S.base.metric 0 = N.normalizedMetric)
    (hmetric : ∀ t ∈ Ico (-1 : ℝ) 0, S.base.metric t = localPullMetric
      (scaleMetric N.scale N.scale_pos (G (s + t / N.scale))) Φ hΦ)
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc)
      (hl : j.succ ≤ Fin.last H.eventCount),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G t = ((H.backwardSurvivorSlabMetric first (Fin.last H.eventCount) hle
          j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first (Fin.last H.eventCount) hle
            E.incoming)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K))
    (hlast : ∀ t ∈ Icc (H.time (Fin.last H.eventCount)) s,
      G t = (H.backwardSurvivorIncomingMetric first (Fin.last H.eventCount) hle
        E.incoming E.terminal t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K))
    (hstart : H.time first ≤ s - N.scale⁻¹)
    (Z : (b : ℕ) → (v : Icc (-1 : ℝ) 0) →
      Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hZ : ∀ b v x, Z b v x = iteratedDerivWithin b
      (fun t => metricTensorField (S.base.metric t) x -
        metricTensorField ((shrinkingCylinderMetric
          ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)) x)
      (Icc (-1 : ℝ) 0) v.1)
    (hclose : ∃ η : ℝ, η < δ ∧ ∀ a b : ℕ, a + 2*b ≤ k →
      ∀ v : Icc (-1 : ℝ) 0, ∀ x ∈ neckClosedTest δ,
        let g := (shrinkingCylinderMetric
          ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
        Real.sqrt (normSq0S g x (a + 2) (cylinderTensorCovDeriv g (Z b v) a x)) ≤ η) :
    ∃ N' : NormalizedNeck
      ((H.appendEvent E.incoming.lt E hinit).event (Fin.last H.eventCount)).terminal.metric δ k,
      HEq N' N ∧ ∃ B : IncomingBackwardNeck (H.appendEvent E.incoming.lt E hinit)
        (Fin.last H.eventCount) N' (Real.sqrt N.scale⁻¹),
        B.metric = S.base.metric ∧ B.timeDifferenceJet = Z := by
  let J := H.appendEvent E.incoming.lt E hinit
  let r := Real.sqrt N.scale⁻¹
  have hrsq : r ^ 2 = N.scale⁻¹ := Real.sq_sqrt (inv_nonneg.mpr N.scale_pos.le)
  have htime : J.time (Fin.last H.eventCount).succ = s :=
    H.appendEvent_time_last E.incoming.lt E hinit
  have hstage (j : Fin (H.eventCount + 1)) : J.stage j.castSucc = H.stage j :=
    H.appendEvent_stage_castSucc E.incoming.lt E hinit j
  have htimeOld (j : Fin (H.eventCount + 1)) : J.time j.castSucc = H.time j :=
    H.appendEvent_time_castSucc E.incoming.lt E hinit j
  have htimeCastSucc (j : Fin H.eventCount) : J.time j.castSucc.succ = H.time j.succ :=
    htimeOld j.succ
  have hevent := appendEvent_event_last_heq H E hinit
  obtain ⟨N', hneck⟩ := exists_neck_heq (hstage (Fin.last H.eventCount)).symm
    (H.extendStage_last Q E.outputMetric).symm
    (htimeOld (Fin.last H.eventCount)).symm htime.symm hevent.symm N
  refine ⟨N', hneck, ?_⟩
  have hf (j : Fin (H.eventCount + 1))
      (ha : J.time (Fin.last H.eventCount).succ - r^2 < J.time j.succ) :
      first ≤ j := by
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · apply first_le_stage_of_time_lt hstart j
      simpa only [htime, hrsq, htimeCastSucc] using ha
    · exact hle
  let Ψ : neckBuffer δ → H.backwardSurvivorDomain first (Fin.last H.eventCount) hle :=
    fun x => (Φ x).val.val
  have hPhiEmb : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Φ := by
    apply Perelman.KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective hΦ
    intro x y hxy
    apply N.chart_smooth.isEmbedding.injective
    rw [← hmap]
    exact congrArg (H.backwardSurvivorIncomingFootprintMap first
      (Fin.last H.eventCount) hle E.incoming K) hxy
  have hΨ : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Ψ := by
    apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen
      NeckCylinderModel ThreeModel
      (H.backwardSurvivorIncomingDomain first (Fin.last H.eventCount) hle E.incoming)
    exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen
      NeckCylinderModel ThreeModel
      (H.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K) Φ hPhiEmb
  let baseChart (j : Fin (H.eventCount + 1)) (hj : first ≤ j) :
      C(neckBuffer δ, (H.stage j).Carrier) :=
    ⟨H.backwardSurvivorMap first (Fin.last H.eventCount) hle j hj (Fin.le_last j) ∘ Ψ,
      ((H.backwardSurvivorMap_isSmoothEmbedding first (Fin.last H.eventCount) hle j hj
        (Fin.le_last j)).contMDiff.comp hΨ.contMDiff).continuous⟩
  let chart (j : Fin J.eventCount) (_hj : j.val ≤ (Fin.last H.eventCount).val)
      (ha : J.time (Fin.last H.eventCount).succ - r^2 < J.time j.succ) :
      C(neckBuffer δ, (J.stage j.castSucc).Carrier) :=
    castStageMap (hstage j).symm (baseChart j (hf j ha))
  change ∃ B : IncomingBackwardNeck J (Fin.last H.eventCount) N' r,
    B.metric = S.base.metric ∧ B.timeDifferenceJet = Z
  refine ⟨{
    radius_pos := Real.sqrt_pos.mpr (inv_pos.mpr N.scale_pos)
    left_nonneg := by erw [htime, hrsq]; exact (H.time_nonneg first).trans hstart
    stageChart := chart
    stageChart_smooth := ?_
    terminal_chart := ?_
    crossing := ?_
    metric := S.base.metric
    terminal_metric := hterminal.trans ?_
    metric_on_slab := ?_
    timeDifferenceJet := Z
    timeDifferenceJet_eq := hZ
    parabolic_closeness := hclose
    metric_smooth := ?_ }, rfl, rfl⟩
  · intro j hj ha
    apply castStageMap_smooth
    exact (H.backwardSurvivorMap_isSmoothEmbedding first (Fin.last H.eventCount) hle j
      (hf j ha) (Fin.le_last j)).comp hΨ (by decide)
  · intro ha
    apply neck_chart_transport (hstage (Fin.last H.eventCount)).symm
      (H.extendStage_last Q E.outputMetric).symm
      (htimeOld (Fin.last H.eventCount)).symm htime.symm hevent.symm hneck.symm
    intro x
    change H.backwardSurvivorMap first (Fin.last H.eventCount) hle
      (Fin.last H.eventCount) _ _ (Ψ x) = _
    rw [H.backwardSurvivorMap_last]
    exact congrArg Subtype.val (congrFun hmap x)
  · intro j hj next ha hn
    let j₀ : Fin H.eventCount := ⟨j.val, hj⟩
    exact crossing_transport (hstage j₀.castSucc).symm (hstage j₀.succ).symm
      (htimeOld j₀.castSucc).symm (htimeOld j₀.succ).symm
      (appendEvent_event_castSucc_heq H E hinit j₀).symm
      (baseChart j₀.castSucc (hf j ha)) (baseChart j₀.succ (hf next hn))
      (fun x => H.backwardSurvivorMap_crossing first (Fin.last H.eventCount) hle j₀
        (hf j ha) (Fin.le_last j₀.succ) (Ψ x))
  · exact neck_normalizedMetric_eq (hstage (Fin.last H.eventCount)).symm
      (H.extendStage_last Q E.outputMetric).symm
      (htimeOld (Fin.last H.eventCount)).symm htime.symm hevent.symm hneck.symm
  · intro j hj ha v hv htlo hthi x V W
    have hnormalized : s + r ^ 2 * v = s + v / N.scale := by
      rw [hrsq, div_eq_mul_inv, mul_comm]
    have hscale : (r ^ 2)⁻¹ = N.scale := by rw [hrsq, inv_inv]
    erw [htime, hnormalized] at htlo hthi ⊢
    rw [hmetric v hv, hscale]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j₀, rfl⟩ | rfl
    · have hlo : H.time j₀.castSucc ≤ s + v / N.scale := by
        erw [htimeOld] at htlo
        exact htlo
      have hhi : s + v / N.scale < H.time j₀.succ := by
        erw [htimeCastSucc] at hthi
        exact hthi
      have hm := H.prospective_slab_metric_inner first (Fin.last H.eventCount) hle
        E.incoming K G N.scale N.scale_pos Φ hΦ j₀ (hf j₀.castSucc ha) (Fin.le_last j₀.succ)
        hhi (hslabs j₀ _ _ _ ⟨hlo, hhi.le⟩) x V W
      have hc := metric_transport (hstage j₀.castSucc).symm (hstage j₀.succ).symm
        (htimeOld j₀.castSucc).symm (htimeOld j₀.succ).symm
        (appendEvent_event_castSucc_heq H E hinit j₀).symm
        (baseChart j₀.castSucc (hf j₀.castSucc ha)) (s + v / N.scale) x V W
      exact hm.trans (congrArg (N.scale * ·) hc.symm)
    · have hlo : H.time (Fin.last H.eventCount) ≤ s + v / N.scale := by
        erw [htimeOld] at htlo
        exact htlo
      have hhi : s + v / N.scale < s := by
        erw [htime] at hthi
        exact hthi
      have hm := H.prospective_final_metric_inner first (Fin.last H.eventCount) hle
        E.incoming E.terminal K G N.scale N.scale_pos Φ hΦ hhi (hlast _ ⟨hlo, hhi.le⟩) x V W
      have hc := metric_transport (hstage (Fin.last H.eventCount)).symm
        (H.extendStage_last Q E.outputMetric).symm
        (htimeOld (Fin.last H.eventCount)).symm htime.symm hevent.symm
        (baseChart (Fin.last H.eventCount) (hf (Fin.last H.eventCount) ha))
        (s + v / N.scale) x V W
      exact hm.trans (congrArg (N.scale * ·) hc.symm)
  · exact solution_metric_smooth_on_neckBuffer hθ S hS

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
