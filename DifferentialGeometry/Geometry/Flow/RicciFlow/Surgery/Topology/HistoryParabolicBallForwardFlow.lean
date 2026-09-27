import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem exists_closedSlab_stageMetric_of_lt_stageEndTime
    (H : ObservedHistory.{u}) (k : Fin (H.eventCount + 1)) (s : ℝ)
    (hks : H.time k < s) (hs : s < H.stageEndTime k) :
    ∃ C : (H.stage k).ClosedSlab (H.time k) s,
      (∀ τ, C.flow.base.metric τ = H.stageMetric k τ) ∧
        C.flow.base.metric (H.time k) = H.initialMetric k := by
  obtain ⟨s', rfl⟩ : ∃ s' : Icc (0 : ℝ) H.horizon, s'.1 = s :=
    ⟨⟨s, (H.time_nonneg k).trans hks.le, hs.le.trans (H.stageEndTime_le_horizon k)⟩, rfl⟩
  have hmem : s'.1 ∈ H.stageDomain k := by
    cases k using Fin.lastCases with
    | last =>
      simp only [stageDomain, Fin.lastCases_last, mem_Icc]
      exact ⟨hks.le, s'.2.2⟩
    | cast i =>
      simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico]
      exact ⟨hks.le, by simpa only [H.stageEndTime_castSucc] using hs⟩
  have hk : H.activeStage s' = k := (H.mem_stageDomain_iff s' k).mp hmem
  subst hk
  exact ⟨H.closedPrefixAt s' hks, H.closedPrefixAt_metric s' hks,
    H.closedPrefixAt_initial s' hks⟩

open _root_.Manifold TopologicalSpace in
private theorem exists_common_flow_past_time_of_parabolicallyRmControlledBall_aux
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) (r : ℝ)
    (hball : H.isParabolicallyRmControlledBall t p r)
    (ht : (t : ℝ) < H.stageEndTime (H.activeStage t)) :
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), a.val = t.val - r ^ 2 ∧
      ∃ (t₁ : ℝ) (htt₁ : t.val < t₁),
      ∃ U : Opens (H.stageAt t).Carrier,
        (U : Set (H.stageAt t).Carrier) = riemannianBallOf (H.stageMetric (H.activeStage t) t) p r ∧
        ∃ f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U → (H.stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ H.activeStage t), ∀ x : U,
              (H.event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : U, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∃ S : SolutionOn (I := ThreeModel) (M := U)
                (RealTimeInterval.closed a.val t₁ ((show (a : ℝ) ≤ t from hat).trans htt₁.le)),
              IsSolutionOn S ∧
              (∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
                ∀ v ∈ Icc a.val t₁, v ∈ H.stageDomain j.val →
                  S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) ∧
              (∀ v ∈ Icc a.val t.val, ∀ x : U,
                r ^ 4 * normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ 1) := by
  classical
  obtain ⟨hr, a, hat, ha, htraces⟩ := hball
  let first := H.activeStage a
  let last := H.activeStage t
  have hle : first ≤ last := H.activeStage_mono hat
  let t₁ : ℝ := (t.val + H.stageEndTime last) / 2
  let t₂ : ℝ := (t₁ + H.stageEndTime last) / 2
  have htt₁ : t.val < t₁ := by simp only [t₁]; linarith
  have ht₁₂ : t₁ < t₂ := by simp only [t₂, t₁]; linarith
  have ht₂ : t₂ < H.stageEndTime last := by simp only [t₂, t₁]; linarith
  have hlast₂ : H.time last < t₂ := (H.activeStage_time_le t).trans_lt (htt₁.trans ht₁₂)
  obtain ⟨C, hCmetric, hCinit⟩ :=
    exists_closedSlab_stageMetric_of_lt_stageEndTime H last t₂ hlast₂ ht₂
  let U : Opens (H.stageAt t).Carrier :=
    ⟨riemannianBallOf (H.stageMetric (H.activeStage t) t) p r,
      isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ p) continuous_const⟩
  let G := C.restrictIncoming le_rfl C.lt le_rfl
  let L := C.endpointTerminalLimitMetric (H.stage last)
  have hG (v : ℝ) : G.flow.base.metric v = H.stageMetric last v := hCmetric v
  have hsurv (x : U) : x.val ∈ H.backwardSurvivorDomain first last hle :=
    ⟨(htraces x.val x.property).choose⟩
  let Ψ₀ : U → H.backwardSurvivorDomain first last hle := fun x => ⟨x.val, hsurv x⟩
  have hΨ₀ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ₀ := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict hsurv (isLocalDiffeomorph_subtype_val U x)
  have hregular (x : U) : Ψ₀ x ∈ H.backwardSurvivorIncomingDomain first last hle G := by
    change x.val ∈ G.terminalRegularRegion
    rw [C.terminalRegularRegion_eq_univ]
    exact mem_univ _
  let Ψ : U → H.backwardSurvivorIncomingDomain first last hle G := fun x => ⟨Ψ₀ x, hregular x⟩
  have hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict hregular (hΨ₀ x)
  let f (j : H.StageInterval first last) : U → (H.stage j.val).Carrier :=
    (H.backwardSurvivorMap first last hle j.val j.property.1 j.property.2 ∘ Subtype.val) ∘ Ψ
  have hf (j : H.StageInterval first last) : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j) :=
    isLocalDiffeomorph_comp
      (isLocalDiffeomorph_comp
        (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j.val j.property.1 j.property.2)
        (isLocalDiffeomorph_subtype_val (H.backwardSurvivorIncomingDomain first last hle G))) hΨ
  have hflast (x : U) : f ⟨last, hle, le_rfl⟩ x = x.val :=
    H.backwardSurvivorMap_last first last hle (Ψ₀ x)
  obtain ⟨gflow, hslabs, hlast, _, hsol⟩ :=
    H.exists_backwardSurvivorIncoming_isSolutionOn first last hle G L hCinit
  let S₀ : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingDomain first last hle G)
      (RealTimeInterval.closed (H.time first) t₂
        ((H.time_strictMono.monotone hle).trans G.lt.le)) := { base := { metric := gflow } }
  let : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first last hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
  have hat₁ : a.val ≤ t₁ := (show (a : ℝ) ≤ t from hat).trans htt₁.le
  let S := (S₀.localPullback Ψ hΨ).timeRestrict (RealTimeInterval.closed a.val t₁ hat₁)
  have hS : IsSolutionOn S := isSolutionOn_timeRestrict (hsol.localPullback Ψ hΨ)
    (Icc_subset_Icc (H.activeStage_time_le a) ht₁₂.le)
    (Ioo_subset_Ioo (H.activeStage_time_le a) ht₁₂.le)
  have hmetric (j : H.StageInterval first last) (v : ℝ) (hv : v ∈ Icc a.val t₁)
      (hjv : v ∈ H.stageDomain j.val) :
      S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j) := by
    change localPullMetric (gflow v) Ψ hΨ = _
    rw [H.metric_eq_stage_pullback_of_backwardSurvivorIncoming first last hle t₂ G L gflow
      (fun i hi hl v hv => hslabs i hi hl v (Ico_subset_Icc_self hv))
      (fun v hv => hlast v (Ico_subset_Icc_self hv)) (fun v _ => hG v)
      j.val j.property.1 j.property.2 hjv (hv.2.trans_lt ht₁₂)]
    exact localPullMetric_comp (H.stageMetric j.val v)
      (H.backwardSurvivorMap first last hle j.val j.property.1 j.property.2 ∘ Subtype.val) Ψ
      (isLocalDiffeomorph_comp
        (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j.val j.property.1 j.property.2)
        (isLocalDiffeomorph_subtype_val (H.backwardSurvivorIncomingDomain first last hle G))) hΨ (hf j)
  refine ⟨a, hat, ha, t₁, htt₁, U, rfl, f, hf, ?_, ?_, hflast, S, hS, hmetric, ?_⟩
  · intro j
    exact (H.backwardSurvivorMap_injective first last hle j.val j.property.1 j.property.2).comp
      (fun x y hxy => Subtype.ext (congrArg (fun z : H.backwardSurvivorDomain first last hle => z.val) hxy))
  · intro i hi hl x
    exact H.backwardSurvivorMap_crossing first last hle i hi hl (Ψ₀ x)
  · intro v hv x
    let v' : Icc (0 : ℝ) H.horizon := ⟨v, a.property.1.trans hv.1, hv.2.trans t.property.2⟩
    have hav : a ≤ v' := hv.1
    have hvt : v' ≤ t := hv.2
    let j : H.StageInterval first last :=
      ⟨H.activeStage v', H.activeStage_mono hav, H.activeStage_mono hvt⟩
    change r ^ 4 * normSq0S (S.base.metric v) x 4 (metricRm04At (S.base.metric v) x) ≤ 1
    rw [hmetric j v ⟨hv.1, hv.2.trans htt₁.le⟩ (H.activeStage_mem v'),
      normSq0S_metricRm04At_localPullMetric]
    obtain ⟨A, hA⟩ := htraces x.val x.property
    have hpoint : f j x = A.point j.val j.property.1 j.property.2 :=
      H.backwardSurvivorMap_eq_point first last hle j.val j.property.1 j.property.2 (Ψ₀ x) A
    rw [hpoint]
    exact hA.1 v' hav hvt

open _root_.Manifold TopologicalSpace in
theorem exists_common_flow_past_time_of_parabolicallyRmControlledBall
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) (r : ℝ)
    (hball : H.isParabolicallyRmControlledBall t p r)
    (ht : (t : ℝ) < H.stageEndTime (H.activeStage t)) :
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), a.val = t.val - r ^ 2 ∧
      ∃ (t₁ : ℝ) (htt₁ : t.val < t₁),
      ∃ U : Opens (H.stageAt t).Carrier,
        (U : Set (H.stageAt t).Carrier) = riemannianBallOf (H.stageMetric (H.activeStage t) t) p r ∧
        ∃ f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U → (H.stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ H.activeStage t), ∀ x : U,
              (H.event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : U, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∃ S : SolutionOn (I := ThreeModel) (M := U)
                (RealTimeInterval.closed a.val t₁ ((show (a : ℝ) ≤ t from hat).trans htt₁.le)),
              IsSolutionOn S ∧
              (∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
                ∀ v ∈ Icc a.val t₁, v ∈ H.stageDomain j.val →
                  S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) ∧
              (∀ v ∈ Icc a.val t.val, ∀ x : U,
                r ^ 4 * normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ 1) ∧
              S.base.metric t = (H.stageMetric (H.activeStage t) t).restrictOpen U ∧
              ∃ (pU : U) (K : Set U), pU.val = p ∧
                Subtype.val '' K =
                  riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (r / 2) ∧
                IsCompact K ∧ pU ∈ interior K ∧
                ∀ x ∈ frontier K,
                  ENNReal.ofReal (r / 2) ≤ riemannianEDistOf (S.base.metric t) pU x := by
  classical
  have hr : 0 < r := hball.1
  obtain ⟨a, hat, ha, t₁, htt₁, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm⟩ :=
    exists_common_flow_past_time_of_parabolicallyRmControlledBall_aux H t p r hball ht
  have hterminal : S.base.metric t = (H.stageMetric (H.activeStage t) t).restrictOpen U := by
    have h := hmetric ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ t
      ⟨hat, htt₁.le⟩ (H.activeStage_mem t)
    have heq : f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ = Subtype.val :=
      funext hlast
    simpa only [heq, localPullMetric_subtype_val] using h
  have hpU : p ∈ U := by
    change p ∈ (U : Set (H.stageAt t).Carrier)
    rw [hU]
    change riemannianEDistOf (H.stageMetric (H.activeStage t) t) p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  let pU : U := ⟨p, hpU⟩
  let K : Set U := Subtype.val ⁻¹'
    riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (r / 2)
  have hclosed : IsClosed (riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (r / 2)) :=
    Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _
  have hsubset : riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (r / 2) ⊆
      range (Subtype.val : U → (H.stageAt t).Carrier) := by
    rw [Subtype.range_coe, hU]
    intro x hx
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))
  have hK : IsCompact K :=
    U.isOpenEmbedding'.isEmbedding.isInducing.isCompact_preimage' hclosed.isCompact hsubset
  have himage : Subtype.val '' K =
      riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (r / 2) :=
    image_preimage_eq_of_subset hsubset
  have hpinterior : pU ∈ interior K := by
    have h := Geometry.Metric.mem_interior_riemannianClosedBallOf
      (H.stageMetric (H.activeStage t) t) p (by linarith : 0 < r / 2)
    rw [← himage,
      ← DifferentialGeometry.Topology.Embedding.image_interior_of_isOpenEmbedding
        U.isOpenEmbedding' K] at h
    obtain ⟨x, hx, hxp⟩ := h
    exact (show x = pU from Subtype.ext hxp) ▸ hx
  refine ⟨a, hat, ha, t₁, htt₁, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm,
    hterminal, pU, K, rfl, himage, hK, hpinterior, ?_⟩
  intro x hx
  have hfrontier : x.val ∈ frontier
      (riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (r / 2)) := by
    rw [← himage,
      ← DifferentialGeometry.Topology.Embedding.image_frontier_of_isOpenEmbedding_of_isCompact
        U.isOpenEmbedding' hK]
    exact ⟨x, hx, rfl⟩
  have hdist := Geometry.Metric.riemannianEDistOf_eq_of_mem_frontier_riemannianClosedBallOf
    (H.stageMetric (H.activeStage t) t) p hfrontier
  rw [hterminal, ← hdist]
  exact riemannianEDistOf_le_restrictOpen
    (H.stageMetric (H.activeStage t) t) U pU x

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
