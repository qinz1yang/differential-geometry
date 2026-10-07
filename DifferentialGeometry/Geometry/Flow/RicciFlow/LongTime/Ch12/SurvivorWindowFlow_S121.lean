import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StageGlue_S110
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncoming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Seam

set_option autoImplicit false

/-!
# CH12-S121 / G1: the glued survivor flow on the window `[t, 2t]` (O2 of the S110 handover)

`exists_windowFlow_S121`: for `a < t`, `2t < b ≤ horizon`, `stages`, there is a smooth Ricci flow `G` on the survivor
domain `N = backwardSurvivorDomain first last` with `Icc t (2t) ⊆ D.regular`, joint smoothness on `Icc t (2t) × N`
and `G r = gStage_S110 … r` on `Icc t (2t)`.  Three cases: (i) `2t < time last`: the survivor flow `F` alone;
(ii) `time last ≤ 2t`, `first < last`: `F` glued at `time last` with the closed prefix of the stage `last` (to `c = (2t+b)/2`);
(iii) `first = last`: the closed prefix alone (`time last < t` by `a < t`).
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter TopologicalSpace Bundle
open DifferentialGeometry.Topology.Manifold Manifold GC.LongTime GC.LongTime.Ch12
open scoped Manifold ContDiff ENNReal Topology
universe u

namespace GC.LongTime.Ch12

/-- a closed slab restricted to an open set: joint smoothness and the Ricci-flow equation. -/
theorem closedSlab_restrictOpen_S121 {P : OrientedThreeStage.{u}} {a b : ℝ} (C : P.ClosedSlab a b)
    (W : Opens P.Carrier) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3))
      ((𝓡 3).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)) ∞
      (fun q : ℝ × W => (⟨q.2, ((C.flow.base.metric q.1).restrictOpen W).inner q.2⟩ :
        TotalSpace (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
          (fun x => TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ)))
      (Icc a b ×ˢ (Set.univ : Set W)) ∧
    ∀ t ∈ Ioo a b, ∀ x : W, ∀ v w : TangentSpace (𝓡 3) x,
      HasDerivAt (fun s => ((C.flow.base.metric s).restrictOpen W).inner x v w)
        (-2 * ricciTensor ((C.flow.base.metric t).restrictOpen W) x v w) t := by
  refine ⟨C.smoothUpTo.restrictOpen_jointContMDiffOn W, ?_⟩
  intro t ht x v w
  have hd := (C.equation.equation ⟨t, ht⟩ x.val v w).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  change HasDerivAt (fun s => (C.flow.base.metric s).inner x.val v w)
    (-2 * metricRicciAt (C.flow.base.metric t) x.val (vec2 v w)) t at hd
  erw [metricRicciAt_apply_eq_ricciTensor (C.flow.base.metric t) x.val v w] at hd
  rw [Geometry.Curvature.ricciTensor_restrictOpen]
  simpa only [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply] using hd

/-- the closed prefix of the stage `last = activeStage c'`, as the stage metric restricted to an open set. -/
theorem rightPiece_S121 (K : ObservedHistory.{u}) (last : Fin (K.eventCount + 1))
    (c' : Icc (0 : ℝ) K.horizon) (hlast : K.activeStage c' = last) (hlc : K.time last < c'.1)
    (W : Opens (K.stage last).Carrier) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3))
      ((𝓡 3).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)) ∞
      (fun q : ℝ × W => (⟨q.2, ((K.stageMetric last q.1).restrictOpen W).inner q.2⟩ :
        TotalSpace (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
          (fun x => TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ)))
      (Icc (K.time last) c'.1 ×ˢ (Set.univ : Set W)) ∧
    ∀ t ∈ Ioo (K.time last) c'.1, ∀ x : W, ∀ v w : TangentSpace (𝓡 3) x,
      HasDerivAt (fun s => ((K.stageMetric last s).restrictOpen W).inner x v w)
        (-2 * ricciTensor ((K.stageMetric last t).restrictOpen W) x v w) t := by
  subst hlast
  have hfun : K.stageMetric (K.activeStage c') = (K.closedPrefixAt c' hlc).flow.base.metric :=
    funext fun τ => (K.closedPrefixAt_metric c' hlc τ).symm
  rw [hfun]
  exact closedSlab_restrictOpen_S121 _ W

/-- `K.time first < t` from `a < t` and the stage bookkeeping. -/
theorem time_first_lt_S121 (K : ObservedHistory.{u}) (first last : Fin (K.eventCount + 1))
    (a b t : ℝ) (ht : 0 < t) (hat : a < t) (htb : t < b) (hbh : b ≤ K.horizon)
    (stages : ∀ r : Icc (0 : ℝ) K.horizon, (r : ℝ) ∈ Ico a b →
      first ≤ K.activeStage r ∧ K.activeStage r ≤ last) :
    K.time first < t := by
  have hr0 : (0 : ℝ) ≤ max a 0 := le_max_right _ _
  have hrh : max a 0 ≤ K.horizon :=
    max_le (hat.le.trans (htb.le.trans hbh)) (ht.le.trans (htb.le.trans hbh))
  have hrab : max a 0 ∈ Ico a b := ⟨le_max_left _ _, max_lt (hat.trans htb) (ht.trans htb)⟩
  have h1 := (stages ⟨max a 0, hr0, hrh⟩ hrab).1
  have h2 : K.time first ≤ K.time (K.activeStage ⟨max a 0, hr0, hrh⟩) :=
    K.time_strictMono.monotone h1
  exact lt_of_le_of_lt (h2.trans (K.activeStage_time_le _)) (max_lt hat ht)

/-- on the last stage (`time last ≤ s`) `gStage` is the stage metric of `last` restricted to the survivor domain. -/
theorem gStage_eq_restrict_S121 (K : ObservedHistory.{u}) (first last : Fin (K.eventCount + 1))
    (ordered : first ≤ last) (a b : ℝ)
    (stages : ∀ r : Icc (0 : ℝ) K.horizon, (r : ℝ) ∈ Ico a b →
      first ≤ K.activeStage r ∧ K.activeStage r ≤ last)
    (g0 : SmoothRiemannianMetric (𝓡 3) (K.backwardSurvivorDomain first last ordered))
    {s : ℝ} (hs : s ∈ Ico a b) (hs0 : s ∈ Icc (0 : ℝ) K.horizon) (hts : K.time last ≤ s) :
    gStage_S110 K first last ordered a b stages g0 s =
      (K.stageMetric last s).restrictOpen (K.backwardSurvivorDomain first last ordered) := by
  have hact : K.activeStage ⟨s, hs0⟩ = last :=
    le_antisymm (stages ⟨s, hs0⟩ hs).2 (K.le_activeStage ⟨s, hs0⟩ last hts)
  rw [gStage_apply_S110 K first last ordered a b stages g0 hs hs0]
  have key : ∀ (j : Fin (K.eventCount + 1)) (hjl : j = last) (hj : first ≤ j) (hl : j ≤ last)
      (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (K.backwardSurvivorMap first last ordered j hj hl)),
      localPullMetric (K.stageMetric j s) (K.backwardSurvivorMap first last ordered j hj hl) hf =
        (K.stageMetric last s).restrictOpen (K.backwardSurvivorDomain first last ordered) := by
    intro j hjl hj hl hf
    subst hjl
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner, SmoothRiemannianMetric.restrictOpen_inner]
    have hmap := funext (K.backwardSurvivorMap_last first j ordered)
    rw [hmap, mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
  exact key _ hact _ _ _

theorem exists_windowFlow_S121 (K : ObservedHistory.{u}) (first last : Fin (K.eventCount + 1))
    (ordered : first ≤ last) (a b t : ℝ) (ht : 0 < t) (hat : a < t) (htb : 2 * t < b)
    (hbh : b ≤ K.horizon)
    (stages : ∀ r : Icc (0 : ℝ) K.horizon, (r : ℝ) ∈ Ico a b →
      first ≤ K.activeStage r ∧ K.activeStage r ≤ last)
    (g0 : SmoothRiemannianMetric (𝓡 3) (K.backwardSurvivorDomain first last ordered)) :
    ∃ (D : RealTimeInterval)
      (G : SolutionOn (I := 𝓡 3) (M := K.backwardSurvivorDomain first last ordered) D),
      IsSolutionOn (I := 𝓡 3) G ∧ Icc t (2 * t) ⊆ D.regular ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3))
        ((𝓡 3).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)) ∞
        (fun q : ℝ × K.backwardSurvivorDomain first last ordered =>
          (⟨q.2, (G.base.metric q.1).inner q.2⟩ :
            TotalSpace (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
              (fun x => TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ)))
        (Icc t (2 * t) ×ˢ (Set.univ : Set (K.backwardSurvivorDomain first last ordered))) ∧
      ∀ r ∈ Icc t (2 * t), G.base.metric r = gStage_S110 K first last ordered a b stages g0 r := by
  classical
  have hmem : ∀ r ∈ Icc t (2 * t), r ∈ Ico a b ∧ r ∈ Icc (0 : ℝ) K.horizon := fun r hr =>
    ⟨⟨hat.le.trans hr.1, by linarith [hr.2]⟩, ht.le.trans hr.1, by linarith [hr.2]⟩
  have hfirst : K.time first < t :=
    time_first_lt_S121 K first last a b t ht hat (by linarith) hbh stages
  by_cases h2 : 2 * t < K.time last
  · -- (i) the survivor flow alone
    have hlt : first < last := K.time_strictMono.lt_iff_lt.mp (by linarith)
    obtain ⟨F, hslab, hinit, hsm, hsol⟩ := K.exists_backwardSurvivor_isSolutionOn first last hlt
    refine ⟨RealTimeInterval.closed (K.time first) (K.time last) (K.time_strictMono hlt).le,
      { base := { metric := F } }, hsol, ?_, ?_, ?_⟩
    · intro r hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    · exact hsm.mono (prod_mono (Icc_subset_Icc hfirst.le (by linarith)) subset_rfl)
    · intro r hr
      obtain ⟨hs, hs0⟩ := hmem r hr
      rw [gStage_apply_S110 K first last ordered a b stages g0 hs hs0]
      exact survivorFlow_eq_stage_pullback_S107 K first last hlt.le F hslab hinit _
        (stages ⟨r, hs0⟩ hs).1 (stages ⟨r, hs0⟩ hs).2 (K.activeStage_mem ⟨r, hs0⟩)
        (by linarith [hr.2])
  · replace h2 : K.time last ≤ 2 * t := not_lt.mp h2
    -- the right piece: the closed prefix of the stage `last` up to `c = (2t + b)/2`
    obtain ⟨c, hc1, hc2⟩ : ∃ c : ℝ, 2 * t < c ∧ c < b := ⟨(2 * t + b) / 2, by linarith, by linarith⟩
    have hc0 : (0 : ℝ) ≤ c := by linarith
    have hch : c ≤ K.horizon := by linarith
    let c' : Icc (0 : ℝ) K.horizon := ⟨c, hc0, hch⟩
    have hcab : (c' : ℝ) ∈ Ico a b := ⟨by linarith, hc2⟩
    have hactc : K.activeStage c' = last :=
      le_antisymm (stages c' hcab).2 (K.le_activeStage c' last (by change K.time last ≤ c; linarith))
    have hlc : K.time last < c := by linarith
    obtain ⟨hRj, hRp⟩ := rightPiece_S121 K last c' hactc hlc
      (K.backwardSurvivorDomain first last ordered)
    let gR : ℝ → SmoothRiemannianMetric (𝓡 3) (K.backwardSurvivorDomain first last ordered) :=
      fun r => (K.stageMetric last r).restrictOpen (K.backwardSurvivorDomain first last ordered)
    rcases eq_or_lt_of_le ordered with he | hlt
    · -- (iii) `first = last`: the prefix alone
      have hlt' : K.time last < t := by rw [← he]; exact hfirst
      refine ⟨RealTimeInterval.closed (K.time last) c hlc.le,
        { base := { metric := gR } }, ?_, ?_, ?_, ?_⟩
      · exact isSolutionOn_of_joint_metric (RealTimeInterval.closed (K.time last) c hlc.le)
          (uniqueDiffOn_Icc hlc) _ hRj (fun τ hτ x v w => (hRp τ hτ x v w).hasDerivWithinAt)
      · intro r hr
        exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
      · exact hRj.mono (prod_mono (Icc_subset_Icc hlt'.le (by linarith)) subset_rfl)
      · intro r hr
        obtain ⟨hs, hs0⟩ := hmem r hr
        exact (gStage_eq_restrict_S121 K first last ordered a b stages g0 hs hs0
          (by linarith [hr.1])).symm
    · -- (ii) glue the survivor flow `F` (on `[time first, time last]`) with the prefix at `time last`
      obtain ⟨F, hslab, hinit, hsm, hsol⟩ := K.exists_backwardSurvivor_isSolutionOn first last hlt
      have ha : K.time first < K.time last := K.time_strictMono hlt
      have hpdeL : ∀ τ ∈ Ioo (K.time first) (K.time last), ∀ x : K.backwardSurvivorDomain first last ordered,
          ∀ v w : TangentSpace (𝓡 3) x,
          HasDerivAt (fun s => (F s).inner x v w) (-2 * ricciTensor (F τ) x v w) τ := by
        intro τ hτ x v w
        have hd := (hsol.equation ⟨τ, hτ⟩ x v w).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
        change HasDerivAt (fun s => (F s).inner x v w)
          (-2 * metricRicciAt (F τ) x (vec2 v w)) τ at hd
        erw [metricRicciAt_apply_eq_ricciTensor (F τ) x v w] at hd
        exact hd
      have hmatch : F (K.time last) = gR (K.time last) := by
        rw [hinit last hlt.le le_rfl, K.backwardSurvivorInitialMetric_last]
        change _ = (K.stageMetric last (K.time last)).restrictOpen _
        rw [K.stageMetric_initial]
      refine ⟨RealTimeInterval.closed (K.time first) c (ha.le.trans hlc.le),
        { base := { metric := fun τ => if τ ≤ K.time last then F τ else gR τ } },
        isSolutionOn_ite_of_ricciFlow F gR ha hlc hsm hRj hpdeL hRp hmatch, ?_, ?_, ?_⟩
      · intro r hr
        exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
      · exact (metricCLMSection_jointContMDiffOn_ite_of_ricciFlow F gR ha hlc hsm hRj hpdeL hRp hmatch).mono
          (prod_mono (Icc_subset_Icc hfirst.le (by linarith)) subset_rfl)
      · intro r hr
        obtain ⟨hs, hs0⟩ := hmem r hr
        by_cases hrl : r ≤ K.time last
        · change (if r ≤ K.time last then F r else _) = _
          rw [ite_eq_left hrl, gStage_apply_S110 K first last ordered a b stages g0 hs hs0]
          exact survivorFlow_eq_stage_pullback_S107 K first last hlt.le F hslab hinit _
            (stages ⟨r, hs0⟩ hs).1 (stages ⟨r, hs0⟩ hs).2 (K.activeStage_mem ⟨r, hs0⟩) hrl
        · change (if r ≤ K.time last then F r else _) = _
          rw [ite_eq_right hrl]
          exact (gStage_eq_restrict_S121 K first last ordered a b stages g0 hs hs0
            (not_le.mp hrl).le).symm

section Post

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- `f` injective on `W` and `f = cast ∘ ψ ∘ φ` (as `HEq`) on `W` ⟹ `φ` injective on `W`. -/
theorem injOn_phi_S121 (H : FiniteVolumeHyperbolicModel.{u}) (n : ℕ)
    (first last : Fin ((F.tower.history n).eventCount + 1)) (ordered : first ≤ last) (a b t : ℝ)
    (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
      first ≤ (F.tower.history n).toHistory.activeStage r ∧
        (F.tower.history n).toHistory.activeStage r ≤ last)
    (ht0 : 0 ≤ t) (hth : t ≤ (F.tower.history n).horizon) (hat : a ≤ t) (htb : t < b)
    (f : H.Carrier → (postStage F.observation t).Carrier)
    (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered)
    (W : Set H.Carrier)
    (hheq : ∀ p ∈ W, HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
        ((F.tower.history n).toHistory.activeStage ⟨t, ht0, hth⟩)
        (stages ⟨t, ht0, hth⟩ ⟨hat, htb⟩).1 (stages ⟨t, ht0, hth⟩ ⟨hat, htb⟩).2 (φ p)) (f p))
    (hfinj : Set.InjOn f W) : Set.InjOn φ W := by
  intro p hp q hq hpq
  apply hfinj hp hq
  refine eq_of_heq ((hheq p hp).symm.trans (HEq.trans ?_ (hheq q hq)))
  rw [hpq]

end Post

end GC.LongTime.Ch12

end
