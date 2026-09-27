import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.Extension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.SmoothExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorGeodesicFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.AbsoluteContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.LocalPullback

noncomputable section
open Set Bundle Filter Manifold TopologicalSpace MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u vA
variable {A : Type vA} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem exists_survivor_geodesic_family_to_older_time_of_regularizedExtendedAction_eq_regularizedCost
    (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (k : Fin H.eventCount) (hf : first ≤ k.castSucc) (hl : k.succ ≤ last),
      ∃ z : (H.event k).old,
        z.val.val = gamma ⟨k.castSucc, hf, k.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time k.succ)) ∧
        (H.event k).oldOutput z = gamma ⟨k.succ, hf.trans k.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time k.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (huw : u < Real.sqrt (T - H.time i.succ))
    (hwv : Real.sqrt (T - H.time i.succ) < v)
    (hcross : (H.event i).RegularCrossing
      (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
        (Real.sqrt (T - H.time i.succ)))
      (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
        (Real.sqrt (T - H.time i.succ)))) :
    ∃ G : (H.stage i.succ).IncomingSlab (H.time i.succ) (H.stageEndTime i.succ),
      (∀ t, G.flow.base.metric t = H.stageMetric i.succ t) ∧
    ∃ (C D : ℝ) (hCs : C < H.time i.succ) (hsD : H.time i.succ < D)
      (W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen)
      (F : PartialDiffeomorph ThreeModel ThreeModel
        (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞)
      (S : SolutionOn (I := ThreeModel) (M := W)
        (RealTimeInterval.closed C D (hCs.trans hsD).le))
      (hlocalOld : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => z.val.val))
      (hlocalNew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => F z.val)),
      H.time i.castSucc < C ∧ D < H.stageEndTime i.succ ∧ F.source = W ∧
      IsSolutionOn S ∧
      (∀ z : W, (H.event i).RegularCrossing z.val.val (F z.val)) ∧
      (∀ t ∈ Ico C (H.time i.succ), S.base.metric t =
        localPullMetric (H.stageMetric i.castSucc t) (fun z : W => z.val.val) hlocalOld) ∧
      (∀ t ∈ Icc (H.time i.succ) D, S.base.metric t =
        localPullMetric (H.stageMetric i.succ t) (fun z : W => F z.val) hlocalNew) ∧
      S.base.metric (H.time i.succ) = (H.event i).terminal.metric.restrictOpen W ∧
      ∃ c d : ℝ, u < c ∧ c < Real.sqrt (T - H.time i.succ) ∧
        Real.sqrt (T - H.time i.succ) < d ∧ d < v ∧
        H.regularizedStageStart T u i.succ < c ∧
        d < H.regularizedStageEnd T v i.castSucc ∧
        (∀ r ∈ Icc c d, T - r ^ 2 ∈ Ioo C D) ∧
      ∃ eta : ℝ → W,
        IsLRegularizedGeodesicOn S T eta (Ioo c d) ∧
        EqOn ((fun z : W => F z.val) ∘ eta)
          (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
          (Icc c (Real.sqrt (T - H.time i.succ))) ∧
        EqOn ((fun z : W => z.val.val) ∘ eta)
          (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
          (Icc (Real.sqrt (T - H.time i.succ)) d) ∧
      ∀ (t₀ q : ℝ), t₀ ∈ Ioo c (Real.sqrt (T - H.time i.succ)) →
        q ∈ Ioo (Real.sqrt (T - H.time i.succ)) (H.regularizedStageEnd T v i.castSucc) →
      ∀ (α : A × ℝ → (H.stage i.succ).Carrier) (V : Set A) (K : Set ℝ) (a0 : A),
        IsOpen V → IsOpen K → IsPreconnected K → a0 ∈ V → t₀ ∈ K →
        ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ α (V ×ˢ K) →
        (∀ z ∈ V, IsLRegularizedGeodesicOn G.flow T (fun r => α (z, r))
          (K ∩ Ioo (H.regularizedStageStart T u i.succ)
            (H.regularizedStageEnd T v i.succ))) →
        EqOn (fun r => α (a0, r))
          (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
          (K ∩ Icc (H.regularizedStageStart T u i.succ)
            (H.regularizedStageEnd T v i.succ)) →
        ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
          ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧
            Real.sqrt (T - H.time i.succ) ∈ J ∧ q ∈ J ∧
            ∃ β : A × ℝ → (H.stage i.castSucc).Carrier,
              ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (U ×ˢ J) ∧
              (∀ p ∈ U, IsLRegularizedGeodesicOn (H.event i).incoming.flow T
                (fun r => β (p, r))
                (J ∩ Ioo (Real.sqrt (T - H.time i.succ))
                  (H.regularizedStageEnd T v i.castSucc))) ∧
              EqOn (fun r => β (a0, r))
                (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
                (J ∩ Icc (Real.sqrt (T - H.time i.succ))
                  (H.regularizedStageEnd T v i.castSucc)) ∧
              ∃ U₁ : Set A, IsOpen U₁ ∧ U ⊆ U₁ ∧ U₁ ⊆ V ∧ a0 ∈ U₁ ∧
                ∃ L : Set ℝ, IsOpen L ∧ IsPreconnected L ∧ t₀ ∈ L ∧
                  Real.sqrt (T - H.time i.succ) ∈ L ∧
                  ∃ θ : A × ℝ → W,
                    ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ θ (U₁ ×ˢ L) ∧
                    (∀ p ∈ U₁, IsLRegularizedGeodesicOn S T (fun r => θ (p, r)) L) ∧
                    EqOn (fun p : A × ℝ => F (θ p).val) α
                      (U₁ ×ˢ (L ∩ K ∩ Ioo c (Real.sqrt (T - H.time i.succ)))) ∧
                    EqOn (fun r => θ (a0, r)) eta (L ∩ Ioo c d) ∧
                    EqOn β (fun p : A × ℝ => (θ p).val.val)
                      (U ×ˢ (L ∩ Ioo c d ∩ Iio (H.regularizedStageEnd T v i.castSucc))) ∧
                    (∀ p ∈ U, β (p, Real.sqrt (T - H.time i.succ)) =
                      (θ (p, Real.sqrt (T - H.time i.succ))).val.val) ∧
                    ∀ p ∈ U, (H.event i).RegularCrossing
                      (β (p, Real.sqrt (T - H.time i.succ)))
                      (F (θ (p, Real.sqrt (T - H.time i.succ))).val) := by
  obtain ⟨C, D, hCs, hsD, W, F, S, hlocalOld, hlocalNew, haC, hDb, hsource,
    hS, hcrossW, hpullOld, hpullNew, hterminal, c, d, huc, hcw, hwd, hdv, hnc, hdo,
    hclock, eta, _, _, hη, hηnew, hηold, _, _⟩ :=
    H.exists_regularizedGeodesic_survivor_lift_of_regularizedExtendedAction_eq_regularizedCost
      first last hle hu hupper hpast hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
      i hf hl huw hwv hcross
  have hout (j : Fin (H.eventCount + 1)) (hj : H.time j < H.stageEndTime j) :
      ∃ G : (H.stage j).IncomingSlab (H.time j) (H.stageEndTime j),
        ∀ t, G.flow.base.metric t = H.stageMetric j t := by
    cases j using Fin.lastCases with
    | last =>
      rw [H.stageEndTime_last]
      have hfinal : H.time (Fin.last H.eventCount) < H.horizon := by
        simpa only [H.stageEndTime_last] using hj
      let G := (H.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl
      refine ⟨G, ?_⟩
      intro t
      simp only [stageMetric, Fin.lastCases_last, dif_pos hfinal]
      rfl
    | cast j =>
      rw [H.stageEndTime_castSucc]
      refine ⟨(H.event j).incoming, ?_⟩
      intro t
      simp only [stageMetric, Fin.lastCases_castSucc]
  obtain ⟨G, hGmetric⟩ := hout i.succ (hsD.trans hDb)
  refine ⟨G, hGmetric, C, D, hCs, hsD, W, F, S, hlocalOld, hlocalNew, haC, hDb,
    hsource, hS, hcrossW, hpullOld, hpullNew, hterminal, c, d, huc, hcw, hwd, hdv,
    hnc, hdo, hclock, eta, hη, hηnew, hηold, ?_⟩
  intro t₀ q ht₀ hq α V K a0 hV hK hKconn ha0 ht₀K hα hαgeo hcenter
  let w := Real.sqrt (T - H.time i.succ)
  have hw : 0 < w := hu.trans_lt huw
  have hwclock : T - w ^ 2 = H.time i.succ := by
    rw [show w ^ 2 = T - H.time i.succ from Real.sq_sqrt (Real.sqrt_pos.mp hw).le]
    ring
  have hsupper : H.time i.succ < T - u ^ 2 := by
    have hh := (sq_lt_sq₀ hu hw.le).mpr huw
    linarith only [hh, hwclock]
  have hlower : T - v ^ 2 < H.time i.succ := by
    have hh := (sq_lt_sq₀ hw.le (hw.le.trans hwv.le)).mpr hwv
    linarith only [hh, hwclock]
  have hOldStart : H.regularizedStageStart T u i.castSucc = w := by
    simp only [regularizedStageStart, H.stageEndTime_castSucc, min_eq_right hsupper.le, w]
  have hNewEnd : H.regularizedStageEnd T v i.succ = w := by
    simp only [regularizedStageEnd, max_eq_right hlower.le, w]
  have hnewClock : ∀ r ∈ Ioo c w,
      T - r ^ 2 ∈ (RealTimeInterval.closedOpen (H.time i.succ) (H.stageEndTime i.succ) G.lt).regular := by
    intro r hr
    have hrcd : r ∈ Icc c d := ⟨hr.1.le, hr.2.le.trans hwd.le⟩
    have hsq := (sq_lt_sq₀ (hu.trans (huc.le.trans hr.1.le)) hw.le).mpr hr.2
    change H.time i.succ < T - r ^ 2 ∧ T - r ^ 2 < H.stageEndTime i.succ
    exact ⟨by linarith only [hsq, hwclock], (hclock r hrcd).2.trans hDb⟩
  have holdClock : ∀ r ∈ Ioo w d,
      T - r ^ 2 ∈ (RealTimeInterval.closedOpen (H.time i.castSucc) (H.time i.succ)
        (H.event i).incoming.lt).regular := by
    intro r hr
    have hrcd : r ∈ Icc c d := ⟨hcw.le.trans hr.1.le, hr.2.le⟩
    have hsq := (sq_lt_sq₀ hw.le (hw.le.trans hr.1.le)).mpr hr.1
    change H.time i.castSucc < T - r ^ 2 ∧ T - r ^ 2 < H.time i.succ
    exact ⟨haC.trans (hclock r hrcd).1, by linarith only [hsq, hwclock]⟩
  have hnewMetric : ∀ r ∈ Ioo c w, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) (fun z : W => F z.val) hlocalNew := by
    intro r hr
    rw [hGmetric]
    exact hpullNew _ ⟨(hnewClock r hr).1.le,
      (hclock r ⟨hr.1.le, hr.2.le.trans hwd.le⟩).2.le⟩
  have holdMetric : ∀ r ∈ Ioo w d, S.base.metric (T - r ^ 2) =
      localPullMetric ((H.event i).incoming.flow.base.metric (T - r ^ 2))
        (fun z : W => z.val.val) hlocalOld := by
    intro r hr
    have hh := hpullOld _ ⟨(hclock r ⟨hcw.le.trans hr.1.le, hr.2.le⟩).1.le,
      (holdClock r hr).2⟩
    simpa only [stageMetric, Fin.lastCases_castSucc] using hh
  let K₀ := K ∩ Ioo c w
  have hK₀ : IsOpen K₀ := hK.inter isOpen_Ioo
  have hK₀conn : IsPreconnected K₀ :=
    (hKconn.ordConnected.inter ordConnected_Ioo).isPreconnected
  have ht₀K₀ : t₀ ∈ K₀ := ⟨ht₀K, ht₀⟩
  have hα₀ : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ α (V ×ˢ K₀) :=
    hα.mono (prod_mono subset_rfl inter_subset_left)
  have hαgeo₀ : ∀ z ∈ V, IsLRegularizedGeodesicOn G.flow T (fun r => α (z, r)) K₀ := by
    intro z hz r hr
    apply hαgeo z hz r
    exact ⟨hr.1, hnc.trans hr.2.1, hNewEnd.symm ▸ hr.2.2⟩
  have hcenter₀ : (fun r => α (a0, r)) =ᶠ[𝓝 t₀] (fun z : W => F z.val) ∘ eta := by
    filter_upwards [hK₀.mem_nhds ht₀K₀] with r hr
    exact (hcenter ⟨hr.1, (hnc.trans hr.2.1).le, hNewEnd.symm ▸ hr.2.2.le⟩).trans
      (hηnew ⟨hr.2.1.le, hr.2.2.le⟩).symm
  obtain ⟨t₁, ht₁⟩ := exists_between hwd
  have hγ : IsLRegularizedGeodesicOn (H.event i).incoming.flow T
      (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
      (Ioo w (H.regularizedStageEnd T v i.castSucc)) := by
    rw [← hOldStart]
    exact H.regularizedGeodesicOn_incoming_stage_of_regularizedExtendedAction_eq_regularizedCost
      first last hle hu (huw.le.trans hwv.le) hupper hpast hscalar gamma hgammaAC hgammaInt
      hgammaNodes hmin i hf (i.castSucc_lt_succ.le.trans hl)
  obtain ⟨U, hU, haU, hUV, J, hJ, hJconn, hwJ, hqJ, β, hβ, hβgeo, hβcenter,
    U₁, hU₁, hUU₁, hU₁V, haU₁, L, hL, hLconn, ht₀L, _, hwL, θ, hθ, hθgeo, hθeq,
    hθcenter, hβeqOn, hβeq, hcrossβ⟩ :=
    (H.event i).exists_survivor_geodesic_family_to_older_time_of_germ
      G W F hsource S hS hlocalNew hlocalOld hcrossW T ht₀ ht₁ hdo.le hq
      hnewClock holdClock hnewMetric holdMetric hV hK₀ hK₀conn ha0 ht₀K₀ hα₀ hαgeo₀
      hη hcenter₀ hγ hηold
  refine ⟨U, hU, haU, hUV, J, hJ, hJconn, hwJ, hqJ, β, hβ, hβgeo, hβcenter,
    U₁, hU₁, hUU₁, hU₁V, haU₁, L, hL, hLconn, ht₀L, hwL, θ, hθ, hθgeo, ?_, hθcenter, hβeqOn, hβeq, hcrossβ⟩
  intro p hp
  exact hθeq ⟨hp.1, ⟨hp.2.1.1, hp.2.1.2, hp.2.2⟩, hp.2.2⟩


private theorem exists_stage_incomingSlab_metric
    (H : ObservedHistory.{u})
    (j : Fin (H.eventCount + 1)) (hj : H.time j < H.stageEndTime j) :
    ∃ G : (H.stage j).IncomingSlab (H.time j) (H.stageEndTime j),
      ∀ t, G.flow.base.metric t = H.stageMetric j t := by
  cases j using Fin.lastCases with
  | last =>
      rw [H.stageEndTime_last]
      have hfinal : H.time (Fin.last H.eventCount) < H.horizon := by simpa only [H.stageEndTime_last] using hj
      refine ⟨(H.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl, ?_⟩
      intro t
      simp only [stageMetric, Fin.lastCases_last, dif_pos hfinal]
      rfl
  | cast i =>
      rw [H.stageEndTime_castSucc]
      refine ⟨(H.event i).incoming, ?_⟩
      intro t
      simp only [stageMetric, Fin.lastCases_castSucc]

private theorem event_clock_strict_bounds
    (H : ObservedHistory.{u})
    {first last : Fin (H.eventCount + 1)} {T u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v)
    (hupper : T - u ^ 2 ∈ Ioo (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) :
    u < Real.sqrt (T - H.time i.succ) ∧ Real.sqrt (T - H.time i.succ) < v := by
  have hs : H.time i.succ < T - u ^ 2 := (H.time_strictMono.monotone hl).trans_lt hupper.1
  have ht : T - v ^ 2 < H.time i.succ := by
    have hh := hpast.2.trans_le (H.stageEndTime_mono hf)
    simpa only [H.stageEndTime_castSucc] using hh
  have hv0 : 0 < v := hu.trans_lt huv
  constructor
  · exact (Real.lt_sqrt hu).mpr (by linarith)
  · exact (Real.sqrt_lt' hv0).mpr (by linarith)


private theorem stage_geodesic_of_minimizer
    (H : ObservedHistory.{u})
    (j : Fin (H.eventCount + 1)) {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := (H.stage j).Carrier) D)
    (hmetric : ∀ t, S.base.metric t = H.stageMetric j t)
    (hregular : D.regular = Ioo (H.time j) (H.stageEndTime j))
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) MeasureTheory.volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    (hj : first ≤ j) (hjlast : j ≤ last) :
    IsLRegularizedGeodesicOn S T (gamma ⟨j, hj, hjlast⟩)
      (Ioo (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j)) := by
  cases j using Fin.lastCases with
  | cast i =>
      have hg := H.regularizedGeodesicOn_incoming_stage_of_regularizedExtendedAction_eq_regularizedCost
        first last hle hu huv hupper hpast hscalar gamma hgammaAC hgammaInt hgammaNodes hmin i hj hjlast
      intro r hr
      have h := hg r hr
      refine ⟨by rw [hregular]; exact H.mapsTo_regularizedStage_Ioo_Ioo T u v i.castSucc hr,
        h.2.1, h.2.2.1, ?_⟩
      have hm : S.base.metric (T - r ^ 2) = (H.event i).incoming.flow.base.metric (T - r ^ 2) := by
        simpa only [stageMetric, Fin.lastCases_castSucc] using hmetric (T - r ^ 2)
      have hsc : S.scalar (T - r ^ 2) = (H.event i).incoming.flow.scalar (T - r ^ 2) := by
        change (fun x => metricScalarAt (S.base.metric (T - r ^ 2)) x) = _
        rw [hm]
        rfl
      simpa only [lRegularizedAccel, hm, hsc] using h.2.2.2
  | last =>
      intro r hr
      have htimes := H.mapsTo_regularizedStage_Ioo_Ioo T u v (Fin.last H.eventCount) hr
      have hfinal : H.time (Fin.last H.eventCount) < H.horizon := by
        simpa only [H.stageEndTime_last] using htimes.1.trans htimes.2
      have hlast : last = Fin.last H.eventCount := le_antisymm (Fin.le_last _) hjlast
      subst last
      have hg := H.regularizedGeodesicOn_final_stage_of_regularizedExtendedAction_eq_regularizedCost
        first hfinal hu huv (by simpa only [H.stageEndTime_last] using hupper) hpast hscalar
        gamma hgammaAC hgammaInt (fun i hf => hgammaNodes i hf (Fin.le_last _)) hmin
      have h := hg r hr
      refine ⟨by rw [hregular]; exact htimes, h.2.1, h.2.2.1, ?_⟩
      have hm : S.base.metric (T - r ^ 2) = (H.finalSlab hfinal).flow.base.metric (T - r ^ 2) := by
        simpa only [stageMetric, Fin.lastCases_last, dif_pos hfinal] using hmetric (T - r ^ 2)
      have hsc : S.scalar (T - r ^ 2) = (H.finalSlab hfinal).flow.scalar (T - r ^ 2) := by
        change (fun x => metricScalarAt (S.base.metric (T - r ^ 2)) x) = _
        rw [hm]
        rfl
      simpa only [lRegularizedAccel, hm, hsc] using h.2.2.2

section
variable {Q : OrientedThreeStage.{u}} {s b : ℝ}

private theorem exists_recent_family_patch
    (G : Q.IncomingSlab s b) {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X] {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := X) D)
    (g : X → Q.Carrier) (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
    (T : ℝ) {r c w d t₀ : ℝ} (hrc : r < c) (ht₀ : t₀ ∈ Ioo c w) (hwd : w < d)
    (hclock : ∀ q ∈ Ioo c w, T - q ^ 2 ∈ (RealTimeInterval.closedOpen s b G.lt).regular)
    (hmetric : ∀ q ∈ Ioo c w, S.base.metric (T - q ^ 2) = localPullMetric (G.flow.base.metric (T - q ^ 2)) g hg)
    {α : A × ℝ → Q.Carrier} {θ : A × ℝ → X} {V U : Set A} {K L : Set ℝ} {a0 : A}
    (hU : IsOpen U) (hUV : U ⊆ V) (haU : a0 ∈ U)
    (hK : IsOpen K) (hKconn : IsPreconnected K) (hrK : r ∈ K) (ht₀K : t₀ ∈ K)
    (hL : IsOpen L) (hLconn : IsPreconnected L) (ht₀L : t₀ ∈ L) (hwL : w ∈ L)
    (hα : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ α (V ×ˢ K))
    (hθ : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ θ (U ×ˢ L))
    (hαgeo : ∀ z ∈ V, IsLRegularizedGeodesicOn G.flow T (fun q => α (z, q)) (K ∩ Ioo r w))
    (hθgeo : ∀ z ∈ U, IsLRegularizedGeodesicOn S T (fun q => θ (z, q)) L)
    (heq : EqOn (fun p : A × ℝ => g (θ p)) α (U ×ˢ (L ∩ K ∩ Ioo c w)))
    {γ : ℝ → Q.Carrier}
    (hαcenter : EqOn (fun q => α (a0, q)) γ (K ∩ Icc r w))
    (hθcenter : EqOn (fun q => g (θ (a0, q))) γ (L ∩ Icc c w)) :
    ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ r ∈ J ∧ w ∈ J ∧
      ∃ δ : A × ℝ → Q.Carrier,
        ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ δ (U ×ˢ J) ∧
        EqOn δ α (U ×ˢ (K ∩ Iio w)) ∧
        (∀ z ∈ U, δ (z, w) = g (θ (z, w))) ∧
        (∀ z ∈ U, IsLRegularizedGeodesicOn G.flow T (fun q => δ (z, q)) (J ∩ Ioo r w)) ∧
        EqOn (fun q => δ (a0, q)) γ (J ∩ Icc r w) ∧
        EqOn δ (fun p : A × ℝ => g (θ p)) (U ×ˢ (L ∩ Ioo c d)) := by
  classical
  let C := L ∩ Ioo c d
  have hC : IsOpen C := hL.inter isOpen_Ioo
  have hCconn : IsPreconnected C := (hLconn.ordConnected.inter ordConnected_Ioo).isPreconnected
  have htC : t₀ ∈ C := ⟨ht₀L, ht₀.1, ht₀.2.trans hwd⟩
  have hwC : w ∈ C := ⟨hwL, ht₀.1.trans ht₀.2, hwd⟩
  let J := (K ∩ Iio w) ∪ C
  let δ : A × ℝ → Q.Carrier := fun p => if p.2 ∈ K ∩ Iio w then α p else g (θ p)
  have hδα : EqOn δ α (U ×ˢ (K ∩ Iio w)) := fun p hp => if_pos hp.2
  have hδθ : EqOn δ (fun p : A × ℝ => g (θ p)) (U ×ˢ C) := by
    intro p hp
    by_cases hr : p.2 ∈ K ∩ Iio w
    · exact (if_pos hr).trans (heq ⟨hp.1, ⟨hp.2.1, hr.1⟩, hp.2.2.1, hr.2⟩).symm
    · exact if_neg hr
  have hδ : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ δ (U ×ˢ J) := by
    rw [prod_union]
    exact ((hα.mono (prod_mono hUV inter_subset_left)).congr hδα).union_of_isOpen
      (((hg.contMDiff.comp_contMDiffOn hθ).mono (prod_mono subset_rfl inter_subset_left)).congr hδθ)
      (hU.prod (hK.inter isOpen_Iio)) (hU.prod hC)
  have hJconn : IsPreconnected J :=
    (hKconn.ordConnected.inter ordConnected_Iio).isPreconnected.union t₀ ⟨ht₀K, ht₀.2⟩ htC hCconn
  refine ⟨J, (hK.inter isOpen_Iio).union hC, hJconn,
    Or.inl ⟨hrK, hrc.trans (ht₀.1.trans ht₀.2)⟩, Or.inr hwC, δ, hδ, hδα,
    (fun z hz => hδθ ⟨hz, hwC⟩), ?_, ?_, hδθ⟩
  · intro z hz q hq
    rcases hq.1 with hqK | hqC
    · have hgerm : (fun x => δ (z, x)) =ᶠ[𝓝 q] (fun x => α (z, x)) := by
        filter_upwards [(hK.inter isOpen_Iio).mem_nhds hqK] with x hx
        exact hδα ⟨hz, hx⟩
      exact lRegularizedData_congr G.flow T q hgerm (hαgeo z (hUV hz) q ⟨hqK.1, hq.2⟩)
    · have hgeo := (show IsLRegularizedGeodesicOn S T (fun x => θ (z, x)) (L ∩ Ioo c w) from
          fun x hx => hθgeo z hz x hx.1).comp_of_localPullMetric (S' := G.flow) hg
          (fun x hx => hmetric x hx.2) (fun x hx _ => hclock x hx.2) (fun x hx => by
            filter_upwards [hL.mem_nhds hx.1] with v hv
            exact (hθgeo z hz v hv).2.1)
      have hgerm : (fun x => δ (z, x)) =ᶠ[𝓝 q] (fun x => g (θ (z, x))) := by
        filter_upwards [hC.mem_nhds hqC] with x hx
        exact hδθ ⟨hz, hx⟩
      exact lRegularizedData_congr G.flow T q hgerm (hgeo q ⟨hqC.1, hqC.2.1, hq.2.2⟩)
  · intro q hq
    rcases hq.1 with hqK | hqC
    · exact (hδα ⟨haU, hqK⟩).trans (hαcenter ⟨hqK.1, hq.2⟩)
    · exact (hδθ ⟨haU, hqC⟩).trans (hθcenter ⟨hqC.1, hqC.2.1.le, hq.2.2⟩)

end

private def seamFamily (H : ObservedHistory.{u}) (i : Fin H.eventCount) (T : ℝ)
    (U : Set A) (α : A × ℝ → (H.stage i.castSucc).Carrier) (β : A × ℝ → (H.stage i.succ).Carrier) : Prop :=
  ∃ (C D : ℝ) (hCs : C < H.time i.succ) (hsD : H.time i.succ < D)
    (W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen)
    (F : PartialDiffeomorph ThreeModel ThreeModel
      (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞)
    (S : SolutionOn (I := ThreeModel) (M := W) (RealTimeInterval.closed C D (hCs.trans hsD).le))
    (hlocalOld : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => z.val.val))
    (hlocalNew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => F z.val)),
    H.time i.castSucc < C ∧ D < H.stageEndTime i.succ ∧ F.source = W ∧ IsSolutionOn S ∧
    (∀ z : W, (H.event i).RegularCrossing z.val.val (F z.val)) ∧
    (∀ t ∈ Ico C (H.time i.succ), S.base.metric t =
      localPullMetric (H.stageMetric i.castSucc t) (fun z : W => z.val.val) hlocalOld) ∧
    (∀ t ∈ Icc (H.time i.succ) D, S.base.metric t =
      localPullMetric (H.stageMetric i.succ t) (fun z : W => F z.val) hlocalNew) ∧
    S.base.metric (H.time i.succ) = (H.event i).terminal.metric.restrictOpen W ∧
    ∃ L : Set ℝ, IsOpen L ∧ IsConnected L ∧ Real.sqrt (T - H.time i.succ) ∈ L ∧
      (∀ r ∈ L, T - r ^ 2 ∈ Ioo C D) ∧
      ∃ θ : A × ℝ → W,
        ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ θ (U ×ˢ L) ∧
        (∀ a ∈ U, IsLRegularizedGeodesicOn S T (fun r => θ (a, r)) L) ∧
        EqOn α (fun p : A × ℝ => (θ p).val.val) (U ×ˢ L) ∧
        EqOn β (fun p : A × ℝ => F (θ p).val) (U ×ˢ L)

private theorem seam_family_congr (H : ObservedHistory.{u}) (i : Fin H.eventCount) (T : ℝ)
    {U V : Set A} {α α' : A × ℝ → (H.stage i.castSucc).Carrier}
    {β β' : A × ℝ → (H.stage i.succ).Carrier}
    (h : seamFamily H i T V α β) (hUV : U ⊆ V)
    (hα : ∀ᶠ r in 𝓝 (Real.sqrt (T - H.time i.succ)), ∀ a ∈ U, α' (a, r) = α (a, r))
    (hβ : ∀ᶠ r in 𝓝 (Real.sqrt (T - H.time i.succ)), ∀ a ∈ U, β' (a, r) = β (a, r)) :
    seamFamily H i T U α' β' := by
  obtain ⟨C, D, hCs, hsD, W, F, S, ho, hn, hC, hD, hsource, hS, hcross,
    hmo, hmn, hmt, L, hL, hLconn, hwL, hclock, θ, hθ, hθgeo, hθo, hθn⟩ := h
  obtain ⟨l, r, hwr, hIr⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hα.and hβ)
  let K := L ∩ Ioo l r
  have hwK : Real.sqrt (T - H.time i.succ) ∈ K := ⟨hwL, hwr⟩
  refine ⟨C, D, hCs, hsD, W, F, S, ho, hn, hC, hD, hsource, hS, hcross, hmo, hmn, hmt,
    K, hL.inter isOpen_Ioo, ⟨⟨_, hwK⟩, (hLconn.isPreconnected.ordConnected.inter ordConnected_Ioo).isPreconnected⟩,
    hwK, (fun t ht => hclock t ht.1), θ,
    hθ.mono (prod_mono hUV inter_subset_left), (fun a ha t ht => hθgeo a (hUV ha) t ht.1), ?_, ?_⟩
  · intro p hp
    exact ((hIr hp.2.2).1 p.1 hp.1).trans (hθo ⟨hUV hp.1, hp.2.1⟩)
  · intro p hp
    exact ((hIr hp.2.2).2 p.1 hp.1).trans (hθn ⟨hUV hp.1, hp.2.1⟩)

private def stageFamily
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (G : (j : H.StageInterval first last) → (H.stage j.val).IncomingSlab (H.time j.val) (H.stageEndTime j.val))
    (T u v : ℝ) (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (a0 : A) (α0 : A × ℝ → (H.stage last).Carrier)
    (f : Fin (H.eventCount + 1)) (U : Set A) (J : H.StageInterval first last → Set ℝ)
    (α : (j : H.StageInterval first last) → A × ℝ → (H.stage j.val).Carrier) : Prop :=
  (∀ j, f ≤ j.val → IsOpen (J j) ∧ IsPreconnected (J j) ∧
    H.regularizedStageStart T u j.val ∈ J j ∧
    (f < j.val → H.regularizedStageEnd T v j.val ∈ J j) ∧
    ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ (α j) (U ×ˢ J j) ∧
    (∀ a ∈ U, IsLRegularizedGeodesicOn (G j).flow T (fun r => α j (a, r))
      (J j ∩ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))) ∧
    EqOn (fun r => α j (a0, r)) (gamma j)
      (J j ∩ Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))) ∧
  (∀ (k : Fin H.eventCount) (hk : first ≤ k.castSucc) (hl : k.succ ≤ last),
    f ≤ k.castSucc → ∀ a ∈ U, (H.event k).RegularCrossing
      (α ⟨k.castSucc, hk, k.castSucc_lt_succ.le.trans hl⟩ (a, Real.sqrt (T - H.time k.succ)))
      (α ⟨k.succ, hk.trans k.castSucc_lt_succ.le, hl⟩ (a, Real.sqrt (T - H.time k.succ)))) ∧
  (∀ a ∈ U, (fun r => α ⟨last, hle, le_rfl⟩ (a, r)) =ᶠ[𝓝 u] (fun r => α0 (a, r))) ∧
  ∀ (k : Fin H.eventCount) (hk : first ≤ k.castSucc) (hl : k.succ ≤ last), f ≤ k.castSucc →
    seamFamily H k T U (α ⟨k.castSucc, hk, k.castSucc_lt_succ.le.trans hl⟩)
      (α ⟨k.succ, hk.trans k.castSucc_lt_succ.le, hl⟩)


section
variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem exists_lRegularizedGeodesicFamily_extension_preserving_boundary_germ
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {α : A × ℝ → M} {V : Set A} {J₀ : Set ℝ} {a0 : A} {w b e : ℝ}
    (hV : IsOpen V) (ha0 : a0 ∈ V) (hJ₀ : IsOpen J₀) (hconn₀ : IsPreconnected J₀)
    (hwJ₀ : w ∈ J₀) (hb : b ∈ Ioo w e)
    (hα : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ α (V ×ˢ J₀))
    (hcurves : ∀ a ∈ V, IsLRegularizedGeodesicOn S T (fun s => α (a, s)) (J₀ ∩ Ioo w e))
    {γ : ℝ → M} (hγ : IsLRegularizedGeodesicOn S T γ (Ioo w e))
    (hcenter : EqOn (fun r => α (a0, r)) γ (J₀ ∩ Icc w e)) :
    ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ K : Set ℝ, IsOpen K ∧ IsPreconnected K ∧ w ∈ K ∧ b ∈ K ∧
        ∃ β : A × ℝ → M,
          ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ β (U ×ˢ K) ∧
          (∀ a ∈ U, IsLRegularizedGeodesicOn S T (fun r => β (a, r)) (K ∩ Ioo w e)) ∧
          EqOn (fun r => β (a0, r)) γ (K ∩ Icc w e) ∧
          ∀ a ∈ U, (fun r => β (a, r)) =ᶠ[𝓝 w] (fun r => α (a, r)) := by
  obtain ⟨l, u, hwlu, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hJ₀.mem_nhds hwJ₀)
  obtain ⟨s0, hws0, hs0⟩ := exists_between (lt_min hwlu.2 (hb.1.trans hb.2))
  have hs0J₀ : s0 ∈ J₀ := hlu ⟨hwlu.1.trans hws0, hs0.trans_le (min_le_left _ _)⟩
  have hs0we : s0 ∈ Ioo w e := ⟨hws0, hs0.trans_le (min_le_right _ _)⟩
  obtain ⟨U, hU, haU, hUV, K, hK, hconnK, hwK, hbK, β, hβ, heq, hgeo, hβcenter⟩ :=
    exists_lRegularizedGeodesicFamily_extension_from_boundary S hS T hV ha0 hJ₀ hconn₀
      hwJ₀ hs0J₀ hs0we hb hα hcurves hγ hcenter
  refine ⟨U, hU, haU, hUV, K, hK, hconnK, hwK, hbK, β, hβ, hgeo, hβcenter, ?_⟩
  intro a ha
  filter_upwards [(hJ₀.inter isOpen_Iio).mem_nhds ⟨hwJ₀, hb.1.trans hb.2⟩] with r hr
  exact heq ⟨ha, hr⟩

end

private theorem stage_family_update
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (G : (j : H.StageInterval first last) → (H.stage j.val).IncomingSlab (H.time j.val) (H.stageEndTime j.val))
    (T u v : ℝ) (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (a0 : A) (α0 : A × ℝ → (H.stage last).Carrier)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {oldU U : Set A} (hU : U ⊆ oldU)
    (J : H.StageInterval first last → Set ℝ)
    (α : (j : H.StageInterval first last) → A × ℝ → (H.stage j.val).Carrier)
    (hIH : stageFamily H first last hle G T u v gamma a0 α0 i.succ oldU J α)
    (Kβ Kδ : Set ℝ) (β : A × ℝ → (H.stage i.castSucc).Carrier)
    (δ : A × ℝ → (H.stage i.succ).Carrier)
    (hKβ : IsOpen Kβ) (hconnβ : IsPreconnected Kβ)
    (hstartβ : H.regularizedStageStart T u i.castSucc ∈ Kβ)
    (hsmoothβ : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (U ×ˢ Kβ))
    (hgeoβ : ∀ a ∈ U, IsLRegularizedGeodesicOn
      (G ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩).flow T (fun r => β (a, r))
      (Kβ ∩ Ioo (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc)))
    (hcenterβ : EqOn (fun r => β (a0, r)) (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
      (Kβ ∩ Icc (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc)))
    (hKδ : IsOpen Kδ) (hconnδ : IsPreconnected Kδ)
    (hstartδ : H.regularizedStageStart T u i.succ ∈ Kδ)
    (hendδ : H.regularizedStageEnd T v i.succ ∈ Kδ)
    (hsmoothδ : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ δ (U ×ˢ Kδ))
    (hgeoδ : ∀ a ∈ U, IsLRegularizedGeodesicOn
      (G ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩).flow T (fun r => δ (a, r))
      (Kδ ∩ Ioo (H.regularizedStageStart T u i.succ) (H.regularizedStageEnd T v i.succ)))
    (hcenterδ : EqOn (fun r => δ (a0, r)) (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
      (Kδ ∩ Icc (H.regularizedStageStart T u i.succ) (H.regularizedStageEnd T v i.succ)))
    (hδuniform : ∀ᶠ r in 𝓝 (H.regularizedStageStart T u i.succ),
      ∀ a ∈ U, δ (a, r) = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (a, r))
    (hseam : seamFamily H i T U β δ)
    (hcross : ∀ a ∈ U, (H.event i).RegularCrossing
      (β (a, Real.sqrt (T - H.time i.succ))) (δ (a, Real.sqrt (T - H.time i.succ))))
    (hclockLater : ∀ k : Fin H.eventCount, i.succ ≤ k.castSucc → k.succ ≤ last → k.castSucc = i.succ →
      Real.sqrt (T - H.time k.succ) = H.regularizedStageStart T u i.succ)
    (hclockPole : last = i.succ → u = H.regularizedStageStart T u i.succ) :
    ∃ J' : H.StageInterval first last → Set ℝ,
      ∃ α' : (j : H.StageInterval first last) → A × ℝ → (H.stage j.val).Carrier,
        J' ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ = Kβ ∧
        (∀ j, j.val ≠ i.castSucc → j.val ≠ i.succ → J' j = J j) ∧
        stageFamily H first last hle G T u v gamma a0 α0 i.castSucc U J' α' := by
  classical
  have hδgerm : ∀ a ∈ U, (fun r => δ (a, r)) =ᶠ[𝓝 (H.regularizedStageStart T u i.succ)]
      (fun r => α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (a, r)) :=
    fun a ha => hδuniform.mono (fun _ h => h a ha)
  let jo : H.StageInterval first last := ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
  let jn : H.StageInterval first last := ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
  have hno : jn ≠ jo := by
    intro h
    have hv := congrArg Subtype.val h
    exact (ne_of_gt i.castSucc_lt_succ) hv
  let J' := Function.update (Function.update J jo Kβ) jn Kδ
  let α' := Function.update (Function.update α jo β) jn δ
  have hJ'o : J' jo = Kβ := by simp [J', hno.symm]
  have hJ'n : J' jn = Kδ := by simp [J']
  have hα'o : α' jo = β := by simp [α', hno.symm]
  have hα'n : α' jn = δ := by simp [α']
  have hJ'eq (j : H.StageInterval first last) (hjo : j ≠ jo) (hjn : j ≠ jn) : J' j = J j := by
    simp [J', hjo, hjn]
  have hα'eq (j : H.StageInterval first last) (hjo : j ≠ jo) (hjn : j ≠ jn) : α' j = α j := by
    simp [α', hjo, hjn]
  have hpoint (j : H.StageInterval first last) (hj : i.succ ≤ j.val)
      (a : A) (ha : a ∈ U) (r : ℝ)
      (hr : j = jn → r = H.regularizedStageStart T u i.succ) : α' j (a, r) = α j (a, r) := by
    by_cases hjn : j = jn
    · subst j
      rw [hα'n, hr rfl]
      exact (hδgerm a ha).self_of_nhds
    · have hjo : j ≠ jo := by
        intro hh
        have hv := congrArg Subtype.val hh
        have hhj := hj
        change i.succ ≤ j.val at hhj
        rw [hv] at hhj
        exact (not_le_of_gt i.castSucc_lt_succ) hhj
      rw [hα'eq j hjo hjn]
  refine ⟨J', α', hJ'o, ?_, ?_⟩
  · intro j hjo hjn
    exact hJ'eq j (fun hh => hjo (congrArg Subtype.val hh))
      (fun hh => hjn (congrArg Subtype.val hh))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjo : j = jo
    · subst j
      rw [hJ'o, hα'o]
      exact ⟨hKβ, hconnβ, hstartβ, fun h => (lt_irrefl _ h).elim, hsmoothβ, hgeoβ, hcenterβ⟩
    by_cases hjn : j = jn
    · subst j
      rw [hJ'n, hα'n]
      exact ⟨hKδ, hconnδ, hstartδ, fun _ => hendδ, hsmoothδ, hgeoδ, hcenterδ⟩
    have hjnle : i.succ ≤ j.val := by
      have hjne : j.val ≠ i.castSucc := fun h => hjo (Subtype.ext h)
      exact Fin.castSucc_lt_iff_succ_le.mp (lt_of_le_of_ne hj (Ne.symm hjne))
    have hjnlt : i.succ < j.val := lt_of_le_of_ne hjnle
      (fun h => hjn (Subtype.ext h.symm))
    rw [hJ'eq j hjo hjn, hα'eq j hjo hjn]
    obtain ⟨hopen, hconn, hstart, hend, hsmooth, hgeo, hcenter⟩ := hIH.1 j hjnle
    exact ⟨hopen, hconn, hstart, fun _ => hend hjnlt,
      hsmooth.mono (prod_mono hU subset_rfl), fun a ha => hgeo a (hU ha), hcenter⟩
  · intro k hk hkl hkf a ha
    by_cases hki : k = i
    · subst k
      change (H.event i).RegularCrossing (α' jo _) (α' jn _)
      rw [hα'o, hα'n]
      exact hcross a ha
    have hik : i.succ ≤ k.castSucc := by
      apply Fin.castSucc_lt_iff_succ_le.mp
      apply lt_of_le_of_ne hkf
      intro hh
      exact hki (Fin.ext (congrArg Fin.val hh).symm)
    let ko : H.StageInterval first last := ⟨k.castSucc, hk, k.castSucc_lt_succ.le.trans hkl⟩
    let kn : H.StageInterval first last := ⟨k.succ, hk.trans k.castSucc_lt_succ.le, hkl⟩
    have hko : α' ko (a, Real.sqrt (T - H.time k.succ)) = α ko (a, Real.sqrt (T - H.time k.succ)) :=
      hpoint ko hik a ha _ (fun hh => hclockLater k hik hkl (congrArg Subtype.val hh))
    have hkn : α' kn (a, Real.sqrt (T - H.time k.succ)) = α kn (a, Real.sqrt (T - H.time k.succ)) := by
      apply hpoint kn (hik.trans k.castSucc_lt_succ.le) a ha
      intro hh
      have hv : k.succ = i.succ := congrArg Subtype.val hh
      exact ((not_lt_of_ge hik) (hv ▸ k.castSucc_lt_succ)).elim
    change (H.event k).RegularCrossing (α' ko _) (α' kn _)
    rw [hko, hkn]
    exact hIH.2.1 k hk hkl hik a (hU ha)
  · intro a ha
    let jl : H.StageInterval first last := ⟨last, hle, le_rfl⟩
    have hbase : (fun r => α jl (a, r)) =ᶠ[𝓝 u] (fun r => α0 (a, r)) := hIH.2.2.1 a (hU ha)
    by_cases hjn : jl = jn
    · have hv : last = i.succ := congrArg Subtype.val hjn
      have hg := hδgerm a ha
      rw [← hclockPole hv] at hg
      have hlocal : (fun r => α' jn (a, r)) =ᶠ[𝓝 u] (fun r => α jn (a, r)) := by
        rw [hα'n]
        exact hg
      have heq : (fun r => α' jl (a, r)) =ᶠ[𝓝 u] (fun r => α jl (a, r)) := hjn.symm ▸ hlocal
      exact heq.trans hbase
    · have hjo : jl ≠ jo := by
        intro hh
        have hv : last = i.castSucc := congrArg Subtype.val hh
        exact (not_le_of_gt i.castSucc_lt_succ) (hv ▸ hl)
      change (fun r => α' jl (a, r)) =ᶠ[𝓝 u] (fun r => α0 (a, r))
      rw [hα'eq jl hjo hjn]
      exact hbase
  · intro k hk hkl hkf
    by_cases hki : k = i
    · subst k
      change seamFamily H i T U (α' jo) (α' jn)
      rw [hα'o, hα'n]
      exact hseam
    have hik : i.succ ≤ k.castSucc := by
      apply Fin.castSucc_lt_iff_succ_le.mp
      apply lt_of_le_of_ne hkf
      intro hh
      exact hki (Fin.ext (congrArg Fin.val hh).symm)
    let ko : H.StageInterval first last := ⟨k.castSucc, hk, k.castSucc_lt_succ.le.trans hkl⟩
    let kn : H.StageInterval first last := ⟨k.succ, hk.trans k.castSucc_lt_succ.le, hkl⟩
    have hko : ∀ᶠ r in 𝓝 (Real.sqrt (T - H.time k.succ)), ∀ a ∈ U, α' ko (a, r) = α ko (a, r) := by
      by_cases hkon : ko = jn
      · have hw := hclockLater k hik hkl (congrArg Subtype.val hkon)
        rw [hw, hkon, hα'n]
        exact hδuniform
      · have hkoo : ko ≠ jo := by
          intro heq
          have hv : k.castSucc = i.castSucc := congrArg Subtype.val heq
          exact hki (Fin.castSucc_injective H.eventCount hv)
        rw [hα'eq ko hkoo hkon]
        exact Filter.Eventually.of_forall (fun _ _ _ => rfl)
    have hkno : kn ≠ jo := by
      intro heq
      have hv : k.succ = i.castSucc := congrArg Subtype.val heq
      exact (not_lt_of_ge hkf) (hv ▸ k.castSucc_lt_succ)
    have hknn : kn ≠ jn := by
      intro heq
      have hv : k.succ = i.succ := congrArg Subtype.val heq
      exact hki (Fin.succ_injective H.eventCount hv)
    apply seam_family_congr H k T (hIH.2.2.2 k hk hkl hik) hU hko
    rw [hα'eq kn hkno hknn]
    exact Filter.Eventually.of_forall (fun _ _ _ => rfl)

private theorem stage_family_last
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (G : (j : H.StageInterval first last) → (H.stage j.val).IncomingSlab (H.time j.val) (H.stageEndTime j.val))
    (T u v : ℝ) (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (a0 : A) (α0 : A × ℝ → (H.stage last).Carrier)
    (U : Set A) (K : Set ℝ) (β : A × ℝ → (H.stage last).Carrier)
    (hK : IsOpen K) (hconn : IsPreconnected K)
    (hstart : H.regularizedStageStart T u last ∈ K)
    (hsmooth : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (U ×ˢ K))
    (hgeo : ∀ a ∈ U, IsLRegularizedGeodesicOn (G ⟨last, hle, le_rfl⟩).flow T (fun r => β (a, r))
      (K ∩ Ioo (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last)))
    (hcenter : EqOn (fun r => β (a0, r)) (gamma ⟨last, hle, le_rfl⟩)
      (K ∩ Icc (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last)))
    (hgerm : ∀ a ∈ U, (fun r => β (a, r)) =ᶠ[𝓝 u] (fun r => α0 (a, r))) :
    ∃ J : H.StageInterval first last → Set ℝ,
      ∃ α : (j : H.StageInterval first last) → A × ℝ → (H.stage j.val).Carrier,
        J ⟨last, hle, le_rfl⟩ = K ∧
        stageFamily H first last hle G T u v gamma a0 α0 last U J α := by
  classical
  let jl : H.StageInterval first last := ⟨last, hle, le_rfl⟩
  let α := Function.update (fun (j : H.StageInterval first last) (p : A × ℝ) => gamma j p.2) jl β
  have hα : α jl = β := by simp [α]
  refine ⟨fun _ => K, α, rfl, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have heq : j = jl := Subtype.ext (le_antisymm j.property.2 hj)
    subst j
    rw [hα]
    exact ⟨hK, hconn, hstart, fun h => (lt_irrefl _ h).elim, hsmooth, hgeo, hcenter⟩
  · intro k hk hl hlast
    exact ((not_lt_of_ge (hl.trans hlast)) k.castSucc_lt_succ).elim
  · intro a ha
    change (fun r => α jl (a, r)) =ᶠ[𝓝 u] (fun r => α0 (a, r))
    rw [hα]
    exact hgerm a ha
  · intro k hk hl hlast
    exact ((not_lt_of_ge (hl.trans hlast)) k.castSucc_lt_succ).elim

private theorem exists_stage_family_step
    (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hupper : T - u ^ 2 ∈ Ioo (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (k : Fin H.eventCount) (hf : first ≤ k.castSucc) (hl : k.succ ≤ last),
      ∃ z : (H.event k).old,
        z.val.val = gamma ⟨k.castSucc, hf, k.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time k.succ)) ∧
        (H.event k).oldOutput z = gamma ⟨k.succ, hf.trans k.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time k.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    (G : (j : H.StageInterval first last) → (H.stage j.val).IncomingSlab (H.time j.val) (H.stageEndTime j.val))
    (hGmetric : ∀ j t, (G j).flow.base.metric t = H.stageMetric j.val t)
    (a0 : A) (α0 : A × ℝ → (H.stage last).Carrier) (V : Set A)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (hcross : (H.event i).RegularCrossing
      (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
      (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    (hIH : ∀ t ∈ Ioo (H.regularizedStageStart T u i.succ) (H.regularizedStageEnd T v i.succ),
      ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
        ∃ (J : H.StageInterval first last → Set ℝ)
          (α : (j : H.StageInterval first last) → A × ℝ → (H.stage j.val).Carrier),
          t ∈ J ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ ∧
          stageFamily H first last hle G T u v gamma a0 α0 i.succ U J α)
    {q : ℝ} (hq : q ∈ Ioo (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc)) :
    ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ (J : H.StageInterval first last → Set ℝ)
        (α : (j : H.StageInterval first last) → A × ℝ → (H.stage j.val).Carrier),
        q ∈ J ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ ∧
        stageFamily H first last hle G T u v gamma a0 α0 i.castSucc U J α := by
  classical
  let jo : H.StageInterval first last := ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
  let jn : H.StageInterval first last := ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
  let w := Real.sqrt (T - H.time i.succ)
  obtain ⟨huw, hwv⟩ := event_clock_strict_bounds H hu huv hupper hpast i hf hl
  have hstart := H.regularizedStageStart_castSucc_eq_event_clock ⟨hupper.1.le, hupper.2.le⟩ i hl
  have hend := H.regularizedStageEnd_succ_eq_event_clock (H.mem_stageDomain_of_mem_Ioo hpast) i hf
  obtain ⟨G₁, hG₁, C, D, hCs, hsD, W, F, S, hlocalOld, hlocalNew, haC, hDb,
    hsource, hS, hcrossW, hpullOld, hpullNew, hterminal, c, d, huc, hcw, hwd, hdv,
    hnc, hdo, hclock, eta, hη, hηnew, hηold, hstep⟩ :=
    H.exists_survivor_geodesic_family_to_older_time_of_regularizedExtendedAction_eq_regularizedCost (A := A)
      first last hle hu ⟨hupper.1.le, hupper.2.le⟩ (H.mem_stageDomain_of_mem_Ioo hpast)
      hscalar gamma hgammaAC hgammaInt hgammaNodes hmin i hf hl huw hwv hcross
  obtain ⟨t₀, ht₀⟩ := exists_between hcw
  obtain ⟨U₀, hU₀, haU₀, hU₀V, J₀, α, ht₀J, hfamily⟩ :=
    hIH t₀ ⟨hnc.trans ht₀.1, hend.symm ▸ ht₀.2⟩
  obtain ⟨hK, hKconn, hrK, _, hα, hαgeo, hαcenter⟩ := hfamily.1 jn le_rfl
  have hαgeo₁ : ∀ z ∈ U₀, IsLRegularizedGeodesicOn G₁.flow T (fun r => α jn (z, r))
      (J₀ jn ∩ Ioo (H.regularizedStageStart T u i.succ) (H.regularizedStageEnd T v i.succ)) := by
    intro z hz
    exact IsLRegularizedGeodesicOn.congr_metric (hαgeo z hz)
      (fun r hr => H.mapsTo_regularizedStage_Ioo_Ioo T u v i.succ hr.2)
      (fun r _ => (hGmetric jn _).trans (hG₁ _).symm)
  obtain ⟨U, hU, haU, hUU₀, Kβ, hKβ, hKβconn, hwKβ, hqKβ, β, hβ, hβgeo, hβcenter,
    U₁, hU₁, hUU₁, hU₁U₀, haU₁, L, hL, hLconn, ht₀L, hwL, θ, hθ, hθgeo, hθeq,
    hθcenter, hβeqOn, hβeq, hcrossβ⟩ :=
    hstep t₀ q ht₀ (hstart ▸ hq) (α jn) U₀ (J₀ jn) a0 hU₀ hK hKconn haU₀ ht₀J
      hα hαgeo₁ hαcenter
  have hw : 0 < w := hu.trans_lt huw
  have hwclock : T - w ^ 2 = H.time i.succ := by
    rw [show w ^ 2 = T - H.time i.succ from Real.sq_sqrt (Real.sqrt_pos.mp hw).le]
    ring
  have hnewClock : ∀ r ∈ Ioo c w,
      T - r ^ 2 ∈ (RealTimeInterval.closedOpen (H.time i.succ) (H.stageEndTime i.succ) G₁.lt).regular := by
    intro r hr
    have hsq := (sq_lt_sq₀ (hu.trans (huc.le.trans hr.1.le)) hw.le).mpr hr.2
    change H.time i.succ < T - r ^ 2 ∧ T - r ^ 2 < H.stageEndTime i.succ
    exact ⟨by linarith only [hsq, hwclock], (hclock r ⟨hr.1.le, hr.2.le.trans hwd.le⟩).2.trans hDb⟩
  have hnewMetric : ∀ r ∈ Ioo c w, S.base.metric (T - r ^ 2) =
      localPullMetric (G₁.flow.base.metric (T - r ^ 2)) (fun z : W => F z.val) hlocalNew := by
    intro r hr
    rw [hG₁]
    exact hpullNew _ ⟨(hnewClock r hr).1.le, (hclock r ⟨hr.1.le, hr.2.le.trans hwd.le⟩).2.le⟩
  let L₁ := L ∩ Ioo c d
  have hL₁ : IsOpen L₁ := hL.inter isOpen_Ioo
  have hL₁conn : IsPreconnected L₁ := (hLconn.ordConnected.inter ordConnected_Ioo).isPreconnected
  have ht₀L₁ : t₀ ∈ L₁ := ⟨ht₀L, ht₀.1, ht₀.2.trans hwd⟩
  have hwL₁ : w ∈ L₁ := ⟨hwL, hcw, hwd⟩
  have hθcenter₁ : EqOn (fun r => F (θ (a0, r)).val) (gamma jn) (L₁ ∩ Icc c w) := by
    intro r hr
    exact (congrArg (fun z : W => F z.val) (hθcenter hr.1)).trans (hηnew hr.2)
  obtain ⟨Kδ, hKδ, hKδconn, hrKδ, hwKδ, δ, hδ, hδeq, hδw, hδgeo, hδcenter, hδθ⟩ :=
    exists_recent_family_patch G₁ S
      (fun z : W => F z.val) hlocalNew T hnc ht₀ hwd hnewClock hnewMetric hU hUU₀ haU
      hK hKconn hrK ht₀J hL₁ hL₁conn ht₀L₁ hwL₁ hα
      (hθ.mono (prod_mono hUU₁ inter_subset_left))
      (by simpa only [hend] using hαgeo₁)
      (fun z hz r hr => hθgeo z (hUU₁ hz) r hr.1)
      (fun p hp => hθeq ⟨hUU₁ hp.1, ⟨hp.2.1.1.1, hp.2.1.2⟩, hp.2.2⟩)
      (by simpa only [jn, hend] using hαcenter) hθcenter₁
  have hβgeo₁ : ∀ z ∈ U, IsLRegularizedGeodesicOn (G jo).flow T (fun r => β (z, r))
      (Kβ ∩ Ioo (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc)) := by
    intro z hz
    apply IsLRegularizedGeodesicOn.congr_metric (by simpa only [hstart] using hβgeo z hz)
      (fun r hr => H.mapsTo_regularizedStage_Ioo_Ioo T u v i.castSucc hr.2)
    intro r _
    rw [hGmetric]
    simp only [jo, stageMetric, Fin.lastCases_castSucc]
  have hδgeo₁ : ∀ z ∈ U, IsLRegularizedGeodesicOn (G jn).flow T (fun r => δ (z, r))
      (Kδ ∩ Ioo (H.regularizedStageStart T u i.succ) (H.regularizedStageEnd T v i.succ)) := by
    intro z hz
    apply IsLRegularizedGeodesicOn.congr_metric (by simpa only [hend] using hδgeo z hz)
      (fun r hr => H.mapsTo_regularizedStage_Ioo_Ioo T u v i.succ hr.2)
    intro r _
    exact (hG₁ _).trans (hGmetric jn _).symm
  have hδuniform : ∀ᶠ r in 𝓝 (H.regularizedStageStart T u i.succ),
      ∀ z ∈ U, δ (z, r) = α jn (z, r) := by
    filter_upwards [(hK.inter isOpen_Iio).mem_nhds ⟨hrK, hnc.trans hcw⟩] with r hr
    intro z hz
    exact hδeq ⟨hz, hr⟩
  have hseam : seamFamily H i T U β δ := by
    refine ⟨C, D, hCs, hsD, W, F, S, hlocalOld, hlocalNew, haC, hDb, hsource, hS,
      hcrossW, hpullOld, hpullNew, hterminal, L₁, hL₁, ⟨⟨w, hwL₁⟩, hL₁conn⟩,
      hwL₁, (fun r hr => hclock r ⟨hr.2.1.le, hr.2.2.le⟩), θ,
      hθ.mono (prod_mono hUU₁ inter_subset_left), (fun z hz r hr => hθgeo z (hUU₁ hz) r hr.1), ?_, ?_⟩
    · intro p hp
      exact hβeqOn ⟨hp.1, hp.2, hp.2.2.2.trans hdo⟩
    · intro p hp
      exact hδθ ⟨hp.1, hp.2, hp.2.2⟩
  have hδcross : ∀ z ∈ U, (H.event i).RegularCrossing (β (z, w)) (δ (z, w)) := by
    intro z hz
    rw [hδw z hz]
    exact hcrossβ z hz
  have hclockLater : ∀ (k : Fin H.eventCount), i.succ ≤ k.castSucc → k.succ ≤ last → k.castSucc = i.succ →
      Real.sqrt (T - H.time k.succ) = H.regularizedStageStart T u i.succ := by
    intro k _ hkl heq
    have hh := H.regularizedStageStart_castSucc_eq_event_clock ⟨hupper.1.le, hupper.2.le⟩ k hkl
    simpa only [heq] using hh.symm
  have hclockPole : last = i.succ → u = H.regularizedStageStart T u i.succ := by
    intro heq
    exact (H.regularizedStageStart_eq_of_mem_Icc hu (by rw [← heq]; exact ⟨hupper.1.le, hupper.2.le⟩)).symm
  obtain ⟨J, α', hJo, _, hfamily'⟩ := stage_family_update H first last hle G T u v gamma a0 α0 i hf hl
    hUU₀ J₀ α hfamily Kβ Kδ β δ hKβ hKβconn (hstart.symm ▸ hwKβ) hβ hβgeo₁
    (by simpa only [hstart] using hβcenter)
    hKδ hKδconn hrKδ (hend.symm ▸ hwKδ) hδ hδgeo₁
    (by simpa only [hend] using hδcenter) hδuniform hseam hδcross hclockLater hclockPole
  exact ⟨U, hU, haU, hUU₀.trans hU₀V, J, α', hJo.symm ▸ hqKβ, hfamily'⟩

private theorem reverse_stage_induction
    {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)}
    (P : Fin (H.eventCount + 1) → Prop) (hle : first ≤ last) (hbase : P last)
    (hstep : ∀ i : Fin H.eventCount, first ≤ i.castSucc → i.succ ≤ last → P i.succ → P i.castSucc) :
    P first := by
  have hrec : ∀ j : Fin (H.eventCount + 1), first ≤ j → j ≤ last → P j := by
    intro j
    induction j using Fin.reverseInduction with
    | last =>
        intro _ h
        have hj : Fin.last H.eventCount = last := le_antisymm h (Fin.le_last _)
        simpa only [hj] using hbase
    | cast i ih =>
        intro hf hl
        by_cases heq : i.castSucc = last
        · simpa only [heq] using hbase
        · exact hstep i hf (Fin.castSucc_lt_iff_succ_le.mp (lt_of_le_of_ne hl heq))
            (ih (hf.trans i.castSucc_lt_succ.le) (Fin.castSucc_lt_iff_succ_le.mp (lt_of_le_of_ne hl heq)))
  exact hrec first le_rfl hle


private theorem exists_stage_family
    (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hupper : T - u ^ 2 ∈ Ioo (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (k : Fin H.eventCount) (hf : first ≤ k.castSucc) (hl : k.succ ≤ last),
      ∃ z : (H.event k).old,
        z.val.val = gamma ⟨k.castSucc, hf, k.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time k.succ)) ∧
        (H.event k).oldOutput z = gamma ⟨k.succ, hf.trans k.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time k.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    (G : (j : H.StageInterval first last) → (H.stage j.val).IncomingSlab (H.time j.val) (H.stageEndTime j.val))
    (hGmetric : ∀ j t, (G j).flow.base.metric t = H.stageMetric j.val t)
    (a0 : A) (α0 : A × ℝ → (H.stage last).Carrier) (V : Set A) (K₀ : Set ℝ)
    (hV : IsOpen V) (haV : a0 ∈ V) (hK₀ : IsOpen K₀) (huK₀ : u ∈ K₀)
    (hα0 : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ α0 (V ×ˢ K₀))
    (hα0geo : ∀ a ∈ V, IsLRegularizedGeodesicOn (G ⟨last, hle, le_rfl⟩).flow T (fun r => α0 (a, r))
      (K₀ ∩ Ioo (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last)))
    (hα0center : EqOn (fun r => α0 (a0, r)) (gamma ⟨last, hle, le_rfl⟩)
      (K₀ ∩ Icc (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last)))
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    {q : ℝ} (hq : q ∈ Ioo (H.regularizedStageStart T u first) (H.regularizedStageEnd T v first)) :
    ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ (J : H.StageInterval first last → Set ℝ)
        (α : (j : H.StageInterval first last) → A × ℝ → (H.stage j.val).Carrier),
        q ∈ J ⟨first, le_rfl, hle⟩ ∧
        stageFamily H first last hle G T u v gamma a0 α0 first U J α := by
  let P (f : Fin (H.eventCount + 1)) : Prop :=
    ∀ (hf : first ≤ f) (hl : f ≤ last), ∀ q ∈ Ioo (H.regularizedStageStart T u f) (H.regularizedStageEnd T v f),
      ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
        ∃ (J : H.StageInterval first last → Set ℝ)
          (α : (j : H.StageInterval first last) → A × ℝ → (H.stage j.val).Carrier),
          q ∈ J ⟨f, hf, hl⟩ ∧ stageFamily H first last hle G T u v gamma a0 α0 f U J α
  have hbase : P last := by
    intro _ _ b hb
    let jl : H.StageInterval first last := ⟨last, hle, le_rfl⟩
    have hγ := stage_geodesic_of_minimizer H last (G jl).flow (hGmetric jl) rfl
      first last hle hu huv.le ⟨hupper.1.le, hupper.2.le⟩ (H.mem_stageDomain_of_mem_Ioo hpast)
      hscalar gamma hgammaAC hgammaInt hgammaNodes hmin hle le_rfl
    have hstart : H.regularizedStageStart T u last = u :=
      H.regularizedStageStart_eq_of_mem_Icc hu ⟨hupper.1.le, hupper.2.le⟩
    obtain ⟨l, r, hur, hlr⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hK₀.mem_nhds huK₀)
    have hα : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ α0 (V ×ˢ Ioo l r) :=
      hα0.mono (prod_mono subset_rfl hlr)
    obtain ⟨U, hU, haU, hUV, K, hK, hKconn, huK, hbK, β, hβ, hβgeo, hβcenter, hgerm⟩ :=
      exists_lRegularizedGeodesicFamily_extension_preserving_boundary_germ (G jl).flow (G jl).equation T
        hV haV isOpen_Ioo isPreconnected_Ioo hur (hstart ▸ hb) hα
        (fun a ha t ht => hα0geo a ha t ⟨hlr ht.1, hstart.symm ▸ ht.2⟩)
        (hstart ▸ hγ) (fun t ht => hα0center ⟨hlr ht.1, hstart.symm ▸ ht.2⟩)
    obtain ⟨J, α, hJl, hfamily⟩ := stage_family_last H first last hle G T u v gamma a0 α0 U K β
      hK hKconn (hstart.symm ▸ huK) hβ (by simpa only [hstart] using hβgeo)
      (by simpa only [hstart] using hβcenter) hgerm
    exact ⟨U, hU, haU, hUV, J, α, hJl.symm ▸ hbK, hfamily⟩
  have hstep : ∀ i : Fin H.eventCount, first ≤ i.castSucc → i.succ ≤ last → P i.succ → P i.castSucc := by
    intro i hf hl hIH _ _ b hb
    exact exists_stage_family_step H first last hle hu huv hupper hpast hscalar gamma
      hgammaAC hgammaInt hgammaNodes hmin G hGmetric a0 α0 V i hf hl (hcross i hf hl)
      (hIH (hf.trans i.castSucc_lt_succ.le) hl) hb
  exact (reverse_stage_induction P hle hbase hstep) le_rfl hle q hq


private theorem exists_stage_family_on_prefix
    (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hupper : T - u ^ 2 ∈ Ioo (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (k : Fin H.eventCount) (hf : first ≤ k.castSucc) (hl : k.succ ≤ last),
      ∃ z : (H.event k).old,
        z.val.val = gamma ⟨k.castSucc, hf, k.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time k.succ)) ∧
        (H.event k).oldOutput z = gamma ⟨k.succ, hf.trans k.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time k.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    (G : (j : H.StageInterval first last) → (H.stage j.val).IncomingSlab (H.time j.val) (H.stageEndTime j.val))
    (hGmetric : ∀ j t, (G j).flow.base.metric t = H.stageMetric j.val t)
    (a0 : A) (α0 : A × ℝ → (H.stage last).Carrier) (V : Set A) (K₀ : Set ℝ)
    (hV : IsOpen V) (haV : a0 ∈ V) (hK₀ : IsOpen K₀) (huK₀ : u ∈ K₀)
    (hα0 : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ α0 (V ×ˢ K₀))
    (hα0geo : ∀ a ∈ V, IsLRegularizedGeodesicOn (G ⟨last, hle, le_rfl⟩).flow T (fun r => α0 (a, r))
      (K₀ ∩ Ioo (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last)))
    (hα0center : EqOn (fun r => α0 (a0, r)) (gamma ⟨last, hle, le_rfl⟩)
      (K₀ ∩ Icc (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last)))
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    {q : ℝ} (hq : q ∈ Ioo (H.regularizedStageStart T u first) (H.regularizedStageEnd T v first)) :
    ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ (J : H.StageInterval first last → Set ℝ)
        (α : (j : H.StageInterval first last) → A × ℝ → (H.stage j.val).Carrier),
        Icc (H.regularizedStageStart T u first) q ⊆ J ⟨first, le_rfl, hle⟩ ∧
        (∀ j : H.StageInterval first last,
          IsOpen (J j) ∧ IsConnected (J j) ∧
          (first < j.val → Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ⊆ J j) ∧
          ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ (α j) (U ×ˢ J j) ∧
          (∀ a ∈ U, IsLRegularizedGeodesicOn (G j).flow T (fun r => α j (a, r))
            (J j ∩ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))) ∧
          EqOn (fun r => α j (a0, r)) (gamma j)
            (J j ∩ Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))) ∧
        (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∀ a ∈ U, (H.event i).RegularCrossing
            (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (a, Real.sqrt (T - H.time i.succ)))
            (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (a, Real.sqrt (T - H.time i.succ)))) ∧
        (∀ a ∈ U,
          α ⟨last, hle, le_rfl⟩ (a, u) = α0 (a, u) ∧
          lVelocity (I := ThreeModel) (fun r => α ⟨last, hle, le_rfl⟩ (a, r)) u =
            lVelocity (I := ThreeModel) (fun r => α0 (a, r)) u ∧
          (fun r => α ⟨last, hle, le_rfl⟩ (a, r)) =ᶠ[𝓝 u] (fun r => α0 (a, r))) ∧
        ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          seamFamily H i T U
            (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
            (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) := by
  obtain ⟨U, hU, haU, hUV, J, α, hqJ, hfamily⟩ :=
    exists_stage_family H first last hle hu huv hupper hpast hscalar gamma hgammaAC hgammaInt
      hgammaNodes hmin G hGmetric a0 α0 V K₀ hV haV hK₀ huK₀ hα0 hα0geo hα0center hcross hq
  refine ⟨U, hU, haU, hUV, J, α, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := hfamily.1 ⟨first, le_rfl, hle⟩ le_rfl
    exact hh.2.1.ordConnected.out hh.2.2.1 hqJ
  · intro j
    obtain ⟨hJ, hconn, hstart, hend, hsmooth, hgeo, hcenter⟩ := hfamily.1 j j.property.1
    exact ⟨hJ, ⟨⟨_, hstart⟩, hconn⟩, fun hj => hconn.ordConnected.out hstart (hend hj),
      hsmooth, hgeo, hcenter⟩
  · intro i hf hl
    exact hfamily.2.1 i hf hl hf
  · intro a ha
    have hg := hfamily.2.2.1 a ha
    refine ⟨hg.self_of_nhds, ?_, hg⟩
    unfold lVelocity
    exact congrArg (fun L : ℝ →L[ℝ] ThreeSpace => L (1 : ℝ))
      (hg.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel))
  · intro i hf hl
    exact hfamily.2.2.2 i hf hl hf

theorem exists_regularizedGeodesic_family_on_stage_prefix_of_regularizedExtendedAction_eq_regularizedCost
    (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hupper : T - u ^ 2 ∈ Ioo (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    (G₀ : (H.stage last).IncomingSlab (H.time last) (H.stageEndTime last))
    (hG₀metric : ∀ t, G₀.flow.base.metric t = H.stageMetric last t)
    (a0 : A) (α0 : A × ℝ → (H.stage last).Carrier) (V : Set A) (K₀ : Set ℝ)
    (hV : IsOpen V) (haV : a0 ∈ V) (hK₀ : IsOpen K₀) (huK₀ : u ∈ K₀)
    (hα0 : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ α0 (V ×ˢ K₀))
    (hα0geo : ∀ a ∈ V, IsLRegularizedGeodesicOn G₀.flow T (fun r => α0 (a, r))
      (K₀ ∩ Ioo (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last)))
    (hα0center : EqOn (fun r => α0 (a0, r)) (gamma ⟨last, hle, le_rfl⟩)
      (K₀ ∩ Icc (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last)))
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    {q : ℝ} (hq : q ∈ Ioo (H.regularizedStageStart T u first) (H.regularizedStageEnd T v first)) :
    ∃ G : (j : H.StageInterval first last) → (H.stage j.val).IncomingSlab (H.time j.val) (H.stageEndTime j.val),
      (∀ j t, (G j).flow.base.metric t = H.stageMetric j.val t) ∧
    ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ (J : H.StageInterval first last → Set ℝ)
        (α : (j : H.StageInterval first last) → A × ℝ → (H.stage j.val).Carrier),
        Icc (H.regularizedStageStart T u first) q ⊆ J ⟨first, le_rfl, hle⟩ ∧
        (∀ j : H.StageInterval first last,
          IsOpen (J j) ∧ IsConnected (J j) ∧
          (first < j.val → Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ⊆ J j) ∧
          ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ (α j) (U ×ˢ J j) ∧
          (∀ a ∈ U, IsLRegularizedGeodesicOn (G j).flow T (fun r => α j (a, r))
            (J j ∩ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))) ∧
          EqOn (fun r => α j (a0, r)) (gamma j)
            (J j ∩ Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))) ∧
        (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∀ a ∈ U, (H.event i).RegularCrossing
            (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (a, Real.sqrt (T - H.time i.succ)))
            (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (a, Real.sqrt (T - H.time i.succ)))) ∧
        (∀ a ∈ U,
          α ⟨last, hle, le_rfl⟩ (a, u) = α0 (a, u) ∧
          lVelocity (I := ThreeModel) (fun r => α ⟨last, hle, le_rfl⟩ (a, r)) u =
            lVelocity (I := ThreeModel) (fun r => α0 (a, r)) u ∧
          (fun r => α ⟨last, hle, le_rfl⟩ (a, r)) =ᶠ[𝓝 u] (fun r => α0 (a, r))) ∧
        ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          let αold := α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          let αnew := α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          ∃ (C D : ℝ) (hCs : C < H.time i.succ) (hsD : H.time i.succ < D)
            (W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen)
            (F : PartialDiffeomorph ThreeModel ThreeModel
              (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞)
            (S : SolutionOn (I := ThreeModel) (M := W) (RealTimeInterval.closed C D (hCs.trans hsD).le))
            (hlocalOld : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => z.val.val))
            (hlocalNew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => F z.val)),
            H.time i.castSucc < C ∧ D < H.stageEndTime i.succ ∧ F.source = W ∧ IsSolutionOn S ∧
            (∀ z : W, (H.event i).RegularCrossing z.val.val (F z.val)) ∧
            (∀ t ∈ Ico C (H.time i.succ), S.base.metric t =
              localPullMetric (H.stageMetric i.castSucc t) (fun z : W => z.val.val) hlocalOld) ∧
            (∀ t ∈ Icc (H.time i.succ) D, S.base.metric t =
              localPullMetric (H.stageMetric i.succ t) (fun z : W => F z.val) hlocalNew) ∧
            S.base.metric (H.time i.succ) = (H.event i).terminal.metric.restrictOpen W ∧
            ∃ L : Set ℝ, IsOpen L ∧ IsConnected L ∧ Real.sqrt (T - H.time i.succ) ∈ L ∧
              (∀ r ∈ L, T - r ^ 2 ∈ Ioo C D) ∧
              ∃ θ : A × ℝ → W,
                ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ θ (U ×ˢ L) ∧
                (∀ a ∈ U, IsLRegularizedGeodesicOn S T (fun r => θ (a, r)) L) ∧
                EqOn αold (fun p : A × ℝ => (θ p).val.val) (U ×ˢ L) ∧
                EqOn αnew (fun p : A × ℝ => F (θ p).val) (U ×ˢ L) := by
  have hgammaNodes : ∀ (k : Fin H.eventCount) (hf : first ≤ k.castSucc) (hl : k.succ ≤ last),
      ∃ z : (H.event k).old,
        z.val.val = gamma ⟨k.castSucc, hf, k.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time k.succ)) ∧
        (H.event k).oldOutput z = gamma ⟨k.succ, hf.trans k.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time k.succ)) := by
    intro i hf hl
    obtain ⟨z, _, hz, hzq⟩ := hcross i hf hl
    exact ⟨z, hz, hzq⟩
  have hstageTime (j : H.StageInterval first last) : H.time j.val < H.stageEndTime j.val := by
    cases hjeq : j.val using Fin.lastCases with
    | last =>
      have hlast : last = Fin.last H.eventCount := le_antisymm (Fin.le_last _) (by simpa only [hjeq] using j.property.2)
      simpa only [hlast, H.stageEndTime_last] using hupper.1.trans hupper.2
    | cast i => simpa only [hjeq, H.stageEndTime_castSucc] using H.time_strictMono i.castSucc_lt_succ
  choose G hGmetric using fun j : H.StageInterval first last => exists_stage_incomingSlab_metric H j.val (hstageTime j)
  have hgeo : ∀ a ∈ V, IsLRegularizedGeodesicOn (G ⟨last, hle, le_rfl⟩).flow T (fun r => α0 (a, r))
      (K₀ ∩ Ioo (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last)) := by
    intro a ha
    exact IsLRegularizedGeodesicOn.congr_metric (hα0geo a ha)
      (fun r hr => H.mapsTo_regularizedStage_Ioo_Ioo T u v last hr.2)
      (fun r _ => (hG₀metric _).trans (hGmetric ⟨last, hle, le_rfl⟩ _).symm)
  exact ⟨G, hGmetric, exists_stage_family_on_prefix H first last hle hu huv hupper hpast hscalar gamma
    hgammaAC hgammaInt hgammaNodes hmin G hGmetric a0 α0 V K₀ hV haV hK₀ huK₀ hα0 hgeo hα0center hcross hq⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Bundle Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u})

theorem exists_regularizedGeodesic_extension_at_ordinary_endpoint_of_regularizedExtendedAction_eq_regularizedCost
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) D)
    (hS : IsSolutionOn S) (hmetric : ∀ t, S.base.metric t = H.stageMetric first t)
    (hregular : D.regular = Ioo (H.time first) (H.stageEndTime first)) :
    ∃ c ∈ Ioo (H.regularizedStageStart T u first) v,
      ∃ U : Set ℝ, IsOpen U ∧ Icc c v ⊆ U ∧
        ∃ β : ℝ → (H.stage first).Carrier,
          ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ β U ∧
          IsLRegularizedGeodesicOn S T β U ∧
          EqOn β (gamma ⟨first, le_rfl, hle⟩) (Icc c v) := by
  let j : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  have hpast' : T - v ^ 2 ∈ H.stageDomain first := H.mem_stageDomain_of_mem_Ioo hpast
  have hv0 : 0 < v := hu.trans_lt huv
  have huv2 : u ^ 2 < v ^ 2 := (sq_lt_sq₀ hu (hu.trans huv.le)).mpr huv
  have hinterval : H.regularizedStageStart T u first < v := by
    apply (Real.sqrt_lt' hv0).mpr
    have hh := lt_min (show T - v ^ 2 < T - u ^ 2 by linarith) hpast.2
    linarith
  have hend : H.regularizedStageEnd T v first = v := H.regularizedStageEnd_eq_of_mem_stageDomain hv0.le hpast'
  obtain ⟨c, hsc, hcv⟩ := exists_between hinterval
  have hwhole : IsLRegularizedGeodesicOn S T (gamma j)
      (Ioo (H.regularizedStageStart T u first) v) := by
    have hh := stage_geodesic_of_minimizer H first S hmetric hregular first last hle hu huv.le
      hupper hpast' hscalar gamma hgammaAC hgammaInt hgammaNodes hmin le_rfl hle
    simpa only [j, hend] using hh
  have hclock (r : ℝ) (hr : r ∈ Icc c v) : T - r ^ 2 ∈ D.regular := by
    rw [hregular]
    rcases hr.2.eq_or_lt with heq | hlt
    · simpa only [heq] using hpast
    · exact H.mapsTo_regularizedStage_Ioo_Ioo T u v first ⟨hsc.trans_le hr.1, by simpa only [hend] using hlt⟩
  have hlag (α : ℝ → (H.stage first).Carrier) : H.stageRegularizedLagrangian first T α = lRegularizedLagrangian S T α := by
    funext r
    unfold stageRegularizedLagrangian lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
    rw [hmetric]
  have hact (α : ℝ → (H.stage first).Carrier) (p q : ℝ) : H.stageRegularizedAction first T α p q = lRegularizedAction S T α p q := by
    unfold stageRegularizedAction lRegularizedAction
    rw [hlag]
  have hAC : Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j) (H.regularizedStageStart T u first) v := by
    simpa only [j, hend] using hgammaAC j
  have hint : IntervalIntegrable (lRegularizedLagrangian S T (gamma j)) volume (H.regularizedStageStart T u first) v := by
    simpa only [j, hend, hlag] using hgammaInt j
  have hminimal (δ : ℝ → (H.stage first).Carrier)
      (hδ : Manifold.absolutelyContinuousOnInterval ThreeModel δ (H.regularizedStageStart T u first) v)
      (hδint : IntervalIntegrable (lRegularizedLagrangian S T δ) volume (H.regularizedStageStart T u first) v)
      (hδs : δ (H.regularizedStageStart T u first) = gamma j (H.regularizedStageStart T u first))
      (hδv : δ v = gamma j v) :
      lRegularizedAction S T (gamma j) (H.regularizedStageStart T u first) v ≤
        lRegularizedAction S T δ (H.regularizedStageStart T u first) v := by
    have hh := H.stageRegularizedAction_le_of_regularizedExtendedAction_eq_regularizedCost first last hle hu huv.le hupper hpast'
      hscalar gamma hgammaAC hgammaInt hgammaNodes hmin j δ
      (by simpa only [j, hend] using hδ) (by simpa only [j, hend, hlag] using hδint) hδs
      (by simpa only [j, hend] using hδv)
    simpa only [j, hend, hact] using hh
  have hsub : uIcc c v ⊆ uIcc (H.regularizedStageStart T u first) v := by
    rw [uIcc_of_le hcv.le, uIcc_of_le hinterval.le]
    exact Icc_subset_Icc hsc.le le_rfl
  have hminSub := lRegularizedAction_minimal_on_subinterval_of_absolutelyContinuousOnInterval S T
    (H.regularizedStageStart T u first) c v v hsc.le hcv.le le_rfl (gamma j) hAC hint hminimal
  let : TopologicalSpace.MetrizableSpace (H.stage first).Carrier := Manifold.metrizableSpace ThreeModel (H.stage first).Carrier
  let : PseudoMetricSpace (H.stage first).Carrier := TopologicalSpace.pseudoMetrizableSpacePseudoMetric (H.stage first).Carrier
  have hC1 := lMinCurve_c1_of_absolutelyContinuousOnInterval S hS T c v hcv (gamma j)
    (Manifold.absolutelyContinuousOnInterval_mono hAC hsub) (hint.mono_set hsub) hclock
    (fun δ hδ hδc hδv => hminSub δ (Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hδ.contMDiffOn)
      (intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one S hS.smoothMetric ⟨hS.scalarCont⟩ T c v hcv.le δ hδ.contMDiffOn hclock) hδc hδv)
  obtain ⟨d, hd, U, hU, hI, β, hβ, hβgeo, hβeq⟩ := exists_lRegularizedGeodesic_smooth_tail_of_contMDiffOn_one S hS T hcv hC1
    (by rw [hregular]; exact hpast) (fun r hr => hwhole r ⟨hsc.trans hr.1, hr.2⟩)
  exact ⟨d, ⟨hsc.trans hd.1, hd.2⟩, U, hU, hI, β, hβ, hβgeo, hβeq⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Bundle Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff _root_.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u vA
variable {A : Type vA} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem exists_regularizedGeodesic_family_of_regularizedExtendedAction_eq_regularizedCost
    (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hupper : T - u ^ 2 ∈ Ioo (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    (G₀ : (H.stage last).IncomingSlab (H.time last) (H.stageEndTime last))
    (hG₀metric : ∀ t, G₀.flow.base.metric t = H.stageMetric last t)
    (a0 : A) (α0 : A × ℝ → (H.stage last).Carrier) (V : Set A) (K₀ : Set ℝ)
    (hV : IsOpen V) (haV : a0 ∈ V) (hK₀ : IsOpen K₀) (huK₀ : u ∈ K₀)
    (hα0 : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ α0 (V ×ˢ K₀))
    (hα0geo : ∀ a ∈ V, IsLRegularizedGeodesicOn G₀.flow T (fun r => α0 (a, r))
      (K₀ ∩ Ioo (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last)))
    (hα0center : EqOn (fun r => α0 (a0, r)) (gamma ⟨last, hle, le_rfl⟩)
      (K₀ ∩ Icc (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last)))
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    : ∃ G : (j : H.StageInterval first last) → (H.stage j.val).IncomingSlab (H.time j.val) (H.stageEndTime j.val),
      (∀ j t, (G j).flow.base.metric t = H.stageMetric j.val t) ∧
    ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ (J : H.StageInterval first last → Set ℝ)
        (α : (j : H.StageInterval first last) → A × ℝ → (H.stage j.val).Carrier),
        (∀ j : H.StageInterval first last,
          IsOpen (J j) ∧ IsConnected (J j) ∧
          Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ⊆ J j ∧
          ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ (α j) (U ×ˢ J j) ∧
          (∀ a ∈ U, IsLRegularizedGeodesicOn (G j).flow T (fun r => α j (a, r))
            (J j ∩ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))) ∧
          EqOn (fun r => α j (a0, r)) (gamma j)
            (J j ∩ Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))) ∧
        (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∀ a ∈ U, (H.event i).RegularCrossing
            (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (a, Real.sqrt (T - H.time i.succ)))
            (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (a, Real.sqrt (T - H.time i.succ)))) ∧
        (∀ a ∈ U, IsLRegularizedGeodesicOn (G ⟨first, le_rfl, hle⟩).flow T
          (fun r => α ⟨first, le_rfl, hle⟩ (a, r)) (J ⟨first, le_rfl, hle⟩ ∩ Ioi (H.regularizedStageStart T u first))) ∧
        (∀ a ∈ U,
          α ⟨last, hle, le_rfl⟩ (a, u) = α0 (a, u) ∧
          lVelocity (I := ThreeModel) (fun r => α ⟨last, hle, le_rfl⟩ (a, r)) u =
            lVelocity (I := ThreeModel) (fun r => α0 (a, r)) u ∧
          (fun r => α ⟨last, hle, le_rfl⟩ (a, r)) =ᶠ[𝓝 u] (fun r => α0 (a, r))) ∧
        ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          let αold := α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          let αnew := α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          ∃ (C D : ℝ) (hCs : C < H.time i.succ) (hsD : H.time i.succ < D)
            (W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen)
            (F : PartialDiffeomorph ThreeModel ThreeModel
              (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞)
            (S : SolutionOn (I := ThreeModel) (M := W) (RealTimeInterval.closed C D (hCs.trans hsD).le))
            (hlocalOld : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => z.val.val))
            (hlocalNew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => F z.val)),
            H.time i.castSucc < C ∧ D < H.stageEndTime i.succ ∧ F.source = W ∧ IsSolutionOn S ∧
            (∀ z : W, (H.event i).RegularCrossing z.val.val (F z.val)) ∧
            (∀ t ∈ Ico C (H.time i.succ), S.base.metric t =
              localPullMetric (H.stageMetric i.castSucc t) (fun z : W => z.val.val) hlocalOld) ∧
            (∀ t ∈ Icc (H.time i.succ) D, S.base.metric t =
              localPullMetric (H.stageMetric i.succ t) (fun z : W => F z.val) hlocalNew) ∧
            S.base.metric (H.time i.succ) = (H.event i).terminal.metric.restrictOpen W ∧
            ∃ L : Set ℝ, IsOpen L ∧ IsConnected L ∧ Real.sqrt (T - H.time i.succ) ∈ L ∧
              (∀ r ∈ L, T - r ^ 2 ∈ Ioo C D) ∧
              ∃ θ : A × ℝ → W,
                ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ θ (U ×ˢ L) ∧
                (∀ a ∈ U, IsLRegularizedGeodesicOn S T (fun r => θ (a, r)) L) ∧
                EqOn αold (fun p : A × ℝ => (θ p).val.val) (U ×ˢ L) ∧
                EqOn αnew (fun p : A × ℝ => F (θ p).val) (U ×ˢ L) := by
  have hgammaNodes : ∀ (k : Fin H.eventCount) (hf : first ≤ k.castSucc) (hl : k.succ ≤ last),
      ∃ z : (H.event k).old,
        z.val.val = gamma ⟨k.castSucc, hf, k.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time k.succ)) ∧
        (H.event k).oldOutput z = gamma ⟨k.succ, hf.trans k.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time k.succ)) := by
    intro i hf hl
    obtain ⟨z, _, hz, hzq⟩ := hcross i hf hl
    exact ⟨z, hz, hzq⟩
  classical
  let jf : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  let jl : H.StageInterval first last := ⟨last, hle, le_rfl⟩
  have hend : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv.le) (H.mem_stageDomain_of_mem_Ioo hpast)
  obtain ⟨Gf, hGf⟩ := exists_stage_incomingSlab_metric H first (hpast.1.trans hpast.2)
  obtain ⟨c, hc, W, hW, htail, τ, hτ, hτgeo, hτγ⟩ :=
    H.exists_regularizedGeodesic_extension_at_ordinary_endpoint_of_regularizedExtendedAction_eq_regularizedCost
      first last hle hu huv ⟨hupper.1.le, hupper.2.le⟩ hpast hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
      Gf.flow Gf.equation hGf rfl
  obtain ⟨q, hq⟩ := exists_between hc.2
  obtain ⟨G, hGmetric, U, hU, haU, hUV, J, α, hprefix, hfamily, hnodes, hphase, hseams⟩ :=
    H.exists_regularizedGeodesic_family_on_stage_prefix_of_regularizedExtendedAction_eq_regularizedCost
      first last hle hu huv hupper hpast hscalar gamma hgammaAC hgammaInt hmin
      G₀ hG₀metric a0 α0 V K₀ hV haV hK₀ huK₀ hα0 hα0geo hα0center hcross
      ⟨hc.1.trans hq.1, hend.symm ▸ hq.2⟩
  have hsJ : H.regularizedStageStart T u first ∈ J jf := hprefix ⟨le_rfl, (hc.1.trans hq.1).le⟩
  have hqJ : q ∈ J jf := hprefix ⟨(hc.1.trans hq.1).le, le_rfl⟩
  obtain ⟨hJf, hJfconn, _, hαf, hαfgeo, hαfcenter⟩ := hfamily jf
  have hτgeo₁ : IsLRegularizedGeodesicOn (G jf).flow T τ W :=
    hτgeo.congr_metric (fun r hr => (hτgeo r hr).1)
      (fun r _ => (hGf _).trans (hGmetric jf _).symm)
  obtain ⟨U₁, hU₁, haU₁, hU₁U, K, hK, hKconn, hsK, hvK, δ, hδ, hδeq, hδgeo, hδcenter⟩ :=
    exists_lRegularizedGeodesicFamily_extension_to_boundary (G jf).flow (G jf).equation T
      hU haU hJf hJfconn.isPreconnected hsJ hqJ hc.1.le hq.1 hq.2 hαf
      (by simpa only [jf, hend] using hαfgeo) hW htail hτgeo₁ hτγ
      (by simpa only [jf, hend] using hαfcenter)
  let J' := Function.update J jf K
  let α' := Function.update α jf δ
  have hJ'f : J' jf = K := by simp [J']
  have hα'f : α' jf = δ := by simp [α']
  have hJ'eq (j : H.StageInterval first last) (hj : j ≠ jf) : J' j = J j := by simp [J', hj]
  have hα'eq (j : H.StageInterval first last) (hj : j ≠ jf) : α' j = α j := by simp [α', hj]
  have hstartv : H.regularizedStageStart T u first < v := hc.1.trans hc.2
  have hpoint (j : H.StageInterval first last) (a : A) (ha : a ∈ U₁) (r : ℝ)
      (hr : j = jf → r = H.regularizedStageStart T u first) : α' j (a, r) = α j (a, r) := by
    by_cases hj : j = jf
    · subst j
      rw [hα'f, hr rfl]
      exact hδeq ⟨ha, hsJ, hstartv⟩
    · rw [hα'eq j hj]
  refine ⟨G, hGmetric, U₁, hU₁, haU₁, hU₁U.trans hUV, J', α', ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = jf
    · subst j
      rw [hJ'f, hα'f]
      refine ⟨hK, ⟨⟨_, hsK⟩, hKconn⟩, ?_, hδ, ?_, ?_⟩
      · simpa only [jf, hend] using hKconn.ordConnected.out hsK hvK
      · intro a ha r hr
        exact hδgeo a ha r ⟨hr.1, hr.2.1⟩
      · simpa only [jf, hend] using hδcenter
    · rw [hJ'eq j hj, hα'eq j hj]
      obtain ⟨hJ, hconn, hI, hsmooth, hgeo, hcenter⟩ := hfamily j
      have hjf : first < j.val := lt_of_le_of_ne j.property.1 (fun hh => hj (Subtype.ext hh.symm))
      exact ⟨hJ, hconn, hI hjf, hsmooth.mono (prod_mono hU₁U subset_rfl),
        fun a ha => hgeo a (hU₁U ha), hcenter⟩
  · intro i hf hl a ha
    let jo : H.StageInterval first last := ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
    let jn : H.StageInterval first last := ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
    have ho : α' jo (a, Real.sqrt (T - H.time i.succ)) = α jo (a, Real.sqrt (T - H.time i.succ)) := by
      apply hpoint jo a ha
      intro hh
      have hv : i.castSucc = first := congrArg Subtype.val hh
      have heq := H.regularizedStageStart_castSucc_eq_event_clock ⟨hupper.1.le, hupper.2.le⟩ i hl
      simpa only [hv] using heq.symm
    have hn : α' jn (a, Real.sqrt (T - H.time i.succ)) = α jn (a, Real.sqrt (T - H.time i.succ)) := by
      apply hpoint jn a ha
      intro hh
      have hv : i.succ = first := congrArg Subtype.val hh
      exact ((not_lt_of_ge hf) (hv ▸ i.castSucc_lt_succ)).elim
    change (H.event i).RegularCrossing (α' jo _) (α' jn _)
    rw [ho, hn]
    exact hnodes i hf hl a (hU₁U ha)
  · intro a ha
    rw [hJ'f, hα'f]
    exact hδgeo a ha
  · intro a ha
    by_cases hj : jl = jf
    · have hv : last = first := congrArg Subtype.val hj
      have hstart : H.regularizedStageStart T u first = u := by
        rw [← hv]
        exact H.regularizedStageStart_eq_of_mem_Icc hu ⟨hupper.1.le, hupper.2.le⟩
      have hg : (fun r => α' jl (a, r)) =ᶠ[𝓝 u] (fun r => α jl (a, r)) := by
        rw [hj, hα'f]
        filter_upwards [(hJf.inter isOpen_Iio).mem_nhds ⟨hstart ▸ hsJ, huv⟩] with r hr
        exact hδeq ⟨ha, hr⟩
      refine ⟨hg.self_of_nhds.trans (hphase a (hU₁U ha)).1, ?_,
        hg.trans (hphase a (hU₁U ha)).2.2⟩
      have hvel : lVelocity (I := ThreeModel) (fun r => α' jl (a, r)) u =
          lVelocity (I := ThreeModel) (fun r => α jl (a, r)) u := by
        unfold lVelocity
        exact congrArg (fun L : ℝ →L[ℝ] ThreeSpace => L (1 : ℝ))
          (hg.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel))
      exact hvel.trans (hphase a (hU₁U ha)).2.1
    · change α' jl (a, u) = α0 (a, u) ∧ _
      rw [hα'eq jl hj]
      exact hphase a (hU₁U ha)
  · intro i hf hl
    let jo : H.StageInterval first last := ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
    let jn : H.StageInterval first last := ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
    have ho : ∀ᶠ r in 𝓝 (Real.sqrt (T - H.time i.succ)), ∀ a ∈ U₁, α' jo (a, r) = α jo (a, r) := by
      by_cases hj : jo = jf
      · have hv : i.castSucc = first := congrArg Subtype.val hj
        have hw := H.regularizedStageStart_castSucc_eq_event_clock ⟨hupper.1.le, hupper.2.le⟩ i hl
        have hw' : Real.sqrt (T - H.time i.succ) = H.regularizedStageStart T u first := by
          simpa only [hv] using hw.symm
        rw [hw', hj, hα'f]
        filter_upwards [(hJf.inter isOpen_Iio).mem_nhds ⟨hsJ, hstartv⟩] with r hr
        intro a ha
        exact hδeq ⟨ha, hr⟩
      · rw [hα'eq jo hj]
        exact Filter.Eventually.of_forall (fun _ _ _ => rfl)
    have hn : jn ≠ jf := by
      intro hh
      have hv : i.succ = first := congrArg Subtype.val hh
      exact (not_lt_of_ge hf) (hv ▸ i.castSucc_lt_succ)
    change seamFamily H i T U₁ (α' jo) (α' jn)
    apply seam_family_congr H i T (show seamFamily H i T U (α jo) (α jn) from hseams i hf hl) hU₁U ho
    rw [hα'eq jn hn]
    exact Filter.Eventually.of_forall (fun _ _ _ => rfl)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem exists_initial_family_of_contMDiffOn_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {γ : ℝ → M} {b : ℝ} (hb : 0 < b)
    (hc1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 b))
    (hclock : ∀ r ∈ Icc 0 b, T - r ^ 2 ∈ D.regular)
    (hgeo : IsLRegularizedGeodesicOn S T γ (Ioo 0 b)) :
    ∃ Z : E, ∃ V : Set E, IsOpen V ∧ Z ∈ V ∧
      ∃ K : Set ℝ, IsOpen K ∧ IsConnected K ∧ (0 : ℝ) ∈ K ∧ K ⊆ Iio b ∧
        ∃ α : E × ℝ → M,
          ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I ∞ α (V ×ˢ K) ∧
          (∀ z ∈ V, α (z, 0) = γ 0 ∧
            lVelocity (I := I) (fun r => α (z, r)) 0 = (2 : ℝ) • z ∧
            IsLRegularizedGeodesicOn S T (fun r => α (z, r)) K) ∧
          EqOn (fun r => α (Z, r)) γ (K ∩ Ici 0) := by
  obtain ⟨η, hηeq, e, he, hηgeo⟩ :=
    exists_lRegularizedExtOn S hS T 0 b hb γ hc1 hclock (fun r hr => (hgeo r hr).2)
  let J := Ioo (0 - e) (b + e)
  have h0J : (0 : ℝ) ∈ J := ⟨by linarith, by linarith⟩
  have hη0 : η 0 = γ 0 := hηeq ⟨le_rfl, hb.le⟩
  let Z : E := (1 / 2 : ℝ) • lVelocity (I := I) η 0
  have hZ : (2 : ℝ) • Z = lVelocity (I := I) η 0 := by
    change (2 : ℝ) • ((1 / 2 : ℝ) • (lVelocity (I := I) η 0 : E)) = _
    rw [smul_smul]
    norm_num
  let ζ : E → TangentBundle I M := fun z => ⟨γ 0, (2 : ℝ) • z⟩
  have hζ : ContMDiff 𝓘(ℝ, E) I.tangent ∞ ζ :=
    (DifferentialGeometry.contMDiff_tangentFiber (I := I) (n := ∞) (γ 0)).comp
      (show ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun z : E => (2 : ℝ) • z) from
        (contDiff_const.smul contDiff_id).contMDiff)
  obtain ⟨V, hV, hZV, _, C, hC, hCconn, h0C, _, α, hα, hcurves, hcenter⟩ :=
    exists_lRegularizedGeodesicFamily_to_time_of_smooth_phase S hS T
      isOpen_univ (mem_univ Z) ζ hζ.contMDiffOn isOpen_Ioo isPreconnected_Ioo h0J h0J
      hη0 hZ.symm hηgeo
  let K := C ∩ J ∩ Iio b
  have h0K : (0 : ℝ) ∈ K := ⟨⟨h0C, h0J⟩, hb⟩
  have hKconn : IsPreconnected K :=
    ((hCconn.ordConnected.inter ordConnected_Ioo).inter ordConnected_Iio).isPreconnected
  refine ⟨Z, V, hV, hZV, K, (hC.inter isOpen_Ioo).inter isOpen_Iio,
    ⟨⟨0, h0K⟩, hKconn⟩, h0K, inter_subset_right, α,
    hα.mono (prod_mono subset_rfl (inter_subset_left.trans inter_subset_left)), ?_, ?_⟩
  · intro z hz
    obtain ⟨hpos, hvel, hgeoz⟩ := hcurves z hz
    exact ⟨hpos, hvel, fun r hr => hgeoz r hr.1.1⟩
  · intro r hr
    exact (hcenter hr.1.1).trans (hηeq ⟨hr.2, hr.1.2.le⟩)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section

open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem exists_initial_family_of_history_minimum
    (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Ioo (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B 0 v gamma =
      H.regularizedCost first last hle T B 0 v
        (gamma ⟨last, hle, le_rfl⟩ 0) (gamma ⟨first, le_rfl, hle⟩ v))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := (H.stage last).Carrier) D)
    (hS : IsSolutionOn S) (hmetric : ∀ t, S.base.metric t = H.stageMetric last t)
    (hregular : D.regular = Ioo (H.time last) (H.stageEndTime last)) :
    ∃ Z : ThreeSpace, ∃ V : Set ThreeSpace, IsOpen V ∧ Z ∈ V ∧
      ∃ K : Set ℝ, IsOpen K ∧ IsConnected K ∧ (0 : ℝ) ∈ K ∧
        K ⊆ Iio (H.regularizedStageEnd T v last) ∧
        ∃ α : ThreeSpace × ℝ → (H.stage last).Carrier,
          ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ α (V ×ˢ K) ∧
          (∀ z ∈ V, α (z, 0) = gamma ⟨last, hle, le_rfl⟩ 0 ∧
            lVelocity (I := ThreeModel) (fun r => α (z, r)) 0 = (2 : ℝ) • z ∧
            IsLRegularizedGeodesicOn S T (fun r => α (z, r)) K) ∧
          EqOn (fun r => α (Z, r)) (gamma ⟨last, hle, le_rfl⟩) (K ∩ Ici 0) := by
  let j : H.StageInterval first last := ⟨last, hle, le_rfl⟩
  have hupper' : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa using (show T ∈ Icc (H.time last) (H.stageEndTime last) from ⟨hupper.1.le, hupper.2.le⟩)
  have hstart : H.regularizedStageStart T 0 last = 0 :=
    H.regularizedStageStart_eq_of_mem_Icc le_rfl hupper'
  have hend : 0 < H.regularizedStageEnd T v last := by
    apply Real.sqrt_pos.mpr
    apply sub_pos.mpr
    exact max_lt (sub_lt_self _ (sq_pos_of_pos hv)) hupper.1
  obtain ⟨b, hb, hbe⟩ := exists_between hend
  have hclock (r : ℝ) (hr : r ∈ Icc 0 b) : T - r ^ 2 ∈ D.regular := by
    rw [hregular]
    rcases hr.1.eq_or_lt with heq | hlt
    · simpa only [← heq, zero_pow (by decide : 2 ≠ 0), sub_zero] using hupper
    · exact H.mapsTo_regularizedStage_Ioo_Ioo T 0 v last
        ⟨hstart.symm ▸ hlt, hr.2.trans_lt hbe⟩
  have hlag (α : ℝ → (H.stage last).Carrier) :
      H.stageRegularizedLagrangian last T α = lRegularizedLagrangian S T α := by
    funext r
    unfold stageRegularizedLagrangian lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
    rw [hmetric]
  have hact (α : ℝ → (H.stage last).Carrier) (p q : ℝ) :
      H.stageRegularizedAction last T α p q = lRegularizedAction S T α p q := by
    unfold stageRegularizedAction lRegularizedAction
    rw [hlag]
  have hAC : Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j) 0 (H.regularizedStageEnd T v last) := by
    simpa only [j, hstart] using hgammaAC j
  have hint : IntervalIntegrable (lRegularizedLagrangian S T (gamma j)) volume 0 (H.regularizedStageEnd T v last) := by
    simpa only [j, hstart, hlag] using hgammaInt j
  have hminimal (δ : ℝ → (H.stage last).Carrier)
      (hδ : Manifold.absolutelyContinuousOnInterval ThreeModel δ 0 (H.regularizedStageEnd T v last))
      (hδint : IntervalIntegrable (lRegularizedLagrangian S T δ) volume 0 (H.regularizedStageEnd T v last))
      (hδs : δ 0 = gamma j 0)
      (hδe : δ (H.regularizedStageEnd T v last) = gamma j (H.regularizedStageEnd T v last)) :
      lRegularizedAction S T (gamma j) 0 (H.regularizedStageEnd T v last) ≤
        lRegularizedAction S T δ 0 (H.regularizedStageEnd T v last) := by
    have hh := H.stageRegularizedAction_le_of_regularizedExtendedAction_eq_regularizedCost
      first last hle le_rfl hv.le hupper' hpast hscalar gamma hgammaAC hgammaInt hgammaNodes hmin j δ
      (by simpa only [j, hstart] using hδ) (by simpa only [j, hstart, hlag] using hδint)
      (by simpa only [j, hstart] using hδs) hδe
    simpa only [j, hstart, hact] using hh
  have hsub : uIcc 0 b ⊆ uIcc 0 (H.regularizedStageEnd T v last) := by
    rw [uIcc_of_le hb.le, uIcc_of_le hend.le]
    exact Icc_subset_Icc le_rfl hbe.le
  have hminSub := lRegularizedAction_minimal_on_subinterval_of_absolutelyContinuousOnInterval S T
    0 0 b (H.regularizedStageEnd T v last) le_rfl hb.le hbe.le (gamma j) hAC hint hminimal
  let : TopologicalSpace.MetrizableSpace (H.stage last).Carrier := Manifold.metrizableSpace ThreeModel (H.stage last).Carrier
  let : PseudoMetricSpace (H.stage last).Carrier := TopologicalSpace.pseudoMetrizableSpacePseudoMetric (H.stage last).Carrier
  have hACsub := Manifold.absolutelyContinuousOnInterval_mono hAC hsub
  have hintSub := hint.mono_set hsub
  have hC1 := lMinCurve_c1_of_absolutelyContinuousOnInterval S hS T 0 b hb (gamma j)
    hACsub hintSub hclock
    (fun δ hδ hδ0 hδb => hminSub δ (Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hδ.contMDiffOn)
      (intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one S hS.smoothMetric ⟨hS.scalarCont⟩ T 0 b hb.le δ hδ.contMDiffOn hclock) hδ0 hδb)
  have hgeo := lMinCurve_regularizedGeodesicOn_of_absolutelyContinuousOnInterval_of_minimal
    S hS T 0 b (gamma j) hACsub hintSub (fun r hr => hclock r (Ioo_subset_Icc_self hr)) hminSub
  obtain ⟨Z, V, hV, hZV, K, hK, hKconn, h0K, hKb, α, hα, hcurves, hcenter⟩ :=
    exists_initial_family_of_contMDiffOn_one S hS T hb hC1 hclock hgeo
  exact ⟨Z, V, hV, hZV, K, hK, hKconn, h0K,
    fun r hr => (hKb hr).trans hbe, α, hα, hcurves, hcenter⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end


noncomputable section
open Set Bundle Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff _root_.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem exists_regularizedGeodesic_pole_family_of_regularizedExtendedAction_eq_regularizedCost
    (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Ioo (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hmin : H.regularizedExtendedAction first last T B 0 v gamma =
      H.regularizedCost first last hle T B 0 v
        (gamma ⟨last, hle, le_rfl⟩ 0) (gamma ⟨first, le_rfl, hle⟩ v))
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    : ∃ G : (j : H.StageInterval first last) → (H.stage j.val).IncomingSlab (H.time j.val) (H.stageEndTime j.val),
      (∀ j t, (G j).flow.base.metric t = H.stageMetric j.val t) ∧
    ∃ Z : ThreeSpace, ∃ U : Set ThreeSpace, IsOpen U ∧ Z ∈ U ∧
      ∃ (J : H.StageInterval first last → Set ℝ)
        (α : (j : H.StageInterval first last) → ThreeSpace × ℝ → (H.stage j.val).Carrier),
        (∀ j : H.StageInterval first last,
          IsOpen (J j) ∧ IsConnected (J j) ∧
          Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) ⊆ J j ∧
          ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ (α j) (U ×ˢ J j) ∧
          (∀ a ∈ U, IsLRegularizedGeodesicOn (G j).flow T (fun r => α j (a, r))
            (J j ∩ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))) ∧
          EqOn (fun r => α j (Z, r)) (gamma j)
            (J j ∩ Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))) ∧
        (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∀ a ∈ U, (H.event i).RegularCrossing
            (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (a, Real.sqrt (T - H.time i.succ)))
            (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (a, Real.sqrt (T - H.time i.succ)))) ∧
        (∀ a ∈ U, IsLRegularizedGeodesicOn (G ⟨first, le_rfl, hle⟩).flow T
          (fun r => α ⟨first, le_rfl, hle⟩ (a, r)) (J ⟨first, le_rfl, hle⟩ ∩ Ioi (H.regularizedStageStart T 0 first))) ∧
        (∀ z ∈ U, IsLRegularizedGeodesicOn (G ⟨last, hle, le_rfl⟩).flow T
          (fun r => α ⟨last, hle, le_rfl⟩ (z, r))
          (J ⟨last, hle, le_rfl⟩ ∩ Ico 0 (H.regularizedStageEnd T v last))) ∧
        (∀ z ∈ U,
          α ⟨last, hle, le_rfl⟩ (z, 0) = gamma ⟨last, hle, le_rfl⟩ 0 ∧
          lVelocity (I := ThreeModel) (fun r => α ⟨last, hle, le_rfl⟩ (z, r)) 0 = (2 : ℝ) • z) ∧
        ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          let αold := α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          let αnew := α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          ∃ (C D : ℝ) (hCs : C < H.time i.succ) (hsD : H.time i.succ < D)
            (W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen)
            (F : PartialDiffeomorph ThreeModel ThreeModel
              (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞)
            (S : SolutionOn (I := ThreeModel) (M := W) (RealTimeInterval.closed C D (hCs.trans hsD).le))
            (hlocalOld : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => z.val.val))
            (hlocalNew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => F z.val)),
            H.time i.castSucc < C ∧ D < H.stageEndTime i.succ ∧ F.source = W ∧ IsSolutionOn S ∧
            (∀ z : W, (H.event i).RegularCrossing z.val.val (F z.val)) ∧
            (∀ t ∈ Ico C (H.time i.succ), S.base.metric t =
              localPullMetric (H.stageMetric i.castSucc t) (fun z : W => z.val.val) hlocalOld) ∧
            (∀ t ∈ Icc (H.time i.succ) D, S.base.metric t =
              localPullMetric (H.stageMetric i.succ t) (fun z : W => F z.val) hlocalNew) ∧
            S.base.metric (H.time i.succ) = (H.event i).terminal.metric.restrictOpen W ∧
            ∃ L : Set ℝ, IsOpen L ∧ IsConnected L ∧ Real.sqrt (T - H.time i.succ) ∈ L ∧
              (∀ r ∈ L, T - r ^ 2 ∈ Ioo C D) ∧
              ∃ θ : ThreeSpace × ℝ → W,
                ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ θ (U ×ˢ L) ∧
                (∀ a ∈ U, IsLRegularizedGeodesicOn S T (fun r => θ (a, r)) L) ∧
                EqOn αold (fun p : ThreeSpace × ℝ => (θ p).val.val) (U ×ˢ L) ∧
                EqOn αnew (fun p : ThreeSpace × ℝ => F (θ p).val) (U ×ˢ L) := by
  have hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ)) := by
    intro i hf hl
    obtain ⟨z, _, hz, hzq⟩ := hcross i hf hl
    exact ⟨z, hz, hzq⟩
  obtain ⟨G₀, hG₀metric⟩ := exists_stage_incomingSlab_metric H last (hupper.1.trans hupper.2)
  obtain ⟨Z, V, hV, hZV, K₀, hK₀, _, h0K₀, _, α0, hα0, hcurves, hcenter⟩ :=
    exists_initial_family_of_history_minimum H first last hle hv hupper
      (H.mem_stageDomain_of_mem_Ioo hpast) hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
      G₀.flow G₀.equation hG₀metric rfl
  have hupper₀ : T - (0 : ℝ) ^ 2 ∈ Ioo (H.time last) (H.stageEndTime last) := by simpa using hupper
  have hstart : H.regularizedStageStart T 0 last = 0 :=
    H.regularizedStageStart_eq_of_mem_Icc le_rfl ⟨hupper₀.1.le, hupper₀.2.le⟩
  obtain ⟨G, hGmetric, U, hU, hZU, hUV, J, α, hfamily, hnodes, hfirstgeo, hphase, hseams⟩ :=
    H.exists_regularizedGeodesic_family_of_regularizedExtendedAction_eq_regularizedCost
      first last hle le_rfl hv hupper₀ hpast hscalar gamma hgammaAC hgammaInt hmin
      G₀ hG₀metric Z α0 V K₀ hV hZV hK₀ h0K₀ hα0
      (fun z hz r hr => (hcurves z hz).2.2 r hr.1)
      (fun r hr => hcenter ⟨hr.1, by simpa only [hstart, mem_Ici] using hr.2.1⟩) hcross
  refine ⟨G, hGmetric, Z, U, hU, hZU, J, α, hfamily, hnodes, hfirstgeo, ?_, ?_, hseams⟩
  · intro z hz r hr
    rcases hr.2.1.eq_or_lt with hzero | hpositive
    · have hrzero : r = 0 := hzero.symm
      subst r
      have hαgeo : IsLRegularizedGeodesicOn (G ⟨last, hle, le_rfl⟩).flow T (fun r => α0 (z, r)) K₀ :=
        ((hcurves z (hUV hz)).2.2).congr_metric
          (fun r hr => ((hcurves z (hUV hz)).2.2 r hr).1)
          (fun r _ => (hG₀metric _).trans (hGmetric ⟨last, hle, le_rfl⟩ _).symm)
      exact lRegularizedData_congr (G ⟨last, hle, le_rfl⟩).flow T 0 (hphase z hz).2.2 (hαgeo 0 h0K₀)
    · exact (hfamily ⟨last, hle, le_rfl⟩).2.2.2.2.1 z hz r
        ⟨hr.1, hstart.symm ▸ hpositive, hr.2.2⟩
  · intro z hz
    exact ⟨(hphase z hz).1.trans (hcurves z (hUV hz)).1,
      (hphase z hz).2.1.trans (hcurves z (hUV hz)).2.1⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end
