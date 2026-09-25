import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorInitialCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFirstLossIncoming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.EqualDimensionImmersion
import DifferentialGeometry.Geometry.Metric.PullbackScaling

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem exists_first_event_normalized_chart_solution_of_scalar_bound_at_later_time
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (next : Fin H.eventCount) (hnext : first ≤ next.castSucc)
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (J : X → (H.stage first).Carrier) (hJ : IsSmoothEmbedding ThreeModel ThreeModel ∞ J)
    {τ : ℝ} (G : (H.stage next.castSucc).IncomingSlab (H.time next.castSucc) τ)
    (L : G.TerminalLimitMetric)
    (hsource : ∀ t, G.flow.base.metric t = (H.event next).incoming.flow.base.metric t)
    (hterminal : L.metric =
      ((H.event next).incoming.flow.base.metric τ).restrictOpen G.terminalRegularOpen)
    (hτ : τ ∈ Ico (H.time next.castSucc) (H.time next.succ))
    (Ψ : X → H.backwardSurvivorIncomingDomain first next.castSucc hnext G)
    (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ)
    (hΨbirth : ∀ x, H.backwardSurvivorMap first next.castSucc hnext first le_rfl hnext
      (Ψ x).val = J x)
    (gflow₀ : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingDomain first next.castSucc hnext G))
    (hslabs₀ : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ next.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow₀ t = (H.backwardSurvivorSlabMetric first next.castSucc hnext j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first next.castSucc hnext G))
    (hlast₀ : ∀ t ∈ Icc (H.time next.castSucc) τ,
      gflow₀ t = H.backwardSurvivorIncomingMetric first next.castSucc hnext G L t)
    {r q C₀ a₀ Kpast : ℝ} {C : ℝ≥0}
    (hC₀ : 0 < C₀) (hq : 0 < q) (hrQ : r ≤ C₀ * q) (haq : 1 ≤ a₀ * q)
    (g₀ : SmoothRiemannianMetric ThreeModel X)
    (hzero : ∀ x (v w : TangentSpace ThreeModel x),
      g₀.inner x v w = q * (H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x w))
    {D₀ : RealTimeInterval} (S₀ : SolutionOn (I := ThreeModel) (M := X) D₀)
    (hmetric₀ : ∀ t ∈ Icc 0 (q * (τ - H.time first)), S₀.base.metric t =
      localPullMetric (scaleMetric q hq (gflow₀ (H.time first + t / q))) Ψ hΨ)
    (hpast : ∀ t ∈ Icc 0 (q * (τ - H.time first)), ∀ x : X,
      normSq0S (S₀.base.metric t) x 4 (S₀.base.rm04 t x) ≤ Kpast)
    (hscalar : ∀ x, (H.event next).incoming.flow.scalar τ (Ψ x).val.val ≤ C₀ * q)
    (hderiv : ∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        r < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last →
      ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ), τ ≤ t →
        ∀ x : (H.stage j.castSucc).Carrier,
          InFixedHamiltonIveyRegion ((H.event j).incoming.flow.base.metric t) a₀ x)
    (htime : 2 * C * C₀ * (q * (H.time last - τ)) ≤ 1)
    (hnot : ¬ range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle)) :
    ∃ (i : Fin H.eventCount) (hf : first ≤ i.castSucc),
      next.castSucc ≤ i.castSucc ∧ i.succ ≤ last ∧
      (∀ (k : Fin (H.eventCount + 1)) (hk : first ≤ k), k ≤ i.castSucc →
        range J ⊆ range (H.backwardSurvivorMap first k hk first le_rfl hk)) ∧
      ∃ Ξ : X → H.backwardSurvivorTerminalFace first i hf,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
        (∀ x, H.backwardSurvivorMap first i.castSucc hf first le_rfl hf (Ξ x).val = J x) ∧
        (∃ x : X, ∀ y : (H.stage i.succ).Carrier,
          ¬ (H.event i).RegularCrossing
            (H.backwardSurvivorTerminalFaceMap first i hf (Ξ x)).val y) ∧
        ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
          (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorTerminalFace first i hf)),
          (∀ (j : Fin H.eventCount) (hj : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
            ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
              gflow t = (H.backwardSurvivorSlabMetric first i.castSucc hf j hj hl t).restrictOpen
                (H.backwardSurvivorTerminalFace first i hf)) ∧
          (∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
            gflow t = H.backwardSurvivorTerminalFaceMetric first i hf t) ∧
          ∃ S : SolutionOn (I := ThreeModel) (M := X)
              (RealTimeInterval.closed 0 (q * (H.time i.succ - H.time first))
                (by have ht := H.time_strictMono (hf.trans_lt i.castSucc_lt_succ); positivity)),
            IsSolutionOn S ∧ S.base.metric 0 = g₀ ∧
            (∀ t, S.base.metric t =
              localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) ∧
            (∀ (x : X) (k l : Fin (Module.finrank ℝ ThreeSpace)),
              ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
                (fun z : ℝ × X => chartGramMatrix (S.base.metric z.1) x z.2 k l)
                (Icc 0 (q * (H.time i.succ - H.time first)) ×ˢ
                  (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).baseSet)) ∧
            (∀ t ∈ Icc 0 (q * (τ - H.time first)), S.base.metric t = S₀.base.metric t) ∧
            ∀ t ∈ Icc 0 (q * (H.time i.succ - H.time first)), ∀ x : X,
              normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤
                max Kpast ((2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2) := by
  have hsurvived : range J ⊆ range
      (H.backwardSurvivorMap first next.castSucc hnext first le_rfl hnext) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(Ψ x).val, hΨbirth x⟩
  have hscalarTrace (x : (H.stage next.castSucc).Carrier)
      (A : BackwardPointTrace H first next.castSucc hnext x)
      (hx : A.point first le_rfl hnext ∈ range J) :
      (H.event next).incoming.flow.scalar τ x ≤ C₀ * q := by
    obtain ⟨y, hy⟩ := hx
    let B : BackwardPointTrace H first next.castSucc hnext (Ψ y).val.val :=
      Classical.choice (Ψ y).val.property
    have he := H.backwardSurvivorMap_eq_point first next.castSucc hnext first le_rfl hnext
      (Ψ y).val B
    have hpoint := B.endpoint_eq_of_point_first_eq A
      (he.symm.trans ((hΨbirth y).trans hy))
    rw [← hpoint]
    exact hscalar y
  have htime' : 2 * C * (H.time last - τ) * (C₀ * q) ≤ 1 := by
    nlinarith [htime]
  obtain ⟨i, hf, hni, hil, hsurvives, Ξ, hΞs, hbirth, hfailed⟩ :=
    H.exists_first_event_incoming_chart_of_scalar_bound_at_later_time first last hle
      J hJ next hnext hsurvived (mul_pos hC₀ hq) le_rfl hτ hscalarTrace
      (fun j hj hl x t ht hs => hderiv j hj hl x t ht (hrQ.trans_lt hs)) htime' hnot
  have hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ := fun x =>
    Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq rfl
      (hΞs.isImmersion.isImmersionAt x)
  obtain ⟨gflow, hslabs, hlast, S, hS, hSzero, hmetric, hgram⟩ :=
    H.exists_normalized_backwardSurvivor_chart_solution first i hf Ξ hΞ J hbirth q hq g₀ hzero
  have hoverlap : ∀ t ∈ Icc 0 (q * (τ - H.time first)),
      S.base.metric t = S₀.base.metric t := by
    intro t ht
    have htphys : H.time first + t / q ∈ Icc (H.time first) τ := by
      constructor
      · exact le_add_of_nonneg_right (div_nonneg ht.1 hq.le)
      · have hh := (div_le_iff₀ hq).mpr
          (show t ≤ (τ - H.time first) * q by nlinarith [ht.2])
        linarith
    rw [hmetric t, hmetric₀ t ht, DifferentialGeometry.localPullMetric_scaleMetric, DifferentialGeometry.localPullMetric_scaleMetric]
    congr 1
    exact (H.localPullMetric_backwardSurvivorIncoming_eq_terminalFace_of_initial_eq
      first next i hnext hf hni hτ G L hsource hterminal gflow₀ gflow
      hslabs₀ hslabs hlast₀ hlast Ψ Ξ hΨ hΞ
      (fun x => (hΨbirth x).trans (hbirth x).symm) htphys).symm
  have htimei : 2 * C * C₀ * (q * (H.time i.succ - τ)) ≤ 1 := by
    calc
      2 * C * C₀ * (q * (H.time i.succ - τ)) =
          (2 * C * C₀ * q) * (H.time i.succ - τ) := by ring
      _ ≤ (2 * C * C₀ * q) * (H.time last - τ) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right (H.time_strictMono.monotone hil) τ)
          (by positivity)
      _ = 2 * C * C₀ * (q * (H.time last - τ)) := by ring
      _ ≤ 1 := htime
  have hlate := curvature_bound_normalized_backwardSurvivor_chart_of_scalar_bound_at_time
    gflow hslabs hlast Ξ hΞ next hnext hni (mul_pos hC₀ hq) hq le_rfl haq
    (fun x j hj hji t ht hs => hderiv j hj
      ((Fin.succ_le_succ_iff.mpr (Fin.castSucc_le_castSucc_iff.mp hji)).trans hil) _ t ht
      (hrQ.trans_lt hs))
    hτ (fun x => by
      have he := H.backwardSurvivorMap_eq_of_initial_eq first next.castSucc i.castSucc
        hnext hf (Ψ x).val (Ξ x).val ((hΨbirth x).trans (hbirth x).symm)
        next.castSucc hnext le_rfl hni
      have hp : (Ψ x).val.val =
          H.backwardSurvivorMap first i.castSucc hf next.castSucc hnext hni (Ξ x).val := by
        simpa only [H.backwardSurvivorMap_last] using he
      rw [← hp]
      exact hscalar x)
    (fun x j hj hji t ht hτt => hpinch j hj
      ((Fin.succ_le_succ_iff.mpr (Fin.castSucc_le_castSucc_iff.mp hji)).trans hil) t ht hτt _)
    htimei S (fun t _ => hmetric t)
  refine ⟨i, hf, hni, hil, hsurvives, Ξ, hΞs, hbirth, hfailed, hΞ, gflow,
    hslabs, hlast, S, hS, hSzero, hmetric, hgram, hoverlap, ?_⟩
  intro t ht x
  by_cases hp : t ≤ q * (τ - H.time first)
  · change normSq0S (S.base.metric t) x 4 (metricRm04At (S.base.metric t) x) ≤ _
    rw [hoverlap t ⟨ht.1, hp⟩]
    exact (hpast t ⟨ht.1, hp⟩ x).trans (le_max_left _ _)
  · exact (hlate t ⟨(lt_of_not_ge hp).le, ht.2⟩ x).trans (le_max_right _ _)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
