import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.MetricLocalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryMinimizerLocalization

noncomputable section

open Set Manifold Bundle Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Tensor0SBundle

universe u

variable (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (i : Fin H.eventCount) (hle : first ≤ i.castSucc)

private theorem exists_positive_time_scale (C r d : ℝ) (hr : 0 < r) (hd : 0 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ b : ℝ, 0 < b → b < ε →
      b ^ 2 < d ∧ 18 * Real.sqrt C * b ^ 2 ≤ Real.log 2 ∧
        288 * b ^ 4 * Real.sqrt C ≤ r ^ 2 := by
  have h1 : ∀ᶠ b : ℝ in 𝓝 0, b ^ 2 < d :=
    (continuousAt_id.pow 2).eventually (gt_mem_nhds (by simpa using hd))
  have h2 : ∀ᶠ b : ℝ in 𝓝 0, 18 * Real.sqrt C * b ^ 2 < Real.log 2 :=
    (continuousAt_const.mul (continuousAt_id.pow 2)).eventually
      (gt_mem_nhds (by simpa using (Real.log_pos (by norm_num : (1 : ℝ) < 2))))
  have h3 : ∀ᶠ b : ℝ in 𝓝 0, 288 * b ^ 4 * Real.sqrt C < r ^ 2 :=
    ((continuousAt_const.mul (continuousAt_id.pow 4)).mul continuousAt_const).eventually
      (gt_mem_nhds (by simpa using sq_pos_of_pos hr))
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.mp (h1.and (h2.and h3))
  refine ⟨ε, hε, fun b hb hbε => ?_⟩
  have hdist : dist b (0 : ℝ) < ε := by simpa only [Real.dist_eq, sub_zero, abs_of_pos hb] using hbε
  exact ⟨(hall hdist).1, (hall hdist).2.1.le, (hall hdist).2.2.le⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pos_ball_subset_backwardSurvivorFootprint
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (T : ℝ) (p : (H.event i).incoming.terminalRegularOpen) (hp : p ∈ interior K) :
    ∃ r : ℝ, 0 < r ∧
      {z | riemannianEDistOf ((H.event i).incoming.flow.base.metric T) p.val z <
        ENNReal.ofReal r} ⊆ Subtype.val '' interior K := by
  let g := (H.event i).incoming.flow.base.metric T
  let _ : IsManifold ThreeModel 1 (H.stage i.castSucc).Carrier :=
    IsManifold.of_le (n := ∞) (by decide)
  let _ : RiemannianBundle (fun z : (H.stage i.castSucc).Carrier => TangentSpace ThreeModel z) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace
      (fun z : (H.stage i.castSucc).Carrier => TangentSpace ThreeModel z) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : PseudoEMetricSpace (H.stage i.castSucc).Carrier :=
    PseudoEMetricSpace.ofRiemannianMetric ThreeModel (H.stage i.castSucc).Carrier
  have hU : IsOpen (Subtype.val '' interior K : Set (H.stage i.castSucc).Carrier) :=
    (H.event i).incoming.terminalRegularOpen.isOpen.isOpenMap_subtype_val _ isOpen_interior
  obtain ⟨ε, hε, hball⟩ := EMetric.mem_nhds_iff.mp (hU.mem_nhds ⟨p, hp, rfl⟩)
  have hpos : (0 : ℝ≥0∞) < min ε 1 := lt_min hε zero_lt_one
  have hfinite : min ε 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  refine ⟨(min ε 1).toReal, ENNReal.toReal_pos hpos.ne' hfinite, ?_⟩
  intro z hz
  apply hball
  change edist z p.val < ε
  rw [edist_comm]
  change riemannianEDistOf g p.val z < ε
  exact hz.trans_le (by rw [ENNReal.ofReal_toReal hfinite]; exact min_le_left _ _)

theorem exists_backwardSurvivor_reducedAction_minimizer_of_distance_le
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K) D)
    (hmetric : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      S.base.metric t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    (C T b r : ℝ) (hb : 0 < b) (hr : 0 < r)
    (hleft : H.time i.castSucc < T - b ^ 2) (hright : T < H.time i.succ)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ x : (H.stage i.castSucc).Carrier,
      normSq0S ((H.event i).incoming.flow.base.metric t) x 4
        ((H.event i).incoming.flow.base.rm04 t x) ≤ C)
    (x y : (H.stage i.castSucc).Carrier)
    (hdist : riemannianEDistOf ((H.event i).incoming.flow.base.metric T) x y ≤
      ENNReal.ofReal (r / 4))
    (htime : 18 * Real.sqrt C * b ^ 2 ≤ Real.log 2)
    (hsmall : 288 * b ^ 4 * Real.sqrt C ≤ r ^ 2)
    (hball : {z | riemannianEDistOf ((H.event i).incoming.flow.base.metric T) x z <
      ENNReal.ofReal r} ⊆ Subtype.val '' interior K)
 :
    ∃ β : ℝ → H.backwardSurvivorFootprintInterior first i hle K,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ β ∧
      (H.backwardSurvivorFootprintMap first i hle K (β 0)).val = x ∧
      (H.backwardSurvivorFootprintMap first i hle K (β b)).val = y ∧
      reducedAction S.base.metric T (b ^ 2) (squareRootReparametrization β) =
        reducedLength (H.event i).incoming.flow.base.metric T isRegularizedAdmissible
          x (b ^ 2) y := by
  have hn : (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 = 9 := by norm_num [ThreeSpace]
  have htime' : 2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C * b ^ 2 ≤
      Real.log 2 := by simpa only [hn, show (2 : ℝ) * 9 = 18 by norm_num] using htime
  have hsmall' : 32 * b ^ 4 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C ≤ r ^ 2 := by
    rw [hn]
    have heq : 32 * b ^ 4 * 9 * Real.sqrt C = 288 * b ^ 4 * Real.sqrt C := by ring
    simpa only [heq] using hsmall
  obtain ⟨α₀, hα₀, h0, h1, _, hgap⟩ := exists_contMDiff_curve_energy_eq_and_radius_bound
    ((H.event i).incoming.flow.base.metric T) (RiemannianMetricComplete.of_compact _)
      C b r hb hr x y hdist htime' hsmall'
  have hgap' : Real.sqrt b * Real.sqrt
      (Real.exp (18 * Real.sqrt C * b ^ 2) *
        (Real.exp (18 * Real.sqrt C * b ^ 2) *
          curveEnergy ((H.event i).incoming.flow.base.metric T) α₀ 0 b +
          72 * b ^ 3 * Real.sqrt C)) < r := by
    rw [hn] at hgap
    have h18 : (2 : ℝ) * 9 = 18 := by norm_num
    have h72 : 8 * b ^ 3 * 9 * Real.sqrt C = 72 * b ^ 3 * Real.sqrt C := by ring
    simpa only [h18, h72] using hgap
  exact H.exists_backwardSurvivor_reducedAction_minimizer first i hle K htrace S hmetric
    C T b r hb hleft hright hRm x y α₀ (hα₀.of_le (by simp)) h0 h1 hball hgap'

theorem exists_radius_time_backwardSurvivor_reducedAction_minimizer
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K) D)
    (hmetric : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      S.base.metric t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    (C T : ℝ) (hleft : H.time i.castSucc < T) (hright : T < H.time i.succ)
    (hRm : ∀ t ∈ Icc (H.time i.castSucc) T, ∀ z : (H.stage i.castSucc).Carrier,
      normSq0S ((H.event i).incoming.flow.base.metric t) z 4
        ((H.event i).incoming.flow.base.rm04 t z) ≤ C)
    (p : (H.event i).incoming.terminalRegularOpen) (hp : p ∈ interior K) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧ ∀ b : ℝ, 0 < b → b < ε →
      ∀ y : (H.stage i.castSucc).Carrier,
      riemannianEDistOf ((H.event i).incoming.flow.base.metric T) p.val y ≤
        ENNReal.ofReal (r / 4) →
      ∃ β : ℝ → H.backwardSurvivorFootprintInterior first i hle K,
        ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ β ∧
        (H.backwardSurvivorFootprintMap first i hle K (β 0)).val = p.val ∧
        (H.backwardSurvivorFootprintMap first i hle K (β b)).val = y ∧
        reducedAction S.base.metric T (b ^ 2) (squareRootReparametrization β) =
          reducedLength (H.event i).incoming.flow.base.metric T isRegularizedAdmissible
            p.val (b ^ 2) y := by
  obtain ⟨r, hr, hball⟩ := H.exists_pos_ball_subset_backwardSurvivorFootprint i K T p hp
  obtain ⟨ε, hε, hscale⟩ := exists_positive_time_scale C r (T - H.time i.castSucc) hr
    (sub_pos.mpr hleft)
  refine ⟨r, ε, hr, hε, ?_⟩
  intro b hb hbε y hdist
  obtain ⟨ht, htime, hsmall⟩ := hscale b hb hbε
  have hleft' : H.time i.castSucc < T - b ^ 2 := by linarith
  exact H.exists_backwardSurvivor_reducedAction_minimizer_of_distance_le first i hle K htrace S
    hmetric C T b r hb hr hleft' hright
    (fun t ht z => hRm t ⟨hleft'.le.trans ht.1, ht.2⟩ z) p.val y
    hdist htime hsmall hball

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
