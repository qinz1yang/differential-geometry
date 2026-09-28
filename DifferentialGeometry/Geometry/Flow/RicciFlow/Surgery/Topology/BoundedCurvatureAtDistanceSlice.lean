import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceTracedPositive
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceChainCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordHorizonExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory


private theorem nonempty_backwardPointTrace_of_chain_of_not_capWindowPoint_aux
    (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M Dcap Dstar θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    (hfinalPinch : Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
      (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (k : Fin (H.eventCount + 1)) (hk : H.toHistory.activeStage t = k)
    {N : ℕ} (pc : ℕ → (H.toHistory.stage k).Carrier) (δ : ℕ → ℝ)
    (hδ : ∀ j ≤ N, 0 < δ j)
    (hchain : ∀ j < N, pc (j + 1) ∈ riemannianBallOf (H.toHistory.stageMetric k t) (pc j) (δ j))
    (hslabs : H.EventSlabsDerivative Ctime qcan k)
    (hfinal : ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime
      qcan t)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ j ≤ N, ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric k t) (pc j) (δ j),
      metricScalarAt (H.toHistory.stageMetric k t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hθ : 4 * M * ((t : ℝ) - u) ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) *
        ∑ i ∈ Finset.range (N + 1), δ i < Dcap)
    (hnot : ¬ H.CapWindowPoint records k (pc 0) t Dcap θcap) :
    ∀ j ≤ N, ∀ z ∈ riemannianBallOf (H.toHistory.stageMetric k t) (pc j) (δ j),
      Nonempty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u) k
        (hk ▸ H.toHistory.activeStage_mono hut) z) := by
  subst hk
  intro j hj z hz
  by_contra hne
  exact hnot (H.capWindowPoint_of_chain_point_without_trace_of_activeStage_eq_last records hcan
    hscale hacc hphi hpinch hut h hlastA hfinalPinch pc δ hδ hchain z ⟨j, hj, hz⟩
    (not_nonempty_iff.mp hne) hslabs hfinal hM hqcan hspace htime hDstar hDmodel hθ hwin)

private theorem sum_range_ite_add {Nc N : ℕ} (a b : ℕ → ℝ) :
    ∑ j ∈ Finset.range (Nc + N + 1), (if j < Nc then a j else b (j - Nc)) =
      ∑ j ∈ Finset.range Nc, a j + ∑ j ∈ Finset.range (N + 1), b j := by
  rw [show Nc + N + 1 = Nc + (N + 1) by ring, Finset.sum_range_add]
  congr 1
  · exact Finset.sum_congr rfl fun j hj => ite_eq_left (Finset.mem_range.mp hj)
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]

theorem chain_traces_of_not_capWindowPoint_of_incomingSlab
    (H : RetainedCoreHistory.{u}) (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {t : ℝ} (ht : H.time (Fin.last H.eventCount) < t) (hts : t < s)
    {p : CutoffParameters} (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan Dcap Dstar θ : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    (hpinchG : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi)
    (hslabs : H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount))
    (hderG : G.DerivativeBoundBefore Ctime qcan t)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (y : (H.stage (Fin.last H.eventCount)).Carrier)
    (hnot : ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θ)
    {Nc : ℕ} (pc : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (δc : ℕ → ℝ) (hpc0 : pc 0 = y)
    (hδc : ∀ k < Nc, 0 < δc k)
    (hchainc : ∀ k < Nc, pc (k + 1) ∈
      riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t) (pc k) (δc k))
    {Mc lamc : ℝ}
    (hMc : ∀ k < Nc, ∀ z ∈ riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t)
      (pc k) (δc k), (G.closedPrefix t ht hts).flow.scalar t z ≤ Mc)
    (hlamc : ∑ k ∈ Finset.range Nc, δc k ≤ lamc) :
    ∀ (N : ℕ) (pp : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (δ : ℕ → ℝ) (M τ : ℝ),
      pp 0 = pc Nc → (∀ k ≤ N, 0 < δ k) →
      (∀ k < N, pp (k + 1) ∈
        riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t) (pp k) (δ k)) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t)
        (pp k) (δ k), (G.closedPrefix t ht hts).flow.scalar t z ≤ M) →
      Mc ≤ M → qcan ≤ M → 1 ≤ M → 0 ≤ τ → τ ≤ t →
      (Ctime : ℝ) * M * τ ≤ 1 / 2 → 4 * M * τ ≤ θ →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) *
          (lamc + ∑ k ∈ Finset.range (N + 1), δ k) < Dcap →
      ∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t)
        (pp k) (δ k),
        ∃ first : Fin (H.eventCount + 1), H.time first ≤ t - τ ∧
          Nonempty (BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z) := by
  intro N pp δ M τ h0 hδ hch hb hMcM hq hM1 hτ0 hτt hC h4 hD k hk z hz
  have hHt : H.horizon ≤ t := hend ▸ ht.le
  set S := G.closedPrefix t ht hts with hSdef
  set H' := H.extendHorizon t hHt S hG with hH'def
  have hh : H'.time (Fin.last H'.eventCount) < H'.horizon := ht
  let t' : Icc (0 : ℝ) H'.toHistory.horizon := ⟨t, H'.horizon_nonneg, le_rfl⟩
  have hu0 : 0 ≤ t - τ := by linarith
  let u' : Icc (0 : ℝ) H'.toHistory.horizon := ⟨t - τ, hu0, by
    change t - τ ≤ t
    linarith⟩
  have hut : u' ≤ t' := by
    change t - τ ≤ t
    linarith
  have hlastA : H'.toHistory.activeStage t' = Fin.last H.eventCount :=
    H.activeStage_extendHorizon_eq_last hHt S hG t' ht.le
  obtain ⟨h, hfp⟩ := RetainedCoreHistory.extendHorizon_finalSlab_phiAlmostNonnegative
    (H := H) (G := G) (hG := hG) (T := t) (hHT := hHt) (hT := ht) (hTs := hts) hpinchG
  have hmet : H'.toHistory.stageMetric (Fin.last H.eventCount) t = S.flow.base.metric t :=
    H.stageMetric_extendHorizon_last hHt S hG ht t
  let records' : ∀ i : Fin H'.eventCount, GeometricCutoffRecord H'.toHistory i p :=
    fun i => (records i).extendHorizon t hHt S hG
  let P : ℕ → (H.stage (Fin.last H.eventCount)).Carrier := fun j =>
    if j < Nc then pc j else pp (j - Nc)
  let Δ : ℕ → ℝ := fun j => if j < Nc then δc j else δ (j - Nc)
  have hP0 : P 0 = y := by
    by_cases hN : 0 < Nc
    · exact (ite_eq_left hN).trans hpc0
    · have : Nc = 0 := by omega
      change (if 0 < Nc then pc 0 else pp (0 - Nc)) = y
      rw [ite_eq_right hN, Nat.zero_sub, h0, this, hpc0]
  have hΔ : ∀ j ≤ Nc + N, 0 < Δ j := by
    intro j hj
    by_cases hjc : j < Nc
    · change 0 < (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_left hjc]
      exact hδc j hjc
    · change 0 < (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_right hjc]
      exact hδ _ (by omega)
  have hchainP : ∀ j < Nc + N, P (j + 1) ∈
      riemannianBallOf (H'.toHistory.stageMetric (Fin.last H.eventCount) t) (P j) (Δ j) := by
    intro j hj
    rw [hmet]
    by_cases hjc : j < Nc
    · change (if j + 1 < Nc then pc (j + 1) else pp (j + 1 - Nc)) ∈
        riemannianBallOf (S.flow.base.metric t)
        (if j < Nc then pc j else pp (j - Nc)) (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_left hjc, ite_eq_left hjc]
      by_cases hjc' : j + 1 < Nc
      · rw [ite_eq_left hjc']
        exact hchainc j hjc
      · rw [ite_eq_right hjc', show j + 1 - Nc = 0 by omega, h0, show Nc = j + 1 by omega]
        exact hchainc j (by omega)
    · change (if j + 1 < Nc then pc (j + 1) else pp (j + 1 - Nc)) ∈
        riemannianBallOf (S.flow.base.metric t)
        (if j < Nc then pc j else pp (j - Nc)) (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_right hjc, ite_eq_right hjc, ite_eq_right (show ¬ (j + 1 < Nc) by omega),
        show j + 1 - Nc = j - Nc + 1 by omega]
      exact hch (j - Nc) (by omega)
  have hspaceP : ∀ j ≤ Nc + N, ∀ w ∈ riemannianBallOf
      (H'.toHistory.stageMetric (Fin.last H.eventCount) t) (P j) (Δ j),
      metricScalarAt (H'.toHistory.stageMetric (Fin.last H.eventCount) t) w ≤ M := by
    intro j hj w hw
    rw [hmet] at hw ⊢
    by_cases hjc : j < Nc
    · change w ∈ riemannianBallOf (S.flow.base.metric t) (if j < Nc then pc j else pp (j - Nc))
        (if j < Nc then δc j else δ (j - Nc)) at hw
      rw [ite_eq_left hjc, ite_eq_left hjc] at hw
      exact (hMc j hjc w hw).trans hMcM
    · change w ∈ riemannianBallOf (S.flow.base.metric t) (if j < Nc then pc j else pp (j - Nc))
        (if j < Nc then δc j else δ (j - Nc)) at hw
      rw [ite_eq_right hjc, ite_eq_right hjc] at hw
      exact hb _ (by omega) w hw
  have hsum : ∑ j ∈ Finset.range (Nc + N + 1), Δ j ≤ lamc + ∑ j ∈ Finset.range (N + 1), δ j := by
    have := sum_range_ite_add (Nc := Nc) (N := N) δc δ
    change ∑ j ∈ Finset.range (Nc + N + 1), (if j < Nc then δc j else δ (j - Nc)) ≤ _
    rw [this]
    linarith
  have htu : (t' : ℝ) - u' = τ := by
    change t - (t - τ) = τ
    ring
  have hnot' : ¬ H'.CapWindowPoint records' (Fin.last H.eventCount) (P 0) t Dcap θ := by
    rw [hP0]
    rintro ⟨j, hl, A, b, xw, h1, h2, h3⟩
    exact hnot ⟨j, hl, ⟨A.point, A.endpoint_eq, A.crossing⟩, b, xw, h1, h2, h3⟩
  have hres := nonempty_backwardPointTrace_of_chain_of_not_capWindowPoint_aux H' records'
    (fun i b => hcan i b) (fun i b w => hscale i b w) hacc hphi hpinch hut hh hlastA hfp
    (Fin.last H.eventCount) hlastA P Δ hΔ hchainP hslabs
    (RetainedCoreHistory.extendHorizon_finalSlab_derivativeBoundBefore (H := H) (G := G)
      (hG := hG) (T := t) (hHT := hHt) (hT := ht) (hTs := hts) hderG le_rfl hh)
    hM1 hq hspaceP (by rw [htu]; exact hC) hDstar hDmodel (by rw [htu]; exact h4)
    (by
      rw [htu]
      refine lt_of_le_of_lt ?_ hD
      have hs0 : 0 ≤ Real.sqrt (8 * M) *
          Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
      have := mul_le_mul_of_nonneg_left hsum hs0
      linarith)
    hnot' (Nc + k) (by omega) z (by
      rw [hmet]
      change z ∈ riemannianBallOf (S.flow.base.metric t)
        (if Nc + k < Nc then pc (Nc + k) else pp (Nc + k - Nc))
        (if Nc + k < Nc then δc (Nc + k) else δ (Nc + k - Nc))
      rw [ite_eq_right (show ¬ (Nc + k < Nc) by omega), ite_eq_right (show ¬ (Nc + k < Nc) by omega),
        Nat.add_sub_cancel_left]
      exact hz)
  obtain ⟨A⟩ := hres
  refine ⟨H'.toHistory.activeStage u', ?_, ⟨⟨A.point, A.endpoint_eq, A.crossing⟩⟩⟩
  exact H'.toHistory.activeStage_time_le u'

end RetainedCoreHistory

private theorem ceil_mul_le {ℓ r₀ : ℝ} (hℓ : 0 ≤ ℓ) (hr₀ : 0 < r₀) :
    ((⌈ℓ / (r₀ / 2)⌉₊ + 1 : ℕ) : ℝ) * r₀ ≤ 2 * ℓ + 2 * r₀ := by
  have h1 : ((⌈ℓ / (r₀ / 2)⌉₊ : ℕ) : ℝ) < ℓ / (r₀ / 2) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hℓ (by positivity))
  have h2 : ℓ / (r₀ / 2) * r₀ = 2 * ℓ := by field_simp
  push_cast
  nlinarith

private theorem div_ceil_lt {ℓ r₀ : ℝ} (hr₀ : 0 < r₀) :
    ℓ / ((⌈ℓ / (r₀ / 2)⌉₊ + 1 : ℕ) : ℝ) < r₀ := by
  have hN : (0 : ℝ) < ((⌈ℓ / (r₀ / 2)⌉₊ + 1 : ℕ) : ℝ) := by positivity
  rw [div_lt_iff₀ hN]
  have h1 : ℓ / (r₀ / 2) ≤ ((⌈ℓ / (r₀ / 2)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ℓ = ℓ / (r₀ / 2) * (r₀ / 2) := by field_simp
  push_cast
  nlinarith

theorem OrientedThreeStage.ClosedSlab.exists_rebase_chain {P : OrientedThreeStage.{u}}
    {a T : ℝ} (A : P.ClosedSlab a T) (Cgrad : ℝ≥0) {q : ℝ} (hq : 0 < q)
    (hgradient : ∀ y, ∀ t ∈ Ioo a T, q < A.flow.scalar t y →
      ∀ v : TangentSpace ThreeModel y,
        |scalarDifferential (A.restrictIncoming le_rfl A.lt le_rfl).flow t y v| ≤
          Cgrad * A.flow.scalar t y * Real.sqrt (A.flow.scalar t y) *
            Real.sqrt ((A.flow.base.metric t).inner y v v))
    (y z : P.Carrier) {r : ℝ}
    (hyz : riemannianEDistOf (A.flow.base.metric T) y z < ENNReal.ofReal r)
    (hz : max q (A.flow.scalar T y) ≤ A.flow.scalar T z) :
    ∃ (x : P.Carrier) (Nc : ℕ) (pc : ℕ → P.Carrier),
      A.flow.scalar T x = max q (A.flow.scalar T y) ∧
      riemannianEDistOf (A.flow.base.metric T) y x < ENNReal.ofReal r ∧
      pc 0 = y ∧ pc Nc = x ∧
      (∀ k < Nc, pc (k + 1) ∈ riemannianBallOf (A.flow.base.metric T) (pc k)
        (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * max q (A.flow.scalar T y))))) ∧
      (∀ k < Nc, ∀ w ∈ riemannianBallOf (A.flow.base.metric T) (pc k)
        (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * max q (A.flow.scalar T y)))),
        A.flow.scalar T w ≤ 6 * max q (A.flow.scalar T y)) ∧
      (Nc : ℝ) * (localPropagationRadius Cgrad / (2 * Real.sqrt (2 * max q (A.flow.scalar T y))))
        ≤ 2 * r + 2 * (localPropagationRadius Cgrad /
          (2 * Real.sqrt (2 * max q (A.flow.scalar T y)))) := by
  set m := max q (A.flow.scalar T y) with hmdef
  have hm : 0 < m := lt_of_lt_of_le hq (le_max_left _ _)
  set r₀ := localPropagationRadius Cgrad / (2 * Real.sqrt (2 * m)) with hr₀def
  have hr₀ : 0 < r₀ := div_pos (localPropagationRadius_pos Cgrad.coe_nonneg) (by positivity)
  have hr : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hyz)
  by_cases hyq : q ≤ A.flow.scalar T y
  · refine ⟨y, 0, fun _ => y, by rw [hmdef, max_eq_right hyq], ?_, rfl, rfl,
      fun k hk => absurd hk (Nat.not_lt_zero k), fun k hk => absurd hk (Nat.not_lt_zero k), ?_⟩
    · rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hr
    · push_cast
      linarith
  · push Not at hyq
    have hmq : m = q := max_eq_left hyq.le
    have hcont : Continuous (A.flow.scalar T) :=
      (metricScalar_smooth (A.flow.base.metric T)).continuous
    have hK : IsCompact {w | A.flow.scalar T w ≤ q} :=
      (isClosed_le hcont continuous_const).isCompact
    obtain ⟨x, gamma, hxq, hfin, hxz, hg0, hgl, -, -, hbelow, hiso⟩ :=
      Geometry.exists_minimizing_segment_to_level_of_isCompact_sublevel
        (A.flow.base.metric T) (A.flow.scalar T) hcont hK y z hyq (by rw [← hmq]; exact hz)
        (ne_top_of_lt hyz)
    set ℓ := (riemannianEDistOf (A.flow.base.metric T) y x).toReal with hℓdef
    have hℓ : 0 ≤ ℓ := ENNReal.toReal_nonneg
    set Nc := ⌈ℓ / (r₀ / 2)⌉₊ + 1 with hNcdef
    have hNc : (0 : ℝ) < Nc := by positivity
    let pc : ℕ → P.Carrier := fun k => gamma (min (k * ℓ / Nc) ℓ)
    have hmem (k : ℕ) : min (k * ℓ / Nc) ℓ ∈ Icc 0 ℓ :=
      ⟨le_min (by positivity) hℓ, min_le_right _ _⟩
    have hxz' : ℓ < r := by
      have h := hxz.trans_lt hyz
      exact (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr h |>.trans_le
        (le_of_eq (ENNReal.toReal_ofReal hr.le))
    refine ⟨x, Nc, pc, by rw [hxq, hmq], hxz.trans_lt hyz, ?_, ?_, fun k hk => ?_,
      fun k _ w hw => ?_, ?_⟩
    · change gamma (min ((0 : ℕ) * ℓ / Nc) ℓ) = y
      rw [Nat.cast_zero, zero_mul, zero_div, min_eq_left hℓ, hg0]
    · change gamma (min ((Nc : ℕ) * ℓ / Nc) ℓ) = x
      rw [mul_div_cancel_left₀ _ hNc.ne', min_self, hgl]
    · change riemannianEDistOf _ (gamma (min (k * ℓ / Nc) ℓ))
        (gamma (min (((k + 1 : ℕ) : ℝ) * ℓ / Nc) ℓ)) < _
      rw [hiso _ (hmem k) _ (hmem (k + 1))]
      have h1 : (k : ℝ) * ℓ / Nc ≤ ℓ := by
        rw [div_le_iff₀ hNc]
        have : (k : ℝ) ≤ Nc := by exact_mod_cast hk.le
        nlinarith
      have h2 : ((k + 1 : ℕ) : ℝ) * ℓ / Nc ≤ ℓ := by
        rw [div_le_iff₀ hNc]
        have : ((k + 1 : ℕ) : ℝ) ≤ Nc := by exact_mod_cast hk
        nlinarith
      rw [min_eq_left h1, min_eq_left h2]
      have heq : (k : ℝ) * ℓ / Nc - ((k + 1 : ℕ) : ℝ) * ℓ / Nc = -(ℓ / Nc) := by
        push_cast
        ring
      rw [heq, abs_neg, abs_of_nonneg (by positivity)]
      exact (ENNReal.ofReal_lt_ofReal_iff hr₀).mpr (div_ceil_lt hr₀)
    · have hpk : A.flow.scalar T (pc k) ≤ m := by
        rw [hmq]
        exact hbelow _ (hmem k)
      exact A.scalar_le_six_mul_on_ball_of_gradient_bound Cgrad hm
        (le_max_left _ _) hgradient (pc k) hpk w hw
    · have h := ceil_mul_le hℓ hr₀
      rw [← hNcdef] at h
      linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
