import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingCurvature

/-!
# L6-B 叶子：`exists_backwardSurvivorIncomingFootprint_curvature_bound` 的足迹局部化（`_P6L`）

局部化合同 `docs/geometrization/chapter8/design-C11-P6-localization-contract-20261006.md` §2 (D-event)：
原 `ST/HistorySurvivorIncomingCurvature.lean:198` 的
`hbound : ∀ j, first ≤ j.castSucc → j.succ ≤ last → ∀ y : (H.stage j.castSucc).Carrier, …`
（stage 全局）在证明里只于 `HSIC:271` 求值一次：
`A.point j.castSucc …`，`A` 是足迹点像 `x ∈ K` 的 backward trace（以下各层 `HSIC:83/101/65`、
`BackwardTraceScalarTime:16`、`BackwardTraceReciprocal:17` 已是逐点形）。这里 `hbound` 改为
**footprint 形**：`∀ j hf hl, ∀ z ∈ U, ∀ A : BackwardPointTrace H first last hle z, ∀ t ∈ Ioo …`，
在 `A.point j.castSucc …` 上求值；加 `U : Set (H.stage last).Carrier` 与 `hKU : ∀ x ∈ K, x.val ∈ U`。
私有引理（`HSIC:12/31/131/182` 与 footprint 的 `SigmaCompactSpace` 局部实例）一并复制为 `_P6L`。证明体照抄。
-/

set_option autoImplicit false

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem scalar_le_four_mul_of_reciprocal_bound_P6L
    {q Q R Rlast Δ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hscalar : Rlast ≤ 2 * Q)
    (hrec : |(max q R)⁻¹ - (max q Rlast)⁻¹| ≤ C * Δ)
    (htime : 4 * C * Δ * Q ≤ 1) : R ≤ 4 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hinv : (2 * Q)⁻¹ ≤ (max q Rlast)⁻¹ :=
    inv_anti₀ (hq.trans_le (le_max_left _ _)) (max_le (by linarith) hscalar)
  have hhalf : C * Δ ≤ (4 * Q)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 4 * Q)).mpr
    nlinarith
  have htwo : (2 * Q)⁻¹ = 2 * (4 * Q)⁻¹ := by field_simp; ring
  have hlower : (4 * Q)⁻¹ ≤ (max q R)⁻¹ := by
    rw [htwo] at hinv
    linarith [(abs_le.mp hrec).1]
  exact (le_max_right _ _).trans
    ((inv_le_inv₀ (by positivity : 0 < 4 * Q) (hq.trans_le (le_max_left q R))).mp hlower)

private theorem incoming_riemannNorm_le_of_scalar_le_P6L
    {P : OrientedThreeStage} {a s : ℝ} (G : P.IncomingSlab a s)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : Perelman.PhiAlmostNonnegative G.flow (Ico a s) Phi)
    {Q t : ℝ} (hQ : 0 < Q) (ht : t ∈ Ico a s) (x : P.Carrier)
    (hscalar : G.flow.scalar t x ≤ 4 * Q) :
    G.riemannNorm t x ≤ 4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0) := by
  have hbridge : Perelman.CanonicalNeighborhood.RmNormBoundOn G.flow (2 * Real.sqrt 3) :=
    fun t y basis horth _ ha =>
      Perelman.CanonicalNeighborhood.sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le
        G.flow t y basis horth ha
  have h := Perelman.CanonicalNeighborhood.sqrt_rmNormSq_le_of_scalar_le
    (by positivity : 0 ≤ 2 * Real.sqrt 3) hbridge hPhi hpinch
    (by simp [ThreeSpace] : Module.finrank ℝ ThreeSpace = 3) ht x hQ hscalar
  exact h.trans_eq (by ring)



private theorem incoming_extended_riemannNorm_le_of_terminal_scalar_le_P6L
    {P : OrientedThreeStage} {a s : ℝ} (G : P.IncomingSlab a s) (L : G.TerminalLimitMetric)
    (x : G.terminalRegularOpen) {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hfinal : ∀ t ∈ Ioo a s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤ C * G.flow.scalar t x.val ^ 2)
    (hscalar : metricScalarAt L.metric x ≤ 2 * Q)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : Perelman.PhiAlmostNonnegative G.flow (Ico a s) Phi)
    {t : ℝ} (ht : t ∈ Icc a s) (htime : 4 * C * (s - t) * Q ≤ 1) :
    Real.sqrt (normSq0S (L.extendedMetric t) x 4 (metricRm04At (L.extendedMetric t) x)) ≤
      4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0) := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hpast (u : ℝ) (hu : u ∈ Ico a s) (htimeu : 4 * C * (s - u) * Q ≤ 1) :
      G.riemannNorm u x.val ≤ 4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0) := by
    have hrec := L.inv_max_scalar_sub_terminal_le G hq x hfinal hu
    exact incoming_riemannNorm_le_of_scalar_le_P6L G hPhi hpinch hQ hu x.val
      (scalar_le_four_mul_of_reciprocal_bound_P6L hq hqQ hscalar hrec htimeu)
  rcases lt_or_eq_of_le ht.2 with hts | hts
  · rw [L.extendedMetric_before hts, Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen]
    exact hpast t ⟨ht.1, hts⟩ htime
  · subst t
    rw [L.extendedMetric_terminal]
    have hnear : ∀ᶠ u in 𝓝[<] s, 4 * C * (s - u) * Q ≤ 1 := by
      have hc : ContinuousAt (fun u : ℝ => 4 * C * (s - u) * Q) s := by fun_prop
      have hs : 4 * C * (s - s) * Q < 1 := by simp
      exact (hc.eventually_lt_const hs).filter_mono nhdsWithin_le_nhds |>.mono fun _ h => h.le
    apply le_of_tendsto (L.tendsto_riemannNorm x)
    filter_upwards [hnear, Ioo_mem_nhdsLT G.lt] with u htimeu hu
    exact hpast u ⟨hu.1.le, hu.2⟩ htimeu


namespace ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)

private local instance (K : Set G.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorIncomingFootprint first last hle G K) := by
  let : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first last hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K).isOpen)

private theorem exists_old_stage_at_time_P6L
    {t : ℝ} (ht : H.time first ≤ t) (htlast : t < H.time last) :
    ∃ j : Fin H.eventCount, first ≤ j.castSucc ∧ j.succ ≤ last ∧
      t ∈ Icc (H.time j.castSucc) (H.time j.succ) := by
  let tH : Icc (0 : ℝ) H.horizon :=
    ⟨t, (H.time_nonneg first).trans ht, htlast.le.trans (H.time_le_horizon_at last)⟩
  let k := H.activeStage tH
  have hk : k < last := by
    apply H.time_strictMono.lt_iff_lt.mp
    exact (H.activeStage_time_le tH).trans_lt htlast
  have hkfirst : first ≤ k := H.le_activeStage tH first ht
  let j : Fin H.eventCount := ⟨k.val, by have := last.isLt; change k.val < H.eventCount; omega⟩
  have hnext := H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)
  refine ⟨j, hkfirst, ?_, H.activeStage_time_le tH, hnext.le⟩
  change k.val + 1 ≤ last.val
  exact hk

/-- **`_P6L`**：原 `ObservedHistory.exists_backwardSurvivorIncomingFootprint_curvature_bound`
（`HistorySurvivorIncomingCurvature:198`）。改动：`hbound` 改 footprint 形（只在 `U` 中点的 backward
trace 点 `A.point j.castSucc …` 上要求），加 `U`、`hKU : ∀ x ∈ K, x.val ∈ U`（成员关系来源：
足迹点像 `x ∈ interior K ⊆ K`）。结论逐字。 -/
theorem exists_backwardSurvivorIncomingFootprint_curvature_bound_P6L
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (K : Set G.terminalRegularOpen) (U : Set (H.stage last).Carrier)
    (hKU : ∀ x ∈ K, x.val ∈ U) {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H first last hle z,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ x ∈ K, ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤ C * G.flow.scalar t x.val ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi)
    (hscalar : ∀ x ∈ K, metricScalarAt L.metric x ≤ 2 * Q)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val))
    {c : ℝ} (hc : H.time first ≤ c) (hcs : c ≤ s)
    (htime : 6 * C * (s - c) * Q ≤ 1) :
    range (H.backwardSurvivorIncomingFootprintMap first last hle G K) = interior K ∧
    ∃ gflow : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorIncomingFootprint first last hle G K),
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
              (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      (∀ t ∈ Icc (H.time last) s,
        gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      gflow s = localPullMetric L.metric
        (H.backwardSurvivorIncomingFootprintMap first last hle G K)
        (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) ∧
      IsSolutionOn ({ base := { metric := gflow } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorIncomingFootprint first last hle G K)
          (RealTimeInterval.closed c s hcs)) ∧
      ∀ t ∈ Icc c s, ∀ z : H.backwardSurvivorIncomingFootprint first last hle G K,
        normSq0S (gflow t) z 4 (metricRm04At (gflow t) z) ≤
          (4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0)) ^ 2 := by
  have hQ : 0 < Q := hq.trans_le hqQ
  obtain ⟨gflow, hslabs, hlast, hterminal, _, hsol⟩ :=
    H.exists_backwardSurvivorIncomingFootprint_isSolutionOn first last hle G L hinit K
  refine ⟨H.range_backwardSurvivorIncomingFootprintMap first last hle G K htrace,
    gflow, hslabs, hlast, hterminal, ?_, ?_⟩
  · exact isSolutionOn_timeRestrict hsol
      (fun t ht => ⟨hc.trans ht.1, ht.2⟩) (fun t ht => ⟨hc.trans_lt ht.1, ht.2⟩)
  · intro t ht z
    let x := H.backwardSurvivorIncomingFootprintMap first last hle G K z
    have hx : x ∈ K := interior_subset z.property
    have htime6 : 6 * C * (s - t) * Q ≤ 1 := by
      apply le_trans _ htime
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sub_le_sub_left ht.1 _) (by positivity)) hQ.le
    have htime4 : 4 * C * (s - t) * Q ≤ 1 := by
      nlinarith [C.coe_nonneg]
    have hb : Real.sqrt (normSq0S (gflow t) z 4 (metricRm04At (gflow t) z)) ≤
        4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0) := by
      by_cases hlastt : H.time last ≤ t
      · rw [hlast t ⟨hlastt, ht.2⟩, Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen]
        change Real.sqrt (normSq0S (localPullMetric _ _ _) _ 4
          (metricRm04At (localPullMetric _ _ _) _)) ≤ _
        rw [normSq0S_metricRm04At_localPullMetric]
        exact incoming_extended_riemannNorm_le_of_terminal_scalar_le_P6L G L x hq hqQ
          (hfinal x hx) (hscalar x hx) hPhi hpinchFinal ⟨hlastt, ht.2⟩ htime4
      · obtain ⟨j, hf, hl, htj⟩ :=
          H.exists_old_stage_at_time_P6L first last (hc.trans ht.1) (lt_of_not_ge hlastt)
        rw [hslabs j hf hl t htj, Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen,
          Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen]
        change Real.sqrt (normSq0S (localPullMetric _ _ _) _ 4
          (metricRm04At (localPullMetric _ _ _) _)) ≤ _
        rw [normSq0S_metricRm04At_localPullMetric]
        let A : BackwardPointTrace H first last hle x.val := Classical.choice z.val.val.property
        let y := H.backwardSurvivorTerminalMap first last hle j hf hl z.val.val
        have hy : y.val = A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl) :=
          H.backwardSurvivorMap_eq_point first last hle j.castSucc hf
            (j.castSucc_lt_succ.le.trans hl) z.val.val A
        have hA := fun j hf hl => hbound j hf hl x.val (hKU x hx) A
        rcases lt_or_eq_of_le htj.2 with htjs | heq
        · rw [(H.event j).terminal.extendedMetric_before htjs,
            Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen]
          rw [hy]
          exact A.riemannNorm_le_of_incoming_terminal_scalar_le G L hinit x hq hqQ hA
            (hfinal x hx) (hscalar x hx) hPhi hpinch j hf hl ⟨htj.1, htjs⟩ htime4
        · subst t
          rw [(H.event j).terminal.extendedMetric_terminal]
          exact A.riemannNorm_terminal_le_of_incoming_terminal_scalar_le G L hinit x hq hqQ hA
            (hfinal x hx) (hscalar x hx) hPhi hpinch j hf hl y hy htime6
    exact (Real.sqrt_le_iff.mp hb).2


end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
