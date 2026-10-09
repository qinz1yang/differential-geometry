import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84SlabBarrierIco_S74

/-!
# CH12-S74 G2 (b1'), the top stage of the trace: backward barrier from an interior time

* `barrier_from_top_S74`: the global backward barrier `(β - 2C(b - t))⁻¹` of `backward_barrier_O16`
  from a *strict* bound `f b < β⁻¹` at the top time `b` (the strict slack replaces the unavailable
  `P2` at the top time itself, so that `b` may be the horizon).
* `closed_scalar_continuousWithinAt_S74`, `closed_hasDerivAt_scalar_S74`: the two analytic facts of a
  `ClosedSlab` flow used for the final stage.
* `top_stage_barrier_S74`: for a regular time `u`, the scalar along the point `y` of the active stage
  of `u` obeys the barrier on the part `[a0, u]` of the active stage (event slab or final slab).
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Operator DifferentialGeometry.CheegerGromovCompactness
  DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

theorem barrier_from_top_S74 {f θ : ℝ → ℝ} {a b M β C : ℝ} (hab : a ≤ b) (hC : 0 < C)
    (hβ : 0 < β) (hβM : β * M < 1) (hcont : ContinuousOn f (Icc a b))
    (hdiff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hP2 : ∀ t ∈ Ioo a b, θ t < f t → |derivWithin f (Iic t) t| ≤ C * f t ^ 2)
    (hθ : ∀ t ∈ Ioo a b, θ t ≤ M) (hden : 0 < β - 2 * C * (b - a)) (hb : f b < β⁻¹) :
    ∀ t ∈ Icc a b, f t ≤ (β - 2 * C * (b - t))⁻¹ := by
  intro t ht
  by_cases htb : t = b
  · rw [htb]; simpa using hb.le
  have htb' : t < b := lt_of_le_of_ne ht.2 htb
  have hab' : a < b := lt_of_le_of_lt ht.1 htb'
  have hmem : Icc a b ∈ 𝓝[<] b := Icc_mem_nhdsLT hab'
  have hT : Tendsto f (𝓝[<] b) (𝓝 (f b)) :=
    ((hcont b ⟨hab, le_rfl⟩).tendsto).mono_left (nhdsWithin_le_of_mem hmem)
  obtain ⟨b', hb1, hb2⟩ := ((hT.eventually (gt_mem_nhds hb)).and (Ioo_mem_nhdsLT htb')).exists
  have hb'b : b' < b := hb2.2
  have hden' : 0 < β - 2 * C * (0 + (b' - a)) := by
    have : 2 * C * (0 + (b' - a)) ≤ 2 * C * (b - a) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hbar := backward_barrier_O16 (f := f) (c := a) (b := b') (M := M) (C := C) (β := β) (σ0 := 0)
    hC hβ hβM le_rfl hden'
    (hcont.mono (Icc_subset_Icc_right hb'b.le))
    (fun s hs => (hdiff s ⟨hs.1, lt_of_le_of_lt hs.2 hb'b⟩).differentiableWithinAt)
    (fun s hs hMs => hP2 s ⟨hs.1, lt_of_le_of_lt hs.2 hb'b⟩
      (lt_of_le_of_lt (hθ s ⟨hs.1, lt_of_le_of_lt hs.2 hb'b⟩) hMs))
    (by simpa using hb1.le)
  have h1 := hbar t ⟨ht.1, hb2.1.le⟩
  refine h1.trans ?_
  have hdent : 0 < β - 2 * C * (b - t) := by
    have : 2 * C * (b - t) ≤ 2 * C * (b - a) :=
      mul_le_mul_of_nonneg_left (by linarith [ht.1]) (by positivity)
    linarith
  apply inv_anti₀ hdent
  have : 2 * C * (0 + (b' - t)) ≤ 2 * C * (b - t) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

theorem closed_scalar_continuousWithinAt_S74 {P : OrientedThreeStage.{u}} {a b : ℝ}
    (G : P.ClosedSlab a b) (y : P.Carrier) {c : ℝ} (hc : c ∈ Icc a b) :
    ContinuousWithinAt (fun v => G.flow.scalar v y) (Icc a b) c := by
  set φ := extChartAt ThreeModel y with hφ
  set W := interior φ.target with hWdef
  let F : ℝ × ThreeSpace → ℝ := fun z =>
    DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := ThreeModel) y
      (metricScalarAt (G.flow.base.metric z.1)) z.2
  have hF : ContDiffOn ℝ ∞ F (Icc a b ×ˢ W) :=
    scalarOnE_contDiffOn_of_chartGramFamilySmoothWithinOn _ y
      (G.flow.chartGramFamilySmoothWithinOn_of_jointContMDiffOn G.smoothUpTo.jointContMDiffOn y)
  have hW : W = φ.target := (isOpen_extChartAt_target y).interior_eq
  have hya : (c, φ y) ∈ Icc a b ×ˢ W := ⟨hc, by rw [hW]; exact mem_extChartAt_target y⟩
  have hfun : (fun v => G.flow.scalar v y) = fun v => F (v, φ y) := by
    funext v
    exact (DifferentialGeometry.Tensor.Coordinates.scalarOnE_extChartAt y _
      (mem_extChartAt_source y)).symm
  rw [hfun]
  have hpair : ContinuousWithinAt (fun v : ℝ => (v, φ y)) (Icc a b) c :=
    continuousWithinAt_id.prodMk continuousWithinAt_const
  have hmaps : MapsTo (fun v : ℝ => (v, φ y)) (Icc a b) (Icc a b ×ˢ W) :=
    fun v hv => ⟨hv, by rw [hW]; exact mem_extChartAt_target y⟩
  exact ContinuousWithinAt.comp (g := F) (f := fun v : ℝ => (v, φ y))
    (hF.continuousOn.continuousWithinAt hya) hpair hmaps

theorem closed_hasDerivAt_scalar_S74 {P : OrientedThreeStage.{u}} {a b : ℝ}
    (G : P.ClosedSlab a b) {t : ℝ} (ht : t ∈ Ioo a b) (y : P.Carrier) :
    HasDerivAt (fun v => G.flow.scalar v y) (scalarEvolutionRate (G.flow.base.metric t) y) t := by
  have h := scalar_curvature_evolution G.flow G.equation ⟨t, ht⟩ y
  have hnhds : (RealTimeInterval.closed a b G.lt.le).carrier ∈ 𝓝 t :=
    mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self
  refine (h.hasDerivAt hnhds).congr_deriv ?_
  rw [scalarEvolutionRate_def]
  simp only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt,
    SolutionOn.family_metric]
  rfl

theorem top_stage_barrier_S74 (H : ObservedHistory.{u}) {C M β a0 : ℝ} {θ : ℝ → ℝ}
    (hC : 0 < C) (hβ : 0 < β) (hβM : β * M < 1)
    (hP2e : ∀ (i : Fin H.eventCount) (y : (H.stage i.castSucc).Carrier),
      ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
      θ t < (H.event i).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event i).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event i).incoming.flow.scalar t y ^ 2)
    (hP2f : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      ∀ (y : (H.stage (Fin.last H.eventCount)).Carrier),
      ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) H.horizon,
      θ t < (H.finalSlab h).flow.scalar t y →
      |derivWithin (fun v => (H.finalSlab h).flow.scalar v y) (Iic t) t| ≤
        C * (H.finalSlab h).flow.scalar t y ^ 2)
    (u : Icc (0 : ℝ) H.horizon) (hθ : ∀ t, a0 ≤ t → t ≤ (u : ℝ) → θ t ≤ M)
    (hreg : H.time (H.activeStage u) < (u : ℝ)) (ha0u : a0 ≤ (u : ℝ))
    (hden : 0 < β - 2 * C * ((u : ℝ) - a0))
    (y : (H.stage (H.activeStage u)).Carrier)
    (hy : metricScalarAt (H.stageMetric (H.activeStage u) u) y < β⁻¹) :
    ∀ t ∈ H.stageDomain (H.activeStage u), a0 ≤ t → t ≤ (u : ℝ) →
      metricScalarAt (H.stageMetric (H.activeStage u) t) y ≤ (β - 2 * C * ((u : ℝ) - t))⁻¹ := by
  have hdenc : ∀ c : ℝ, a0 ≤ c → 0 < β - 2 * C * ((u : ℝ) - c) := fun c hc => by
    have : 2 * C * ((u : ℝ) - c) ≤ 2 * C * ((u : ℝ) - a0) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have gen : ∀ j : Fin (H.eventCount + 1), H.activeStage u = j → H.time j < (u : ℝ) →
      ∀ y : (H.stage j).Carrier, metricScalarAt (H.stageMetric j u) y < β⁻¹ →
      ∀ t ∈ H.stageDomain j, a0 ≤ t → t ≤ (u : ℝ) →
        metricScalarAt (H.stageMetric j t) y ≤ (β - 2 * C * ((u : ℝ) - t))⁻¹ := by
    intro j
    induction j using Fin.lastCases with
    | last =>
      intro hj hlt y hy t ht hat htu
      have h : H.time (Fin.last H.eventCount) < H.horizon := hlt.trans_le u.2.2
      have hm : H.stageMetric (Fin.last H.eventCount) = (H.finalSlab h).flow.base.metric := by
        simp only [ObservedHistory.stageMetric, Fin.lastCases_last, h, dite_true]
      have hd : t ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon := by
        simpa [ObservedHistory.stageDomain] using ht
      rw [hm] at hy ⊢
      have hbar := barrier_from_top_S74 (f := fun v => (H.finalSlab h).flow.scalar v y) (θ := θ)
        (a := max a0 (H.time (Fin.last H.eventCount))) (b := (u : ℝ)) (M := M) (β := β) (C := C)
        (max_le ha0u hlt.le) hC hβ hβM
        (fun v hv => (closed_scalar_continuousWithinAt_S74 (H.finalSlab h) y
          ⟨(le_max_right _ _).trans hv.1, hv.2.trans u.2.2⟩).mono
          (Icc_subset_Icc (le_max_right _ _) u.2.2))
        (fun v hv => (closed_hasDerivAt_scalar_S74 (H.finalSlab h)
          ⟨lt_of_le_of_lt (le_max_right _ _) hv.1, lt_of_lt_of_le hv.2 u.2.2⟩ y).differentiableAt)
        (fun v hv hθv => hP2f h y v
          ⟨lt_of_le_of_lt (le_max_right _ _) hv.1, lt_of_lt_of_le hv.2 u.2.2⟩ hθv)
        (fun v hv => hθ v ((le_max_left _ _).trans hv.1.le) hv.2.le)
        (hdenc _ (le_max_left _ _)) hy
      exact hbar t ⟨max_le hat hd.1, htu⟩
    | cast i =>
      intro hj hlt y hy t ht hat htu
      have hval : (H.activeStage u).val < H.eventCount := by rw [hj]; exact i.isLt
      have hnext : (u : ℝ) < H.time i.succ := by
        have h := H.activeStage_before_next u hval
        have he : (⟨(H.activeStage u).val + 1, by omega⟩ : Fin (H.eventCount + 1)) = i.succ := by
          ext; simp [hj]
        rw [he] at h; exact h
      have hm : H.stageMetric i.castSucc = (H.event i).incoming.flow.base.metric := by
        simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
      have hd : t ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
        simpa [ObservedHistory.stageDomain] using ht
      rw [hm] at hy ⊢
      have hbar := barrier_from_top_S74
        (f := fun v => (H.event i).incoming.flow.scalar v y) (θ := θ)
        (a := max a0 (H.time i.castSucc)) (b := (u : ℝ)) (M := M) (β := β) (C := C)
        (max_le ha0u hlt.le) hC hβ hβM
        (fun v hv => (scalar_continuousWithinAt_Ico_S74 (H.event i).incoming y
          ⟨(le_max_right _ _).trans hv.1, lt_of_le_of_lt hv.2 hnext⟩).mono
          (Icc_subset_Ico_right hnext |>.trans (Ico_subset_Ico_left (le_max_right _ _))))
        (fun v hv => ((H.event i).incoming.hasDerivAt_scalar_scalarEvolutionRate
          ⟨lt_of_le_of_lt (le_max_right _ _) hv.1, lt_trans hv.2 hnext⟩ y).differentiableAt)
        (fun v hv hθv => hP2e i y v
          ⟨lt_of_le_of_lt (le_max_right _ _) hv.1, lt_trans hv.2 hnext⟩ hθv)
        (fun v hv => hθ v ((le_max_left _ _).trans hv.1.le) hv.2.le)
        (hdenc _ (le_max_left _ _)) hy
      exact hbar t ⟨max_le hat hd.1, htu⟩
  exact gen _ rfl hreg y hy

end GC.LongTime.Ch12
