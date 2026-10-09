import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OpenStep_S145
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison

set_option autoImplicit false

/-! # CH12-S145 G2b: `closed_step_S145` — the closed step of the continuity method

If `x_k` solve `mold σ_k x_k = w σ_k` with `σ_k ↓ s*` and `d_h(q', x_k) ≤ D_k → D'`, then there is `x'` with
`mold s* x' = w s*` and `d_h(q', x') ≤ D'`.  Proof: cluster point `a` of `x_k` in the compact closed ball; patch at
`(s*, a)`; for large `k`, `w s* = ψ_{s*}(map(σ_k, x_k))` (`flowline_unique_Icc_S115` against the survivor flow-line of
`map(σ_k, x_k)`); `ψ_{s*} ∘ map` is continuous, so `ψ_{s*}(map(σ_k,x_k)) → ψ_{s*}(map(s*, a)) = mold s* a` and the
stage carrier is Hausdorff. -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Collapse
open Manifold GC.LongTime GC.LongTime.Ch12 GC.LongTime.CuspP1
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

theorem continuous_cast_S145 {A B : OrientedThreeStage.{u}} (h : A = B) :
    Continuous (cast (congrArg OrientedThreeStage.Carrier h)) := by
  subst h
  exact continuous_id

section Patch

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {Hold : FiniteVolumeHyperbolicModel.{u}} {start : ℝ} {α : ℝ → ℝ}
  {Ω : TopologicalSpace.Opens (ℝ × Hold.Carrier)}
  {mold : ∀ t : ℝ, start ≤ t → Hold.Carrier → (postStage F.observation t).Carrier}
  {t₀ : ℝ} {x₀ : Hold.Carrier}

theorem liftMap_map_eq_mold_S145 (p : PersistentModelPatch F Hold start α (sourceSlice_CX5 Ω) mold t₀ x₀)
    (τ : Icc (0 : ℝ) (F.tower.history p.n).horizon) (hτ : (τ : ℝ) ∈ Ioo p.a p.b)
    (hT : start ≤ (τ : ℝ)) {x : Hold.Carrier} (hx : x ∈ p.neighborhood) :
    liftMap_S65 (F := F) p.n p.first p.last p.ordered τ (p.stages τ hτ).1 (p.stages τ hτ).2
      (p.map ((τ : ℝ), x)) = mold τ hT x :=
  eq_of_heq ((liftMap_heq_S65 (F := F) p.n p.first p.last p.ordered τ (p.stages τ hτ).1
    (p.stages τ hτ).2 (p.map ((τ : ℝ), x))).symm.trans (p.agrees τ hτ hT x hx))

theorem liftMap_continuous_S145 (p : PersistentModelPatch F Hold start α (sourceSlice_CX5 Ω) mold t₀ x₀)
    (τ : Icc (0 : ℝ) (F.tower.history p.n).horizon) (hτ : (τ : ℝ) ∈ Ioo p.a p.b) :
    Continuous (liftMap_S65 (F := F) p.n p.first p.last p.ordered τ (p.stages τ hτ).1 (p.stages τ hτ).2) :=
  (continuous_cast_S145 (postStage_eq_stage_active_CPD2 F.observation p.n τ).symm).comp
    (backwardSurvivorMap_contMDiff_S110 (F.tower.history p.n).toHistory p.first p.last p.ordered _ _ _).continuous

/-- Survivor flow-line of `y`: equals `liftMap y` at every time of the patch window (value form). -/
theorem patch_flowline2_S145 (p : PersistentModelPatch F Hold start α (sourceSlice_CX5 Ω) mold t₀ x₀)
    (y : (F.tower.history p.n).toHistory.backwardSurvivorDomain p.first p.last p.ordered)
    (W : Set ℝ) (w₀ : ∀ s : ℝ, s ∈ W → (postStage F.observation s).Carrier) :
    ∃ w₂ : ∀ s : ℝ, s ∈ W → (postStage F.observation s).Carrier,
      (∀ (τ : Icc (0 : ℝ) (F.tower.history p.n).horizon) (hτ : (τ : ℝ) ∈ Ioo p.a p.b)
        (hτW : (τ : ℝ) ∈ W),
        w₂ τ hτW = liftMap_S65 (F := F) p.n p.first p.last p.ordered τ (p.stages τ hτ).1
          (p.stages τ hτ).2 y) ∧
      (∀ s : ℝ, p.a < s → s < p.b → ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
          (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
          (_ : b ≤ (F.tower.history n).horizon)
          (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
            first ≤ (F.tower.history n).toHistory.activeStage r ∧
              (F.tower.history n).toHistory.activeStage r ≤ last)
          (y : (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
          ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b) (hrW : (r : ℝ) ∈ W),
            HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
              ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 y)
              (w₂ r hrW)) := by
  classical
  let w₂ : ∀ s : ℝ, s ∈ W → (postStage F.observation s).Carrier := fun s hsW =>
    if h : s ∈ Ioo p.a p.b then
      liftMap_S65 (F := F) p.n p.first p.last p.ordered
        ⟨s, p.a_nonneg.trans h.1.le, h.2.le.trans p.horizon⟩
        (p.stages ⟨s, p.a_nonneg.trans h.1.le, h.2.le.trans p.horizon⟩ h).1
        (p.stages ⟨s, p.a_nonneg.trans h.1.le, h.2.le.trans p.horizon⟩ h).2 y
    else w₀ s hsW
  have hval : ∀ (τ : Icc (0 : ℝ) (F.tower.history p.n).horizon) (hτ : (τ : ℝ) ∈ Ioo p.a p.b)
      (hτW : (τ : ℝ) ∈ W), w₂ τ hτW = liftMap_S65 (F := F) p.n p.first p.last p.ordered τ
        (p.stages τ hτ).1 (p.stages τ hτ).2 y := by
    intro τ hτ hτW
    change (if h : (τ : ℝ) ∈ Ioo p.a p.b then _ else _) = _
    simp only [hτ, ↓reduceDIte]
  refine ⟨w₂, hval, ?_⟩
  intro s hsa hsb
  refine ⟨p.n, p.first, p.last, p.ordered, p.a, p.b, hsa, hsb, p.horizon, p.stages, y, ?_⟩
  intro r hr hrW
  rw [hval r hr hrW]
  exact liftMap_heq_S65 (F := F) p.n p.first p.last p.ordered r (p.stages r hr).1 (p.stages r hr).2 y

end Patch

theorem closed_step_S145 {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (Hold : FiniteVolumeHyperbolicModel.{u}) (start : ℝ) (hstart : 0 < start)
    (mold : ∀ t : ℝ, start ≤ t → Hold.Carrier → (postStage F.observation t).Carrier)
    (α : ℝ → ℝ) (Ω : TopologicalSpace.Opens (ℝ × Hold.Carrier))
    (hball : ∀ t, start ≤ t →
      riemannianBallOf Hold.metric Hold.basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t)
    (hpatch : ∀ t (_ : start ≤ t), ∀ x ∈ sourceSlice_CX5 Ω t,
      Nonempty (PersistentModelPatch F Hold start α (sourceSlice_CX5 Ω) mold t x))
    (R r : ℝ) (hr : start ≤ r) (hRα : ∀ s, r ≤ s → R < 2 * (α s)⁻¹)
    (t : ℝ) (W : Set ℝ) (w : ∀ s : ℝ, s ∈ W → (postStage F.observation s).Carrier) (hW : Icc r t ⊆ W)
    (hlift : ∀ s ∈ Icc r t, ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
          (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
          (_ : b ≤ (F.tower.history n).horizon)
          (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
            first ≤ (F.tower.history n).toHistory.activeStage r ∧
              (F.tower.history n).toHistory.activeStage r ≤ last)
          (y : (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
          ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b) (hrW : (r : ℝ) ∈ W),
            HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
              ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 y)
              (w r hrW))
    {s : ℝ} (hs : s ∈ Icc r t) (q' : Hold.Carrier) (ρ : ℝ)
    (hρ : riemannianClosedBallOf Hold.metric q' ρ ⊆ riemannianBallOf Hold.metric Hold.basepoint R)
    (σ : ℕ → ℝ) (hσs : ∀ k, s < σ k) (hσt : ∀ k, σ k ≤ t) (hσlim : Tendsto σ atTop (nhds s))
    (x : ℕ → Hold.Carrier)
    (hxm : ∀ k, mold (σ k) (hr.trans (hs.1.trans (hσs k).le)) (x k) =
      w (σ k) (hW ⟨hs.1.trans (hσs k).le, hσt k⟩))
    (D : ℕ → ℝ) (D' : ℝ) (hD : Tendsto D atTop (nhds D')) (hDρ : ∀ k, D k ≤ ρ)
    (hxd : ∀ k, riemannianEDistOf Hold.metric q' (x k) ≤ ENNReal.ofReal (D k)) :
    ∃ x' : Hold.Carrier, mold s (hr.trans hs.1) x' = w s (hW hs) ∧
      riemannianEDistOf Hold.metric q' x' ≤ ENNReal.ofReal D' := by
  have hss : start ≤ s := hr.trans hs.1
  have hs0 : 0 < s := hstart.trans_le hss
  have hK := isCompact_riemannianClosedBallOf Hold.complete q' ρ
  have hxK : ∀ k, x k ∈ riemannianClosedBallOf Hold.metric q' ρ := fun k =>
    (hxd k).trans (ENNReal.ofReal_le_ofReal (hDρ k))
  obtain ⟨a, haK, hxφ⟩ := hK.exists_mapClusterPt_of_frequently (l := atTop) (f := x)
    (Filter.Eventually.frequently (Filter.Eventually.of_forall hxK))
  have hda : riemannianEDistOf Hold.metric q' a ≤ ENNReal.ofReal D' := by
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hc1, hc2⟩ := exists_between hcon
    have hctop : c ≠ ⊤ := ne_top_of_lt hc2
    have hcr : c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hctop).symm
    have hD'c : D' < c.toReal := by
      rw [hcr] at hc1
      exact (ENNReal.ofReal_lt_ofReal_iff'.1 hc1).1
    have hev : ∀ᶠ k in atTop, x k ∈ riemannianClosedBallOf Hold.metric q' c.toReal := by
      filter_upwards [hD.eventually (gt_mem_nhds hD'c)] with k hk
      exact (hxd k).trans (ENNReal.ofReal_le_ofReal hk.le)
    have hmem := (Geometry.Metric.isClosed_riemannianClosedBallOf Hold.metric q' c.toReal).mem_of_mapClusterPt
      hxφ hev
    have : riemannianEDistOf Hold.metric q' a ≤ c := by
      have h1 : riemannianEDistOf Hold.metric q' a ≤ ENNReal.ofReal c.toReal := hmem
      rwa [← hcr] at h1
    exact absurd (this.trans_lt hc2) (lt_irrefl _)
  have hB := riemannianBallOf_mono Hold.metric Hold.basepoint (hRα s hs.1).le (hρ haK)
  obtain ⟨p⟩ := hpatch s hss a (hball s hss hB)
  have hsab : s ∈ Ioo p.a p.b := ⟨p.before, p.after⟩
  let τs : Icc (0 : ℝ) (F.tower.history p.n).horizon :=
    ⟨s, p.a_nonneg.trans hsab.1.le, hsab.2.le.trans p.horizon⟩
  let Fm : ℝ × Hold.Carrier → (postStage F.observation s).Carrier := fun q =>
    liftMap_S65 (F := F) p.n p.first p.last p.ordered τs (p.stages τs hsab).1 (p.stages τs hsab).2 (p.map q)
  have hk3 : ∀ k, σ k ∈ Ioo p.a p.b → x k ∈ p.neighborhood → w s (hW hs) = Fm (σ k, x k) := by
    intro k hk1 hk2
    obtain ⟨w₂, hw₂val, hw₂lift⟩ := patch_flowline2_S145 p (p.map (σ k, x k)) W w
    have hσk := hσs k
    have hIcc : Icc s (σ k) ⊆ W := fun u hu => hW ⟨hs.1.trans hu.1, hu.2.trans (hσt _)⟩
    have hab : ∀ u ∈ Icc s (σ k), u ∈ Ioo p.a p.b := fun u hu =>
      ⟨lt_of_lt_of_le p.before hu.1, lt_of_le_of_lt hu.2 hk1.2⟩
    have hfl := flowline_unique_Icc_S115 F W w w₂ s (σ k) hs0 hσk.le hIcc
      (fun u hu => hlift u ⟨hs.1.trans hu.1, hu.2.trans (hσt _)⟩)
      (fun u hu => hw₂lift u (hab u hu).1 (hab u hu).2)
      (by
        rw [hw₂val ⟨σ k, p.a_nonneg.trans hk1.1.le, hk1.2.le.trans p.horizon⟩ hk1 (hIcc ⟨hσk.le, le_rfl⟩)]
        rw [liftMap_map_eq_mold_S145 p ⟨σ k, p.a_nonneg.trans hk1.1.le, hk1.2.le.trans p.horizon⟩ hk1
          (hr.trans (hs.1.trans hσk.le)) hk2]
        exact (hxm k).symm)
    rw [hfl s ⟨le_rfl, hσk.le⟩, hw₂val τs hsab (hIcc ⟨le_rfl, hσk.le⟩)]
  have hmapc : ContinuousAt p.map (s, a) :=
    (p.smooth.contMDiffAt ((isOpen_Ioo.prod p.neighborhood.isOpen).mem_nhds
      ⟨hsab, p.mem_neighborhood⟩)).continuousAt
  have hFc : ContinuousAt Fm (s, a) :=
    ((liftMap_continuous_S145 p τs hsab).continuousAt).comp hmapc
  have hall : ∀ V ∈ nhds (Fm (s, a)), w s (hW hs) ∈ V := by
    intro V hV
    obtain ⟨U1, hU1, U2, hU2, hsub⟩ := mem_nhds_prod_iff.1 (hFc.preimage_mem_nhds hV)
    have hev1 : ∀ᶠ k in atTop, σ k ∈ U1 ∩ Ioo p.a p.b :=
      hσlim.eventually (inter_mem hU1 (isOpen_Ioo.mem_nhds hsab))
    have hfr : ∃ᶠ k in atTop, x k ∈ U2 ∩ (p.neighborhood : Set Hold.Carrier) :=
      mapClusterPt_iff_frequently.1 hxφ _ (inter_mem hU2 (p.neighborhood.isOpen.mem_nhds p.mem_neighborhood))
    obtain ⟨k, hk1, hk2⟩ := (hev1.and_frequently hfr).exists
    rw [hk3 k hk1.2 hk2.2]
    exact hsub ⟨hk1.1, hk2.1⟩
  have hz : Fm (s, a) = w s (hW hs) := by
    refine eq_of_nhds_neBot (Filter.neBot_of_le (le_inf ?_ (pure_le_nhds (w s (hW hs)))))
    exact (pure_le_iff.2 hall : pure (w s (hW hs)) ≤ nhds (Fm (s, a)))
  refine ⟨a, ?_, hda⟩
  rw [← hz]
  exact (liftMap_map_eq_mold_S145 p τs hsab hss p.mem_neighborhood).symm

end GC.LongTime.Ch12
