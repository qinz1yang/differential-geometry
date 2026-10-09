import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchSpeed_S145
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.FlowlineUnique_S115
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CurveLog_S136
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchCore_S61

set_option autoImplicit false

/-! # CH12-S145 G2a: `open_step_S145` — downward openness of the continuity method

Given `x2 ∈ B(R)` with `mold σ2 x2 = w σ2` (`w` a flow-line, lifted at every `s ∈ [r,t]`), the IFT curve `c` of a patch
at `(σ2, x2)` (`map (σ, c σ) = map (σ2, x2)`) satisfies `mold σ (c σ) = w σ` (`flowline_unique_Icc_S115` against the
survivor flow-line of `y = map (σ2, x2)`) and `d_h (c σ, x2) ≤ √2 · α_r · log (σ2/σ)`
(`patch_speed_S145` + `edist_curve_log_S136`). -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Manifold GC.LongTime GC.LongTime.Ch12 GC.LongTime.CuspP1
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

theorem hlow_S145 {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (Hold : FiniteVolumeHyperbolicModel.{u}) (start : ℝ)
    (mold : ∀ t : ℝ, start ≤ t → Hold.Carrier → (postStage F.observation t).Carrier) (α : ℝ → ℝ)
    (hck0 : ∀ t (ht : start ≤ t), ∀ q ∈ riemannianBallOf Hold.metric Hold.basepoint (2 * (α t)⁻¹),
      ckErr_S45 Hold (postMetric F.observation t) t⁻¹ (mold t ht) 0 q < α t)
    {t : ℝ} (ht : start ≤ t) {q : Hold.Carrier}
    (hq : q ∈ riemannianBallOf Hold.metric Hold.basepoint (2 * (α t)⁻¹)) (w : TangentSpace (𝓡 3) q) :
    (1 - α t) * Hold.metric.inner q w w ≤
      t⁻¹ * (postMetric F.observation t).inner (mold t ht q)
        (mfderiv (𝓡 3) (𝓡 3) (mold t ht) q w) (mfderiv (𝓡 3) (𝓡 3) (mold t ht) q w) :=
  pullback_inner_ge_of_ckErr_S90 Hold (postMetric F.observation t) t⁻¹ (mold t ht) q (hck0 t ht q hq) w

section Patch

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {Hold : FiniteVolumeHyperbolicModel.{u}} {start : ℝ} {α : ℝ → ℝ}
  {Ω : TopologicalSpace.Opens (ℝ × Hold.Carrier)}
  {mold : ∀ t : ℝ, start ≤ t → Hold.Carrier → (postStage F.observation t).Carrier}
  {t₀ : ℝ} {x₀ : Hold.Carrier}

/-- The survivor flow-line of `y` inside the patch window, extended arbitrarily (by `w₀`) outside it. -/
theorem patch_flowline_S145 (p : PersistentModelPatch F Hold start α (sourceSlice_CX5 Ω) mold t₀ x₀)
    (y : (F.tower.history p.n).toHistory.backwardSurvivorDomain p.first p.last p.ordered)
    (W : Set ℝ) (w₀ : ∀ s : ℝ, s ∈ W → (postStage F.observation s).Carrier) :
    ∃ w₂ : ∀ s : ℝ, s ∈ W → (postStage F.observation s).Carrier,
      (∀ (τ : Icc (0 : ℝ) (F.tower.history p.n).horizon) (_ : (τ : ℝ) ∈ Ioo p.a p.b)
        (hT : start ≤ (τ : ℝ)) (hτW : (τ : ℝ) ∈ W) (x : Hold.Carrier) (_ : x ∈ p.neighborhood),
        p.map ((τ : ℝ), x) = y → w₂ τ hτW = mold τ hT x) ∧
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
  refine ⟨w₂, ?_, ?_⟩
  · intro τ hτ hT hτW x hx hxy
    have hd : w₂ τ hτW = liftMap_S65 (F := F) p.n p.first p.last p.ordered τ (p.stages τ hτ).1
        (p.stages τ hτ).2 y := by
      change (if h : (τ : ℝ) ∈ Ioo p.a p.b then _ else _) = _
      simp only [hτ, ↓reduceDIte]
    rw [hd, ← hxy]
    exact eq_of_heq ((liftMap_heq_S65 (F := F) p.n p.first p.last p.ordered τ (p.stages τ hτ).1
      (p.stages τ hτ).2 (p.map ((τ : ℝ), x))).symm.trans (p.agrees τ hτ hT x hx))
  · intro s hsa hsb
    refine ⟨p.n, p.first, p.last, p.ordered, p.a, p.b, hsa, hsb, p.horizon, p.stages, y, ?_⟩
    intro r hr hrW
    have hd : w₂ r hrW = liftMap_S65 (F := F) p.n p.first p.last p.ordered r (p.stages r hr).1
        (p.stages r hr).2 y := by
      change (if h : (r : ℝ) ∈ Ioo p.a p.b then _ else _) = _
      simp only [hr, ↓reduceDIte]
    rw [hd]
    exact liftMap_heq_S65 (F := F) p.n p.first p.last p.ordered r (p.stages r hr).1 (p.stages r hr).2 y

end Patch

theorem open_step_S145 {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (Hold : FiniteVolumeHyperbolicModel.{u}) (start : ℝ) (hstart : 0 < start)
    (mold : ∀ t : ℝ, start ≤ t → Hold.Carrier → (postStage F.observation t).Carrier)
    (α : ℝ → ℝ) (Ω : TopologicalSpace.Opens (ℝ × Hold.Carrier))
    (hαpos : ∀ t, start ≤ t → 0 < α t) (hanti : AntitoneOn α (Ici start))
    (hck0 : ∀ t (ht : start ≤ t), ∀ q ∈ riemannianBallOf Hold.metric Hold.basepoint (2 * (α t)⁻¹),
      ckErr_S45 Hold (postMetric F.observation t) t⁻¹ (mold t ht) 0 q < α t)
    (hball : ∀ t, start ≤ t →
      riemannianBallOf Hold.metric Hold.basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t)
    (hpatch : ∀ t (_ : start ≤ t), ∀ x ∈ sourceSlice_CX5 Ω t,
      Nonempty (PersistentModelPatch F Hold start α (sourceSlice_CX5 Ω) mold t x))
    (R r : ℝ) (hr : start ≤ r) (hα12 : ∀ s, r ≤ s → α s < 1 / 2)
    (hRα : ∀ s, r ≤ s → R < 2 * (α s)⁻¹)
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
    {σ2 : ℝ} (hσ2 : σ2 ∈ Ioc r t) {x2 : Hold.Carrier}
    (hx2 : x2 ∈ riemannianBallOf Hold.metric Hold.basepoint R)
    (hx2m : mold σ2 (hr.trans hσ2.1.le) x2 = w σ2 (hW ⟨hσ2.1.le, hσ2.2⟩)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ (hσ : σ ∈ Ioc (σ2 - δ) σ2) (hrσ : r ≤ σ), ∃ x : Hold.Carrier,
      mold σ (hr.trans hrσ) x = w σ (hW ⟨hrσ, hσ.2.trans hσ2.2⟩) ∧
      riemannianEDistOf Hold.metric x x2 ≤
        ENNReal.ofReal (Real.sqrt 2 * α r * Real.log (σ2 / σ)) := by
  have hσ2s : start ≤ σ2 := hr.trans hσ2.1.le
  have hB : ∀ s, r ≤ s → riemannianBallOf Hold.metric Hold.basepoint R ⊆
      riemannianBallOf Hold.metric Hold.basepoint (2 * (α s)⁻¹) := fun s hs =>
    riemannianBallOf_mono _ _ (hRα s hs).le
  have hx2' := hB σ2 hσ2.1.le hx2
  obtain ⟨p⟩ := hpatch σ2 hσ2s x2 (hball σ2 hσ2s hx2')
  have hσ2ab : σ2 ∈ Ioo p.a p.b := ⟨p.before, p.after⟩
  let τ2 : Icc (0 : ℝ) (F.tower.history p.n).horizon :=
    ⟨σ2, p.a_nonneg.trans hσ2ab.1.le, hσ2ab.2.le.trans p.horizon⟩
  let U : TopologicalSpace.Opens (ℝ × Hold.Carrier) :=
    ⟨Ioo p.a p.b ×ˢ (p.neighborhood : Set Hold.Carrier), isOpen_Ioo.prod p.neighborhood.isOpen⟩
  have hinj := patch_inj_S145 p τ2 hσ2ab hσ2s p.mem_neighborhood
    (by linarith [hα12 σ2 hσ2.1.le])
    (fun w' => hlow_S145 F Hold start mold α hck0 hσ2s hx2' w')
  obtain ⟨c, hc0, δ1, hδ1, hc⟩ := local_curve_S136 (Θ := p.map) U p.smooth (σ1 := σ2) (x1 := x2)
    ⟨hσ2ab, p.mem_neighborhood⟩ hinj
  have hcont : ContinuousAt c σ2 := (hc σ2 ⟨by linarith, by linarith⟩).2.2.continuousAt
  have hev : ∀ᶠ σ in nhds σ2, c σ ∈ riemannianBallOf Hold.metric Hold.basepoint R :=
    hcont.eventually_mem ((isOpen_riemannianBallOf_S61 Hold R).mem_nhds (hc0 ▸ hx2))
  obtain ⟨δ2, hδ2, hδ2'⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro σ hσ hrσ
  have hmin1 := min_le_left δ1 δ2
  have hmin2 := min_le_right δ1 δ2
  have hσσ2 : σ ≤ σ2 := hσ.2
  have hτ1 : ∀ τ ∈ Icc σ σ2, τ ∈ Ioo (σ2 - δ1) (σ2 + δ1) := fun τ hτ =>
    ⟨by linarith [hσ.1, hτ.1], by linarith [hτ.2]⟩
  have hτR : ∀ τ ∈ Icc σ σ2, c τ ∈ riemannianBallOf Hold.metric Hold.basepoint R := fun τ hτ =>
    hδ2' (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hσ.1, hτ.1, hτ.2])
  have hab : ∀ s ∈ Icc σ σ2, s ∈ Ioo p.a p.b := fun s hs =>
    ((hc s (hτ1 s hs)).1 : (s, c s) ∈ Ioo p.a p.b ×ˢ (p.neighborhood : Set Hold.Carrier)).1
  have hcN : ∀ s ∈ Icc σ σ2, c s ∈ p.neighborhood := fun s hs =>
    ((hc s (hτ1 s hs)).1 : (s, c s) ∈ Ioo p.a p.b ×ˢ (p.neighborhood : Set Hold.Carrier)).2
  have hσpos : 0 < σ := hstart.trans_le (hr.trans hrσ)
  have hIcc : Icc σ σ2 ⊆ W := fun s hs => hW ⟨hrσ.trans hs.1, hs.2.trans hσ2.2⟩
  obtain ⟨w₂, hw₂eq, hw₂lift⟩ := patch_flowline_S145 p (p.map (σ2, x2)) W w
  have hfl := flowline_unique_Icc_S115 F W w w₂ σ σ2 hσpos hσσ2 hIcc
    (fun s hs => hlift s ⟨hrσ.trans hs.1, hs.2.trans hσ2.2⟩)
    (fun s hs => hw₂lift s (hab s hs).1 (hab s hs).2)
    ((hx2m.symm.trans (hw₂eq τ2 hσ2ab hσ2s (hIcc ⟨hσσ2, le_rfl⟩) x2 p.mem_neighborhood rfl).symm))
  have hστ : σ ∈ Ioo p.a p.b := hab σ ⟨le_rfl, hσσ2⟩
  have hmeq : mold σ (hr.trans hrσ) (c σ) = w σ (hW ⟨hrσ, hσ.2.trans hσ2.2⟩) := by
    have e1 := hw₂eq ⟨σ, p.a_nonneg.trans hστ.1.le, hστ.2.le.trans p.horizon⟩ hστ (hr.trans hrσ)
      (hIcc ⟨le_rfl, hσσ2⟩) (c σ) (hcN σ ⟨le_rfl, hσσ2⟩) (hc σ (hτ1 σ ⟨le_rfl, hσσ2⟩)).2.1
    exact e1.symm.trans (hfl σ ⟨le_rfl, hσσ2⟩).symm
  refine ⟨c σ, hmeq, ?_⟩
  have hsq2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hK0 : 0 ≤ Real.sqrt 2 * α r := (mul_pos hsq2 (hαpos r hr)).le
  have hmd : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 c (Icc σ σ2) := fun τ hτ =>
    ((hc τ (hτ1 τ hτ)).2.2.of_le (by exact_mod_cast le_top)).contMDiffWithinAt
  have hspd : ∀ τ ∈ Ioo σ σ2, Real.sqrt (Hold.metric.inner (c τ)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c τ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c τ 1)) ≤ Real.sqrt 2 * α r / τ := by
    intro τ hτ
    have hτI : τ ∈ Icc σ σ2 := ⟨hτ.1.le, hτ.2.le⟩
    have hτab := hab τ hτI
    have hrτ : r ≤ τ := hrσ.trans hτ.1.le
    have hTτ : start ≤ τ := hr.trans hrτ
    have hτ0 : 0 < τ := hσpos.trans hτ.1
    let τe : Icc (0 : ℝ) (F.tower.history p.n).horizon :=
      ⟨τ, p.a_nonneg.trans hτab.1.le, hτab.2.le.trans p.horizon⟩
    have hy : ∀ᶠ σ' in nhds τ, p.map (σ', c σ') = p.map (σ2, x2) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (hτ1 τ hτI)) fun σ' h => (hc σ' h).2.1
    have hspeed := patch_speed_S145 p τe hτab hTτ c (hcN τ hτI)
      ((hc τ (hτ1 τ hτI)).2.2.mdifferentiableAt (by simp)) (p.map (σ2, x2)) hy
      (fun w' => hlow_S145 F Hold start mold α hck0 hTτ (hB τ hrτ (hτR τ hτI)) w')
    have hατ := hα12 τ hrτ
    have hατpos := hαpos τ hTτ
    have hατr : α τ ≤ α r := hanti (mem_Ici.2 hr) (mem_Ici.2 hTτ) hrτ
    have hnn := metric_inner_self_nonneg Hold.metric (c τ) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c τ 1)
    set I := Hold.metric.inner (c τ) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c τ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c τ 1) with hI
    have h1 : I ≤ 2 * ((1 - α τ) * I) := by nlinarith
    have h2 : α τ ^ 2 / τ ^ 2 ≤ α r ^ 2 / τ ^ 2 := by gcongr
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    calc I ≤ 2 * ((1 - α τ) * I) := h1
      _ ≤ 2 * (α τ ^ 2 / τ ^ 2) := by linarith
      _ ≤ 2 * (α r ^ 2 / τ ^ 2) := by linarith
      _ = 2 * α r ^ 2 / τ ^ 2 := by ring
  have hcurve := edist_curve_log_S136 Hold.metric c hK0 hσpos hσσ2 hmd hspd
  rw [hc0] at hcurve
  exact hcurve

end GC.LongTime.Ch12
