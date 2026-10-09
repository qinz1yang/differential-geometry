import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ClosedStep_S145
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.NearIso_S128

set_option autoImplicit false

/-! # CH12-S145 G2b: continuity method and `hdrift_S145`

`P(s) := ∃ x, mold s x = w s ∧ d_h(q', x) ≤ 2 α_r log (t/s)` on `[r, t]`: `P(t)` (`x = q'`), open step
(`open_step_S145`), closed step (`closed_step_S145`); `backward_induction_S145` gives `P(r)`, and
`nearIso_S128` (up part) turns `d_h(q', x) ≤ 2 α_r log 2` into `d_r(mold r q', mold r x) < ε`.
`hdrift_S145` is the `hdrift` binder of `hflow_S128`, verbatim. -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Collapse
open Manifold GC.LongTime GC.LongTime.Ch12 GC.LongTime.CuspP1
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

theorem backward_induction_S145 (r t : ℝ) (hrt : r ≤ t) (S : Set ℝ) (ht : t ∈ S)
    (hopen : ∀ s ∈ S, r < s → s ≤ t → ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Ioc (s - δ) s, r ≤ σ → σ ∈ S)
    (hclosed : ∀ s ∈ Icc r t, (∀ σ ∈ Ioc s t, σ ∈ S) → s ∈ S) :
    ∀ s ∈ Icc r t, s ∈ S := by
  let T : Set ℝ := {s | s ∈ Icc r t ∧ ∀ σ ∈ Icc s t, σ ∈ S}
  have htT : t ∈ T := ⟨⟨hrt, le_rfl⟩, fun σ hσ => by rw [le_antisymm hσ.2 hσ.1]; exact ht⟩
  have hbdd : BddBelow T := ⟨r, fun s hs => hs.1.1⟩
  have hne : T.Nonempty := ⟨t, htT⟩
  have hmr : r ≤ sInf T := le_csInf hne (fun s hs => hs.1.1)
  have hmt : sInf T ≤ t := csInf_le hbdd htT
  have hgt : ∀ σ ∈ Ioc (sInf T) t, σ ∈ S := by
    intro σ hσ
    obtain ⟨s', hs'T, hs'σ⟩ := exists_lt_of_csInf_lt hne hσ.1
    exact hs'T.2 σ ⟨hs'σ.le, hσ.2⟩
  have hmS : sInf T ∈ S := hclosed _ ⟨hmr, hmt⟩ hgt
  have hmT : sInf T ∈ T := ⟨⟨hmr, hmt⟩, fun σ hσ => by
    rcases eq_or_lt_of_le hσ.1 with h | h
    · rw [← h]; exact hmS
    · exact hgt σ ⟨h, hσ.2⟩⟩
  have hmeq : sInf T = r := by
    by_contra hne'
    have hlt : r < sInf T := lt_of_le_of_ne hmr (Ne.symm hne')
    obtain ⟨δ, hδ, hδS⟩ := hopen _ hmS hlt hmt
    have hm'm : max r (sInf T - δ / 2) < sInf T := max_lt hlt (by linarith)
    have hm'T : max r (sInf T - δ / 2) ∈ T := ⟨⟨le_max_left _ _, hm'm.le.trans hmt⟩, fun σ hσ => by
      rcases le_or_gt σ (sInf T) with h | h
      · exact hδS σ ⟨by have := le_max_right r (sInf T - δ / 2); linarith [hσ.1], h⟩
          ((le_max_left _ _).trans hσ.1)
      · exact hgt σ ⟨h, hσ.2⟩⟩
    exact absurd (csInf_le hbdd hm'T) (not_le.2 hm'm)
  intro s hs
  have hrT : r ∈ T := hmeq ▸ hmT
  exact hrT.2 s hs

theorem ball_add_S145 (Hold : FiniteVolumeHyperbolicModel.{u}) (Rold : ℝ) {q' : Hold.Carrier}
    (hq' : q' ∈ riemannianBallOf Hold.metric Hold.basepoint Rold) {ρ : ℝ} (hρ : ρ ≤ 1 / 2) :
    riemannianClosedBallOf Hold.metric q' ρ ⊆ riemannianBallOf Hold.metric Hold.basepoint (Rold + 1 / 2) := by
  intro y hy
  have hR0 : 0 < Rold := ENNReal.ofReal_pos.mp (lt_of_le_of_lt (by simp) hq')
  have h1 := riemannianEDistOf_triangle Hold.metric Hold.basepoint q' y
  have h2 : riemannianEDistOf Hold.metric Hold.basepoint q' + riemannianEDistOf Hold.metric q' y <
      ENNReal.ofReal Rold + ENNReal.ofReal ρ :=
    ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy) hq' hy
  have h3 : ENNReal.ofReal Rold + ENNReal.ofReal ρ ≤ ENNReal.ofReal (Rold + 1 / 2) :=
    calc ENNReal.ofReal Rold + ENNReal.ofReal ρ ≤ ENNReal.ofReal Rold + ENNReal.ofReal (1 / 2) :=
          add_le_add le_rfl (ENNReal.ofReal_le_ofReal hρ)
      _ = ENNReal.ofReal (Rold + 1 / 2) := (ENNReal.ofReal_add hR0.le (by norm_num)).symm
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)


theorem hdrift_one_S145 {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (Hold : FiniteVolumeHyperbolicModel.{u}) (start : ℝ) (hstart : 0 < start) (K : ℕ)
    (mold : ∀ t : ℝ, start ≤ t → Hold.Carrier → (postStage F.observation t).Carrier)
    (α : ℝ → ℝ) (Ω : TopologicalSpace.Opens (ℝ × Hold.Carrier))
    (hαpos : ∀ t, start ≤ t → 0 < α t) (hanti : AntitoneOn α (Ici start))
    (hαlim : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε)
    (hsm : ∀ t (ht : start ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold t ht) (sourceSlice_CX5 Ω t))
    (hemb : ∀ t (ht : start ≤ t),
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => mold t ht x))
    (hball : ∀ t, start ≤ t →
      riemannianBallOf Hold.metric Hold.basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t)
    (hck : ∀ t (ht : start ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
      ∀ p ∈ riemannianBallOf Hold.metric Hold.basepoint (2 * (α t)⁻¹),
        ckErr_S45 Hold (postMetric F.observation t) t⁻¹ (mold t ht) k p < α t)
    (hpatch : ∀ t (_ : start ≤ t), ∀ x ∈ sourceSlice_CX5 Ω t,
      Nonempty (PersistentModelPatch F Hold start α (sourceSlice_CX5 Ω) mold t x))
    (Rold : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ T0 : ℝ, ∀ (r t : ℝ) (hri : start ≤ r) (hti : start ≤ t),
        T0 ≤ r → ∀ (hrt : r ≤ t), t ≤ 2 * r →
        ∀ q' ∈ riemannianBallOf Hold.metric Hold.basepoint Rold,
        ∀ (W : Set ℝ) (w : ∀ s : ℝ, s ∈ W → (postStage F.observation s).Carrier) (hW : Icc r t ⊆ W),
        (∀ s ∈ Icc r t, ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
          (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
          (_ : b ≤ (F.tower.history n).horizon)
          (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
            first ≤ (F.tower.history n).toHistory.activeStage r ∧
              (F.tower.history n).toHistory.activeStage r ≤ last)
          (y : (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
          ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b) (hrW : (r : ℝ) ∈ W),
            HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
              ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 y)
              (w r hrW)) →
        w t (hW ⟨hrt, le_rfl⟩) = mold t hti q' →
        riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr (hstart.trans_le hri)) (postMetric F.observation r))
          (mold r hri q') (w r (hW ⟨le_rfl, hrt⟩)) < ENNReal.ofReal ε := by
  obtain ⟨T1, hT1⟩ := nearIso_S128 F Hold K start hstart mold α Ω hαpos hαlim hsm hemb hball hck
    (Rold + 1 / 2) (1 / 2) (by norm_num)
  obtain ⟨Tα, hTα⟩ := hαlim (min (min (1 / 4) (ε / 4)) (1 / (|Rold| + 1))) (by positivity)
  refine ⟨max (max T1 Tα) start, ?_⟩
  intro r t hri hti hT0 hrt htr q' hq' W w hW hlift hwt
  have hT1r : T1 ≤ r := (le_max_left _ _).trans ((le_max_left _ _).trans hT0)
  have hTαr : Tα ≤ r := (le_max_right _ _).trans ((le_max_left _ _).trans hT0)
  have hαs : ∀ s, r ≤ s → α s < min (min (1 / 4) (ε / 4)) (1 / (|Rold| + 1)) := fun s hs =>
    hTα s (hTαr.trans hs)
  have hα14 : ∀ s, r ≤ s → α s < 1 / 4 := fun s hs =>
    (hαs s hs).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hα12 : ∀ s, r ≤ s → α s < 1 / 2 := fun s hs => (hα14 s hs).trans (by norm_num)
  have hRα : ∀ s, r ≤ s → Rold + 1 / 2 < 2 * (α s)⁻¹ := by
    intro s hs
    have hα0 := hαpos s (hri.trans hs)
    have hαR : α s < 1 / (|Rold| + 1) := (hαs s hs).trans_le (min_le_right _ _)
    have h1 : |Rold| + 1 < (α s)⁻¹ := by
      rw [lt_inv_comm₀ (by positivity) hα0]
      simpa [one_div] using hαR
    have := le_abs_self Rold
    have hpos : 0 < (α s)⁻¹ := inv_pos.mpr hα0
    linarith
  have hck0 : ∀ t (ht : start ≤ t), ∀ q ∈ riemannianBallOf Hold.metric Hold.basepoint (2 * (α t)⁻¹),
      ckErr_S45 Hold (postMetric F.observation t) t⁻¹ (mold t ht) 0 q < α t :=
    fun t ht q hq => hck t ht 0 (Nat.zero_le _) q hq
  have hrpos : 0 < r := hstart.trans_le hri
  have hαr0 := hαpos r hri
  have hαr14 := hα14 r le_rfl
  have hlog2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set ρ : ℝ := 2 * α r * Real.log 2 with hρdef
  have hρ12 : ρ < 1 / 2 := by nlinarith
  have hρ0 : 0 ≤ ρ := by positivity
  have hρR := ball_add_S145 Hold Rold hq' hρ12.le
  -- the continuity-method predicate
  let S : Set ℝ := {s | ∃ (hs : s ∈ Icc r t) (x : Hold.Carrier),
    mold s (hri.trans hs.1) x = w s (hW hs) ∧
    riemannianEDistOf Hold.metric q' x ≤ ENNReal.ofReal (2 * α r * Real.log (t / s))}
  have hlogle : ∀ s ∈ Icc r t, Real.log (t / s) ≤ Real.log 2 := fun s hs =>
    Real.log_le_log (div_pos (hrpos.trans_le (hs.1.trans hs.2)) (hrpos.trans_le hs.1))
      ((div_le_iff₀ (hrpos.trans_le hs.1)).2 (by linarith [hs.1]))
  have hlog0 : ∀ s ∈ Icc r t, 0 ≤ Real.log (t / s) := fun s hs =>
    Real.log_nonneg ((one_le_div (hrpos.trans_le hs.1)).2 hs.2)
  have hrIcc : r ∈ Icc r t := ⟨le_rfl, hrt⟩
  have htIcc : t ∈ Icc r t := ⟨hrt, le_rfl⟩
  have htS : t ∈ S := ⟨htIcc, q', hwt.symm, by rw [riemannianEDistOf_self]; exact zero_le⟩
  have hopen : ∀ s ∈ S, r < s → s ≤ t → ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Ioc (s - δ) s, r ≤ σ → σ ∈ S := by
    intro s hsS hrs hst
    obtain ⟨hsI, x, hxm, hxd⟩ := hsS
    have hxd' : x ∈ riemannianClosedBallOf Hold.metric q' ρ :=
      hxd.trans (ENNReal.ofReal_le_ofReal (by
        have := hlogle s hsI
        have h2 : 0 ≤ 2 * α r := by positivity
        nlinarith))
    obtain ⟨δ, hδ, hδS⟩ := open_step_S145 F Hold start hstart mold α Ω hαpos hanti hck0 hball hpatch
      (Rold + 1 / 2) r hri hα12 hRα t W w hW hlift (σ2 := s) ⟨hrs, hst⟩ (x2 := x) (hρR hxd') hxm
    refine ⟨δ, hδ, fun σ hσ hrσ => ?_⟩
    obtain ⟨x', hx'm, hx'd⟩ := hδS σ hσ hrσ
    have hσI : σ ∈ Icc r t := ⟨hrσ, hσ.2.trans hst⟩
    have hσ0 : 0 < σ := hrpos.trans_le hrσ
    have hs0 : 0 < s := hrpos.trans hrs
    refine ⟨hσI, x', hx'm, ?_⟩
    have htri := riemannianEDistOf_triangle Hold.metric q' x x'
    rw [riemannianEDistOf_comm Hold.metric x' x] at hx'd
    refine htri.trans ?_
    have hA : 0 ≤ 2 * α r * Real.log (t / s) := by have := hlog0 s hsI; positivity
    have hsq : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    have hlsσ : 0 ≤ Real.log (s / σ) := Real.log_nonneg ((one_le_div hσ0).2 hσ.2)
    have hB : 0 ≤ Real.sqrt 2 * α r * Real.log (s / σ) := by positivity
    calc _ ≤ ENNReal.ofReal (2 * α r * Real.log (t / s)) +
          ENNReal.ofReal (Real.sqrt 2 * α r * Real.log (s / σ)) := add_le_add hxd hx'd
      _ = ENNReal.ofReal (2 * α r * Real.log (t / s) + Real.sqrt 2 * α r * Real.log (s / σ)) :=
          (ENNReal.ofReal_add hA hB).symm
      _ ≤ ENNReal.ofReal (2 * α r * Real.log (t / σ)) := by
          apply ENNReal.ofReal_le_ofReal
          have hlog : Real.log (t / σ) = Real.log (t / s) + Real.log (s / σ) := by
            rw [Real.log_div (by linarith) hσ0.ne', Real.log_div (by linarith) hs0.ne',
              Real.log_div hs0.ne' hσ0.ne']
            ring
          rw [hlog]
          have : Real.sqrt 2 * α r * Real.log (s / σ) ≤ 2 * α r * Real.log (s / σ) := by
            have := mul_le_mul_of_nonneg_right hsq (mul_nonneg hαr0.le hlsσ)
            nlinarith
          nlinarith
  have hclosed : ∀ s ∈ Icc r t, (∀ σ ∈ Ioc s t, σ ∈ S) → s ∈ S := by
    intro s hsI hall
    rcases eq_or_lt_of_le hsI.2 with hst | hst
    · rw [hst]; exact htS
    have hs0 : 0 < s := hrpos.trans_le hsI.1
    let σ : ℕ → ℝ := fun k => s + (t - s) * (1 / ((k : ℝ) + 1))
    have hσk : ∀ k, σ k ∈ Ioc s t := fun k => by
      have hk1 : 0 < 1 / ((k : ℝ) + 1) := by positivity
      have hk2 : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      constructor
      · have := mul_pos (sub_pos.2 hst) hk1; simp only [σ]; linarith
      · have := mul_le_mul_of_nonneg_left hk2 (sub_pos.2 hst).le; simp only [σ]; linarith
    have hσlim : Tendsto σ atTop (nhds s) := by
      have := (tendsto_const_nhds (x := s)).add
        ((tendsto_const_nhds (x := t - s)).mul tendsto_one_div_add_atTop_nhds_zero_nat)
      rw [mul_zero, add_zero] at this
      exact this
    have hSk := fun k => hall (σ k) (hσk k)
    choose hsk x hxk using hSk
    refine (?_ : ∃ x' : Hold.Carrier, mold s (hri.trans hsI.1) x' = w s (hW hsI) ∧
      riemannianEDistOf Hold.metric q' x' ≤ ENNReal.ofReal (2 * α r * Real.log (t / s))).elim
      (fun x' hx' => ⟨hsI, x', hx'⟩)
    refine closed_step_S145 F Hold start hstart mold α Ω hball hpatch (Rold + 1 / 2) r hri hRα t W w hW
      hlift hsI q' ρ hρR (fun k => σ k) (fun k => (hσk k).1) (fun k => (hσk k).2) hσlim x
      (fun k => (hxk k).1) (fun k => 2 * α r * Real.log (t / σ k)) (2 * α r * Real.log (t / s))
      ?_ (fun k => ?_) (fun k => (hxk k).2)
    · have h1 : Tendsto (fun k => Real.log (t / σ k)) atTop (nhds (Real.log (t / s))) :=
        Filter.Tendsto.log (tendsto_const_nhds.div hσlim hs0.ne') (div_pos (hrpos.trans_le (hsI.1.trans hsI.2)) hs0).ne'
      exact h1.const_mul _
    · have hkI : σ k ∈ Icc r t := ⟨hsI.1.trans (hσk k).1.le, (hσk k).2⟩
      have := hlogle (σ k) hkI
      have h2 : 0 ≤ 2 * α r := by positivity
      nlinarith
  have hr_all := backward_induction_S145 r t hrt S htS hopen hclosed r hrIcc
  obtain ⟨_, x, hxm, hxd⟩ := hr_all
  have hxd' : riemannianEDistOf Hold.metric q' x ≤ ENNReal.ofReal ρ :=
    hxd.trans (ENNReal.ofReal_le_ofReal (by
      have := hlogle r hrIcc
      have h2 : 0 ≤ 2 * α r := by positivity
      nlinarith))
  have hxL : riemannianEDistOf Hold.metric q' x < ENNReal.ofReal (1 / 2) :=
    lt_of_le_of_lt hxd' ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hρ12)
  obtain ⟨-, -, hup⟩ := hT1 r hri hT1r
  have hq'' : q' ∈ riemannianBallOf Hold.metric Hold.basepoint (Rold + 1 / 2 - 1 / 2) := by
    rwa [add_sub_cancel_right]
  have hu := hup q' hq'' x hxL
  rw [← hxm]
  refine lt_of_le_of_lt hu ?_
  calc ENNReal.ofReal (Real.sqrt (1 + α r)) * riemannianEDistOf Hold.metric q' x
      ≤ ENNReal.ofReal (Real.sqrt (1 + α r)) * ENNReal.ofReal ρ := by gcongr
    _ = ENNReal.ofReal (Real.sqrt (1 + α r) * ρ) := (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
    _ < ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_lt_ofReal_iff hε]
        have hsq : Real.sqrt (1 + α r) ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩
        have hεα : α r < ε / 4 := (hαs r le_rfl).trans_le
          ((min_le_left _ _).trans (min_le_right _ _))
        have hρle : ρ ≤ 2 * α r := by nlinarith
        have := mul_le_mul hsq hρle hρ0 (by norm_num)
        nlinarith

theorem hdrift_S145 {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
    (Rold : Fin old → ℝ) :
    ∀ i' : Fin old, ∀ (hs : 0 < sold i') (K : ℕ) (α : ℝ → ℝ)
        (Ω : TopologicalSpace.Opens (ℝ × (Hold i').Carrier)),
      ((∀ t, sold i' ≤ t → 0 < α t) ∧ AntitoneOn α (Ici (sold i')) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε) ∧
      (∀ t (ht : sold i' ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i' t ht) (sourceSlice_CX5 Ω t)) ∧
      (∀ t (ht : sold i' ≤ t),
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => mold i' t ht x)) ∧
      (∀ t, sold i' ≤ t →
        riemannianBallOf (Hold i').metric (Hold i').basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t) ∧
      (∀ t (ht : sold i' ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (2 * (α t)⁻¹),
          ckErr_S45 (Hold i') (postMetric F.observation t) t⁻¹ (mold i' t ht) k p < α t) ∧
      (∀ t (_ht : sold i' ≤ t), ∀ x ∈ sourceSlice_CX5 Ω t,
        Nonempty (PersistentModelPatch F (Hold i') (sold i') α (sourceSlice_CX5 Ω) (mold i') t x))) →
      ∀ ε : ℝ, 0 < ε → ∃ T0 : ℝ, ∀ (r t : ℝ) (hri : sold i' ≤ r) (hti : sold i' ≤ t),
        T0 ≤ r → ∀ (hrt : r ≤ t), t ≤ 2 * r →
        ∀ q' ∈ riemannianBallOf (Hold i').metric (Hold i').basepoint (Rold i'),
        ∀ (W : Set ℝ) (w : ∀ s : ℝ, s ∈ W → (postStage F.observation s).Carrier) (hW : Icc r t ⊆ W),
        (∀ s ∈ Icc r t, ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
          (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
          (_ : b ≤ (F.tower.history n).horizon)
          (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
            first ≤ (F.tower.history n).toHistory.activeStage r ∧
              (F.tower.history n).toHistory.activeStage r ≤ last)
          (y : (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
          ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b) (hrW : (r : ℝ) ∈ W),
            HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
              ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 y)
              (w r hrW)) →
        w t (hW ⟨hrt, le_rfl⟩) = mold i' t hti q' →
        riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr (hs.trans_le hri)) (postMetric F.observation r))
          (mold i' r hri q') (w r (hW ⟨le_rfl, hrt⟩)) < ENNReal.ofReal ε := by
  intro i' hs K α Ω hb ε hε
  obtain ⟨hαpos, hanti, hαlim, hsm, hemb, hball, hck, hpat⟩ := hb
  exact hdrift_one_S145 F (Hold i') (sold i') hs K (mold i') α Ω hαpos hanti hαlim hsm hemb hball hck hpat
    (Rold i') ε hε

end GC.LongTime.Ch12
