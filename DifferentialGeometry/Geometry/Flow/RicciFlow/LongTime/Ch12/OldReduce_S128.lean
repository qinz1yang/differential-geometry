import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.NearIso_S128

set_option autoImplicit false

/-! # CH12-S128 G1b: `OLD_of_drift_S128` — the old half `OLD_S128` from the model-drift lemma `hdrift`

`OLD_S128` (frozen v2): `∀ L > 0, ∃ T0, ∀ r ≤ t ≤ 2 r (r ≥ T0), q ∈ B(Rold-L), 0 < δ ≤ L/4, w` a flow-line lifted at every
`s ∈ [r,t]` with `d_t(mold t q, w t) < δ` : `d_r(mold r q, w r) < 2 δ + L/16`.
Split: (cover + two-sided near-isometry, `nearIso_S128`) `w t = mold t q'`, `q' ∈ B(Rold)`, `d_r(mold r q, mold r q') < 2δ`;
(drift, the ONLY remaining input `hdrift`) `d_r(mold r q', w r) < L/16`; then the triangle inequality. -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

theorem mul_lt_ofReal_S128 {c δ : ℝ} (hc : 0 < c) {d : ℝ≥0∞} (hd : d < ENNReal.ofReal δ) :
    ENNReal.ofReal c * d < ENNReal.ofReal (c * δ) := by
  rw [ENNReal.ofReal_mul hc.le, mul_comm (ENNReal.ofReal c) d,
    mul_comm (ENNReal.ofReal c) (ENNReal.ofReal δ)]
  exact ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top hd

theorem OLD_of_drift_S128 {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (Hold : FiniteVolumeHyperbolicModel.{u}) (K : ℕ) (start : ℝ) (hstart : 0 < start)
    (mold : (t : ℝ) → start ≤ t → Hold.Carrier → (postStage F.observation t).Carrier)
    (α : ℝ → ℝ) (Ω : TopologicalSpace.Opens (ℝ × Hold.Carrier))
    (hαpos : ∀ t, start ≤ t → 0 < α t)
    (hαlim : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε)
    (hsm : ∀ t (ht : start ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold t ht) (sourceSlice_CX5 Ω t))
    (hemb : ∀ t (ht : start ≤ t),
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => mold t ht x))
    (hball : ∀ t, start ≤ t →
      riemannianBallOf Hold.metric Hold.basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t)
    (hck : ∀ t (ht : start ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
      ∀ p ∈ riemannianBallOf Hold.metric Hold.basepoint (2 * (α t)⁻¹),
        ckErr_S45 Hold (postMetric F.observation t) t⁻¹ (mold t ht) k p < α t)
    (Rold : ℝ)
    (hdrift : ∀ ε : ℝ, 0 < ε → ∃ T0 : ℝ, ∀ (r t : ℝ) (hri : start ≤ r) (hti : start ≤ t),
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
        (mold r hri q') (w r (hW ⟨le_rfl, hrt⟩)) < ENNReal.ofReal ε)
    (L : ℝ) (hL : 0 < L) :
    ∃ T0 : ℝ, ∀ (r t : ℝ) (hri : start ≤ r) (hti : start ≤ t), T0 ≤ r → ∀ (hrt : r ≤ t), t ≤ 2 * r →
      ∀ q ∈ riemannianBallOf Hold.metric Hold.basepoint (Rold - L), ∀ δ : ℝ, 0 < δ → δ ≤ L / 4 →
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
      riemannianEDistOf (scaleMetric t⁻¹ (inv_pos.mpr (hstart.trans_le hti)) (postMetric F.observation t))
        (mold t hti q) (w t (hW ⟨hrt, le_rfl⟩)) < ENNReal.ofReal δ →
      riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr (hstart.trans_le hri)) (postMetric F.observation r))
        (mold r hri q) (w r (hW ⟨le_rfl, hrt⟩)) < ENNReal.ofReal (2 * δ + L / 16) := by
  obtain ⟨T1, hT1⟩ := nearIso_S128 F Hold K start hstart mold α Ω hαpos hαlim hsm hemb hball hck Rold L hL
  obtain ⟨T2, hT2⟩ := hdrift (L / 16) (by positivity)
  refine ⟨max (max T1 T2) start, fun r t hri hti hT hrt htr q hq δ hδ hδL W w hW hlift hd => ?_⟩
  have hr1 : T1 ≤ r := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hr2 : T2 ≤ r := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have ht1 : T1 ≤ t := hr1.trans hrt
  obtain ⟨hαt, hlowt, -⟩ := hT1 t hti ht1
  obtain ⟨hαr, -, hupr⟩ := hT1 r hri hr1
  obtain ⟨q', hq', hq'y, hdh⟩ := hlowt q hq (A := δ) (by linarith) _ hd
  have hαt0 := hαpos t hti
  have hαr0 := hαpos r hri
  have hv : 7 / 10 < Real.sqrt (1 - α t) := by
    rw [Real.lt_sqrt (by norm_num)]; nlinarith
  have hvpos : 0 < Real.sqrt (1 - α t) := by linarith
  have hupos : 0 < Real.sqrt (1 + α r) := Real.sqrt_pos.mpr (by linarith)
  have hu : Real.sqrt (1 + α r) < 5 / 4 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  have hc : 1 / Real.sqrt (1 - α t) < 10 / 7 := by
    rw [div_lt_iff₀ hvpos]; nlinarith
  have hcpos : 0 < 1 / Real.sqrt (1 - α t) := by positivity
  have hdh' : riemannianEDistOf Hold.metric q q' <
      ENNReal.ofReal (1 / Real.sqrt (1 - α t) * δ) := lt_of_le_of_lt hdh (mul_lt_ofReal_S128 hcpos hd)
  have hdhL : riemannianEDistOf Hold.metric q q' < ENNReal.ofReal L := by
    refine lt_of_lt_of_le hdh' (ENNReal.ofReal_le_ofReal ?_)
    nlinarith
  have hd1 := hupr q hq q' hdhL
  have hd2 : riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr (hstart.trans_le hri))
      (postMetric F.observation r)) (mold r hri q) (mold r hri q') < ENNReal.ofReal (2 * δ) := by
    refine lt_of_le_of_lt hd1 (lt_of_lt_of_le (mul_lt_ofReal_S128 hupos hdh') ?_)
    apply ENNReal.ofReal_le_ofReal
    have h1 : Real.sqrt (1 + α r) * (1 / Real.sqrt (1 - α t)) ≤ 2 := by
      have := mul_le_mul hu.le hc.le hcpos.le (by norm_num)
      linarith
    nlinarith
  have hd3 := hT2 r t hri hti hr2 hrt htr q' hq' W w hW hlift hq'y.symm
  calc _ ≤ riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr (hstart.trans_le hri))
        (postMetric F.observation r)) (mold r hri q) (mold r hri q') +
        riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr (hstart.trans_le hri))
        (postMetric F.observation r)) (mold r hri q') (w r (hW ⟨le_rfl, hrt⟩)) :=
        riemannianEDistOf_triangle _ _ _ _
    _ < ENNReal.ofReal (2 * δ) + ENNReal.ofReal (L / 16) := ENNReal.add_lt_add hd2 hd3
    _ = ENNReal.ofReal (2 * δ + L / 16) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

end GC.LongTime.Ch12
