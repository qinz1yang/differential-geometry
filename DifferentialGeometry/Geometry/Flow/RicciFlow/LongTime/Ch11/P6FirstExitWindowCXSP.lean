import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.FirstExitDistanceP6M4

/-!
# CX-SPINE G6: first exit with a Ricci bound conditional on the whole remaining window

Source: `FirstExitDistanceP6M4.firstExit_distance_P6M4`, lines 50–119.
Source SHA-256:
`f9ae4c2759be953b967e450d9dea0dff4166a61ebcfa1e58fd83f570fa909413`.

Only the conditional Ricci input and its use in `hdist` change. For each `s`,
the Ricci producer receives the full fact that the distance stays below `X`
on `Ioo s t`; it then supplies the endpoint Ricci bounds on that same interval.
The original distance margin, strict slab endpoints, and distance conclusion
are retained. The remaining `sInf` and upper-semicontinuity argument is unchanged.

This theorem does not assume that the whole window already has the desired
footprint, nor does it produce the conditional Ricci input from Good data.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- A Ricci bound produced from each entire unexited window suffices for the
same quantitative first-exit distance estimate on the full closed interval. -/
theorem ObservedHistory.firstExit_distance_of_window_ricci_CXSP
    (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    {a t ℓ : ℝ} (hℓ : 0 < ℓ) (hat : a ≤ t) (ha : H.time e.castSucc < a)
    (ht : t < H.time e.succ) (p q : (H.stage e.castSucc).Carrier) {X : ℝ≥0∞}
    (hmargin : riemannianEDistOf ((H.event e).incoming.flow.base.metric t) p q +
      ENNReal.ofReal ((8 / ℓ) * (t - a)) < X)
    (hRic : ∀ s ∈ Icc a t,
      (∀ u ∈ Ioo s t,
        riemannianEDistOf ((H.event e).incoming.flow.base.metric u) p q < X) →
      ∀ u ∈ Ioo s t,
      ∀ z : (H.stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf ((H.event e).incoming.flow.base.metric u) p z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf ((H.event e).incoming.flow.base.metric u) q z < ENNReal.ofReal ℓ) →
      ricciTensor ((H.event e).incoming.flow.base.metric u) z ξ ξ ≤
        (3 / ℓ ^ 2) * ((H.event e).incoming.flow.base.metric u).inner z ξ ξ) :
    ∀ s ∈ Icc a t, riemannianEDistOf ((H.event e).incoming.flow.base.metric s) p q ≤
      riemannianEDistOf ((H.event e).incoming.flow.base.metric t) p q +
        ENNReal.ofReal ((8 / ℓ) * (t - s)) := by
  -- 区间 `[s, t]`（`a ≤ s`）上 Good ⇒ I.8.3(b)
  have hdist : ∀ s, a ≤ s → s ≤ t →
      (∀ s' ∈ Ioo s t, riemannianEDistOf ((H.event e).incoming.flow.base.metric s') p q < X) →
      riemannianEDistOf ((H.event e).incoming.flow.base.metric s) p q ≤
        riemannianEDistOf ((H.event e).incoming.flow.base.metric t) p q +
          ENNReal.ofReal ((8 / ℓ) * (t - s)) := by
    intro s has hst hgood
    exact H.edist_le_add_of_slab_ricci_P6M4 e hℓ hst (ha.trans_le has) ht p q
      (hRic s ⟨has, hst⟩ hgood)
  -- Good 集合与首出时刻
  let S : Set ℝ := {s | a ≤ s ∧ s ≤ t ∧
    ∀ s' ∈ Icc s t, riemannianEDistOf ((H.event e).incoming.flow.base.metric s') p q < X}
  have htS : t ∈ S := by
    refine ⟨hat, le_rfl, fun s' hs' => ?_⟩
    have h : s' = t := le_antisymm hs'.2 hs'.1
    rw [h]
    exact lt_of_le_of_lt le_self_add hmargin
  have hne : S.Nonempty := ⟨t, htS⟩
  have hbdd : BddBelow S := ⟨a, fun s hs => hs.1⟩
  have hastar : a ≤ sInf S := le_csInf hne fun s hs => hs.1
  have hstart : sInf S ≤ t := csInf_le hbdd htS
  have hup : ∀ s' ∈ Ioc (sInf S) t,
      riemannianEDistOf ((H.event e).incoming.flow.base.metric s') p q < X := by
    intro s' hs'
    obtain ⟨s, hsS, hss'⟩ := exists_lt_of_csInf_lt hne hs'.1
    exact hsS.2.2 s' ⟨hss'.le, hs'.2⟩
  have hℓ8 : (8 / ℓ) * (t - sInf S) ≤ (8 / ℓ) * (t - a) :=
    mul_le_mul_of_nonneg_left (by linarith) (div_pos (by norm_num) hℓ).le
  have hstar_lt : riemannianEDistOf ((H.event e).incoming.flow.base.metric (sInf S)) p q < X :=
    lt_of_le_of_lt ((hdist (sInf S) hastar hstart fun s' hs' => hup s' ⟨hs'.1, hs'.2.le⟩).trans
      (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hℓ8))) hmargin
  have hstarS : sInf S ∈ S := by
    refine ⟨hastar, hstart, fun s' hs' => ?_⟩
    rcases eq_or_lt_of_le hs'.1 with h | h
    · rw [← h]
      exact hstar_lt
    · exact hup s' ⟨h, hs'.2⟩
  -- 首出时刻 = `a`（USC 左延拓）
  have hstar_eq : sInf S = a := by
    by_contra hne'
    have hlt : a < sInf S := lt_of_le_of_ne hastar (Ne.symm hne')
    obtain ⟨s₁, has₁, hs₁, hnear⟩ := edist_lt_near_left_P6L4 (H.event e).incoming.flow
      (H.event e).incoming.equation hlt
      (fun r hr => ⟨ha.trans_le hr.1, lt_of_le_of_lt (hr.2.trans hstart) ht⟩) p q hstar_lt
    have hs₁S : s₁ ∈ S := by
      refine ⟨has₁, hs₁.le.trans hstart, fun s' hs' => ?_⟩
      rcases le_or_gt s' (sInf S) with h | h
      · exact hnear s' ⟨hs'.1, h⟩
      · exact hup s' ⟨h, hs'.2⟩
    have := csInf_le hbdd hs₁S
    linarith
  intro s hs
  refine hdist s hs.1 hs.2 fun s' hs' => hstarS.2.2 s' ⟨?_, hs'.2.le⟩
  rw [hstar_eq]
  exact hs.1.trans hs'.1.le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
