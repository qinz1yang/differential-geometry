import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas

open Set Filter
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

def UpperRightDiniLE (f : ℝ → ℝ) (x d : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ y in 𝓝[>] x, slope f x y ≤ d + ε

theorem upperRightDiniLE_iff_eventually_lt {f : ℝ → ℝ} {x d : ℝ} :
    UpperRightDiniLE f x d ↔ ∀ r > d, ∀ᶠ y in 𝓝[>] x, slope f x y < r := by
  constructor
  · intro h r hr
    filter_upwards [h ((r - d) / 2) (by linarith)] with y hy
    linarith
  · intro h ε hε
    exact (h (d + ε) (by linarith)).mono fun _ hy => hy.le

theorem upperRightDiniLE_iff_before {f : ℝ → ℝ} {x d H : ℝ} (hx : x < H) :
    UpperRightDiniLE f x d ↔
      ∀ ε > 0, ∀ᶠ y in 𝓝[>] x, y ≤ H → (f y - f x) / (y - x) ≤ d + ε := by
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with y hy _
    simpa only [slope_def_field] using hy
  · intro h ε hε
    filter_upwards [h ε hε, Ioc_mem_nhdsGT hx] with y hy hyH
    simpa only [slope_def_field] using hy hyH.2

theorem upperRightDiniLE_iff_increment {f : ℝ → ℝ} {x d H : ℝ} (hx : x < H) :
    UpperRightDiniLE f x d ↔ ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0 : ℝ),
      x + h ≤ H → (f (x + h) - f x) / h ≤ d + ε := by
  have hplus : Tendsto (fun h : ℝ => x + h) (𝓝[>] 0) (𝓝[>] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (show ContinuousAt (fun h : ℝ => x + h) 0 from
        continuousAt_const.add continuousAt_id).tendsto.mono_left
          (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact lt_add_of_pos_right x hh.out
  have hminus : Tendsto (fun y : ℝ => y - x) (𝓝[>] x) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (show ContinuousAt (fun y : ℝ => y - x) x from
        continuousAt_id.sub continuousAt_const).tendsto.mono_left
          (nhdsWithin_le_nhds : 𝓝[>] x ≤ 𝓝 x)
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact sub_pos.mpr hy.out
  rw [upperRightDiniLE_iff_before hx]
  constructor
  · intro h ε hε
    simpa using hplus.eventually (h ε hε)
  · intro h ε hε
    simpa using hminus.eventually (h ε hε)

theorem antitoneOn_of_upperRightDiniLE {f : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ico a b, UpperRightDiniLE f x 0) : AntitoneOn f (Icc a b) := by
  intro x hx y hy hxy
  apply image_le_of_liminf_slope_right_le_deriv_boundary
    (hc.mono (Icc_subset_Icc hx.1 hy.2)) (B := fun _ => f x) (B' := fun _ => 0)
    le_rfl continuousOn_const (fun z _ => hasDerivWithinAt_const z _ (f x))
  · intro z hz r hr
    exact ((upperRightDiniLE_iff_eventually_lt.mp
      (hd z ⟨hx.1.trans hz.1, hz.2.trans_le hy.2⟩)) r hr).frequently
  · exact ⟨hxy, le_rfl⟩

private theorem endpoint_le_of_no_events {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ∀ x ∈ Ioo a b, ContinuousAt f x)
    (hd : ∀ x ∈ Ioo a b, UpperRightDiniLE f x 0)
    (hr : ContinuousWithinAt f (Ici a) a)
    (hl : ∀ r < f b, ∀ᶠ s in 𝓝[<] b, r < f s) : f b ≤ f a := by
  have hm : AntitoneOn f (Ioo a b) := by
    intro x hx y hy hxy
    apply antitoneOn_of_upperRightDiniLE
      (fun z hz => (hc z ⟨hx.1.trans_le hz.1, hz.2.trans_lt hy.2⟩).continuousWithinAt)
      (fun z hz => hd z ⟨hx.1.trans_le hz.1, hz.2.trans hy.2⟩)
      ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
  have hu : ∀ y ∈ Ioo a b, f y ≤ f a := by
    intro y hy
    apply ge_of_tendsto (hr.mono Ioi_subset_Ici_self)
    filter_upwards [Ioo_mem_nhdsGT hy.1] with x hx
    exact hm ⟨hx.1, hx.2.trans hy.2⟩ hy hx.2.le
  by_contra hn
  obtain ⟨r, har, hrb⟩ := exists_between (lt_of_not_ge hn)
  obtain ⟨s, hrs, hs⟩ := ((hl r hrb).and (Ioo_mem_nhdsLT hab)).exists
  exact (hu s hs).not_gt (har.trans hrs)

private theorem endpoint_le_of_finite_events {f : ℝ → ℝ} {E : Set ℝ} (hE : E.Finite) :
    ∀ {a b : ℝ}, a < b →
      (∀ x ∈ Ioo a b, x ∉ E → ContinuousAt f x) →
      (∀ x ∈ Ioo a b, x ∉ E → UpperRightDiniLE f x 0) →
      (∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x) →
      (∀ x ∈ Ioc a b, ∀ r < f x, ∀ᶠ s in 𝓝[<] x, r < f s) → f b ≤ f a := by
  induction E, hE using Set.Finite.induction_on with
  | empty =>
    intro a b hab hc hd hr hl
    exact endpoint_le_of_no_events hab (fun x hx => hc x hx (by simp))
      (fun x hx => hd x hx (by simp)) (hr a ⟨le_rfl, hab⟩)
      (hl b ⟨hab, le_rfl⟩)
  | @insert e E he hE ih =>
    intro a b hab hc hd hr hl
    by_cases heab : e ∈ Ioo a b
    · have hleft : f e ≤ f a := by
        apply ih heab.1
        · intro x hx hxE
          exact hc x ⟨hx.1, hx.2.trans heab.2⟩
            (by simp only [mem_insert_iff, not_or]; exact ⟨ne_of_lt hx.2, hxE⟩)
        · intro x hx hxE
          exact hd x ⟨hx.1, hx.2.trans heab.2⟩
            (by simp only [mem_insert_iff, not_or]; exact ⟨ne_of_lt hx.2, hxE⟩)
        · intro x hx
          exact hr x ⟨hx.1, hx.2.trans heab.2⟩
        · intro x hx
          exact hl x ⟨hx.1, hx.2.trans heab.2.le⟩
      have hright : f b ≤ f e := by
        apply ih heab.2
        · intro x hx hxE
          exact hc x ⟨heab.1.trans hx.1, hx.2⟩
            (by simp only [mem_insert_iff, not_or]; exact ⟨ne_of_gt hx.1, hxE⟩)
        · intro x hx hxE
          exact hd x ⟨heab.1.trans hx.1, hx.2⟩
            (by simp only [mem_insert_iff, not_or]; exact ⟨ne_of_gt hx.1, hxE⟩)
        · intro x hx
          exact hr x ⟨heab.1.le.trans hx.1, hx.2⟩
        · intro x hx
          exact hl x ⟨heab.1.trans hx.1, hx.2⟩
      exact hright.trans hleft
    · apply ih hab
      · intro x hx hxE
        apply hc x hx
        simp only [mem_insert_iff, not_or]
        exact ⟨fun h => heab (h ▸ hx), hxE⟩
      · intro x hx hxE
        apply hd x hx
        simp only [mem_insert_iff, not_or]
        exact ⟨fun h => heab (h ▸ hx), hxE⟩
      · exact hr
      · exact hl

theorem eventually_lt_of_le_incoming_liminf {f : ℝ → ℝ} {e : ℝ}
    (hj : (f e : EReal) ≤ liminf (fun s => (f s : EReal)) (𝓝[<] e))
    {r : ℝ} (hr : r < f e) : ∀ᶠ s in 𝓝[<] e, r < f s := by
  have hh := eventually_lt_of_lt_liminf ((EReal.coe_lt_coe_iff.mpr hr).trans_le hj)
  exact hh.mono fun _ hs => EReal.coe_lt_coe_iff.mp hs

theorem antitoneOn_of_finite_jumps_upperRightDiniLE {f : ℝ → ℝ} {H : ℝ} {E : Set ℝ}
    (hE : E.Finite)
    (hc : ∀ x ∈ Icc 0 H, x ∉ E → ContinuousWithinAt f (Icc 0 H) x)
    (hr : ∀ x ∈ Ico 0 H, ContinuousWithinAt f (Ici x) x)
    (hd : ∀ x ∈ Ico 0 H, x ∉ E → UpperRightDiniLE f x 0)
    (hj : ∀ e ∈ E, (f e : EReal) ≤ liminf (fun s => (f s : EReal)) (𝓝[<] e)) :
    AntitoneOn f (Icc 0 H) := by
  intro a ha b hb hab
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  apply endpoint_le_of_finite_events hE hab
  · intro x hx hxE
    exact (hc x ⟨ha.1.trans hx.1.le, hx.2.le.trans hb.2⟩ hxE).continuousAt
      (Icc_mem_nhds (ha.1.trans_lt hx.1) (hx.2.trans_le hb.2))
  · intro x hx hxE
    exact hd x ⟨ha.1.trans hx.1.le, hx.2.trans_le hb.2⟩ hxE
  · intro x hx
    exact hr x ⟨ha.1.trans hx.1, hx.2.trans_le hb.2⟩
  · intro x hx r hrx
    by_cases hxE : x ∈ E
    · exact eventually_lt_of_le_incoming_liminf (hj x hxE) hrx
    · have ht : Tendsto f (𝓝[<] x) (𝓝 (f x)) :=
        (hc x ⟨ha.1.trans hx.1.le, hx.2.trans hb.2⟩ hxE).mono_left
          (nhdsWithin_le_of_mem (Icc_mem_nhdsLT_of_mem
            ⟨ha.1.trans_lt hx.1, hx.2.trans hb.2⟩))
      exact ht.eventually_const_lt hrx

theorem incoming_limit_of_antitoneOn {f : ℝ → ℝ} {H e : ℝ}
    (hm : AntitoneOn f (Icc 0 H)) (hb : BddBelow (f '' Icc 0 H))
    (he : e ∈ Ioc 0 H) :
    ∃ L : ℝ, Tendsto f (𝓝[<] e) (𝓝 L) ∧ f e ≤ L := by
  have hsub : Ioo 0 e ⊆ Icc 0 H := fun _ hx => ⟨hx.1.le, hx.2.le.trans he.2⟩
  have ht := (hm.mono hsub).tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr he.1)
    (hb.mono (image_mono hsub))
  refine ⟨sInf (f '' Ioo 0 e), ht, ?_⟩
  apply ge_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsLT he.1] with s hs
  exact hm (hsub hs) ⟨he.1.le, he.2⟩ hs.2.le

theorem finite_jumps_incoming_limit {f : ℝ → ℝ} {H : ℝ} {E : Set ℝ}
    (hE : E.Finite) (hEH : E ⊆ Ioc 0 H) (hb : BddBelow (f '' Icc 0 H))
    (hc : ∀ x ∈ Icc 0 H, x ∉ E → ContinuousWithinAt f (Icc 0 H) x)
    (hr : ∀ x ∈ Ico 0 H, ContinuousWithinAt f (Ici x) x)
    (hd : ∀ x ∈ Ico 0 H, x ∉ E → UpperRightDiniLE f x 0)
    (hj : ∀ e ∈ E, (f e : EReal) ≤ liminf (fun s => (f s : EReal)) (𝓝[<] e)) :
    AntitoneOn f (Icc 0 H) ∧
      ∀ e ∈ E, ∃ L : ℝ, Tendsto f (𝓝[<] e) (𝓝 L) ∧ f e ≤ L := by
  have hm := antitoneOn_of_finite_jumps_upperRightDiniLE hE hc hr hd hj
  exact ⟨hm, fun e he => incoming_limit_of_antitoneOn hm hb (hEH he)⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
