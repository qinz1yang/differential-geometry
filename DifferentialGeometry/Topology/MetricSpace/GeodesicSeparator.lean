import DifferentialGeometry.Topology.FirstExit
import DifferentialGeometry.Topology.Compactness.ConvergentFamily
import DifferentialGeometry.Topology.Embedding.Frontier
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace EMetric

variable {X : Type*} [PseudoEMetricSpace X]

theorem edist_lt_edist_add_edist_of_close_to_center
    {p q x y : X} {r : ℝ} (hr : 0 ≤ r)
    (hx : edist q x ≤ ENNReal.ofReal r) (hy : edist q y ≤ ENNReal.ofReal r)
    (hfar : ENNReal.ofReal (2 * r) < edist q p) :
    edist x y < edist x p + edist p y := by
  have hxy : edist x y ≤ ENNReal.ofReal (2 * r) := by
    calc
      _ ≤ edist x q + edist q y := edist_triangle _ _ _
      _ ≤ ENNReal.ofReal r + ENNReal.ofReal r := by
        rw [edist_comm x q]
        exact add_le_add hx hy
      _ = ENNReal.ofReal (2 * r) := by rw [← ENNReal.ofReal_add hr hr]; congr 1; ring
  by_cases hxp : edist x p = ⊤
  · rw [hxp, top_add]
    exact lt_of_le_of_lt hxy ENNReal.ofReal_lt_top
  by_cases hpy : edist p y = ⊤
  · rw [hpy, add_top]
    exact lt_of_le_of_lt hxy ENNReal.ofReal_lt_top
  have hqx : edist q x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
  have hqy : edist q y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy
  have hqp : edist q p ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hqx, hxp⟩)
    (edist_triangle q x p)
  have hfarR : 2 * r < (edist q p).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by positivity : 0 ≤ 2 * r) hqp).mp hfar
  have hxR := ENNReal.toReal_le_of_le_ofReal hr hx
  have hyR := ENNReal.toReal_le_of_le_ofReal hr hy
  have htx := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hqx, hxp⟩) (edist_triangle q x p)
  have hty := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hqy, by simpa only [edist_comm] using hpy⟩)
    (edist_triangle q y p)
  rw [ENNReal.toReal_add hqx hxp] at htx
  rw [ENNReal.toReal_add hqy (by simpa only [edist_comm] using hpy), edist_comm y p] at hty
  apply hxy.trans_lt
  apply (ENNReal.ofReal_lt_iff_lt_toReal (by positivity : 0 ≤ 2 * r) (ENNReal.add_ne_top.mpr ⟨hxp, hpy⟩)).mpr
  rw [ENNReal.toReal_add hxp hpy]
  linarith

end EMetric


namespace EMetric

variable {X : Type*} [PseudoEMetricSpace X]

theorem not_mem_interior_of_minimizing_of_frontier_edist_lt
    {γ : ℝ → X} {a t b : ℝ} (hat : a < t) (htb : t < b)
    (hmin : ∀ s ∈ Icc a b, ∀ u ∈ Icc a b, edist (γ s) (γ u) = ENNReal.ofReal |s - u|)
    {U : Set X} (ha : γ a ∉ interior U) (hb : γ b ∉ interior U)
    (hshort : ∀ x ∈ frontier U, ∀ y ∈ frontier U,
      edist x y < edist x (γ t) + edist (γ t) y) :
    γ t ∉ interior U := by
  intro htU
  have hcont : ContinuousOn γ (Icc a b) := by
    have hLip : LipschitzOnWith 1 γ (Icc a b) := by
      intro s hs u hu
      rw [hmin s hs u hu]
      simp only [ENNReal.coe_one, one_mul, edist_dist, Real.dist_eq]
      exact le_rfl
    exact hLip.continuousOn
  have hleft : ContinuousOn (fun s => γ (t - s)) (Icc 0 (t - a)) :=
    hcont.comp (by fun_prop) (by
      intro s hs
      exact ⟨by linarith only [hs.2], by linarith only [hs.1, htb]⟩)
  have hright : ContinuousOn (fun s => γ (t + s)) (Icc 0 (b - t)) :=
    hcont.comp (by fun_prop) (by
      intro s hs
      exact ⟨by linarith only [hs.1, hat], by linarith only [hs.2]⟩)
  obtain ⟨u, hu, _, huF⟩ :=
    DifferentialGeometry.exists_first_exit_frontier_of_not_mem_interior
      (sub_pos.mpr hat) hleft (by simpa only [sub_zero] using htU)
      (by simpa only [sub_sub_cancel] using ha)
  obtain ⟨v, hv, _, hvF⟩ :=
    DifferentialGeometry.exists_first_exit_frontier_of_not_mem_interior
      (sub_pos.mpr htb) hright (by simpa only [add_zero] using htU)
      (by simpa only [add_sub_cancel] using hb)
  have htu : t - u ∈ Icc a b :=
    ⟨by linarith only [hu.2], by linarith only [hu.1, htb]⟩
  have htv : t + v ∈ Icc a b :=
    ⟨by linarith only [hv.1, hat], by linarith only [hv.2]⟩
  have ht : t ∈ Icc a b := ⟨hat.le, htb.le⟩
  have heq : edist (γ (t - u)) (γ (t + v)) =
      edist (γ (t - u)) (γ t) + edist (γ t) (γ (t + v)) := by
    rw [hmin _ htu _ htv, hmin _ htu _ ht, hmin _ ht _ htv,
      abs_of_nonpos (by linarith only [hu.1, hv.1] : t - u - (t + v) ≤ 0),
      abs_of_nonpos (by linarith only [hu.1] : t - u - t ≤ 0),
      abs_of_nonpos (by linarith only [hv.1] : t - (t + v) ≤ 0)]
    rw [← ENNReal.ofReal_add (by linarith only [hu.1]) (by linarith only [hv.1])]
    congr 1
    ring
  exact (hshort _ huF _ hvF).ne heq

end EMetric


namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

theorem dist_lt_dist_add_dist_of_mem_closedBall
    {p q x y : X} {r : ℝ} (hx : x ∈ closedBall q r) (hy : y ∈ closedBall q r)
    (hfar : 2 * r < dist q p) : dist x y < dist x p + dist p y := by
  have hxy := dist_triangle x q y
  have hxp := dist_triangle q x p
  have hyp := dist_triangle q y p
  rw [dist_comm q x] at hxp
  rw [dist_comm q y] at hxy hyp
  rw [dist_comm y p] at hyp
  change dist x q ≤ r at hx
  change dist y q ≤ r at hy
  linarith only [hxy, hxp, hyp, hx, hy, hfar]

theorem not_mem_interior_of_minimizing_of_frontier_dist_lt
    {γ : ℝ → X} {a t b : ℝ} (hat : a < t) (htb : t < b)
    (hmin : ∀ s ∈ Icc a b, ∀ u ∈ Icc a b, dist (γ s) (γ u) = |s - u|)
    {U : Set X} (ha : γ a ∉ interior U) (hb : γ b ∉ interior U)
    (hshort : ∀ x ∈ frontier U, ∀ y ∈ frontier U,
      dist x y < dist x (γ t) + dist (γ t) y) :
    γ t ∉ interior U := by
  apply EMetric.not_mem_interior_of_minimizing_of_frontier_edist_lt hat htb
    (fun s hs u hu => by rw [edist_dist, hmin s hs u hu]) ha hb
  intro x hx y hy
  rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.mpr (hshort x hx y hy)


theorem not_mem_interior_of_minimizing_of_diam_frontier_lt
    {γ : ℝ → X} {a t b : ℝ} (hat : a < t) (htb : t < b)
    (hmin : ∀ s ∈ Icc a b, ∀ u ∈ Icc a b, dist (γ s) (γ u) = |s - u|)
    {U : Set X} (ha : γ a ∉ interior U) (hb : γ b ∉ interior U)
    (hbounded : Bornology.IsBounded (frontier U)) {r : ℝ}
    (hdiam : diam (frontier U) < 2 * r)
    (hfar : ∀ x ∈ frontier U, r ≤ dist x (γ t)) :
    γ t ∉ interior U := by
  apply not_mem_interior_of_minimizing_of_frontier_dist_lt hat htb hmin ha hb
  intro x hx y hy
  have hxy := (dist_le_diam_of_mem hbounded hx hy).trans_lt hdiam
  have hx := hfar x hx
  have hy := hfar y hy
  rw [dist_comm y (γ t)] at hy
  linarith only [hxy, hx, hy]

theorem ne_of_minimizing_of_convergent_separators
    {Y X : Type*} [TopologicalSpace Y] [MetricSpace X]
    {e : Y → X} (he : Topology.IsOpenEmbedding e) {q : X} (hq : q ∉ range e)
    {A : ℕ → Set Y} (hA : ∀ n, IsCompact (A n))
    (hlim : ∀ U ∈ 𝓝 q, ∀ᶠ n in atTop, e '' A n ⊆ U)
    (hnhds : insert q (⋃ n, e '' A n) ∈ 𝓝 q)
    (hshort : ∀ᶠ N in atTop, ∀ x ∈ frontier (⋃ n, A (n + N)),
      ∀ y ∈ frontier (⋃ n, A (n + N)), dist (e x) (e y) < dist (e x) q + dist q (e y))
    (β : ℝ → X) (u v w : ℝ) (huv : u < v) (hvw : v < w)
    (hmin : ∀ s ∈ Icc u w, ∀ t ∈ Icc u w, dist (β s) (β t) = |s - t|) :
    β v ≠ q := by
  intro heq
  let T (N : ℕ) : Set X := insert q (⋃ n, e '' A (n + N))
  have hTclosed (N : ℕ) : IsClosed (T N) := by
    apply IsCompact.isClosed
    apply isCompact_insert_iUnion_of_eventually_subset (fun n => (hA (n + N)).image he.continuous)
    intro U hU
    simpa only [Nat.cofinite_eq_atTop] using (tendsto_add_atTop_nat N).eventually (hlim U hU)
  have hTnhds (N : ℕ) : T N ∈ 𝓝 q :=
    insert_iUnion_nat_add_mem_nhds (fun n => ((hA n).image he.continuous).isClosed)
      (fun n hn => hq (image_subset_range e (A n) hn)) hnhds N
  have hTfront (N : ℕ) : frontier (T N) = e '' frontier (⋃ n, A (n + N)) := by
    have heq : T N = insert q (e '' (⋃ n, A (n + N))) := by rw [image_iUnion]
    rw [heq]
    exact he.frontier_insert_image hq (heq ▸ hTclosed N) (heq ▸ hTnhds N)
  have huq : β u ≠ q := by
    intro h
    have hh := hmin u ⟨le_rfl, huv.le.trans hvw.le⟩ v ⟨huv.le, hvw.le⟩
    rw [h, heq, dist_self, abs_of_neg (sub_neg.mpr huv)] at hh
    linarith only [hh, huv]
  have hwq : β w ≠ q := by
    intro h
    have hh := hmin v ⟨huv.le, hvw.le⟩ w ⟨huv.le.trans hvw.le, le_rfl⟩
    rw [h, heq, dist_self, abs_of_neg (sub_neg.mpr hvw)] at hh
    linarith only [hh, hvw]
  have hU : ({β u, β w} : Set X)ᶜ ∈ 𝓝 q :=
    (isClosed_singleton.union isClosed_singleton).isOpen_compl.mem_nhds (by
      exact not_or.mpr ⟨Ne.symm huq, Ne.symm hwq⟩)
  obtain ⟨N, hNshort, hNsub⟩ := (hshort.and (eventually_insert_iUnion_nat_add_subset hlim hU)).exists
  have hu : β u ∉ interior (T N) := by
    intro h
    exact (hNsub (interior_subset h)) (by simp)
  have hw : β w ∉ interior (T N) := by
    intro h
    exact (hNsub (interior_subset h)) (by simp)
  have hnot := Metric.not_mem_interior_of_minimizing_of_frontier_dist_lt huv hvw hmin hu hw (by
    rw [hTfront N]
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    rw [heq]
    exact hNshort a ha b hb)
  exact hnot (heq.symm ▸ mem_interior_iff_mem_nhds.mpr (hTnhds N))

end Metric
