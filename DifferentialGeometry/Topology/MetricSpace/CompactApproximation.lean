import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology

namespace Metric

theorem exists_isometry_mapClusterPt_of_compact_approximation
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
    {ι : Type*} {l : Filter ι} [l.NeBot] (f : ι → X → Y)
    {eps : ι → ℝ} (heps : Tendsto eps l (𝓝 0))
    (hdist : ∀ᶠ i in l, ∀ x y, |dist (f i x) (f i y) - dist x y| ≤ eps i)
    (p : X) (R : ℝ)
    (hcover : ∀ᶠ i in l, ∀ y ∈ ball (f i p) R, ∃ x, dist y (f i x) ≤ eps i) :
    ∃ F : X → Y, Isometry F ∧ MapClusterPt F l f ∧ ball (F p) R ⊆ range F := by
  classical
  obtain ⟨F, _, hF⟩ := (isCompact_univ : IsCompact (univ : Set (X → Y))).exists_mapClusterPt
    (u := f) (f := l) (by simp)
  obtain ⟨U, hUl, hFU⟩ := mapClusterPt_iff_ultrafilter.mp hF
  have hconv (x : X) : Tendsto (fun i => f i x) U (𝓝 (F x)) :=
    (continuous_apply x).tendsto F |>.comp hFU
  have hFiso : Isometry F := by
    apply Isometry.of_dist_eq
    intro x y
    have hh : |dist (F x) (F y) - dist x y| ≤ 0 :=
      le_of_tendsto_of_tendsto (((hconv x).dist (hconv y)).sub tendsto_const_nhds).abs
        (heps.mono_left hUl) (Filter.Eventually.mono (hUl hdist) fun i hi => hi x y)
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)
  refine ⟨F, hFiso, hF, ?_⟩
  intro y hy
  change dist y (F p) < R at hy
  have hyU : ∀ᶠ i in (U : Filter ι), dist y (f i p) < R :=
    ((tendsto_const_nhds.dist (hconv p)).eventually (eventually_lt_nhds hy))
  let z (i : ι) : X := if h : ∃ x, dist y (f i x) ≤ eps i then h.choose else p
  have hz : ∀ᶠ i in (U : Filter ι), dist y (f i (z i)) ≤ eps i := by
    filter_upwards [hUl hcover, hyU] with i hi hiy
    have hex : ∃ x, dist y (f i x) ≤ eps i := hi y hiy
    simpa only [z, dite_eq_left hex] using hex.choose_spec
  obtain ⟨x, _, hx⟩ := (isCompact_univ : IsCompact (univ : Set X)).exists_mapClusterPt
    (u := z) (f := (U : Filter ι)) (by simp)
  obtain ⟨V, hVU, hxV⟩ := mapClusterPt_iff_ultrafilter.mp hx
  have heV := heps.mono_left (hVU.trans hUl)
  have hfxV := (hconv x).mono_left hVU
  have hzV := tendsto_iff_dist_tendsto_zero.mp hxV
  have hsum : Tendsto (fun i => eps i + (dist (z i) x + eps i) + dist (f i x) (F x))
      V (𝓝 (0 : ℝ)) := by
    simpa only [zero_add, add_zero] using
      (heV.add (hzV.add heV)).add (tendsto_iff_dist_tendsto_zero.mp hfxV)
  have hle : ∀ᶠ i in (V : Filter ι),
      dist y (F x) ≤ eps i + (dist (z i) x + eps i) + dist (f i x) (F x) := by
    filter_upwards [hVU hz, hVU (hUl hdist)] with i hi hdi
    have hd := (abs_le.mp (hdi (z i) x)).2
    have ht := dist_triangle4 y (f i (z i)) (f i x) (F x)
    linarith only [hi, hd, ht]
  have heq : y = F x := dist_le_zero.mp (le_of_tendsto_of_tendsto tendsto_const_nhds hsum hle)
  exact ⟨x, heq.symm⟩

theorem exists_isometry_of_compact_approximation
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
    {ι : Type*} {l : Filter ι} [l.NeBot] (f : ι → X → Y)
    {eps : ι → ℝ} (heps : Tendsto eps l (𝓝 0))
    (hdist : ∀ᶠ i in l, ∀ x y, |dist (f i x) (f i y) - dist x y| ≤ eps i)
    (p : X) (R : ℝ)
    (hcover : ∀ᶠ i in l, ∀ y ∈ ball (f i p) R, ∃ x, dist y (f i x) ≤ eps i) :
    ∃ F : X → Y, Isometry F ∧ ball (F p) R ⊆ range F := by
  obtain ⟨F, hF, _, hcoverF⟩ := exists_isometry_mapClusterPt_of_compact_approximation
    f heps hdist p R hcover
  exact ⟨F, hF, hcoverF⟩

variable {A B : Type*} [MetricSpace A] [CompactSpace A]
  [MetricSpace B] [CompactSpace B]

theorem exists_isometryEquiv_mapClusterPt_of_approx_relations
    {ι : Type*} {l : Filter ι} [NeBot l]
    (R : ι → Set (A × B)) (f : ι → A → B) (p : A) (q : B)
    (leftError distortion rightError : ι → ℝ)
    (hleftZero : Tendsto leftError l (𝓝 0))
    (hdistZero : Tendsto distortion l (𝓝 0))
    (hrightZero : Tendsto rightError l (𝓝 0))
    (hbase : Tendsto (fun i => f i p) l (𝓝 q))
    (hrelations : ∀ᶠ i in l,
      (∀ x : A, ∃ a, (a, f i x) ∈ R i ∧ dist x a ≤ leftError i) ∧
      (∀ y : B, ∃ a b, (a, b) ∈ R i ∧ dist y b ≤ rightError i) ∧
      ∀ a b a' b', (a, b) ∈ R i → (a', b') ∈ R i →
        |dist a a' - dist b b'| ≤ distortion i) :
    ∃ e : A ≃ᵢ B, MapClusterPt (e : A → B) l f ∧ e p = q := by
  classical
  let eps : ι → ℝ := fun i =>
    max (2 * leftError i + distortion i) (rightError i + (leftError i + distortion i))
  have heps : Tendsto eps l (𝓝 0) := by
    simpa only [eps, mul_zero, zero_add, max_self] using
      ((tendsto_const_nhds.mul hleftZero).add hdistZero).max
        (hrightZero.add (hleftZero.add hdistZero))
  have hdist : ∀ᶠ i in l, ∀ x y,
      |dist (f i x) (f i y) - dist x y| ≤ eps i := by
    filter_upwards [hrelations] with i hi x y
    obtain ⟨a, ha, hxa⟩ := hi.1 x
    obtain ⟨b, hb, hyb⟩ := hi.1 y
    have hxy := abs_le.mp (hi.2.2 a (f i x) b (f i y) ha hb)
    have hupper := dist_triangle4 a x y b
    have hlower := dist_triangle4 x a b y
    rw [dist_comm a x] at hupper
    rw [dist_comm b y] at hlower
    have hxy' : |dist (f i x) (f i y) - dist x y| ≤
        2 * leftError i + distortion i := by
      apply abs_le.mpr
      constructor <;> linarith only [hxy.1, hxy.2, hxa, hyb, hupper, hlower]
    exact hxy'.trans (le_max_left _ _)
  let Rdiam : ℝ := diam (univ : Set B) + 1
  have hcover : ∀ᶠ i in l, ∀ y ∈ ball (f i p) Rdiam,
      ∃ x, dist y (f i x) ≤ eps i := by
    filter_upwards [hrelations] with i hi y _
    obtain ⟨a, b, hab, hyb⟩ := hi.2.1 y
    obtain ⟨a', ha', haa'⟩ := hi.1 a
    have hba' := (abs_le.mp (hi.2.2 a b a' (f i a) hab ha')).1
    have hba : dist b (f i a) ≤ leftError i + distortion i := by
      linarith only [hba', haa']
    refine ⟨a, ?_⟩
    exact (dist_triangle y b (f i a)).trans
      ((add_le_add hyb hba).trans (le_max_right _ _))
  obtain ⟨F, hF, hcluster, hcoverF⟩ :=
    exists_isometry_mapClusterPt_of_compact_approximation f heps hdist p Rdiam hcover
  obtain ⟨U, hUl, hFU⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  have hFp : Tendsto (fun i => f i p) U (𝓝 (F p)) :=
    (continuous_apply p).tendsto F |>.comp hFU
  have hqp : Tendsto (fun i => f i p) U (𝓝 q) := hbase.mono_left hUl
  have hpq : F p = q := tendsto_nhds_unique hFp hqp
  have hsurj : Function.Surjective F := by
    intro y
    have hy : dist y q < Rdiam := by
      exact (dist_le_diam_of_mem isBounded_of_compactSpace (mem_univ _) (mem_univ _)).trans_lt
        (lt_add_one _)
    have hyball : y ∈ ball (F p) Rdiam := by
      rw [hpq]
      exact hy
    exact hcoverF hyball
  let e : A ≃ᵢ B := {
    toEquiv := Equiv.ofBijective F ⟨hF.injective, hsurj⟩
    isometry_toFun := hF
  }
  refine ⟨e, ?_, ?_⟩
  · change MapClusterPt F l f
    exact hcluster
  · exact hpq


end Metric
