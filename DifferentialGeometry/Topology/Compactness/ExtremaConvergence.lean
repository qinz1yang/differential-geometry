import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Real
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace IsCompact

variable {X ι : Type*} [TopologicalSpace X] {l : Filter ι}
  {K : Set X} {F : ι → X → ℝ} {f : X → ℝ} {x : X} {z : ι → X}

theorem tendsto_of_isMaxOn_of_tendstoUniformlyOn
    (hK : IsCompact K) (hf : UpperSemicontinuousOn f K) (hx : x ∈ K)
    (hstrict : ∀ y ∈ K, y ≠ x → f y < f x)
    (hconv : TendstoUniformlyOn F f l K)
    (hmax : ∀ᶠ i in l, z i ∈ K ∧ IsMaxOn (F i) K (z i)) :
    Tendsto z l (𝓝 x) := by
  apply tendsto_nhds.mpr
  intro U hU hxU
  by_cases hne : (K \ U).Nonempty
  · obtain ⟨y, hy, hyle⟩ := UpperSemicontinuousOn.exists_isMaxOn hne (hK.diff hU) (hf.mono sdiff_subset)
    have hyx : y ≠ x := by intro heq; exact hy.2 (heq ▸ hxU)
    have hgap := hstrict y hy.1 hyx
    let eps := (f x - f y) / 3
    have heps : 0 < eps := by dsimp [eps]; linarith
    have he := (Metric.tendstoUniformlyOn_iff.mp hconv) eps heps
    filter_upwards [he, hmax] with i hi hmi
    by_contra hn
    have hzi := hyle ⟨hmi.1, hn⟩
    change f (z i) ≤ f y at hzi
    have hcompare : F i x ≤ F i (z i) := hmi.2 hx
    have hxi := hi x hx
    have hz := hi (z i) hmi.1
    rw [Real.dist_eq] at hxi hz
    have h1 := (abs_lt.mp hxi).2
    have h2 := (abs_lt.mp hz).1
    dsimp only [eps] at h1 h2
    linarith
  · filter_upwards [hmax] with i hi
    by_contra hn
    exact hne ⟨z i, hi.1, hn⟩

theorem tendsto_of_isMinOn_of_tendstoUniformlyOn
    (hK : IsCompact K) (hf : LowerSemicontinuousOn f K) (hx : x ∈ K)
    (hstrict : ∀ y ∈ K, y ≠ x → f x < f y)
    (hconv : TendstoUniformlyOn F f l K)
    (hmin : ∀ᶠ i in l, z i ∈ K ∧ IsMinOn (F i) K (z i)) :
    Tendsto z l (𝓝 x) := by
  apply hK.tendsto_of_isMaxOn_of_tendstoUniformlyOn hf.neg hx
    (fun y hy hne => neg_lt_neg (hstrict y hy hne)) hconv.neg
  filter_upwards [hmin] with i hi
  refine ⟨hi.1, ?_⟩
  intro y hy
  change -F i y ≤ -F i (z i)
  exact neg_le_neg (hi.2 hy)

theorem exists_tendsto_isLocalMax_of_tendstoUniformlyOn [l.NeBot]
    (hK : IsCompact K) (hx : K ∈ 𝓝 x)
    (hF : ∀ i, ContinuousOn (F i) K)
    (hstrict : ∀ y ∈ K, y ≠ x → f y < f x)
    (hconv : TendstoUniformlyOn F f l K) :
    ∃ z : ι → X, Tendsto z l (𝓝 x) ∧
      (∀ i, z i ∈ K ∧ IsMaxOn (F i) K (z i)) ∧
      ∀ᶠ i in l, IsLocalMax (F i) (z i) := by
  classical
  have hxK : x ∈ K := mem_of_mem_nhds hx
  choose z hz hmax using fun i => hK.exists_isMaxOn ⟨x, hxK⟩ (hF i)
  have hlim : Tendsto z l (𝓝 x) := hK.tendsto_of_isMaxOn_of_tendstoUniformlyOn
    (hconv.continuousOn (Eventually.of_forall hF).frequently).upperSemicontinuousOn hxK hstrict hconv
    (Eventually.of_forall (fun i => ⟨hz i, hmax i⟩))
  refine ⟨z, hlim, fun i => ⟨hz i, hmax i⟩, ?_⟩
  filter_upwards [hlim.eventually (interior_mem_nhds.mpr hx)] with i hi
  exact (hmax i).isLocalMax (mem_interior_iff_mem_nhds.mp hi)

theorem exists_tendsto_isLocalMin_of_tendstoUniformlyOn [l.NeBot]
    (hK : IsCompact K) (hx : K ∈ 𝓝 x)
    (hF : ∀ i, ContinuousOn (F i) K)
    (hstrict : ∀ y ∈ K, y ≠ x → f x < f y)
    (hconv : TendstoUniformlyOn F f l K) :
    ∃ z : ι → X, Tendsto z l (𝓝 x) ∧
      (∀ i, z i ∈ K ∧ IsMinOn (F i) K (z i)) ∧
      ∀ᶠ i in l, IsLocalMin (F i) (z i) := by
  obtain ⟨z, hlim, hmax, hlocal⟩ := hK.exists_tendsto_isLocalMax_of_tendstoUniformlyOn hx
    (fun i => (hF i).neg) (fun y hy hne => neg_lt_neg (hstrict y hy hne)) hconv.neg
  refine ⟨z, hlim, ?_, ?_⟩
  · intro i
    refine ⟨(hmax i).1, ?_⟩
    intro y hy
    change F i (z i) ≤ F i y
    exact neg_le_neg_iff.mp ((hmax i).2 hy)
  · filter_upwards [hlocal] with i hi
    filter_upwards [hi] with y hy
    exact neg_le_neg_iff.mp hy

end IsCompact
