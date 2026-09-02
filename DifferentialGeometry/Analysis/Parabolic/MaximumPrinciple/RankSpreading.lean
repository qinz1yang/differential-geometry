import DifferentialGeometry.Analysis.Spectral.LowerKyFan
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

universe u

variable {X : Type u}

theorem rank_eq_at_positive_time_of_spreading
    {rank : Real → X → Nat} {T : Real}
    (hlower : ∀ t ∈ Ioc 0 T, ∀ x,
      ∀ᶠ s in 𝓝[Icc 0 T] t, rank t x ≤ rank s x)
    (hspread : ∀ {s t : Real}, 0 ≤ s → s < t → t ≤ T →
      ∀ x y, rank s x ≤ rank t y)
    {t : Real} (ht : t ∈ Ioc 0 T) (x y : X) :
    rank t x = rank t y := by
  have hsubset : Ioo 0 t ⊆ Icc 0 T := by
    intro s hs
    exact ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hxy : rank t x ≤ rank t y := by
    have hev : ∀ᶠ s in 𝓝[Ioo 0 t] t, rank t x ≤ rank s x :=
      (hlower t ht x).filter_mono (nhdsWithin_mono t hsubset)
    have hmem : ∀ᶠ s in 𝓝[Ioo 0 t] t, s ∈ Ioo 0 t := self_mem_nhdsWithin
    let _ : (𝓝[Ioo 0 t] t).NeBot := right_nhdsWithin_Ioo_neBot ht.1
    obtain ⟨s, hs_mem, hs_rank⟩ := (hmem.and hev).exists
    exact hs_rank.trans (hspread hs_mem.1.le hs_mem.2 ht.2 x y)
  have hyx : rank t y ≤ rank t x := by
    have hev : ∀ᶠ s in 𝓝[Ioo 0 t] t, rank t y ≤ rank s y :=
      (hlower t ht y).filter_mono (nhdsWithin_mono t hsubset)
    have hmem : ∀ᶠ s in 𝓝[Ioo 0 t] t, s ∈ Ioo 0 t := self_mem_nhdsWithin
    let _ : (𝓝[Ioo 0 t] t).NeBot := right_nhdsWithin_Ioo_neBot ht.1
    obtain ⟨s, hs_mem, hs_rank⟩ := (hmem.and hev).exists
    exact hs_rank.trans (hspread hs_mem.1.le hs_mem.2 ht.2 y x)
  exact le_antisymm hxy hyx

theorem rank_monotoneOn_of_spreading
    {rank : Real → X → Nat} {T : Real}
    (hspread : ∀ {s t : Real}, 0 ≤ s → s < t → t ≤ T →
      ∀ x y, rank s x ≤ rank t y)
    (x : X) : MonotoneOn (fun t => rank t x) (Ioc 0 T) := by
  intro s hs t ht hst
  rcases hst.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact hspread hs.1.le hlt ht.2 x x

theorem rank_eq_on_left_interval_of_spreading
    {rank : Real → X → Nat} {T : Real}
    (hlower : ∀ t ∈ Ioc 0 T, ∀ x,
      ∀ᶠ s in 𝓝[Icc 0 T] t, rank t x ≤ rank s x)
    (hspread : ∀ {s t : Real}, 0 ≤ s → s < t → t ≤ T →
      ∀ x y, rank s x ≤ rank t y)
    {t : Real} (ht : t ∈ Ioc 0 T) (x : X) :
    ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t, rank s x = rank t x := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp (hlower t ht x)
  let ε := min δ t
  have hεpos : 0 < ε := lt_min hδ ht.1
  have hεt : ε ≤ t := min_le_right δ t
  have hεδ : ε ≤ δ := min_le_left δ t
  refine ⟨ε, ⟨hεpos, hεt⟩, ?_⟩
  intro s hs
  have hs0 : 0 < s := by linarith [hs.1, hεt]
  have hsT : s ≤ T := hs.2.trans ht.2
  have hdist : dist s t < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2)]
    linarith [hs.1, hεδ]
  have hlowerst : rank t x ≤ rank s x :=
    hball ⟨Metric.mem_ball.mpr hdist, ⟨hs0.le, hsT⟩⟩
  have hupperst : rank s x ≤ rank t x := by
    rcases hs.2.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact hspread hs0.le hlt ht.2 x x
  exact le_antisymm hupperst hlowerst

theorem exists_rank_eq_on_initial_interval_of_spreading
    [Nonempty X] {rank : Real → X → Nat} {T : Real}
    (hT : 0 < T)
    (hspread : ∀ {s t : Real}, 0 ≤ s → s < t → t ≤ T →
      ∀ x y, rank s x ≤ rank t y) :
    ∃ δ ∈ Ioc 0 T, ∃ q : Nat, ∀ t ∈ Ioc 0 δ, ∀ x, rank t x = q := by
  let values : Set Nat := {q | ∃ t ∈ Ioc 0 T, ∃ x, rank t x = q}
  have hvalues : values.Nonempty := by
    exact ⟨rank T (Classical.choice inferInstance), T, ⟨hT, le_rfl⟩,
      Classical.choice inferInstance, rfl⟩
  let q := sInf values
  have hqmem : q ∈ values := Nat.sInf_mem hvalues
  obtain ⟨tstar, htstar, xstar, hxstar⟩ := hqmem
  refine ⟨tstar / 2,
    ⟨half_pos htstar.1, (half_le_self htstar.1.le).trans htstar.2⟩, q, ?_⟩
  intro t ht x
  have htT : t ∈ Ioc 0 T :=
    ⟨ht.1, ht.2.trans ((half_le_self htstar.1.le).trans htstar.2)⟩
  have hqle : q ≤ rank t x := Nat.sInf_le ⟨t, htT, x, rfl⟩
  have httstar : t < tstar := by linarith [ht.2, htstar.1]
  have hle : rank t x ≤ q := by
    rw [← hxstar]
    exact hspread ht.1.le httstar htstar.2 x xstar
  exact le_antisymm hle hqle

theorem rank_spatially_constant_and_locally_constant_from_left_of_spreading
    [Nonempty X] {rank : Real → X → Nat} {T : Real}
    (hT : 0 < T)
    (hlower : ∀ t ∈ Ioc 0 T, ∀ x,
      ∀ᶠ s in 𝓝[Icc 0 T] t, rank t x ≤ rank s x)
    (hspread : ∀ {s t : Real}, 0 ≤ s → s < t → t ≤ T →
      ∀ x y, rank s x ≤ rank t y) :
    (∀ t ∈ Ioc 0 T, ∀ x y, rank t x = rank t y) ∧
      (∀ x, MonotoneOn (fun t => rank t x) (Ioc 0 T)) ∧
      (∀ t ∈ Ioc 0 T, ∀ x,
        ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t, rank s x = rank t x) ∧
      ∃ δ ∈ Ioc 0 T, ∃ q : Nat,
        ∀ t ∈ Ioc 0 δ, ∀ x, rank t x = q := by
  refine ⟨?_, ?_, ?_, exists_rank_eq_on_initial_interval_of_spreading hT hspread⟩
  · intro t ht x y
    exact rank_eq_at_positive_time_of_spreading hlower hspread ht x y
  · intro x
    exact rank_monotoneOn_of_spreading hspread x
  · intro t ht x
    exact rank_eq_on_left_interval_of_spreading hlower hspread ht x

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem finrank_range_eq_at_positive_time_of_spreading
    {A : ℝ → X → {B : E →L[ℝ] E // B.IsPositive}} {T : ℝ}
    (hcontinuous : ∀ x, ContinuousOn (fun t => A t x) (Icc 0 T))
    (hspread : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      Module.finrank ℝ (A s x).1.range ≤
        Module.finrank ℝ (A t y).1.range)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x y : X) :
    Module.finrank ℝ (A t x).1.range =
      Module.finrank ℝ (A t y).1.range := by
  apply rank_eq_at_positive_time_of_spreading
    (rank := fun s z => Module.finrank ℝ (A s z).1.range)
    (T := T) (t := t)
  · intro s hs z
    exact ContinuousLinearMap.IsPositive.eventually_finrank_range_ge_of_tendsto
      (hcontinuous z s ⟨hs.1.le, hs.2⟩)
  · exact hspread
  · exact ht

theorem finrank_range_le_of_lowerKyFanSum_pos_spreading
    {A : ℝ → X → {B : E →L[ℝ] E // B.IsPositive}} {T : ℝ}
    (hkyfan : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      ∀ k : ℕ, 1 ≤ k → k ≤ Module.finrank ℝ E →
        0 < ((A s x).2.toLinearMap.isSymmetric.lowerKyFanSum k) →
        0 < ((A t y).2.toLinearMap.isSymmetric.lowerKyFanSum k))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (x y : X) :
    Module.finrank ℝ (A s x).1.range ≤
      Module.finrank ℝ (A t y).1.range := by
  exact LinearMap.IsPositive.finrank_range_le_of_lowerKyFanSum_pos
    (A s x).2.toLinearMap (A t y).2.toLinearMap
    (fun k hk₁ hkE hkpos => hkyfan hs hst ht x y k hk₁ hkE hkpos)

theorem finrank_range_spatially_constant_and_locally_constant_from_lowerKyFanSum_pos
    [Nonempty X]
    {A : ℝ → X → {B : E →L[ℝ] E // B.IsPositive}} {T : ℝ}
    (hT : 0 < T)
    (hcontinuous : ∀ x, ContinuousOn (fun t => A t x) (Icc 0 T))
    (hkyfan : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      ∀ k : ℕ, 1 ≤ k → k ≤ Module.finrank ℝ E →
        0 < ((A s x).2.toLinearMap.isSymmetric.lowerKyFanSum k) →
        0 < ((A t y).2.toLinearMap.isSymmetric.lowerKyFanSum k)) :
    (∀ t ∈ Ioc 0 T, ∀ x y,
      Module.finrank ℝ (A t x).1.range =
        Module.finrank ℝ (A t y).1.range) ∧
      (∀ x, MonotoneOn
        (fun t => Module.finrank ℝ (A t x).1.range) (Ioc 0 T)) ∧
      (∀ t ∈ Ioc 0 T, ∀ x,
        ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t,
          Module.finrank ℝ (A s x).1.range =
            Module.finrank ℝ (A t x).1.range) ∧
      ∃ δ ∈ Ioc 0 T, ∃ q : Nat, ∀ t ∈ Ioc 0 δ, ∀ x,
        Module.finrank ℝ (A t x).1.range = q := by
  refine rank_spatially_constant_and_locally_constant_from_left_of_spreading
    hT ?_ ?_
  · intro t ht x
    exact ContinuousLinearMap.IsPositive.eventually_finrank_range_ge_of_tendsto
      (hcontinuous x t ⟨ht.1.le, ht.2⟩)
  · intro s t hs hst ht x y
    exact finrank_range_le_of_lowerKyFanSum_pos_spreading
      hkyfan hs hst ht x y

theorem finrank_range_spatially_constant_and_locally_constant_from_left_of_spreading
    [Nonempty X]
    {A : ℝ → X → {B : E →L[ℝ] E // B.IsPositive}} {T : ℝ}
    (hT : 0 < T)
    (hcontinuous : ∀ x, ContinuousOn (fun t => A t x) (Icc 0 T))
    (hspread : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      Module.finrank ℝ (A s x).1.range ≤
        Module.finrank ℝ (A t y).1.range) :
    (∀ t ∈ Ioc 0 T, ∀ x y,
      Module.finrank ℝ (A t x).1.range =
        Module.finrank ℝ (A t y).1.range) ∧
      (∀ x, MonotoneOn
        (fun t => Module.finrank ℝ (A t x).1.range) (Ioc 0 T)) ∧
      (∀ t ∈ Ioc 0 T, ∀ x,
        ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t,
          Module.finrank ℝ (A s x).1.range =
            Module.finrank ℝ (A t x).1.range) ∧
      ∃ δ ∈ Ioc 0 T, ∃ q : Nat, ∀ t ∈ Ioc 0 δ, ∀ x,
        Module.finrank ℝ (A t x).1.range = q := by
  apply rank_spatially_constant_and_locally_constant_from_left_of_spreading
    hT _ hspread
  intro t ht x
  exact ContinuousLinearMap.IsPositive.eventually_finrank_range_ge_of_tendsto
    (hcontinuous x t ⟨ht.1.le, ht.2⟩)
