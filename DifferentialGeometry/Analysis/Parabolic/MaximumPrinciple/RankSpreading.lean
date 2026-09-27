import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.KyFanBarrier
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Barrier
import DifferentialGeometry.Geometry.Boundary.SmoothAnnulus
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.InitialData
import DifferentialGeometry.Geometry.Metric.Family.Regularity.DifferentialOperator
import DifferentialGeometry.Analysis.FiniteDimensional.Rank
import DifferentialGeometry.Topology.ConnectedCompactNeighborhood
import DifferentialGeometry.Topology.MonotoneStratification
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

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

theorem exists_positive_time_rank_function_of_spreading
    [Nonempty X] {rank : ℝ → X → ℕ} {T : ℝ} (hT : 0 < T)
    (hlower : ∀ t ∈ Ioc 0 T, ∀ x,
      ∀ᶠ s in 𝓝[Icc 0 T] t, rank t x ≤ rank s x)
    (hspread : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ x y, rank s x ≤ rank t y) :
    ∃ ρ : ℝ → ℕ,
      (∀ t ∈ Ioc 0 T, ∀ x, rank t x = ρ t) ∧
      MonotoneOn ρ (Ioc 0 T) ∧
      (∀ t ∈ Ioc 0 T, ∃ ε ∈ Ioc 0 t,
        ∀ s ∈ Ioc (t - ε) t, ρ s = ρ t) ∧
      (∃ δ ∈ Ioc 0 T, ∀ t ∈ Ioc 0 δ, ρ t = ρ δ) ∧
      (ρ '' Ioc 0 T).Finite := by
  classical
  let x : X := Classical.choice inferInstance
  let ρ : ℝ → ℕ := fun t => rank t x
  obtain ⟨hspace, hmono, hleft, δ, hδ, q, hinit⟩ :=
    rank_spatially_constant_and_locally_constant_from_left_of_spreading hT hlower hspread
  refine ⟨ρ, (fun t ht y => hspace t ht y x), hmono x,
    (fun t ht => hleft t ht x), ?_, ?_⟩
  · exact ⟨δ, hδ, fun t ht => (hinit t ht x).trans (hinit δ ⟨hδ.1, le_rfl⟩ x).symm⟩
  · apply (finite_Iic (ρ T)).subset
    rintro _ ⟨t, ht, rfl⟩
    exact hmono x ht ⟨hT, le_rfl⟩ ht.2

theorem rank_finite_interval_partition_of_spreading
    [Nonempty X] {rank : ℝ → X → ℕ} {T : ℝ} (hT : 0 < T)
    (hlower : ∀ t ∈ Ioc 0 T, ∀ x,
      ∀ᶠ s in 𝓝[Icc 0 T] t, rank t x ≤ rank s x)
    (hspread : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ x y, rank s x ≤ rank t y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ T) :
    ∃ Q : Finset ℕ,
      Icc a b = ⋃ q ∈ Q, {t | t ∈ Icc a b ∧ ∀ x, rank t x = q} ∧
      (Q : Set ℕ).PairwiseDisjoint
        (fun q => {t | t ∈ Icc a b ∧ ∀ x, rank t x = q}) ∧
      ∀ q ∈ Q, {t | t ∈ Icc a b ∧ ∀ x, rank t x = q}.Nonempty ∧
        ∃ l u : ℝ, a ≤ l ∧ l ≤ u ∧ u ≤ b ∧
          ({t | t ∈ Icc a b ∧ ∀ x, rank t x = q} = Icc a u ∧
              (∀ x, rank a x = q) ∨
            {t | t ∈ Icc a b ∧ ∀ x, rank t x = q} = Ioc l u ∧
              ¬ ∀ x, rank a x = q) := by
  obtain ⟨ρ, hspace, hmono, hleft, -, hfinite⟩ :=
    exists_positive_time_rank_function_of_spreading hT hlower hspread
  have hsub : Icc a b ⊆ Ioc 0 T := by
    intro t ht
    exact ⟨ha.trans_le ht.1, ht.2.trans hb⟩
  have hfiber (q : ℕ) :
      {t | t ∈ Icc a b ∧ ∀ x, rank t x = q} =
        {t | t ∈ Icc a b ∧ ρ t = q} := by
    ext t
    constructor
    · intro ht
      exact ⟨ht.1, (hspace t (hsub ht.1) (Classical.choice inferInstance)).symm.trans
        (ht.2 (Classical.choice inferInstance))⟩
    · intro ht
      exact ⟨ht.1, fun x => (hspace t (hsub ht.1) x).trans ht.2⟩
  have hqa (q : ℕ) : (∀ x, rank a x = q) ↔ ρ a = q := by
    constructor
    · intro hq
      exact (hspace a (hsub ⟨le_rfl, hab⟩) (Classical.choice inferInstance)).symm.trans
        (hq (Classical.choice inferInstance))
    · intro hq x
      exact (hspace a (hsub ⟨le_rfl, hab⟩) x).trans hq
  have hparts := exists_finite_level_set_partition_of_monotoneOn_left_constant
    (hfinite.subset (image_mono hsub)) (hmono.mono hsub) (by
      intro t ht
      obtain ⟨ε, hε, hconst⟩ := hleft t (hsub ⟨ht.1.le, ht.2⟩)
      exact ⟨ε, hε.1, fun s _ hs hst => hconst s ⟨hs, hst⟩⟩)
  simpa only [hfiber, hqa] using hparts

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

theorem finrank_range_le_of_lowerKyFanSum_pos_spreading_of_finrank_eq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {A : E →L[ℝ] E} {B : F →L[ℝ] F}
    (hA : A.IsPositive) (hB : B.IsPositive)
    (hfinrank : Module.finrank ℝ E = Module.finrank ℝ F)
    (hkyfan : ∀ k : ℕ, 1 ≤ k → k ≤ Module.finrank ℝ E →
      0 < hA.toLinearMap.isSymmetric.lowerKyFanSum k →
      0 < hB.toLinearMap.isSymmetric.lowerKyFanSum k) :
    Module.finrank ℝ A.range ≤ Module.finrank ℝ B.range :=
  LinearMap.IsPositive.finrank_range_le_of_lowerKyFanSum_pos_of_finrank_eq
    hA.toLinearMap hB.toLinearMap hfinrank hkyfan

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

private theorem exists_uniform_lower_bound_near_terminal_time
    {M : Type*} [TopologicalSpace M] [T2Space M]
    {K : Set M} (hK : IsCompact K) {s t : Real} (hst : s ≤ t)
    (phi : Real → M → Real)
    (hphi : ContinuousOn (fun p : Real × M => phi p.1 p.2) (Icc s t ×ˢ K))
    (hpos : ∀ x ∈ K, 0 < phi t x) :
    ∃ delta eta : Real, 0 < delta ∧ 0 < eta ∧
      ∀ q ∈ Icc s t, t - delta < q → ∀ x ∈ K, eta ≤ phi q x := by
  have hslice : ContinuousOn (phi t) K := hphi.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun x hx => ⟨⟨hst, le_rfl⟩, hx⟩)
  obtain ⟨m, hm, hmin⟩ := hK.exists_forall_le' hslice hpos
  let slab : Set (Real × M) := Icc s t ×ˢ K
  let bad : Set (Real × M) :=
    slab ∩ (fun p : Real × M => phi p.1 p.2) ⁻¹' Iic (m / 2)
  have hslab : IsCompact slab := isCompact_Icc.prod hK
  have hbadClosed : IsClosed bad :=
    hphi.preimage_isClosed_of_isClosed hslab.isClosed isClosed_Iic
  have hbad : IsCompact bad := hslab.of_isClosed_subset hbadClosed (fun _ hp => hp.1)
  by_cases hbadNe : bad.Nonempty
  · obtain ⟨p, hp, hpmax⟩ := hbad.exists_isMaxOn hbadNe continuous_fst.continuousOn
    have hpt : p.1 < t := by
      apply lt_of_le_of_ne hp.1.1.2
      intro heq
      have hvalue : phi p.1 p.2 ≤ m / 2 := hp.2
      have hlower := hmin p.2 hp.1.2
      rw [heq] at hvalue
      linarith only [hm, hvalue, hlower]
    refine ⟨t - p.1, m / 2, sub_pos.mpr hpt, half_pos hm, ?_⟩
    intro q hq hlate x hx
    by_contra hfail
    have hqx : (q, x) ∈ bad := ⟨⟨hq, hx⟩, (lt_of_not_ge hfail).le⟩
    have hmax : q ≤ p.1 := hpmax hqx
    linarith only [hlate, hmax]
  · refine ⟨1, m / 2, by norm_num, half_pos hm, ?_⟩
    intro q hq hlate x hx
    by_contra hfail
    exact hbadNe ⟨(q, x), ⟨⟨hq, hx⟩, (lt_of_not_ge hfail).le⟩⟩

variable {EModel : Type*} [NormedAddCommGroup EModel] [NormedSpace ℝ EModel]
  [FiniteDimensional ℝ EModel]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EModel H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private theorem exists_smooth_bump_mul_le_of_pos_on
    {phi : M → ℝ} {K : Set M} {x : M} (hphi : ContinuousAt phi x)
    (hphiNonneg : ∀ y ∈ K, 0 ≤ phi y)
    (hx : 0 < phi x) {U : Set M} (hU : U ∈ 𝓝 x)
    {k : ℕ} (hk : 0 < k) :
    ∃ f : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
      (∀ y, 0 ≤ f y) ∧ HasCompactSupport f ∧
      tsupport f ⊆ U ∧ 0 < f x ∧
      ∀ y ∈ K, (k : ℝ) * f y ≤ phi y := by
  let U' : Set M := U ∩ phi ⁻¹' Ioi (phi x / 2)
  have hU' : U' ∈ 𝓝 x := by
    refine inter_mem hU (hphi.preimage_mem_nhds ?_)
    exact isOpen_Ioi.mem_nhds (half_lt_self hx)
  obtain ⟨chi, -, hchi⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hU'
  let a : ℝ := phi x / (2 * (k : ℝ))
  let f : M → ℝ := fun y ↦ a * chi y
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have ha : 0 < a := div_pos hx (mul_pos zero_lt_two hkReal)
  refine ⟨f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact contMDiff_const.mul chi.contMDiff
  · intro y
    exact mul_nonneg ha.le chi.nonneg
  · exact chi.hasCompactSupport.mul_left
  · exact tsupport_mul_subset_right.trans (hchi.trans inter_subset_left)
  · rw [show f x = a * chi x by rfl, chi.eq_one, mul_one]
    exact ha
  · intro y hyK
    by_cases hy : chi y = 0
    · simp only [f, hy, mul_zero, mul_zero]
      exact hphiNonneg y hyK
    · have hyU' : y ∈ U' := hchi (subset_tsupport _ hy)
      have hyphi : phi x / 2 < phi y := hyU'.2
      have hchile : chi y ≤ 1 := chi.le_one
      dsimp only [f, a]
      calc
        (k : ℝ) * (phi x / (2 * (k : ℝ)) * chi y) =
            phi x / 2 * chi y := by field_simp
        _ ≤ phi x / 2 := by
          exact mul_le_of_le_one_right (half_pos hx).le hchile
        _ ≤ phi y := hyphi.le

namespace PositiveSystem

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem lowerKyFanSum_pos_on_annulus
    [VectorBundle Real EModel (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ y, FiniteDimensional Real (V y)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (cov : Real → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T s t : Real} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    {k : Nat} (hkpos : 0 < k) (hk : k ≤ Module.finrank Real F)
    (rho : M → Real) (hrho : ContMDiff I 𝓘(Real, Real) ∞ rho)
    {r R : Real} (hrR : r < R)
    (hK : IsCompact {y : M | r ≤ rho y ∧ rho y ≤ R})
    (hKInterior : interior {y : M | r ≤ rho y ∧ rho y ≤ R} ⊆ I.interior M)
    (A : Real → Cₛ^∞⟮I; F →L[Real] F, (fun x : M ↦ V x →L[Real] V x)⟯)
    (hAsymm : ∀ q y,
      ((A q y : V y →L[Real] V y) : V y →ₗ[Real] V y).IsSymmetric)
    (hApos : ∀ q ∈ Icc s t, ∀ y ∈ {y : M | r ≤ rho y ∧ rho y ≤ R},
      (A q y).IsPositive)
    (hphiCont : ContinuousOn (fun p : Real × M ↦
      (hAsymm p.1 p.2).lowerKyFanSum k)
      (Icc s t ×ˢ {y : M | r ≤ rho y ∧ rho y ≤ R}))
    {B : Real} (hB : ∀ q ∈ Icc s t,
      ∀ y ∈ {y : M | r ≤ rho y ∧ rho y ≤ R}, ‖A q y‖ ≤ B)
    (X : Real → (y : M) → TangentSpace I y)
    (reaction : Real → (y : M) →
      (V y →L[Real] V y) → V y →L[Real] V y)
    (hreactionNull : ∀ q y, satisfiesNullEigenvectorCondition (reaction q y))
    {Klip : NNReal}
    (hreactionLip : ∀ q ∈ Ioc s t,
      ∀ y ∈ interior {y : M | r ≤ rho y ∧ rho y ≤ R},
      LipschitzOnWith Klip (reaction q y)
        {D : V y →L[Real] V y | D.IsPositive ∧ ‖D‖ ≤ 2 * B})
    (hgrad : ContinuousOn (fun p : Real × M =>
      (G.metric p.1).inner p.2
        (gradientFun (I := I) (G.metric p.1) rho p.2)
        (gradientFun (I := I) (G.metric p.1) rho p.2))
      (Icc s t ×ˢ {x : M | r ≤ rho x ∧ rho x ≤ R}))
    (hgrad_ne : ∀ q ∈ Icc s t, ∀ x ∈ {x : M | r ≤ rho x ∧ rho x ≤ R},
      gradientFun (I := I) (G.metric q) rho x ≠ 0)
    (hheat : ContinuousOn (fun p : Real × M =>
      heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
      (Icc s t ×ˢ {x : M | r ≤ rho x ∧ rho x ≤ R}))
    (hinner : ∀ y, rho y = r → 0 < (hAsymm t y).lowerKyFanSum k)
    (hGconn : ∀ q ∈ Ioc s t,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioc s t, ∀ y ∈ interior {y : M | r ≤ rho y ∧ rho y ≤ R},
      DifferentiableAt Real (fun a ↦ A a y) q)
    (hevolution : ∀ q ∈ Ioc s t,
      ∀ y ∈ interior {y : M | r ≤ rho y ∧ rho y ≤ R},
      deriv (fun a ↦ A a y) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun z ↦ A q z) y +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun z ↦ A q z) y (X q y) +
          reaction q y (A q y)) :
    ∀ y ∈ {y : M | r ≤ rho y ∧ rho y < R},
      0 < (hAsymm t y).lowerKyFanSum k := by
  intro z hz
  have hzK : z ∈ {y : M | r ≤ rho y ∧ rho y ≤ R} := ⟨hz.1, hz.2.le⟩
  let _ : NeZero (Module.finrank Real EModel) := ⟨by
    intro hzero
    let _ : Subsingleton EModel := (Module.finrank_zero_iff (R := Real) (M := EModel)).mp hzero
    let _ : Subsingleton (TangentSpace I z) := by unfold TangentSpace; infer_instance
    exact hgrad_ne t ⟨hst.le, le_rfl⟩ z hzK (Subsingleton.elim _ _)⟩
  let K : Set M := {y : M | r ≤ rho y ∧ rho y ≤ R}
  let L : Set M := {y : M | rho y = r}
  have hLK : L ⊆ K := by
    intro y hy
    change rho y = r at hy
    exact ⟨hy.ge, hy.le.trans hrR.le⟩
  have hL : IsCompact L := hK.of_isClosed_subset
    (isClosed_eq hrho.continuous continuous_const) hLK
  have hphiL : ContinuousOn (fun p : Real × M =>
      (hAsymm p.1 p.2).lowerKyFanSum k) (Icc s t ×ˢ L) :=
    hphiCont.mono (fun _ hp => ⟨hp.1, hLK hp.2⟩)
  obtain ⟨delta, eta, hdelta, heta, hsource⟩ :=
    exists_uniform_lower_bound_near_terminal_time hL hst.le
      (fun q y => (hAsymm q y).lowerKyFanSum k) hphiL hinner
  have hkReal : 0 < (k : Real) := by exact_mod_cast hkpos
  let c : Real := (Klip : Real) + 1
  have hc : (Klip : Real) < c := by dsimp only [c]; linarith
  obtain ⟨f, hfSmooth, hfInitial, hfBound, hfOuter, hfEarly, hfFinal, hfP⟩ :=
    exists_annular_parabolic_subsolution G hs hst ht X rho hrho hrR hK
      hgrad hgrad_ne hheat (c := c) hdelta (div_pos heta hkReal)
  have hphiNonneg (q : Real) (hq : q ∈ Icc s t) (y : M) (hy : y ∈ K) :
      0 ≤ (hAsymm q y).lowerKyFanSum k :=
    LinearMap.IsSymmetric.lowerKyFanSum_nonneg
      ((ContinuousLinearMap.isPositive_toLinearMap_iff (A q y)).mpr (hApos q hq y hy)) k
  have hfSlice (q : Real) : ContMDiff I 𝓘(Real, Real) ∞ (f q) :=
    hfSmooth.comp (contMDiff_const.prodMk contMDiff_id)
  have hfBoundary (q : Real) (hq : q ∈ Icc s t) (y : M) (hy : y ∈ frontier K) :
      (k : Real) * f q y ≤ (hAsymm q y).lowerKyFanSum k := by
    have hyK : y ∈ K := by
      have hycl : y ∈ closure K := frontier_subset_closure hy
      rwa [(show IsClosed K from hK.isClosed).closure_eq] at hycl
    have hnonpos (hf : f q y ≤ 0) :
        (k : Real) * f q y ≤ (hAsymm q y).lowerKyFanSum k :=
      (mul_nonpos_of_nonneg_of_nonpos hkReal.le hf).trans (hphiNonneg q hq y hyK)
    rcases DifferentialGeometry.Geometry.Boundary.frontier_levelSet_annulus_subset
        hrho.continuous hy with hyr | hyR
    · by_cases hqEarly : q ≤ t - delta
      · exact hnonpos (hfEarly q hq hqEarly y hyK)
      · have hsourceBound := hsource q hq (lt_of_not_ge hqEarly) y hyr
        apply le_trans ?_ hsourceBound
        have hmul := mul_le_mul_of_nonneg_left (hfBound q hq y hyK).le hkReal.le
        simpa only [mul_div_cancel₀ eta hkReal.ne'] using hmul
    · exact hnonpos (hfOuter q hq y hyK hyR)
  have hT : 0 < T := (hs.trans_lt hst).trans_le ht
  have hcomparison := mul_le_lowerKyFanSum_on_compact_set_of_subsolution
    G cov hcov hT hs ht hkpos hk hK hKInterior A hAsymm hApos hphiCont hB
      X reaction hreactionNull hreactionLip f hfSmooth.continuous.continuousOn
      (fun y hy => (mul_nonpos_of_nonneg_of_nonpos hkReal.le (hfInitial y hy)).trans
        (hphiNonneg s ⟨le_rfl, hst.le⟩ y hy)) hfBoundary
      (fun q _ y _ =>
        ((contMDiff_iff_contDiff.mp
          (hfSmooth.comp (contMDiff_id.prodMk contMDiff_const))).differentiable
          (by norm_num)) q)
      (fun q _ y _ => (hfSlice q).mdifferentiable (by simp) y)
      (fun q _ y _ => gradientFun_mdiffAt (I := I) (G.metric q) (hfSlice q) y)
      hc (fun q hq y hy _ => hfP q ⟨hq.1.le, hq.2⟩ y (interior_subset hy))
      hGconn hAt hevolution
  exact (mul_pos hkReal (hfFinal z hzK hz.2)).trans_le
    (hcomparison t ⟨hst.le, le_rfl⟩ z hzK)

theorem exists_lowerKyFanSum_positive_propagation_neighborhood
    [VectorBundle Real EModel (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ y, FiniteDimensional Real (V y)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (cov : Real → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T s t : Real} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    {Omega : Set M} (hOmega : IsOpen Omega) (hOmegaInterior : Omega ⊆ I.interior M)
    (a : M) (ha : a ∈ Omega)
    {k : Nat} (hkpos : 0 < k) (hk : k ≤ Module.finrank Real F)
    (A : Real → Cₛ^∞⟮I; F →L[Real] F, (fun x : M ↦ V x →L[Real] V x)⟯)
    (hAsymm : ∀ q y,
      ((A q y : V y →L[Real] V y) : V y →ₗ[Real] V y).IsSymmetric)
    (hApos : ∀ q ∈ Icc s t, ∀ y ∈ Omega, (A q y).IsPositive)
    (hphiCont : ContinuousOn (fun p : Real × M =>
      (hAsymm p.1 p.2).lowerKyFanSum k) (Icc s t ×ˢ Omega))
    (hA_bound : ∀ {K : Set M}, IsCompact K → K ⊆ Omega →
      ∃ B : Real, ∀ q ∈ Icc s t, ∀ y ∈ K, ‖A q y‖ ≤ B)
    (X : Real → (y : M) → TangentSpace I y)
    (reaction : Real → (y : M) →
      (V y →L[Real] V y) → V y →L[Real] V y)
    (hreactionNull : ∀ q y, satisfiesNullEigenvectorCondition (reaction q y))
    (hreactionLip : ∀ {K : Set M}, IsCompact K → K ⊆ Omega → ∀ B : Real,
      ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ y ∈ K,
        LipschitzOnWith Klip (reaction q y)
          {D : V y →L[Real] V y | D.IsPositive ∧ ‖D‖ ≤ 2 * B})
    (hgrad : ∀ (rho : M → Real), ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2)) (Icc s t ×ˢ Omega))
    (hheat : ∀ (rho : M → Real), ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2) (Icc s t ×ˢ Omega))
    (hGconn : ∀ q ∈ Ioc s t,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioc s t, ∀ y ∈ Omega, DifferentiableAt Real (fun r ↦ A r y) q)
    (hevolution : ∀ q ∈ Ioc s t, ∀ y ∈ Omega,
      deriv (fun r ↦ A r y) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun z ↦ A q z) y +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun z ↦ A q z) y (X q y) +
          reaction q y (A q y)) :
    ∃ U : Set M, IsOpen U ∧ a ∈ U ∧ IsCompact (closure U) ∧ closure U ⊆ Omega ∧
      ∀ x ∈ U, 0 < (hAsymm t x).lowerKyFanSum k →
        ∀ y ∈ U, 0 < (hAsymm t y).lowerKyFanSum k := by
  obtain ⟨U, hUopen, haU, hUcompact, hUOmega, hUprop⟩ :=
    SmoothBumpFunction.exists_annulus_neighborhood (I := I) a (hOmega.mem_nhds ha)
  refine ⟨U, hUopen, haU, hUcompact, hUOmega, ?_⟩
  intro x hx hxpos y hy
  by_cases hxy : x = y
  · subst y
    exact hxpos
  have hxOmega : x ∈ Omega := hUOmega (subset_closure hx)
  have htIcc : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  have hphiWithin : ContinuousWithinAt (fun z => (hAsymm t z).lowerKyFanSum k) Omega x :=
    (hphiCont (t, x) ⟨htIcc, hxOmega⟩).comp
      (continuousAt_const.prodMk continuousAt_id).continuousWithinAt
      (fun z hz => ⟨htIcc, hz⟩)
  have hphiAt : ContinuousAt (fun z => (hAsymm t z).lowerKyFanSum k) x :=
    hphiWithin.continuousAt (hOmega.mem_nhds hxOmega)
  have hV : {z | 0 < (hAsymm t z).lowerKyFanSum k} ∈ nhds x :=
    hphiAt.preimage_mem_nhds (Ioi_mem_nhds hxpos)
  obtain ⟨rho, r, R, hrho, -, -, hrR, hK, hKOmega, hry, hyR, hinner, hgrad_ne⟩ :=
    hUprop x hx y hy hxy _ hV
  obtain ⟨B, hB⟩ := hA_bound hK hKOmega
  obtain ⟨Klip, hLip⟩ := hreactionLip hK hKOmega B
  exact lowerKyFanSum_pos_on_annulus G cov hcov hs hst ht hkpos hk rho hrho hrR hK
    (interior_subset.trans (hKOmega.trans hOmegaInterior)) A hAsymm
    (fun q hq z hz => hApos q hq z (hKOmega hz))
    (hphiCont.mono (fun p hp => ⟨hp.1, hKOmega hp.2⟩)) hB X reaction hreactionNull
    (fun q hq z hz => hLip q hq z (interior_subset hz))
    ((hgrad rho hrho).mono (fun p hp => ⟨hp.1, hKOmega hp.2⟩))
    (fun q _ z hz => hgrad_ne (G.metric q) z hz)
    ((hheat rho hrho).mono (fun p hp => ⟨hp.1, hKOmega hp.2⟩))
    hinner hGconn (fun q hq z hz => hAt q hq z (hKOmega (interior_subset hz)))
    (fun q hq z hz => hevolution q hq z (hKOmega (interior_subset hz))) y ⟨hry, hyR⟩

theorem lowerKyFanSum_pos_on_preconnected_open_set
    [VectorBundle Real EModel (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ y, FiniteDimensional Real (V y)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (cov : Real → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T s t : Real} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    {Omega : Set M} (hOmega : IsOpen Omega) (hOmegaInterior : Omega ⊆ I.interior M)
    (hOmegaConnected : IsPreconnected Omega)
    {k : Nat} (hkpos : 0 < k) (hk : k ≤ Module.finrank Real F)
    (A : Real → Cₛ^∞⟮I; F →L[Real] F, (fun x : M ↦ V x →L[Real] V x)⟯)
    (hAsymm : ∀ q y,
      ((A q y : V y →L[Real] V y) : V y →ₗ[Real] V y).IsSymmetric)
    (hApos : ∀ q ∈ Icc s t, ∀ y ∈ Omega, (A q y).IsPositive)
    (hphiCont : ContinuousOn (fun p : Real × M =>
      (hAsymm p.1 p.2).lowerKyFanSum k) (Icc s t ×ˢ Omega))
    (hA_bound : ∀ {K : Set M}, IsCompact K → K ⊆ Omega →
      ∃ B : Real, ∀ q ∈ Icc s t, ∀ y ∈ K, ‖A q y‖ ≤ B)
    (X : Real → (y : M) → TangentSpace I y)
    (reaction : Real → (y : M) →
      (V y →L[Real] V y) → V y →L[Real] V y)
    (hreactionNull : ∀ q y, satisfiesNullEigenvectorCondition (reaction q y))
    (hreactionLip : ∀ {K : Set M}, IsCompact K → K ⊆ Omega → ∀ B : Real,
      ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ y ∈ K,
        LipschitzOnWith Klip (reaction q y)
          {D : V y →L[Real] V y | D.IsPositive ∧ ‖D‖ ≤ 2 * B})
    (hgrad : ∀ (rho : M → Real), ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2)) (Icc s t ×ˢ Omega))
    (hheat : ∀ (rho : M → Real), ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2) (Icc s t ×ˢ Omega))
    (hGconn : ∀ q ∈ Ioc s t,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioc s t, ∀ y ∈ Omega, DifferentiableAt Real (fun r ↦ A r y) q)
    (hevolution : ∀ q ∈ Ioc s t, ∀ y ∈ Omega,
      deriv (fun r ↦ A r y) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun z ↦ A q z) y +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun z ↦ A q z) y (X q y) +
          reaction q y (A q y))
    {x : M} (hx : x ∈ Omega) (hxpos : 0 < (hAsymm t x).lowerKyFanSum k) :
    ∀ y ∈ Omega, 0 < (hAsymm t y).lowerKyFanSum k := by
  refine IsPreconnected.forall_of_locally_imp
    (P := fun z => 0 < (hAsymm t z).lowerKyFanSum k) hOmegaConnected ?_ hx hxpos
  intro a ha
  obtain ⟨U, hUopen, haU, -, hUOmega, hUprop⟩ :=
      exists_lowerKyFanSum_positive_propagation_neighborhood G cov hcov hs hst ht
        hOmega hOmegaInterior a ha hkpos hk A hAsymm hApos hphiCont hA_bound
        X reaction hreactionNull hreactionLip hgrad hheat hGconn hAt hevolution
  exact ⟨U, hUopen, haU, subset_closure.trans hUOmega, hUprop⟩


theorem lowerKyFanSum_pos_at_of_local_dirichlet_solution_exists
    [VectorBundle ℝ EModel (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ z, FiniteDimensional ℝ (V z)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    {k : ℕ} (hkpos : 0 < k) (hk : k ≤ Module.finrank ℝ F)
    {Kset : Set M} (hKset : IsCompact Kset)
    (hKsetInterior : interior Kset ⊆ I.interior M)
    {x y : M} (hxKset : x ∈ interior Kset) (hyKset : y ∈ interior Kset)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAsymm : ∀ q z,
      ((A q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric)
    (hApos : ∀ q ∈ Icc s t, ∀ z ∈ Kset, (A q z).IsPositive)
    (hphiCont : ContinuousOn (fun p : ℝ × M ↦
      (hAsymm p.1 p.2).lowerKyFanSum k) (Icc s t ×ˢ Kset))
    (hsource : 0 < (hAsymm s x).lowerKyFanSum k)
    {R : ℝ} (hR : ∀ q ∈ Icc s t, ∀ z ∈ Kset, ‖A q z‖ ≤ R)
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) →
      (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q z,
      satisfiesNullEigenvectorCondition (reaction q z))
    {Klip : NNReal}
    (hreactionLip : ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
      LipschitzOnWith Klip (reaction q z)
        {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    (hdirichlet : HasLocalScalarDirichletSolution
      (I := I) G T X s t Kset)
    (hGconn : ∀ q ∈ Ioc s t,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
      DifferentiableAt ℝ (fun r ↦ A r z) q)
    (hevolution : ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
      deriv (fun r ↦ A r z) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z)) :
    0 < (hAsymm t y).lowerKyFanSum k := by
  let phi : M → ℝ := fun z ↦ (hAsymm s z).lowerKyFanSum k
  have hsIcc : s ∈ Icc s t := ⟨le_rfl, hst.le⟩
  have hphiWithin : ContinuousWithinAt phi Kset x := by
    exact (hphiCont (s, x) ⟨hsIcc, interior_subset hxKset⟩).comp
      (continuousAt_const.prodMk continuousAt_id).continuousWithinAt
      (fun z hz ↦ ⟨hsIcc, hz⟩)
  have hKsetNhd : Kset ∈ 𝓝 x :=
    mem_of_superset (isOpen_interior.mem_nhds hxKset) interior_subset
  have hphiAt : ContinuousAt phi x := hphiWithin.continuousAt hKsetNhd
  have hphiNonneg : ∀ z ∈ Kset, 0 ≤ phi z := by
    intro z hz
    exact LinearMap.IsSymmetric.lowerKyFanSum_nonneg
      ((ContinuousLinearMap.isPositive_toLinearMap_iff (A s z)).mpr
        (hApos s hsIcc z hz)) k
  obtain ⟨f₀, hf₀Smooth, hf₀Nonneg, hf₀Compact, hf₀Support,
      hf₀x, hf₀Le⟩ :=
    exists_smooth_bump_mul_le_of_pos_on (I := I) (K := Kset)
      hphiAt hphiNonneg hsource
      (isOpen_interior.mem_nhds hxKset) hkpos
  let c : ℝ := (Klip : ℝ) + 1
  have hcNonneg : 0 ≤ c := by
    dsimp only [c]
    positivity
  obtain ⟨f, hfCont, hfInitialEq, hfBoundary, hfPos, hfTime,
      hfSpace, hfGrad, hfEquation⟩ :=
    HasLocalScalarDirichletSolution.exists_solution hdirichlet hcNonneg
      hf₀Smooth hf₀Nonneg hf₀Compact hf₀Support ⟨x, hxKset, hf₀x⟩
  have hc : (Klip : ℝ) < c := by
    dsimp only [c]
    linarith
  have hfInitial : ∀ z ∈ Kset,
      (k : ℝ) * f s z ≤ (hAsymm s z).lowerKyFanSum k := by
    intro z hz
    rw [hfInitialEq z hz]
    exact hf₀Le z hz
  exact lowerKyFanSum_pos_on_compact_set_of_dirichlet_solution
    (I := I) G cov hcov hT hs ht hkpos hk hKset hKsetInterior
      A hAsymm hApos hphiCont hR X reaction hreactionNull hreactionLip
      f hfCont hfInitial hfBoundary hfPos hfTime hfSpace hfGrad hc
      hfEquation hGconn hAt hevolution t ⟨hst, le_rfl⟩ y hyKset

theorem finrank_range_le_at_of_local_dirichlet_solution_exists
    [VectorBundle ℝ EModel (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ z, FiniteDimensional ℝ (V z)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    {Kset : Set M} (hKset : IsCompact Kset)
    (hKsetInterior : interior Kset ⊆ I.interior M)
    {x y : M} (hxKset : x ∈ interior Kset) (hyKset : y ∈ interior Kset)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAsymm : ∀ q z,
      ((A q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric)
    (hApos : ∀ q ∈ Icc s t, ∀ z ∈ Kset, (A q z).IsPositive)
    (hphiCont : ∀ k, k ≤ Module.finrank ℝ F →
      ContinuousOn (fun p : ℝ × M ↦
        (hAsymm p.1 p.2).lowerKyFanSum k) (Icc s t ×ˢ Kset))
    {R : ℝ} (hR : ∀ q ∈ Icc s t, ∀ z ∈ Kset, ‖A q z‖ ≤ R)
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) →
      (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q z,
      satisfiesNullEigenvectorCondition (reaction q z))
    {Klip : NNReal}
    (hreactionLip : ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
      LipschitzOnWith Klip (reaction q z)
        {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    (hdirichlet : HasLocalScalarDirichletSolution
      (I := I) G T X s t Kset)
    (hGconn : ∀ q ∈ Ioc s t,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
      DifferentiableAt ℝ (fun r ↦ A r z) q)
    (hevolution : ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
      deriv (fun r ↦ A r z) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z)) :
    Module.finrank ℝ (A s x).range ≤ Module.finrank ℝ (A t y).range := by
  have hsIcc : s ∈ Icc s t := ⟨le_rfl, hst.le⟩
  have htIcc : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  let ex := (trivializationAt F V x).linearEquivAt ℝ x
    (mem_baseSet_trivializationAt F V x)
  let ey := (trivializationAt F V y).linearEquivAt ℝ y
    (mem_baseSet_trivializationAt F V y)
  have hfinrank : Module.finrank ℝ (V x) = Module.finrank ℝ (V y) :=
    ex.finrank_eq.trans ey.finrank_eq.symm
  apply finrank_range_le_of_lowerKyFanSum_pos_spreading_of_finrank_eq
    (hApos s hsIcc x (interior_subset hxKset))
    (hApos t htIcc y (interior_subset hyKset)) hfinrank
  intro k hkpos hkx hsource
  have hkF : k ≤ Module.finrank ℝ F := by
    rw [← ex.finrank_eq]
    exact hkx
  exact lowerKyFanSum_pos_at_of_local_dirichlet_solution_exists
    (I := I) G cov hcov hT hs hst ht hkpos hkF hKset hKsetInterior
      hxKset hyKset A hAsymm hApos (hphiCont k hkF) hsource hR X
      reaction hreactionNull hreactionLip hdirichlet hGconn hAt hevolution

theorem finrank_range_le_of_local_dirichlet_solution_exists
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ EModel (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ z, FiniteDimensional ℝ (V z)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAsymm : ∀ q z,
      ((A q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric)
    (hApos : ∀ q ∈ Icc 0 T, ∀ z, (A q z).IsPositive)
    (hphiCont : ∀ k, k ≤ Module.finrank ℝ F →
      ContinuousOn (fun p : ℝ × M ↦
        (hAsymm p.1 p.2).lowerKyFanSum k)
        (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hA_bound : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset →
        ∃ R, ∀ q ∈ Icc s t, ∀ z ∈ Kset, ‖A q z‖ ≤ R)
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) →
      (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R,
        ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
          LipschitzOnWith Klip (reaction q z)
            {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    (hdirichlet : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset →
        IsConnected (interior Kset) →
        HasLocalScalarDirichletSolution (I := I) G T X s t Kset)
    (hGconn : ∀ q ∈ Ioc 0 T,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioc 0 T, ∀ z,
      DifferentiableAt ℝ (fun r ↦ A r z) q)
    (hevolution : ∀ q ∈ Ioc 0 T, ∀ z,
      deriv (fun r ↦ A r z) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (x y : M) :
    Module.finrank ℝ (A s x).range ≤ Module.finrank ℝ (A t y).range := by
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace H M
  obtain ⟨U, hU, hUconn, hxU, hyU, hcompact⟩ :=
    DifferentialGeometry.exists_isOpen_isConnected_isCompact_closure x y
  let Kset := closure U
  have hKsetConn : IsPreconnected (interior Kset) :=
    hUconn.isPreconnected.subset_closure hU.subset_interior_closure interior_subset
  have hxKset : x ∈ interior Kset :=
    (interior_maximal subset_closure hU) hxU
  have hyKset : y ∈ interior Kset :=
    (interior_maximal subset_closure hU) hyU
  have hKsetInterior : interior Kset ⊆ I.interior M := by
    rw [I.interior_eq_univ]
    exact subset_univ _
  obtain ⟨R, hR⟩ := hA_bound hs hst ht hcompact
  obtain ⟨Klip, hKlip⟩ := hreactionLip hs hst ht hcompact R
  have hApos' : ∀ q ∈ Icc s t, ∀ z ∈ Kset, (A q z).IsPositive := by
    intro q hq z hz
    exact hApos q ⟨hs.trans hq.1, hq.2.trans ht⟩ z
  have hphiCont' : ∀ k, k ≤ Module.finrank ℝ F →
      ContinuousOn (fun p : ℝ × M ↦
        (hAsymm p.1 p.2).lowerKyFanSum k) (Icc s t ×ˢ Kset) := by
    intro k hk
    exact (hphiCont k hk).mono fun p hp ↦
      ⟨⟨hs.trans hp.1.1, hp.1.2.trans ht⟩, Set.mem_univ p.2⟩
  have hGconn' : ∀ q ∈ Ioc s t,
      G.connection q = LeviCivita (I := I) (G.metric q) := by
    intro q hq
    exact hGconn q ⟨hs.trans_lt hq.1, hq.2.trans ht⟩
  have hAt' : ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
      DifferentiableAt ℝ (fun r ↦ A r z) q := by
    intro q hq z hz
    exact hAt q ⟨hs.trans_lt hq.1, hq.2.trans ht⟩ z
  have hevolution' : ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
      deriv (fun r ↦ A r z) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z) := by
    intro q hq z hz
    exact hevolution q ⟨hs.trans_lt hq.1, hq.2.trans ht⟩ z
  exact finrank_range_le_at_of_local_dirichlet_solution_exists
    (I := I) (G := G) (cov := cov) (T := T) (s := s) (t := t)
    (Kset := Kset) (x := x) (y := y) (A := A) (R := R)
    (X := X) (reaction := reaction) (Klip := Klip)
    hcov hT hs hst ht hcompact hKsetInterior hxKset hyKset
    hAsymm hApos' hphiCont' hR hreactionNull hKlip
    (hdirichlet hs hst ht hcompact ⟨⟨x, hxKset⟩, hKsetConn⟩) hGconn' hAt' hevolution'

theorem finrank_range_spatially_constant_and_locally_constant_of_local_dirichlet_solution_exists
    [I.Boundaryless] [ConnectedSpace M] [Nonempty M]
    [VectorBundle ℝ EModel (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ z, FiniteDimensional ℝ (V z)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAsymm : ∀ q z,
      ((A q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric)
    (hApos : ∀ q ∈ Icc 0 T, ∀ z, (A q z).IsPositive)
    (hphiCont : ∀ k, k ≤ Module.finrank ℝ F →
      ContinuousOn (fun p : ℝ × M ↦
        (hAsymm p.1 p.2).lowerKyFanSum k)
        (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hA_bound : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset →
        ∃ R, ∀ q ∈ Icc s t, ∀ z ∈ Kset, ‖A q z‖ ≤ R)
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) →
      (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R,
        ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
          LipschitzOnWith Klip (reaction q z)
            {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    (hdirichlet : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset →
        IsConnected (interior Kset) →
        HasLocalScalarDirichletSolution (I := I) G T X s t Kset)
    (hGconn : ∀ q ∈ Ioc 0 T,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioc 0 T, ∀ z,
      DifferentiableAt ℝ (fun r ↦ A r z) q)
    (hevolution : ∀ q ∈ Ioc 0 T, ∀ z,
      deriv (fun r ↦ A r z) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z)) :
    (∀ t ∈ Ioc 0 T, ∀ x y,
      Module.finrank ℝ (A t x).range =
        Module.finrank ℝ (A t y).range) ∧
      (∀ x, MonotoneOn
        (fun t ↦ Module.finrank ℝ (A t x).range) (Ioc 0 T)) ∧
      (∀ t ∈ Ioc 0 T, ∀ x,
        ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t,
          Module.finrank ℝ (A s x).range =
            Module.finrank ℝ (A t x).range) ∧
      ∃ δ ∈ Ioc 0 T, ∃ q : Nat, ∀ t ∈ Ioc 0 δ, ∀ x,
        Module.finrank ℝ (A t x).range = q := by
  have hspread : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      Module.finrank ℝ (A s x).range ≤
        Module.finrank ℝ (A t y).range := by
    intro s t hs hst ht x y
    exact finrank_range_le_of_local_dirichlet_solution_exists
      (I := I) G cov hcov hT A hAsymm hApos hphiCont hA_bound
      X reaction hreactionNull hreactionLip hdirichlet hGconn hAt
      hevolution hs hst ht x y
  apply rank_spatially_constant_and_locally_constant_from_left_of_spreading
    (rank := fun t x ↦ Module.finrank ℝ (A t x).range) hT
  · intro t ht x
    exact (ContinuousAt.eventually_finrank_range_ge
      (hAt t ht x).continuousAt).filter_mono inf_le_left
  · intro s t hs hst ht x y
    exact hspread hs hst ht x y

theorem exists_pos_le_lowerKyFanSum_on_time_interval
    [I.Boundaryless]
    [VectorBundle ℝ EModel (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ z, FiniteDimensional ℝ (V z)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T)
    {k : ℕ} (hkpos : 0 < k) (hk : k ≤ Module.finrank ℝ F)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAsymm : ∀ q z,
      ((A q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric)
    (hApos : ∀ q ∈ Icc 0 T, ∀ z, (A q z).IsPositive)
    (hphiCont : ContinuousOn (fun p : ℝ × M ↦
        (hAsymm p.1 p.2).lowerKyFanSum k)
        (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hA_bound : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset →
        ∃ R, ∀ q ∈ Icc s t, ∀ z ∈ Kset, ‖A q z‖ ≤ R)
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) →
      (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R,
        ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ z ∈ Kset,
          LipschitzOnWith Klip (reaction q z)
            {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    (hgrad : ∀ (rho : M → ℝ), ContMDiff I 𝓘(ℝ, ℝ) ∞ rho →
      ContinuousOn (fun p : ℝ × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hheat : ∀ (rho : M → ℝ), ContMDiff I 𝓘(ℝ, ℝ) ∞ rho →
      ContinuousOn (fun p : ℝ × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hGconn : ∀ q ∈ Ioo 0 T,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioo 0 T, ∀ z,
      DifferentiableAt ℝ (fun r ↦ A r z) q)
    (hevolution : ∀ q ∈ Ioo 0 T, ∀ z,
      deriv (fun r ↦ A r z) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (x : M) (hsource : 0 < (hAsymm s x).lowerKyFanSum k) :
    ∃ η : ℝ, 0 < η ∧ ∀ q ∈ Icc s t, η ≤ (hAsymm q x).lowerKyFanSum k := by
  let phi : ℝ → M → ℝ := fun q z => (hAsymm q z).lowerKyFanSum k
  have hsT : s ∈ Icc 0 T := ⟨hs, hst.le.trans ht⟩
  have hphiAt : ContinuousAt (phi s) x := by
    have hcont := hphiCont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun z (_ : z ∈ (Set.univ : Set M)) => ⟨hsT, Set.mem_univ z⟩)
    exact (continuousOn_univ.mp hcont).continuousAt
  obtain ⟨U, hUopen, hxU, hUcompact, -, -⟩ :=
    SmoothBumpFunction.exists_annulus_neighborhood (I := I) x
      (show (Set.univ : Set M) ∈ 𝓝 x from univ_mem)
  let Kset : Set M := closure U
  have hxKset : x ∈ interior Kset := hUopen.subset_interior_closure hxU
  let W : Set M := U ∩ (phi s) ⁻¹' Ioi (phi s x / 2)
  have hW : W ∈ 𝓝 x :=
    inter_mem (hUopen.mem_nhds hxU)
      (hphiAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds (half_lt_self hsource)))
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hkpos
  let epsilon : ℝ := phi s x / (2 * (k : ℝ))
  have hepsilon : 0 < epsilon := div_pos hsource (mul_pos (by norm_num) hkReal)
  have hkepsilon : (k : ℝ) * epsilon = phi s x / 2 := by
    dsimp only [epsilon]
    field_simp
  obtain ⟨b, C, hb, hbx, hbeps, hbW, hC, hbheat⟩ :=
    exists_spatial_barrier_positive_at (I := I) G hT X hgrad hheat hW hepsilon
  obtain ⟨R, hR⟩ := hA_bound hs hst ht hUcompact
  obtain ⟨Klip, hKlip⟩ := hreactionLip hs hst ht hUcompact R
  let c : ℝ := (Klip : ℝ) + 1
  have hc : (Klip : ℝ) < c := by dsimp only [c]; linarith
  let f : ℝ → M → ℝ := fun q z => Real.exp (-(c + C) * (q - s)) * b z
  have hfSmooth : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) := by
    exact ((Real.contDiff_exp.contMDiff.comp
      (contMDiff_const.mul (contMDiff_fst.sub contMDiff_const))).mul
      (hb.comp contMDiff_snd))
  have hApos' : ∀ q ∈ Icc s t, ∀ z ∈ Kset, (A q z).IsPositive := by
    intro q hq z _
    exact hApos q ⟨hs.trans hq.1, hq.2.trans ht⟩ z
  have hphiNonneg : ∀ q ∈ Icc s t, ∀ z ∈ Kset, 0 ≤ phi q z := by
    intro q hq z hz
    exact LinearMap.IsSymmetric.lowerKyFanSum_nonneg
      ((ContinuousLinearMap.isPositive_toLinearMap_iff (A q z)).mpr
        (hApos' q hq z hz)) k
  have hfInitial : ∀ z ∈ Kset, (k : ℝ) * f s z ≤ phi s z := by
    intro z hz
    simp only [f, sub_self, mul_zero, Real.exp_zero, one_mul]
    by_cases hbz : 0 < b z
    · have hzW := hbW z hbz
      have hkb : (k : ℝ) * b z < phi s x / 2 := by
        rw [← hkepsilon]
        exact mul_lt_mul_of_pos_left (hbeps z) hkReal
      exact (hkb.trans hzW.2).le
    · exact (mul_nonpos_of_nonneg_of_nonpos hkReal.le (le_of_not_gt hbz)).trans
        (hphiNonneg s ⟨le_rfl, hst.le⟩ z hz)
  have hfBoundary : ∀ q ∈ Icc s t, ∀ z ∈ frontier Kset,
      (k : ℝ) * f q z ≤ phi q z := by
    intro q hq z hz
    have hzKset : z ∈ Kset := by
      simpa only [Kset, closure_closure] using frontier_subset_closure hz
    have hbz : b z ≤ 0 := by
      by_contra hneg
      have hzU := (hbW z (lt_of_not_ge hneg)).1
      exact hz.2 (hUopen.subset_interior_closure hzU)
    exact (mul_nonpos_of_nonneg_of_nonpos hkReal.le
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hbz)).trans
      (hphiNonneg q hq z hzKset)
  have hfSlice (q : ℝ) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (f q) :=
    contMDiff_const.mul hb
  have hfSubsolution : ∀ q ∈ Ioo s t, ∀ z ∈ interior Kset, 0 < f q z →
      parabolicOperatorWithDrift (I := I) G T X f q z ≤ -c * f q z := by
    intro q hq z _ hfqz
    have hqT : q ∈ Icc 0 T := ⟨(hs.trans_lt hq.1).le, hq.2.le.trans ht⟩
    have huniq := (uniqueDiffOn_Icc hT).uniqueDiffWithinAt hqT
    have hbz : 0 < b z := (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hfqz
    have hderiv : HasDerivAt (fun r => f r z) (-(c + C) * f q z) q := by
      have hd : HasDerivAt (fun r : ℝ => Real.exp (-(c + C) * (r - s)) * b z)
          (Real.exp (-(c + C) * (q - s)) * (-(c + C)) * b z) q := by
        simpa only [id_eq, mul_one] using
          ((((hasDerivAt_id q).sub_const s).const_mul (-(c + C))).exp.mul_const (b z))
      exact hd.congr_deriv (by dsimp only [f]; ring)
    have hheatEq : heatOperatorWithDrift (I := I) G q (X q) (f q) z =
        Real.exp (-(c + C) * (q - s)) *
          heatOperatorWithDrift (I := I) G q (X q) b z :=
      heatOperatorWithDrift_const_smul (I := I) G q (X q) _
        (fun w => hb.mdifferentiable (by simp) w)
        (gradientFun_mdiffAt (I := I) (G.metric q) hb z)
    unfold parabolicOperatorWithDrift
    rw [hderiv.hasDerivWithinAt.derivWithin huniq, hheatEq]
    have hbound := mul_le_mul_of_nonneg_left (hbheat q hqT z hbz)
      (Real.exp_pos (-(c + C) * (q - s))).le
    dsimp only [f] at hbound ⊢
    nlinarith
  have hKsetInterior : interior Kset ⊆ I.interior M := by
    rw [I.interior_eq_univ]
    exact subset_univ _
  have hcompare := mul_le_lowerKyFanSum_on_compact_set_of_subsolution_on_Ioo
    (I := I) G cov hcov hT hs ht hkpos hk hUcompact hKsetInterior
    A hAsymm hApos'
    (hphiCont.mono fun p hp =>
      ⟨⟨hs.trans hp.1.1, hp.1.2.trans ht⟩, Set.mem_univ p.2⟩)
    hR X reaction hreactionNull
    (fun q hq z hz => hKlip q ⟨hq.1, hq.2.le⟩ z (interior_subset hz))
    f hfSmooth.continuous.continuousOn hfInitial hfBoundary
    (fun q _ z _ => by dsimp only [f]; fun_prop)
    (fun q _ z _ => (hfSlice q).mdifferentiable (by simp) z)
    (fun q _ z _ => gradientFun_mdiffAt (I := I) (G.metric q) (hfSlice q) z)
    hc hfSubsolution
    (fun q hq => hGconn q ⟨hs.trans_lt hq.1, hq.2.trans_le ht⟩)
    (fun q hq z _ => hAt q ⟨hs.trans_lt hq.1, hq.2.trans_le ht⟩ z)
    (fun q hq z _ => hevolution q ⟨hs.trans_lt hq.1, hq.2.trans_le ht⟩ z)
  let η : ℝ := (k : ℝ) * (Real.exp (-(c + C) * (t - s)) * b x)
  refine ⟨η, mul_pos hkReal (mul_pos (Real.exp_pos _) hbx), ?_⟩
  intro q hq
  have hcc : 0 ≤ c + C := by dsimp only [c]; positivity
  have hexp : Real.exp (-(c + C) * (t - s)) ≤
      Real.exp (-(c + C) * (q - s)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hq.2]
  have hle : η ≤ (k : ℝ) * f q x := by
    dsimp only [η, f]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hexp hbx.le) hkReal.le
  exact hle.trans (hcompare q hq x (interior_subset hxKset))

theorem lowerKyFanSum_pos_at_later_time_of_interior_evolution
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ EModel (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ z, FiniteDimensional ℝ (V z)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T)
    {k : ℕ} (hkpos : 0 < k) (hk : k ≤ Module.finrank ℝ F)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAsymm : ∀ q z,
      ((A q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric)
    (hApos : ∀ q ∈ Icc 0 T, ∀ z, (A q z).IsPositive)
    (hphiCont : ContinuousOn (fun p : ℝ × M ↦
        (hAsymm p.1 p.2).lowerKyFanSum k)
        (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hA_bound : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset →
        ∃ R, ∀ q ∈ Icc s t, ∀ z ∈ Kset, ‖A q z‖ ≤ R)
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) →
      (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R,
        ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ z ∈ Kset,
          LipschitzOnWith Klip (reaction q z)
            {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    (hgrad : ∀ (rho : M → ℝ), ContMDiff I 𝓘(ℝ, ℝ) ∞ rho →
      ContinuousOn (fun p : ℝ × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hheat : ∀ (rho : M → ℝ), ContMDiff I 𝓘(ℝ, ℝ) ∞ rho →
      ContinuousOn (fun p : ℝ × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hGconn : ∀ q ∈ Ioo 0 T,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioo 0 T, ∀ z,
      DifferentiableAt ℝ (fun r ↦ A r z) q)
    (hevolution : ∀ q ∈ Ioo 0 T, ∀ z,
      deriv (fun r ↦ A r z) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (x y : M) (hsource : 0 < (hAsymm s x).lowerKyFanSum k) :
    0 < (hAsymm t y).lowerKyFanSum k := by
  let u : ℝ := (s + t) / 2
  have hsu : s < u := by dsimp [u]; linarith
  have hut : u < t := by dsimp [u]; linarith
  have huT : u < T := hut.trans_le ht
  obtain ⟨η, hη, hηbound⟩ := exists_pos_le_lowerKyFanSum_on_time_interval
    G cov hcov hT hkpos hk A hAsymm hApos hphiCont hA_bound X reaction hreactionNull
    hreactionLip hgrad hheat hGconn hAt hevolution hs hsu huT.le x hsource
  have hxu : 0 < (hAsymm u x).lowerKyFanSum k :=
    hη.trans_le (hηbound u ⟨hsu.le, le_rfl⟩)
  have hyu : 0 < (hAsymm u y).lowerKyFanSum k := by
    exact lowerKyFanSum_pos_on_preconnected_open_set (I := I) G cov hcov hs hsu huT.le
      isOpen_univ (by rw [I.interior_eq_univ]) isPreconnected_univ hkpos hk A hAsymm
      (fun q hq z _ => hApos q ⟨hs.trans hq.1, hq.2.trans huT.le⟩ z)
      (hphiCont.mono fun p hp => ⟨⟨hs.trans hp.1.1, hp.1.2.trans huT.le⟩, hp.2⟩)
      (fun hK _ => hA_bound hs hsu huT.le hK) X reaction hreactionNull
      (fun hK _ B => hreactionLip hs hsu huT.le hK B)
      (fun rho hrho => (hgrad rho hrho).mono fun p hp =>
        ⟨⟨hs.trans hp.1.1, hp.1.2.trans huT.le⟩, hp.2⟩)
      (fun rho hrho => (hheat rho hrho).mono fun p hp =>
        ⟨⟨hs.trans hp.1.1, hp.1.2.trans huT.le⟩, hp.2⟩)
      (fun q hq => hGconn q ⟨hs.trans_lt hq.1, hq.2.trans_lt huT⟩)
      (fun q hq z _ => hAt q ⟨hs.trans_lt hq.1, hq.2.trans_lt huT⟩ z)
      (fun q hq z _ => hevolution q ⟨hs.trans_lt hq.1, hq.2.trans_lt huT⟩ z)
      (Set.mem_univ x) hxu y (Set.mem_univ y)
  obtain ⟨δ, hδ, hδbound⟩ := exists_pos_le_lowerKyFanSum_on_time_interval
    G cov hcov hT hkpos hk A hAsymm hApos hphiCont hA_bound X reaction hreactionNull
    hreactionLip hgrad hheat hGconn hAt hevolution (hs.trans hsu.le) hut ht y hyu
  exact hδ.trans_le (hδbound t ⟨hut.le, le_rfl⟩)

theorem finrank_range_le_at_later_time_of_interior_evolution
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ EModel (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ z, FiniteDimensional ℝ (V z)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAsymm : ∀ q z,
      ((A q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric)
    (hApos : ∀ q ∈ Icc 0 T, ∀ z, (A q z).IsPositive)
    (hphiCont : ∀ k, k ≤ Module.finrank ℝ F →
      ContinuousOn (fun p : ℝ × M ↦
        (hAsymm p.1 p.2).lowerKyFanSum k)
        (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hA_bound : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset →
        ∃ R, ∀ q ∈ Icc s t, ∀ z ∈ Kset, ‖A q z‖ ≤ R)
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) →
      (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R,
        ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ z ∈ Kset,
          LipschitzOnWith Klip (reaction q z)
            {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    (hgrad : ∀ (rho : M → ℝ), ContMDiff I 𝓘(ℝ, ℝ) ∞ rho →
      ContinuousOn (fun p : ℝ × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hheat : ∀ (rho : M → ℝ), ContMDiff I 𝓘(ℝ, ℝ) ∞ rho →
      ContinuousOn (fun p : ℝ × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hGconn : ∀ q ∈ Ioo 0 T,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioo 0 T, ∀ z,
      DifferentiableAt ℝ (fun r ↦ A r z) q)
    (hevolution : ∀ q ∈ Ioo 0 T, ∀ z,
      deriv (fun r ↦ A r z) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (x y : M) :
    Module.finrank ℝ (A s x).range ≤ Module.finrank ℝ (A t y).range := by
  let ex := (trivializationAt F V x).linearEquivAt ℝ x
    (mem_baseSet_trivializationAt F V x)
  let ey := (trivializationAt F V y).linearEquivAt ℝ y
    (mem_baseSet_trivializationAt F V y)
  have hfinrank : Module.finrank ℝ (V x) = Module.finrank ℝ (V y) :=
    ex.finrank_eq.trans ey.finrank_eq.symm
  apply finrank_range_le_of_lowerKyFanSum_pos_spreading_of_finrank_eq
    (hApos s ⟨hs, hst.le.trans ht⟩ x)
    (hApos t ⟨hs.trans hst.le, ht⟩ y) hfinrank
  intro k hkpos hkx hsource
  have hkF : k ≤ Module.finrank ℝ F := by
    rw [← ex.finrank_eq]
    exact hkx
  exact lowerKyFanSum_pos_at_later_time_of_interior_evolution
    (I := I) G cov hcov hT hkpos hkF A hAsymm hApos (hphiCont k hkF)
    hA_bound X reaction hreactionNull hreactionLip hgrad hheat hGconn hAt
    hevolution hs hst ht x y hsource


theorem lowerKyFanSum_pos_at_later_time_of_metricFamilySmoothOn
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ EModel (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ z, FiniteDimensional ℝ (V z)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T)
    {k : ℕ} (hkpos : 0 < k) (hk : k ≤ Module.finrank ℝ F)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAsymm : ∀ q z,
      ((A q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric)
    (hApos : ∀ q ∈ Icc 0 T, ∀ z, (A q z).IsPositive)
    (hphiCont : ContinuousOn (fun p : ℝ × M ↦
        (hAsymm p.1 p.2).lowerKyFanSum k)
        (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hA_bound : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset →
        ∃ R, ∀ q ∈ Icc s t, ∀ z ∈ Kset, ‖A q z‖ ≤ R)
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) →
      (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R,
        ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ z ∈ Kset,
          LipschitzOnWith Klip (reaction q z)
            {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hreg : Icc 0 T ⊆ D.regular)
    (hX : ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' EModel p.2 (X p.1 p.2) : TangentBundle I M))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hGconnClosed : ∀ q ∈ Icc 0 T,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioc 0 T, ∀ z,
      DifferentiableAt ℝ (fun r ↦ A r z) q)
    (hevolution : ∀ q ∈ Ioc 0 T, ∀ z,
      deriv (fun r ↦ A r z) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (x y : M) (hsource : 0 < (hAsymm s x).lowerKyFanSum k) :
    0 < (hAsymm t y).lowerKyFanSum k := by
  exact lowerKyFanSum_pos_at_later_time_of_interior_evolution
    G cov hcov hT hkpos hk A hAsymm hApos hphiCont hA_bound X reaction
    hreactionNull hreactionLip
    (fun rho hrho => G.gradient_norm_sq_continuousOn hG hreg hrho)
    (fun rho hrho => G.heatOperatorWithDrift_continuousOn hG hreg
      (uniqueDiffOn_Icc hT) hGconnClosed X hrho
      (G.driftTerm_continuousOn hG hreg X hX hrho))
    (fun q hq => hGconnClosed q ⟨hq.1.le, hq.2.le⟩)
    (fun q hq => hAt q ⟨hq.1, hq.2.le⟩)
    (fun q hq => hevolution q ⟨hq.1, hq.2.le⟩) hs hst ht x y hsource

theorem finrank_range_le_at_later_time_of_metricFamilySmoothOn
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ EModel (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ z, FiniteDimensional ℝ (V z)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAsymm : ∀ q z,
      ((A q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric)
    (hApos : ∀ q ∈ Icc 0 T, ∀ z, (A q z).IsPositive)
    (hphiCont : ∀ k, k ≤ Module.finrank ℝ F →
      ContinuousOn (fun p : ℝ × M ↦
        (hAsymm p.1 p.2).lowerKyFanSum k)
        (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hA_bound : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset →
        ∃ R, ∀ q ∈ Icc s t, ∀ z ∈ Kset, ‖A q z‖ ≤ R)
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) →
      (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R,
        ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ z ∈ Kset,
          LipschitzOnWith Klip (reaction q z)
            {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hreg : Icc 0 T ⊆ D.regular)
    (hX : ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' EModel p.2 (X p.1 p.2) : TangentBundle I M))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hGconnClosed : ∀ q ∈ Icc 0 T,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioc 0 T, ∀ z,
      DifferentiableAt ℝ (fun r ↦ A r z) q)
    (hevolution : ∀ q ∈ Ioc 0 T, ∀ z,
      deriv (fun r ↦ A r z) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (x y : M) :
    Module.finrank ℝ (A s x).range ≤ Module.finrank ℝ (A t y).range := by
  let ex := (trivializationAt F V x).linearEquivAt ℝ x
    (mem_baseSet_trivializationAt F V x)
  let ey := (trivializationAt F V y).linearEquivAt ℝ y
    (mem_baseSet_trivializationAt F V y)
  have hfinrank : Module.finrank ℝ (V x) = Module.finrank ℝ (V y) :=
    ex.finrank_eq.trans ey.finrank_eq.symm
  apply finrank_range_le_of_lowerKyFanSum_pos_spreading_of_finrank_eq
    (hApos s ⟨hs, hst.le.trans ht⟩ x)
    (hApos t ⟨hs.trans hst.le, ht⟩ y) hfinrank
  intro k hkpos hkx hsource
  have hkF : k ≤ Module.finrank ℝ F := by
    rw [← ex.finrank_eq]
    exact hkx
  exact lowerKyFanSum_pos_at_later_time_of_metricFamilySmoothOn
    (I := I) G cov hcov hT hkpos hkF A hAsymm hApos (hphiCont k hkF)
    hA_bound X reaction hreactionNull hreactionLip hG hreg hX hGconnClosed hAt
    hevolution hs hst ht x y hsource

theorem finrank_range_spatially_constant_and_locally_constant_of_metricFamilySmoothOn
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ EModel (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ z, FiniteDimensional ℝ (V z)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAsymm : ∀ q z,
      ((A q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric)
    (hApos : ∀ q ∈ Icc 0 T, ∀ z, (A q z).IsPositive)
    (hphiCont : ∀ k, k ≤ Module.finrank ℝ F →
      ContinuousOn (fun p : ℝ × M ↦
        (hAsymm p.1 p.2).lowerKyFanSum k)
        (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hA_bound : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset →
        ∃ R, ∀ q ∈ Icc s t, ∀ z ∈ Kset, ‖A q z‖ ≤ R)
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) →
      (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R,
        ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ z ∈ Kset,
          LipschitzOnWith Klip (reaction q z)
            {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hreg : Icc 0 T ⊆ D.regular)
    (hX : ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' EModel p.2 (X p.1 p.2) : TangentBundle I M))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hGconnClosed : ∀ q ∈ Icc 0 T,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioc 0 T, ∀ z,
      DifferentiableAt ℝ (fun r ↦ A r z) q)
    (hevolution : ∀ q ∈ Ioc 0 T, ∀ z,
      deriv (fun r ↦ A r z) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z)) :
    (∀ t ∈ Ioc 0 T, ∀ x y,
      Module.finrank ℝ (A t x).range =
        Module.finrank ℝ (A t y).range) ∧
      (∀ x, MonotoneOn
        (fun t ↦ Module.finrank ℝ (A t x).range) (Ioc 0 T)) ∧
      (∀ t ∈ Ioc 0 T, ∀ x,
        ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t,
          Module.finrank ℝ (A s x).range =
            Module.finrank ℝ (A t x).range) ∧
      ∃ δ ∈ Ioc 0 T, ∃ q : Nat, ∀ t ∈ Ioc 0 δ, ∀ x,
        Module.finrank ℝ (A t x).range = q := by
  have hspread : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      Module.finrank ℝ (A s x).range ≤
        Module.finrank ℝ (A t y).range := by
    intro s t hs hst ht x y
    exact finrank_range_le_at_later_time_of_metricFamilySmoothOn
      (I := I) G cov hcov hT A hAsymm hApos hphiCont hA_bound
      X reaction hreactionNull hreactionLip hG hreg hX hGconnClosed hAt
      hevolution hs hst ht x y
  apply rank_spatially_constant_and_locally_constant_from_left_of_spreading
    (rank := fun t x ↦ Module.finrank ℝ (A t x).range) hT
  · intro t ht x
    exact (ContinuousAt.eventually_finrank_range_ge
      (hAt t ht x).continuousAt).filter_mono inf_le_left
  · intro s t hs hst ht x y
    exact hspread hs hst ht x y

end PositiveSystem
