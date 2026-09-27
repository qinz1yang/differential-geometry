import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter Function Topology
open scoped Topology

namespace DifferentialGeometry.Topology.Collar

variable {S C X : Type*} [TopologicalSpace S] [TopologicalSpace C]
  [TopologicalSpace X] [CompactSpace S]

theorem exists_pos_negative_half_collar_subset_compl
    {r w : ℝ} (hr : 0 < r) (hw : 0 < w)
    {k : C → X} (hk : IsClosedEmbedding k)
    {c : S × Ico (0 : ℝ) w → C} (hc : IsOpenMap c)
    {f : S × Ioo (-r) r → X} (hf : Continuous f) (hinj : Injective f)
    (hmatch : ∀ (s : S) (t : Ioo (-r) r) (ht : 0 ≤ t.val) (htw : t.val < w),
      f (s, t) = k (c (s, ⟨t.val, ht, htw⟩)))
    {T : Set X} (hT : IsClosed T)
    (hzero : ∀ s, f (s, ⟨0, neg_lt_zero.mpr hr, hr⟩) ∉ T) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧
      ∀ (s : S) (t : Ioo (-r) r), -ε < t.val → t.val < 0 →
        f (s, t) ∉ range k ∪ T := by
  let a := min r w / 2
  have hmin : 0 < min r w := lt_min hr hw
  have ha : 0 < a := half_pos hmin
  have har : a < r := (half_lt_self hmin).trans_le (min_le_left r w)
  let U : Set C := c '' {p | p.2.val < a}
  have hU : IsOpen U := hc _ (isOpen_lt
    (continuous_subtype_val.comp continuous_snd) continuous_const)
  let O : Set X := (k '' Uᶜ ∪ T)ᶜ
  have hO : IsOpen O := ((hk.isClosedMap _ hU.isClosed_compl).union hT).isOpen_compl
  let z : Ioo (-r) r := ⟨0, neg_lt_zero.mpr hr, hr⟩
  have hzeroO (s : S) : f (s, z) ∈ O := by
    rintro (⟨x, hx, hxk⟩ | hx)
    · have hxc : x = c (s, ⟨0, le_rfl, hw⟩) :=
        hk.injective (hxk.trans (hmatch s z le_rfl hw))
      apply hx
      rw [hxc]
      exact ⟨(s, ⟨0, le_rfl, hw⟩), ha, rfl⟩
    · exact hzero s hx
  have hprod : f ⁻¹' O ∈ nhdsSet (univ : Set S) ×ˢ nhds z :=
    isCompact_univ.mem_nhdsSet_prod_of_forall (fun s _ => by
      simpa only [nhds_prod_eq] using (hO.preimage hf).mem_nhds (hzeroO s))
  obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp hprod
  have hVall (s : S) : s ∈ V := by
    have hVu : V = univ := by simpa using hV
    simp [hVu]
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨min δ r, lt_min hδ hr, min_le_right _ _, ?_⟩
  intro s t ht htn
  have htd : dist t z < δ := by
    change dist t.val (0 : ℝ) < δ
    rw [Real.dist_eq, sub_zero, abs_of_neg htn]
    have he : min δ r ≤ δ := min_le_left _ _
    linarith
  have hfO : f (s, t) ∈ O := hVW ⟨hVall s, hδW htd⟩
  rintro (⟨x, hx⟩ | hx)
  · have hxU : x ∈ U := by
      by_contra hxU
      exact hfO (Or.inl ⟨x, hxU, hx⟩)
    obtain ⟨p, hp, hpc⟩ := hxU
    let q : Ioo (-r) r := ⟨p.2.val, (neg_lt_zero.mpr hr).trans_le p.2.property.1,
      hp.trans har⟩
    have hfp : f (p.1, q) = f (s, t) :=
      (hmatch p.1 q p.2.property.1 p.2.property.2).trans ((congrArg k hpc).trans hx)
    have hqt : p.2.val = t.val := congrArg (fun y : S × Ioo (-r) r => y.2.val)
      (hinj hfp)
    have htnonneg : 0 ≤ t.val := hqt ▸ p.2.property.1
    exact (not_lt_of_ge htnonneg htn).elim
  · exact hfO (Or.inr hx)

end DifferentialGeometry.Topology.Collar
