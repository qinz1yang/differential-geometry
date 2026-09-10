import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

open Set Filter Topology

namespace Poincare.Topology.Compactness

theorem exists_injOn_prod_nhds
    {X Y Z : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Z]
    {f : X × Y → Z} {y₀ : Y}
    (hf : Continuous f) (hzero : Function.Injective (fun x ↦ f (x, y₀)))
    (hlocal : ∀ x, ∃ U ∈ 𝓝 (x, y₀), InjOn f U) :
    ∃ V ∈ 𝓝 y₀, InjOn f (univ ×ˢ V) := by
  let S : Set ((X × X) × (Y × Y)) :=
    {q | f (q.1.1, q.2.1) = f (q.1.2, q.2.2) → (q.1.1, q.2.1) = (q.1.2, q.2.2)}
  have hS : S ∈ (𝓝ˢ (univ : Set (X × X))) ×ˢ 𝓝 (y₀, y₀) := by
    apply isCompact_univ.mem_nhdsSet_prod_of_forall
    intro p _
    rw [← nhds_prod_eq]
    by_cases hpp : p.1 = p.2
    · obtain ⟨U, hU, hinj⟩ := hlocal p.1
      have hleft : ∀ᶠ q in 𝓝 (p, (y₀, y₀)), (q.1.1, q.2.1) ∈ U :=
        ((continuousAt_fst.fst).prodMk (continuousAt_snd.fst)).preimage_mem_nhds hU
      have hright : ∀ᶠ q in 𝓝 (p, (y₀, y₀)), (q.1.2, q.2.2) ∈ U :=
        ((continuousAt_fst.snd).prodMk (continuousAt_snd.snd)).preimage_mem_nhds
          (by simpa only [hpp] using hU)
      filter_upwards [hleft, hright] with q hql hqr
      exact fun heq ↦ hinj hql hqr heq
    · have hne : f (p.1, y₀) ≠ f (p.2, y₀) := fun h ↦ hpp (hzero h)
      have hopen : IsOpen {q : (X × X) × (Y × Y) |
          f (q.1.1, q.2.1) ≠ f (q.1.2, q.2.2)} :=
        (isClosed_eq (hf.comp ((continuous_fst.fst).prodMk (continuous_snd.fst)))
          (hf.comp ((continuous_fst.snd).prodMk (continuous_snd.snd)))).isOpen_compl
      exact Filter.mem_of_superset (hopen.mem_nhds hne) (fun q hq heq ↦ (hq heq).elim)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_prod_iff.mp hS
  rw [nhds_prod_eq] at hB
  obtain ⟨V₁, hV₁, V₂, hV₂, hV⟩ := mem_prod_iff.mp hB
  refine ⟨V₁ ∩ V₂, inter_mem hV₁ hV₂, ?_⟩
  intro z hz w hw heq
  exact hAB (show ((z.1, w.1), (z.2, w.2)) ∈ A ×ˢ B from
    ⟨subset_of_mem_nhdsSet hA (mem_univ _), hV ⟨hz.2.1, hw.2.2⟩⟩) heq

set_option backward.isDefEq.respectTransparency false in
theorem exists_isClosedEmbedding_on_Icc
    {X Z : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Z] [T2Space Z]
    {ρ : ℝ} (hρ : 0 < ρ) {f : X × Icc (0 : ℝ) ρ → Z}
    (hf : Continuous f)
    (hzero : Function.Injective (fun x ↦ f (x, ⟨0, le_rfl, hρ.le⟩)))
    (hlocal : ∀ x, ∃ U ∈ 𝓝 (x, (⟨0, le_rfl, hρ.le⟩ : Icc (0 : ℝ) ρ)), InjOn f U) :
    ∃ ε > 0, ∃ hερ : ε < ρ,
      IsClosedEmbedding (fun z : X × Icc (0 : ℝ) ε ↦
        f (z.1, ⟨z.2.1, z.2.2.1, z.2.2.2.trans hερ.le⟩)) := by
  let t₀ : Icc (0 : ℝ) ρ := ⟨0, le_rfl, hρ.le⟩
  obtain ⟨V, hV, hinj⟩ := exists_injOn_prod_nhds hf hzero hlocal
  have hV' : V ∈ comap (Subtype.val : Icc (0 : ℝ) ρ → ℝ) (𝓝 0) := by
    simpa only [t₀, nhds_subtype_eq_comap] using hV
  obtain ⟨A, hA, hAV⟩ := mem_comap.mp hV'
  obtain ⟨δ, hδ, hδA⟩ := Metric.mem_nhds_iff.mp hA
  let ε := min (ρ / 2) (δ / 2)
  have hε : 0 < ε := lt_min (half_pos hρ) (half_pos hδ)
  have hερ : ε < ρ := (min_le_left _ _).trans_lt (half_lt_self hρ)
  let j : Icc (0 : ℝ) ε → Icc (0 : ℝ) ρ := fun r ↦
    ⟨r.1, r.2.1, r.2.2.trans hερ.le⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hjV : ∀ r, j r ∈ V := by
    intro r
    apply hAV
    apply hδA
    change dist r.1 0 < δ
    rw [Real.dist_eq, sub_zero, abs_of_nonneg r.2.1]
    exact (r.2.2.trans (min_le_right _ _)).trans_lt (half_lt_self hδ)
  refine ⟨ε, hε, hερ, ?_⟩
  apply (hf.comp (continuous_id.prodMap hj)).isClosedEmbedding
  intro z w heq
  have heq' : (z.1, j z.2) = (w.1, j w.2) :=
    hinj ⟨mem_univ _, hjV z.2⟩ ⟨mem_univ _, hjV w.2⟩ heq
  exact Prod.ext (Prod.mk.inj heq').1
    (Subtype.ext (congrArg (fun y : Icc (0 : ℝ) ρ ↦ y.1) (Prod.mk.inj heq').2))

end Poincare.Topology.Compactness
