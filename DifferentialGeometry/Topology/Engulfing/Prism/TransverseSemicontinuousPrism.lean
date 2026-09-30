import DifferentialGeometry.Topology.Engulfing.Prism.SemicontinuousPrism
import DifferentialGeometry.Topology.Engulfing.Prism.TransversePrism

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Topology

theorem exists_transverse_semicontinuous_prism_engulfing {Y Z : Type*}
    [MetricSpace Y] [MetricSpace Z] (o : Y) {F : Set Z} (hF : IsClosed F)
    {l f g : F → ℝ} (hl : LowerSemicontinuous l) (hf : UpperSemicontinuous f)
    (hg : Continuous g) (hlf : ∀ z, l z ≤ f z) (_hfg : ∀ z, f z ≤ g z)
    (hboundary : ∀ z : F, z.1 ∈ frontier F → f z = g z)
    {U W : Set ((Y × Z) × ℝ)} (hU : IsOpen U) (hW : IsOpen W)
    (hbase : ∀ (z : F) t, t ∈ Icc (l z) (f z) → ((o, z.1), t) ∈ U)
    (hprism : ∀ (z : F) t, t ∈ Ioc (f z) (g z) → ((o, z.1), t) ∈ W) :
    ∃ H : ((Y × Z) × ℝ) ≃ₜ ((Y × Z) × ℝ),
      (∀ p, (H p).1 = p.1) ∧ (∀ p ∉ W, H p = p) ∧
      (∀ p, p.1.2 ∉ interior F → H p = p) ∧
      (∀ (z : F) t, t ≤ f z → H ((o, z.1), t) = ((o, z.1), t)) ∧
      ∀ (z : F) t, t ∈ Icc (l z) (g z) → ((o, z.1), t) ∈ H '' U := by
  let j₀ : F → Y × Z := fun z => (o, z.1)
  have hj₀ : IsClosedEmbedding j₀ := by
    refine ⟨(isEmbedding_prodMkRight o).comp IsEmbedding.subtypeVal, ?_⟩
    have hr : range j₀ = {o} ×ˢ F := by
      ext p
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨rfl, z.2⟩
      · rintro ⟨hy, hz⟩
        exact ⟨⟨p.2, hz⟩, Prod.ext hy.symm rfl⟩
    rw [hr]
    exact isClosed_singleton.prod hF
  let j : F × ℝ → (Y × Z) × ℝ := Prod.map j₀ id
  have hj : IsClosedEmbedding j := hj₀.prodMap IsClosedEmbedding.id
  obtain ⟨h, hh, hfh, hhU⟩ := exists_semicontinuous_prism_majorant hl hf hlf
    (hU.preimage hj.continuous) hbase
  obtain ⟨α, hα, hfαh⟩ := exists_continuous_between_strict hf hh.lowerSemicontinuous hfh
  obtain ⟨a, ha⟩ := ContinuousMap.exists_restrict_eq hF (⟨α, hα⟩ : C(F, ℝ))
  obtain ⟨b, hb⟩ := ContinuousMap.exists_restrict_eq hF (⟨g, hg⟩ : C(F, ℝ))
  have hae (z : F) : a z = α z := congrArg (fun k : C(F, ℝ) => k z) ha
  have hbe (z : F) : b z = g z := congrArg (fun k : C(F, ℝ) => k z) hb
  let C : Set Z := F ∩ {z | a z ≤ b z}
  have hC : IsClosed C := hF.inter (isClosed_le a.continuous b.continuous)
  have hCF : C ⊆ F := inter_subset_left
  let ι : C → F := fun z => ⟨z.1, z.2.1⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hmemC (z : F) : z.1 ∈ C ↔ α z ≤ g z := by
    change (z.1 ∈ F ∧ a z.1 ≤ b z.1) ↔ α z ≤ g z
    rw [hae z, hbe z]
    exact and_iff_right z.2
  have hfrontier (z : C) (hz : z.1 ∈ frontier C) : α (ι z) = g (ι z) := by
    have hle := (hmemC (ι z)).mp z.2
    apply le_antisymm hle
    by_contra hn
    have hlt : α (ι z) < g (ι z) := lt_of_not_ge hn
    have hzint : z.1 ∈ interior F := by
      by_contra hnot
      have hfg := hboundary (ι z) ⟨subset_closure z.2.1, hnot⟩
      have hfa := (hfαh (ι z)).1
      rw [hfg] at hfa
      exact (not_lt_of_ge hle) hfa
    apply hz.2
    have hsub : interior F ∩ {z | a z < b z} ⊆ C := fun z hz =>
      ⟨interior_subset hz.1, (show a z < b z from hz.2).le⟩
    apply interior_maximal hsub
      (isOpen_interior.inter (isOpen_lt a.continuous b.continuous))
    refine ⟨hzint, ?_⟩
    change a (ι z) < b (ι z)
    rwa [hae, hbe]
  let B₀ : Set ((Y × Z) × ℝ) := j '' {p | p.2 ≤ f p.1}
  let B₁ : Set ((Y × Z) × ℝ) := j '' {p | h p.1 ≤ p.2}
  have hB₀ : IsClosed B₀ := hj.isClosedMap _ hf.IsClosed_hypograph
  have hB₁ : IsClosed B₁ := hj.isClosedMap _ hh.lowerSemicontinuous.isClosed_epigraph
  have hB₀mem (z : F) (t : ℝ) : ((o, z.1), t) ∈ B₀ ↔ t ≤ f z := by
    change j (z, t) ∈ j '' {p | p.2 ≤ f p.1} ↔ (z, t) ∈ {p | p.2 ≤ f p.1}
    exact hj.injective.mem_set_image
  have hB₁mem (z : F) (t : ℝ) : ((o, z.1), t) ∈ B₁ ↔ h z ≤ t := by
    change j (z, t) ∈ j '' {p | h p.1 ≤ p.2} ↔ (z, t) ∈ {p | h p.1 ≤ p.2}
    exact hj.injective.mem_set_image
  obtain ⟨H, hHfst, hHfix, hHout, hHprism⟩ := exists_transverse_closed_prism_engulfing
    o hC (hα.comp hι) (hg.comp hι) (fun z => (hmemC (ι z)).mp z.2) hfrontier
    (hU.sdiff hB₁) (hW.sdiff hB₀)
    (fun z => ⟨hhU (ι z) (α (ι z)) ⟨(hlf (ι z)).trans (hfαh (ι z)).1.le,
      (hfαh (ι z)).2.le⟩, by
        rw [hB₁mem (ι z)]
        exact not_le_of_gt (hfαh (ι z)).2⟩)
    (fun z t ht => ⟨hprism (ι z) t ⟨(hfαh (ι z)).1.trans_le ht.1, ht.2⟩, by
      rw [hB₀mem (ι z)]
      exact not_le_of_gt ((hfαh (ι z)).1.trans_le ht.1)⟩)
  have hfix (z : F) (t : ℝ) (ht : t ≤ f z) : H ((o, z.1), t) = ((o, z.1), t) :=
    hHfix _ (fun hp => hp.2 ((hB₀mem z t).mpr ht))
  have hifst (p : (Y × Z) × ℝ) : (H.symm p).1 = p.1 :=
    (hHfst (H.symm p)).symm.trans (congrArg Prod.fst (H.apply_symm_apply p))
  have hifix (z : F) (t : ℝ) (ht : t ≤ f z) :
      H.symm ((o, z.1), t) = ((o, z.1), t) := by
    have he := congrArg H.symm (hfix z t ht)
    simpa only [H.symm_apply_apply] using he.symm
  refine ⟨H, hHfst, fun p hp => hHfix p (fun h => hp h.1), ?_, hfix, ?_⟩
  · intro p hp
    exact hHout p (fun hi => hp (interior_mono hCF hi))
  · intro z t ht
    by_cases hz : z.1 ∈ C
    · let c : C := ⟨z.1, hz⟩
      have hic : ι c = z := Subtype.ext rfl
      have htarget (t : ℝ) (ht : t ∈ Icc (α z) (g z)) :
          ((o, z.1), t) ∈ H '' (U \ B₁) := by
        apply hHprism c t
        simpa only [Function.comp_apply, hic] using ht
      by_cases hαt : α z ≤ t
      · exact image_mono sdiff_subset (htarget t ⟨hαt, ht.2⟩)
      by_cases htf : t ≤ f z
      · exact ⟨((o, z.1), t), hbase z t ⟨ht.1, htf⟩, hfix z t htf⟩
      have hmono := strictMono_homeomorph_fiber H.symm hifst (o, z.1)
        (a := f z - 1) (b := f z) (by linarith)
        (hifix z (f z - 1) (by linarith)) (hifix z (f z) le_rfl)
      obtain ⟨q, hq, hqeq⟩ := htarget (α z) ⟨le_rfl, (hmemC z).mp hz⟩
      have hqi : q = H.symm ((o, z.1), α z) := by
        simpa only [H.symm_apply_apply] using congrArg H.symm hqeq
      have hqfst : q.1 = (o, z.1) := by rw [hqi, hifst]
      have hqbound : q.2 < h z := by
        apply lt_of_not_ge
        intro hle
        apply hq.2
        have hp := (hB₁mem z q.2).mpr hle
        simpa only [← hqfst, Prod.mk.eta] using hp
      have hlower : f z ≤ (H.symm ((o, z.1), t)).2 := by
        have hm := hmono.monotone (le_of_not_ge htf)
        simpa only [hifix z (f z) le_rfl] using hm
      have hupper : (H.symm ((o, z.1), t)).2 ≤ h z := by
        have hm := hmono.monotone (le_of_not_ge hαt)
        rw [← hqi] at hm
        exact hm.trans hqbound.le
      refine ⟨H.symm ((o, z.1), t), ?_, H.apply_symm_apply _⟩
      have hp := hhU z (H.symm ((o, z.1), t)).2 ⟨(hlf z).trans hlower, hupper⟩
      change ((o, z.1), (H.symm ((o, z.1), t)).2) ∈ U at hp
      convert hp using 1
      exact Prod.ext (hifst _) rfl
    · have hga : g z < α z := lt_of_not_ge (fun h => hz ((hmemC z).mpr h))
      refine ⟨((o, z.1), t), hhU z t ⟨ht.1, ht.2.trans (hga.trans (hfαh z).2).le⟩, ?_⟩
      exact hHout _ (fun hi => hz (interior_subset hi))

theorem exists_transverse_semicontinuous_prism_engulfing_keeping {Y Z : Type*}
    [MetricSpace Y] [MetricSpace Z] (o : Y) {F : Set Z} (hF : IsClosed F)
    {l f g : F → ℝ} (hl : LowerSemicontinuous l) (hf : UpperSemicontinuous f)
    (hg : Continuous g) (hlf : ∀ z, l z ≤ f z) (hfg : ∀ z, f z ≤ g z)
    (hboundary : ∀ z : F, z.1 ∈ frontier F → f z = g z)
    {U W A : Set ((Y × Z) × ℝ)} (hU : IsOpen U) (hW : IsOpen W)
    (hA : IsClosed A) (hAU : A ⊆ U)
    (hbase : ∀ (z : F) t, t ∈ Icc (l z) (f z) → ((o, z.1), t) ∈ U)
    (hprism : ∀ (z : F) t, t ∈ Ioc (f z) (g z) → ((o, z.1), t) ∈ W)
    (havoid : ∀ (z : F) t, t ∈ Ioc (f z) (g z) → ((o, z.1), t) ∉ A) :
    ∃ H : ((Y × Z) × ℝ) ≃ₜ ((Y × Z) × ℝ),
      (∀ p, (H p).1 = p.1) ∧ (∀ p ∉ W, H p = p) ∧
      (∀ p ∈ A, H p = p) ∧ (∀ p, p.1.2 ∉ interior F → H p = p) ∧
      A ⊆ H '' U ∧
      ∀ (z : F) t, t ∈ Icc (l z) (g z) → ((o, z.1), t) ∈ H '' U := by
  obtain ⟨H, hHfst, hHfix, hHout, -, hHprism⟩ :=
    exists_transverse_semicontinuous_prism_engulfing o hF hl hf hg hlf hfg hboundary
      hU (hW.sdiff hA) hbase (fun z t ht => ⟨hprism z t ht, havoid z t ht⟩)
  have hHA (p) (hp : p ∈ A) : H p = p := hHfix p (fun h => h.2 hp)
  exact ⟨H, hHfst, fun p hp => hHfix p (fun h => hp h.1), hHA, hHout,
    fun p hp => ⟨p, hAU hp, hHA p hp⟩, hHprism⟩

end DifferentialGeometry.Topology.Engulfing
