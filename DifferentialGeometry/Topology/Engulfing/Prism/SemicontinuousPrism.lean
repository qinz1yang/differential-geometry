import DifferentialGeometry.Topology.Engulfing.Prism.Prism
import DifferentialGeometry.Topology.Order.SemicontinuousInsertion.WeakInsertion
import Mathlib.Topology.Order.IntermediateValue

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Topology Filter

theorem exists_semicontinuous_prism_majorant {X : Type*} [MetricSpace X]
    {l f : X → ℝ} (hl : LowerSemicontinuous l) (hf : UpperSemicontinuous f)
    (hlf : ∀ x, l x ≤ f x) {U : Set (X × ℝ)} (hU : IsOpen U)
    (hprism : ∀ x t, t ∈ Icc (l x) (f x) → (x, t) ∈ U) :
    ∃ h : X → ℝ, Continuous h ∧ (∀ x, f x < h x) ∧
      ∀ x t, t ∈ Icc (l x) (h x) → (x, t) ∈ U := by
  let S : X → Set ℝ := fun x => {y | f x < y ∧ ∀ t ∈ Icc (l x) y, (x, t) ∈ U}
  have hnonempty (x : X) : (S x).Nonempty := by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU (x, f x)
      (hprism x (f x) ⟨hlf x, le_rfl⟩)
    refine ⟨f x + ε / 2, ?_, ?_⟩
    · linarith
    intro t ht
    by_cases htf : t ≤ f x
    · exact hprism x t ⟨ht.1, htf⟩
    · apply hεU
      rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq,
        max_eq_right (abs_nonneg _), abs_of_nonneg (by linarith)]
      linarith [ht.2]
  have hconvex (x : X) : Convex ℝ (S x) := by
    apply Set.OrdConnected.convex
    constructor
    intro a ha b hb t ht
    exact ⟨ha.1.trans_le ht.1, fun u hu => hb.2 u ⟨hu.1, hu.2.trans ht.2⟩⟩
  have hsections : HasOpenLowerSections S := by
    rw [hasOpenLowerSections_iff_isOpen]
    intro y
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    change f x < y ∧ ∀ t ∈ Icc (l x) y, (x, t) ∈ U at hx
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU (x, l x)
      (hx.2 (l x) ⟨le_rfl, (hlf x).trans hx.1.le⟩)
    let a := l x - ε / 2
    have hay : a ≤ y := by dsimp [a]; linarith [hlf x, hx.1]
    have hinterval : ∀ t ∈ Icc a y, (x, t) ∈ U := by
      intro t ht
      by_cases hlt : l x ≤ t
      · exact hx.2 t ⟨hlt, ht.2⟩
      · apply hεU
        rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq,
          max_eq_right (abs_nonneg _), abs_of_nonpos (by linarith)]
        dsimp [a] at ht
        linarith [ht.1]
    have hn := (isOpen_prism_neighborhood (X := X) (f := fun _ => a)
      (g := fun _ => y) continuous_const continuous_const (fun _ => hay) hU).mem_nhds
      hinterval
    have hln := (hl.isOpen_preimage a).mem_nhds (show a < l x by dsimp [a]; linarith)
    have hfn := (hf.isOpen_preimage y).mem_nhds hx.1
    filter_upwards [hn, hln, hfn] with z hz hlz hfz
    exact ⟨hfz, fun t ht => hz t ⟨hlz.le.trans ht.1, ht.2⟩⟩
  obtain ⟨h, hh, hS⟩ := hsections.exists_continuous_selection hnonempty hconvex
  exact ⟨h, hh, fun x => (hS x).1, fun x => (hS x).2⟩

theorem strictMono_homeomorph_fiber {X : Type*} [TopologicalSpace X]
    (H : (X × ℝ) ≃ₜ (X × ℝ)) (hfst : ∀ p, (H p).1 = p.1) (x : X)
    {a b : ℝ} (hab : a < b) (ha : H (x, a) = (x, a)) (hb : H (x, b) = (x, b)) :
    StrictMono (fun t => (H (x, t)).2) := by
  have hc : Continuous (fun t : ℝ => (H (x, t)).2) :=
    continuous_snd.comp (H.continuous.comp (continuous_const.prodMk continuous_id))
  have hi : Function.Injective (fun t : ℝ => (H (x, t)).2) := by
    intro s t hst
    have he : H (x, s) = H (x, t) := Prod.ext (by rw [hfst, hfst]) hst
    exact congrArg Prod.snd (H.injective he)
  rcases hc.strictMono_of_inj hi with hm | hm
  · exact hm
  · have hlt := hm hab
    dsimp only at hlt
    rw [ha, hb] at hlt
    exact False.elim (not_lt_of_ge hab.le hlt)

theorem exists_semicontinuous_prism_engulfing {X : Type*} [MetricSpace X]
    {l f g : X → ℝ} (hl : LowerSemicontinuous l) (hf : UpperSemicontinuous f)
    (hg : Continuous g) (hlf : ∀ x, l x ≤ f x) (_hfg : ∀ x, f x ≤ g x)
    {U W : Set (X × ℝ)} (hU : IsOpen U) (hW : IsOpen W)
    (hbase : ∀ x t, t ∈ Icc (l x) (f x) → (x, t) ∈ U)
    (hprism : ∀ x t, t ∈ Ioc (f x) (g x) → (x, t) ∈ W) :
    ∃ H : (X × ℝ) ≃ₜ (X × ℝ),
      (∀ p, (H p).1 = p.1) ∧ (∀ p ∉ W, H p = p) ∧
      (∀ x t, t ≤ f x → H (x, t) = (x, t)) ∧
      (∀ x, f x = g x → ∀ t, H (x, t) = (x, t)) ∧
      ∀ x t, t ∈ Icc (l x) (g x) → (x, t) ∈ H '' U := by
  obtain ⟨h, hh, hfh, hhU⟩ := exists_semicontinuous_prism_majorant hl hf hlf hU hbase
  obtain ⟨α, hα, hfαh⟩ := exists_continuous_between_strict hf hh.lowerSemicontinuous hfh
  let F : Set X := {x | α x ≤ g x}
  have hF : IsClosed F := isClosed_le hα hg
  have hfrontier (x : F) (hx : x.1 ∈ frontier F) : α x.1 = g x.1 := by
    apply le_antisymm x.2
    by_contra hn
    have hlt : α x.1 < g x.1 := lt_of_not_ge hn
    exact hx.2 (interior_maximal
      (show {z | α z < g z} ⊆ F from fun z hz =>
        show α z ≤ g z from (show α z < g z from hz).le) (isOpen_lt hα hg) hlt)
  let U' : Set (X × ℝ) := U ∩ {p | p.2 < h p.1}
  let W' : Set (X × ℝ) := W ∩ {p | f p.1 < p.2}
  have hU' : IsOpen U' := hU.inter (isOpen_lt continuous_snd (hh.comp continuous_fst))
  have hW' : IsOpen W' := hW.inter (by
    simpa only [compl_ofPred, not_le] using hf.IsClosed_hypograph.isOpen_compl)
  obtain ⟨H, hHfst, hHfix, hHout, -, hHprism⟩ := exists_closed_prism_engulfing hF
    (hα.comp continuous_subtype_val) (hg.comp continuous_subtype_val)
    (fun x => x.2) hfrontier hU' hW'
    (fun x => ⟨hhU x.1 (α x.1) ⟨(hlf x.1).trans (hfαh x.1).1.le,
      (hfαh x.1).2.le⟩, (hfαh x.1).2⟩)
    (fun x t ht => ⟨hprism x.1 t ⟨(hfαh x.1).1.trans_le ht.1, ht.2⟩,
      (hfαh x.1).1.trans_le ht.1⟩)
  have hfix (x : X) (t : ℝ) (ht : t ≤ f x) : H (x, t) = (x, t) :=
    hHfix (x, t) (fun hp => not_lt_of_ge ht hp.2)
  have hifst (p : X × ℝ) : (H.symm p).1 = p.1 :=
    (hHfst (H.symm p)).symm.trans (congrArg Prod.fst (H.apply_symm_apply p))
  have hifix (x : X) (t : ℝ) (ht : t ≤ f x) : H.symm (x, t) = (x, t) := by
    have he := congrArg H.symm (hfix x t ht)
    simpa only [H.symm_apply_apply] using he.symm
  refine ⟨H, hHfst, fun p hp => hHfix p (fun h => hp h.1), hfix, ?_, ?_⟩
  · intro x hx t
    apply hHout (x, t)
    intro hi
    have hax : α x ≤ g x := (show x ∈ F from interior_subset hi)
    rw [← hx] at hax
    exact not_lt_of_ge hax (hfαh x).1
  intro x t ht
  by_cases hx : x ∈ F
  · by_cases hαt : α x ≤ t
    · exact image_mono inter_subset_left (hHprism ⟨x, hx⟩ t ⟨hαt, ht.2⟩)
    by_cases htf : t ≤ f x
    · exact ⟨(x, t), hbase x t ⟨ht.1, htf⟩, hfix x t htf⟩
    have hmono := strictMono_homeomorph_fiber H.symm hifst x
      (a := f x - 1) (b := f x) (by linarith)
      (hifix x (f x - 1) (by linarith)) (hifix x (f x) le_rfl)
    obtain ⟨q, hq, hqeq⟩ := hHprism ⟨x, hx⟩ (α x) ⟨le_rfl, hx⟩
    have hqi : q = H.symm (x, α x) := by
      simpa only [H.symm_apply_apply] using congrArg H.symm hqeq
    have hlower : f x ≤ (H.symm (x, t)).2 := by
      have hm := hmono.monotone (le_of_not_ge htf)
      simpa only [hifix x (f x) le_rfl] using hm
    have hupper : (H.symm (x, t)).2 ≤ h x := by
      have hm := hmono.monotone (le_of_not_ge hαt)
      rw [← hqi] at hm
      have hqfst : q.1 = x := by rw [hqi, hifst]
      have hqbound : q.2 < h q.1 := hq.2
      rw [hqfst] at hqbound
      exact hm.trans hqbound.le
    refine ⟨H.symm (x, t), ?_, H.apply_symm_apply (x, t)⟩
    have hp := hhU x (H.symm (x, t)).2 ⟨(hlf x).trans hlower, hupper⟩
    convert hp using 1
    exact Prod.ext (hifst (x, t)) rfl
  · have hga : g x < α x := lt_of_not_ge hx
    exact ⟨(x, t), hhU x t ⟨ht.1, ht.2.trans (hga.trans (hfαh x).2).le⟩,
      hHout (x, t) (fun hi => hx (interior_subset hi))⟩

theorem exists_closed_semicontinuous_prism_engulfing {X : Type*} [MetricSpace X]
    {F : Set X} (hF : IsClosed F) {l f g : F → ℝ}
    (hl : LowerSemicontinuous l) (hf : UpperSemicontinuous f) (hg : Continuous g)
    (hlf : ∀ x, l x ≤ f x) (hfg : ∀ x, f x ≤ g x)
    (hboundary : ∀ x : F, x.1 ∈ frontier F → f x = g x)
    {U W : Set (X × ℝ)} (hU : IsOpen U) (hW : IsOpen W)
    (hbase : ∀ (x : F) t, t ∈ Icc (l x) (f x) → (x.1, t) ∈ U)
    (hprism : ∀ (x : F) t, t ∈ Ioc (f x) (g x) → (x.1, t) ∈ W) :
    ∃ H : (X × ℝ) ≃ₜ (X × ℝ),
      (∀ p, (H p).1 = p.1) ∧ (∀ p ∉ W, H p = p) ∧
      (∀ p, p.1 ∉ interior F → H p = p) ∧
      (∀ (x : F) t, t ≤ f x → H (x.1, t) = (x.1, t)) ∧
      ∀ (x : F) t, t ∈ Icc (l x) (g x) → (x.1, t) ∈ H '' U := by
  let j : F × ℝ → X × ℝ := Prod.map Subtype.val id
  have hj : IsClosedEmbedding j := hF.isClosedEmbedding_subtypeVal.prodMap IsClosedEmbedding.id
  have hrange : range j = F ×ˢ (univ : Set ℝ) := by
    simp only [j, range_prodMap, Subtype.range_coe, range_id]
  obtain ⟨G, hGfst, hGfix, hGlower, hGdeg, hGprism⟩ :=
    exists_semicontinuous_prism_engulfing hl hf hg hlf hfg
      (hU.preimage hj.continuous) (hW.preimage hj.continuous) hbase hprism
  obtain ⟨H, hHj, hHout⟩ := exists_homeomorph_extension_of_isClosedEmbedding hj G (by
    intro p hp
    rw [hrange, frontier_prod_univ_eq] at hp
    exact hGdeg p.1 (hboundary p.1 hp.1) p.2)
  have hHoutside (p : X × ℝ) (hp : p.1 ∉ interior F) : H p = p := by
    apply hHout
    rw [hrange, interior_prod_eq, interior_univ]
    exact fun h => hp h.1
  refine ⟨H, ?_, ?_, hHoutside, ?_, ?_⟩
  · intro p
    by_cases hp : p.1 ∈ F
    · let q : F × ℝ := (⟨p.1, hp⟩, p.2)
      have hpq : j q = p := rfl
      rw [← hpq, hHj]
      exact congrArg Subtype.val (hGfst q)
    · rw [hHoutside p (fun h => hp (interior_subset h))]
  · intro p hpW
    by_cases hp : p.1 ∈ F
    · let q : F × ℝ := (⟨p.1, hp⟩, p.2)
      have hpq : j q = p := rfl
      rw [← hpq, hHj, hGfix q hpW]
    · exact hHoutside p (fun h => hp (interior_subset h))
  · intro x t ht
    change H (j (x, t)) = j (x, t)
    rw [hHj, hGlower x t ht]
  · intro x t ht
    obtain ⟨q, hq, hqt⟩ := hGprism x t ht
    exact ⟨j q, hq, by rw [hHj, hqt]; rfl⟩

end DifferentialGeometry.Topology.Engulfing
