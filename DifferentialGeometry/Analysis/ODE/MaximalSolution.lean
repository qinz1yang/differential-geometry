import DifferentialGeometry.Analysis.ODE.InvariantSet
import DifferentialGeometry.Analysis.ODE.Uniqueness
import DifferentialGeometry.Topology.Order.Interval
import Mathlib.Order.Zorn

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsMaximalIntegralCurveOn (γ : ℝ → E) (f : ℝ → E → E) (I J : Set ℝ) : Prop where
  ordConnected : I.OrdConnected
  subset : I ⊆ J
  isIntegralCurveOn : IsIntegralCurveOn γ f I
  maximal : ∀ {η : ℝ → E} {L : Set ℝ}, L.OrdConnected → L ⊆ J → I ⊆ L →
    IsIntegralCurveOn η f L → EqOn γ η I → L ⊆ I

private def integralCurveGraph (γ : ℝ → E) (I : Set ℝ) : Set (ℝ × E) :=
  {p | p.1 ∈ I ∧ p.2 = γ p.1}

private def isIntegralCurveGraph (f : ℝ → E → E) (J : Set ℝ) (s : Set (ℝ × E)) : Prop :=
  ∃ I : Set ℝ, ∃ γ : ℝ → E, I.Nonempty ∧ I.OrdConnected ∧ I ⊆ J ∧
    IsIntegralCurveOn γ f I ∧ s = integralCurveGraph γ I

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem integralCurveGraph_subset_iff {γ η : ℝ → E} {I J : Set ℝ} :
    integralCurveGraph γ I ⊆ integralCurveGraph η J ↔ I ⊆ J ∧ EqOn γ η I := by
  constructor
  · intro h
    exact ⟨fun t ht => (h (show (t, γ t) ∈ integralCurveGraph γ I from ⟨ht, rfl⟩)).1,
      fun t ht => (h (show (t, γ t) ∈ integralCurveGraph γ I from ⟨ht, rfl⟩)).2⟩
  · rintro ⟨hsub, heq⟩ p hp
    exact ⟨hsub hp.1, hp.2.trans (heq hp.1)⟩

private theorem isIntegralCurveGraph_sUnion {f : ℝ → E → E} {J : Set ℝ}
    {c : Set (Set (ℝ × E))} (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (hgraphs : ∀ s ∈ c, isIntegralCurveGraph f J s) : isIntegralCurveGraph f J (⋃₀ c) := by
  classical
  have hpair (s : Set (ℝ × E)) (hs : s ∈ c) (r : Set (ℝ × E)) (hr : r ∈ c) :
      ∃ q ∈ c, s ⊆ q ∧ r ⊆ q := by
    by_cases heq : s = r
    · subst r
      exact ⟨s, hs, subset_rfl, subset_rfl⟩
    rcases hc hs hr heq with h | h
    · exact ⟨r, hr, h, subset_rfl⟩
    · exact ⟨s, hs, subset_rfl, h⟩
  let U := ⋃₀ c
  let D : Set ℝ := {t | ∃ v : E, (t, v) ∈ U}
  have hfunctional {t : ℝ} {v w : E} (hv : (t, v) ∈ U) (hw : (t, w) ∈ U) : v = w := by
    obtain ⟨s, hs, hvs⟩ := mem_sUnion.mp hv
    obtain ⟨r, hr, hwr⟩ := mem_sUnion.mp hw
    obtain ⟨q, hq, hsq, hrq⟩ := hpair s hs r hr
    obtain ⟨I, γ, _, _, _, _, hgraph⟩ := hgraphs q hq
    have hvq := hsq hvs
    have hwq := hrq hwr
    rw [hgraph] at hvq hwq
    exact hvq.2.trans hwq.2.symm
  let γ : ℝ → E := fun t => if ht : t ∈ D then Classical.choose ht else 0
  have hmem (t : ℝ) (ht : t ∈ D) : (t, γ t) ∈ U := by
    dsimp only [γ]
    rw [dif_pos ht]
    exact Classical.choose_spec ht
  have heqGraph : U = integralCurveGraph γ D := by
    ext ⟨t, v⟩
    constructor
    · intro h
      have ht : t ∈ D := ⟨v, h⟩
      exact ⟨ht, hfunctional h (hmem t ht)⟩
    · rintro ⟨ht, hv⟩
      change v = γ t at hv
      rw [hv]
      exact hmem t ht
  have hDne : D.Nonempty := by
    obtain ⟨s, hs⟩ := hne
    obtain ⟨I, η, ⟨t, ht⟩, _, _, _, hgraph⟩ := hgraphs s hs
    exact ⟨t, η t, mem_sUnion.mpr ⟨s, hs, hgraph.symm ▸ ⟨ht, rfl⟩⟩⟩
  have hDsub : D ⊆ J := by
    rintro t ⟨v, hv⟩
    obtain ⟨s, hs, hp⟩ := mem_sUnion.mp hv
    obtain ⟨I, η, _, _, hIJ, _, hgraph⟩ := hgraphs s hs
    rw [hgraph] at hp
    exact hIJ hp.1
  have hfinite {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) :
      ∃ I : Set ℝ, ∃ η : ℝ → E, a ∈ I ∧ b ∈ I ∧ I.OrdConnected ∧
        IsIntegralCurveOn η f I ∧ I ⊆ D ∧ EqOn γ η I := by
    obtain ⟨va, hva⟩ := ha
    obtain ⟨vb, hvb⟩ := hb
    obtain ⟨s, hs, has⟩ := mem_sUnion.mp hva
    obtain ⟨r, hr, hbr⟩ := mem_sUnion.mp hvb
    obtain ⟨q, hq, hsq, hrq⟩ := hpair s hs r hr
    obtain ⟨I, η, _, hI, _, hη, hgraph⟩ := hgraphs q hq
    have hag := hsq has
    have hbg := hrq hbr
    rw [hgraph] at hag hbg
    have hsub : integralCurveGraph η I ⊆ integralCurveGraph γ D := by
      rw [← hgraph, ← heqGraph]
      exact subset_sUnion_of_mem hq
    have hsub' := integralCurveGraph_subset_iff.mp hsub
    exact ⟨I, η, hag.1, hbg.1, hI, hη, hsub'.1, hsub'.2.symm⟩
  have hD : D.OrdConnected := by
    constructor
    intro a ha b hb t ht
    obtain ⟨I, η, haI, hbI, hI, _, hID, _⟩ := hfinite ha hb
    exact hID (hI.out haI hbI ht)
  refine ⟨D, γ, hDne, hD, hDsub, ?_, heqGraph⟩
  intro t ht
  obtain ⟨a, b, _, htC, hCD, hCnhds⟩ := hD.exists_Icc_subset_mem_nhdsWithin ht ht
  have hab : a ≤ b := htC.1.trans htC.2
  obtain ⟨I, η, haI, hbI, hI, hη, _, heq⟩ :=
    hfinite (hCD (left_mem_Icc.mpr hab)) (hCD (right_mem_Icc.mpr hab))
  have hCI : Icc a b ⊆ I := hI.out haI hbI
  have hInhds : I ∈ 𝓝[D] t := mem_of_superset hCnhds hCI
  have htI : t ∈ I := hCI htC
  rw [heq htI]
  exact ((hη t htI).mono_of_mem_nhdsWithin hInhds).congr_of_eventuallyEq
    (eventually_of_mem hInhds fun r hr => heq hr) (heq htI)

theorem IsIntegralCurveOn.exists_isMaximalIntegralCurveOn
    {γ : ℝ → E} {f : ℝ → E → E} {I J : Set ℝ}
    (hγ : IsIntegralCurveOn γ f I) (hne : I.Nonempty) (hI : I.OrdConnected) (hIJ : I ⊆ J) :
    ∃ L : Set ℝ, ∃ η : ℝ → E, I ⊆ L ∧ EqOn γ η I ∧ IsMaximalIntegralCurveOn η f L J := by
  classical
  let S := {s : Set (ℝ × E) | isIntegralCurveGraph f J s}
  have hbase : integralCurveGraph γ I ∈ S := ⟨I, γ, hne, hI, hIJ, hγ, rfl⟩
  obtain ⟨s, hGs, hmax⟩ := zorn_subset_nonempty S (fun c hcS hc hcne =>
    ⟨⋃₀ c, isIntegralCurveGraph_sUnion hc hcne (fun _ hs => hcS hs),
      fun _ hs => subset_sUnion_of_mem hs⟩) (integralCurveGraph γ I) hbase
  obtain ⟨L, η, hLne, hL, hLJ, hη, hgraph⟩ := hmax.prop
  have hsub := integralCurveGraph_subset_iff.mp (hgraph ▸ hGs)
  refine ⟨L, η, hsub.1, hsub.2, ⟨hL, hLJ, hη, ?_⟩⟩
  intro ζ K hK hKJ hLK hζ heq
  have hnew : integralCurveGraph ζ K ∈ S :=
    ⟨K, ζ, hLne.mono hLK, hK, hKJ, hζ, rfl⟩
  have hle : s ⊆ integralCurveGraph ζ K := by
    rw [hgraph]
    exact integralCurveGraph_subset_iff.mpr ⟨hLK, heq⟩
  have hback : integralCurveGraph ζ K ⊆ integralCurveGraph η L := by
    rw [← hgraph, hmax.eq_of_subset hnew hle]
  exact (integralCurveGraph_subset_iff.mp hback).1

theorem exists_isMaximalIntegralCurveOn
    (f : ℝ → E → E) {J : Set ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : E) :
    ∃ I : Set ℝ, ∃ γ : ℝ → E, t₀ ∈ I ∧ γ t₀ = x₀ ∧
      IsMaximalIntegralCurveOn γ f I J := by
  have hγ : IsIntegralCurveOn (fun _ => x₀) f {t₀} :=
    fun _ _ => HasFDerivWithinAt.singleton
  obtain ⟨I, γ, hI, heq, hmax⟩ :=
    IsIntegralCurveOn.exists_isMaximalIntegralCurveOn hγ (singleton_nonempty t₀)
      ordConnected_singleton (singleton_subset_iff.mpr ht₀)
  exact ⟨I, γ, hI (mem_singleton t₀), (heq (mem_singleton t₀)).symm, hmax⟩

theorem IsForwardInvariantForODEOn.mapsTo_of_isIntegralCurveOn
    {f : ℝ → E → E} {C : Set E} {I J : Set ℝ} {γ : ℝ → E} {t₀ : ℝ}
    (hC : IsForwardInvariantForODEOn f C J) (hI : I.OrdConnected) (hIJ : I ⊆ J)
    (hγ : IsIntegralCurveOn γ f I) (ht₀ : t₀ ∈ I) (hinit : γ t₀ ∈ C) :
    MapsTo γ (I ∩ Ici t₀) C := by
  intro t ht
  have hsub : Icc t₀ t ⊆ I := hI.out ht₀ ht.1
  exact hC t₀ t ht.2 (hsub.trans hIJ) γ (hγ.mono hsub) hinit ⟨ht.2, le_rfl⟩

theorem isForwardInvariantForODEOn_iff_maximal
    {f : ℝ → E → E} {C : Set E} {J : Set ℝ} :
    IsForwardInvariantForODEOn f C J ↔
      ∀ (I : Set ℝ) (γ : ℝ → E), IsMaximalIntegralCurveOn γ f I J →
        ∀ t₀ ∈ I, γ t₀ ∈ C → MapsTo γ (I ∩ Ici t₀) C := by
  constructor
  · intro h I γ hmax t₀ ht₀ hinit
    exact h.mapsTo_of_isIntegralCurveOn hmax.ordConnected hmax.subset
      hmax.isIntegralCurveOn ht₀ hinit
  · intro h a b hab hsub γ hγ hinit
    have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
    obtain ⟨I, η, hI, heq, hmax⟩ :=
      IsIntegralCurveOn.exists_isMaximalIntegralCurveOn hγ ⟨a, ha⟩ ordConnected_Icc hsub
    have hinit' : η a ∈ C := (heq ha) ▸ hinit
    have hmap := h I η hmax a (hI ha) hinit'
    intro t ht
    rw [heq ht]
    exact hmap ⟨hI ht, ht.1⟩

private theorem integralCurveOn_piecewise_Iic
    {γ η : ℝ → E} {f : ℝ → E → E} {I : Set ℝ} {t₀ : ℝ}
    (hγ : IsIntegralCurveOn γ f (I ∩ Iic t₀))
    (hη : IsIntegralCurveOn η f (I ∩ Ici t₀)) (hinit : γ t₀ = η t₀) :
    IsIntegralCurveOn (fun t => if t ≤ t₀ then γ t else η t) f I := by
  let ζ : ℝ → E := fun t => if t ≤ t₀ then γ t else η t
  have heqγ : EqOn ζ γ (Iic t₀) := fun t ht => if_pos ht
  have heqη : EqOn ζ η (Ici t₀) := by
    intro t ht
    by_cases h : t ≤ t₀
    · have he : t = t₀ := le_antisymm h ht
      subst t
      exact (if_pos le_rfl).trans hinit
    · exact if_neg h
  intro t ht
  change HasDerivWithinAt ζ (f t (ζ t)) I t
  rcases lt_trichotomy t t₀ with hlt | he | hgt
  · have hN : I ∩ Iic t₀ ∈ 𝓝[I] t :=
      inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hlt))
    rw [heqγ hlt.le]
    exact ((hγ t ⟨ht, hlt.le⟩).mono_of_mem_nhdsWithin hN).congr_of_eventuallyEq
      (eventually_of_mem (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hlt))
        fun r hr => heqγ hr) (heqγ hlt.le)
  · subst t
    have hleft : HasDerivWithinAt ζ (f t₀ (ζ t₀)) (I ∩ Iic t₀) t₀ := by
      rw [heqγ (show t₀ ∈ Iic t₀ from le_refl t₀)]
      exact (hγ t₀ ⟨ht, le_refl t₀⟩).congr_of_eventuallyEq
        (eventually_of_mem self_mem_nhdsWithin fun r hr => heqγ hr.2)
        (heqγ (show t₀ ∈ Iic t₀ from le_refl t₀))
    have hright : HasDerivWithinAt ζ (f t₀ (ζ t₀)) (I ∩ Ici t₀) t₀ := by
      rw [heqη (show t₀ ∈ Ici t₀ from le_refl t₀)]
      exact (hη t₀ ⟨ht, le_refl t₀⟩).congr_of_eventuallyEq
        (eventually_of_mem self_mem_nhdsWithin fun r hr => heqη hr.2)
        (heqη (show t₀ ∈ Ici t₀ from le_refl t₀))
    simpa only [← inter_union_distrib_left, Iic_union_Ici, inter_univ] using hleft.union hright
  · have hN : I ∩ Ici t₀ ∈ 𝓝[I] t :=
      inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hgt))
    rw [heqη hgt.le]
    exact ((hη t ⟨ht, hgt.le⟩).mono_of_mem_nhdsWithin hN).congr_of_eventuallyEq
      (eventually_of_mem (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hgt))
        fun r hr => heqη hr) (heqη hgt.le)

private theorem maximalIntegralCurveOn_subset_of_eqOn
    {γ η : ℝ → E} {f : ℝ → E → E} {I J L : Set ℝ} {t₀ : ℝ}
    (hγ : IsMaximalIntegralCurveOn γ f I J) (hη : IsIntegralCurveOn η f L)
    (hL : L.OrdConnected) (hLJ : L ⊆ J) (ht₀ : t₀ ∈ I ∩ L)
    (heq : EqOn γ η (I ∩ L)) : L ⊆ I := by
  intro t ht
  by_contra hn
  have hinit : γ t₀ = η t₀ := heq ht₀
  rcases le_total t₀ t with hle | hle
  · let D := I ∪ Icc t₀ t
    have hbound (s : ℝ) (hs : s ∈ I) : s ≤ t := by
      by_contra h
      exact hn (hγ.ordConnected.out ht₀.1 hs ⟨hle, (not_le.mp h).le⟩)
    have hD : D.OrdConnected := isPreconnected_iff_ordConnected.mp
      (isPreconnected_iff_ordConnected.mpr hγ.ordConnected |>.union t₀ ht₀.1
        (left_mem_Icc.mpr hle) isPreconnected_Icc)
    have hDJ : D ⊆ J := union_subset hγ.subset ((hL.out ht₀.2 ht).trans hLJ)
    have hleft : D ∩ Iic t₀ ⊆ I := by
      rintro s ⟨hs | hs, hst₀⟩
      · exact hs
      · have he : s = t₀ := le_antisymm hst₀ hs.1
        exact he ▸ ht₀.1
    have hright : D ∩ Ici t₀ ⊆ L := by
      rintro s ⟨hs | hs, ht₀s⟩
      · exact hL.out ht₀.2 ht ⟨ht₀s, hbound s hs⟩
      · exact hL.out ht₀.2 ht hs
    have hζ := integralCurveOn_piecewise_Iic (hγ.isIntegralCurveOn.mono hleft)
      (hη.mono hright) hinit
    have hDsub := hγ.maximal hD hDJ subset_union_left hζ (fun s hs => by
      by_cases h : s ≤ t₀
      · exact (if_pos h).symm
      · rw [if_neg h]
        exact heq ⟨hs, hL.out ht₀.2 ht ⟨(not_le.mp h).le, hbound s hs⟩⟩)
    exact hn (hDsub (Or.inr (right_mem_Icc.mpr hle)))
  · let D := I ∪ Icc t t₀
    have hbound (s : ℝ) (hs : s ∈ I) : t ≤ s := by
      by_contra h
      exact hn (hγ.ordConnected.out hs ht₀.1 ⟨(not_le.mp h).le, hle⟩)
    have hD : D.OrdConnected := isPreconnected_iff_ordConnected.mp
      (isPreconnected_iff_ordConnected.mpr hγ.ordConnected |>.union t₀ ht₀.1
        (right_mem_Icc.mpr hle) isPreconnected_Icc)
    have hDJ : D ⊆ J := union_subset hγ.subset ((hL.out ht ht₀.2).trans hLJ)
    have hleft : D ∩ Iic t₀ ⊆ L := by
      rintro s ⟨hs | hs, hst₀⟩
      · exact hL.out ht ht₀.2 ⟨hbound s hs, hst₀⟩
      · exact hL.out ht ht₀.2 hs
    have hright : D ∩ Ici t₀ ⊆ I := by
      rintro s ⟨hs | hs, ht₀s⟩
      · exact hs
      · have he : s = t₀ := le_antisymm hs.2 ht₀s
        exact he ▸ ht₀.1
    have hζ := integralCurveOn_piecewise_Iic (hη.mono hleft)
      (hγ.isIntegralCurveOn.mono hright) hinit.symm
    have hDsub := hγ.maximal hD hDJ subset_union_left hζ (fun s hs => by
      by_cases h : s ≤ t₀
      · rw [if_pos h]
        exact heq ⟨hs, hL.out ht ht₀.2 ⟨hbound s hs, h⟩⟩
      · exact (if_neg h).symm)
    exact hn (hDsub (Or.inr (left_mem_Icc.mpr hle)))

theorem IsMaximalIntegralCurveOn.extends_of_locallyLipschitzOn
    {γ η : ℝ → E} {f : ℝ → E → E} {I J L : Set ℝ} {t₀ : ℝ}
    (hγ : IsMaximalIntegralCurveOn γ f I J) (hη : IsIntegralCurveOn η f L)
    (hL : L.OrdConnected) (hLJ : L ⊆ J)
    (hf : LocallyLipschitzOn (J ×ˢ (univ : Set E)) (Function.uncurry f))
    (ht₀ : t₀ ∈ I ∩ L) (hinit : γ t₀ = η t₀) : L ⊆ I ∧ EqOn γ η L := by
  have heq : EqOn γ η (I ∩ L) := IsIntegralCurveOn.eqOn_of_locallyLipschitzOn
    (hγ.isIntegralCurveOn.mono inter_subset_left) (hη.mono inter_subset_right)
    (hγ.ordConnected.inter hL)
    (hf.mono (prod_mono_left (inter_subset_left.trans hγ.subset))) ht₀ hinit
  have hsub := maximalIntegralCurveOn_subset_of_eqOn hγ hη hL hLJ ht₀ heq
  exact ⟨hsub, fun s hs => heq ⟨hsub hs, hs⟩⟩

theorem IsMaximalIntegralCurveOn.eq_of_locallyLipschitzOn
    {γ η : ℝ → E} {f : ℝ → E → E} {I J L : Set ℝ} {t₀ : ℝ}
    (hγ : IsMaximalIntegralCurveOn γ f I J) (hη : IsMaximalIntegralCurveOn η f L J)
    (hf : LocallyLipschitzOn (J ×ˢ (univ : Set E)) (Function.uncurry f))
    (ht₀ : t₀ ∈ I ∩ L) (hinit : γ t₀ = η t₀) : I = L ∧ EqOn γ η I := by
  have h₁ := hγ.extends_of_locallyLipschitzOn hη.isIntegralCurveOn hη.ordConnected
    hη.subset hf ht₀ hinit
  have h₂ := hη.extends_of_locallyLipschitzOn hγ.isIntegralCurveOn hγ.ordConnected
    hγ.subset hf ⟨ht₀.2, ht₀.1⟩ hinit.symm
  exact ⟨Subset.antisymm h₂.1 h₁.1, h₂.2.symm⟩

theorem IsMaximalIntegralCurveOn.extends_of_contDiffOn
    {γ η : ℝ → E} {f : ℝ → E → E} {I J L : Set ℝ} {t₀ : ℝ}
    (hγ : IsMaximalIntegralCurveOn γ f I J) (hη : IsIntegralCurveOn η f L)
    (hL : L.OrdConnected) (hLJ : L ⊆ J) (hJ : J.OrdConnected)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (J ×ˢ (univ : Set E)))
    (ht₀ : t₀ ∈ I ∩ L) (hinit : γ t₀ = η t₀) : L ⊆ I ∧ EqOn γ η L :=
  hγ.extends_of_locallyLipschitzOn hη hL hLJ
    (hf.locallyLipschitzOn ((convex_iff_ordConnected.mpr hJ).prod convex_univ)) ht₀ hinit

theorem IsMaximalIntegralCurveOn.eq_of_contDiffOn
    {γ η : ℝ → E} {f : ℝ → E → E} {I J L : Set ℝ} {t₀ : ℝ}
    (hγ : IsMaximalIntegralCurveOn γ f I J) (hη : IsMaximalIntegralCurveOn η f L J)
    (hJ : J.OrdConnected)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (J ×ˢ (univ : Set E)))
    (ht₀ : t₀ ∈ I ∩ L) (hinit : γ t₀ = η t₀) : I = L ∧ EqOn γ η I :=
  hγ.eq_of_locallyLipschitzOn hη
    (hf.locallyLipschitzOn ((convex_iff_ordConnected.mpr hJ).prod convex_univ)) ht₀ hinit

theorem isForwardInvariantForODEOn_iff_exists_maximal_of_contDiffOn
    {f : ℝ → E → E} {C : Set E} {J : Set ℝ} (hJ : J.OrdConnected)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (J ×ˢ (univ : Set E))) :
    IsForwardInvariantForODEOn f C J ↔
      ∀ t₀ ∈ J, ∀ x₀ ∈ C, ∃ I : Set ℝ, ∃ γ : ℝ → E,
        t₀ ∈ I ∧ γ t₀ = x₀ ∧ IsMaximalIntegralCurveOn γ f I J ∧
          MapsTo γ (I ∩ Ici t₀) C := by
  constructor
  · intro h t₀ ht₀ x₀ hx₀
    obtain ⟨I, γ, ht, hinit, hmax⟩ := exists_isMaximalIntegralCurveOn f ht₀ x₀
    exact ⟨I, γ, ht, hinit, hmax,
      h.mapsTo_of_isIntegralCurveOn hmax.ordConnected hmax.subset hmax.isIntegralCurveOn
        ht (hinit.symm ▸ hx₀)⟩
  · intro h a b hab hsub η hη hinit
    have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
    obtain ⟨I, γ, haI, hγa, hmax, hmap⟩ := h a (hsub ha) (η a) hinit
    obtain ⟨hI, heq⟩ := hmax.extends_of_contDiffOn hη ordConnected_Icc hsub hJ hf
      ⟨haI, ha⟩ hγa
    intro t ht
    rw [← heq ht]
    exact hmap ⟨hI ht, ht.1⟩

end DifferentialGeometry.Analysis.ODE
