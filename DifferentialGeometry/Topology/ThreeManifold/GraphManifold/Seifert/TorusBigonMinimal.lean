import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonJordan

/-!
# Minimal upper bigons are empty

Let `Γ : ι → ℝ → ℝ × ℝ` be a family of pairwise disjoint embedded lines leaving every bounded set
in both directions, crossing the line `y = c` only transversally, and let `Γ i₀ '' [t₁, t₂]`
bound an upper bigon at level `c` lying below `y = c + 1`, with `Γ i₀` below the line just
outside `[t₁, t₂]`. If no upper arc of the family inside the bigon is shorter (horizontal extent
of its ends) than the bigon itself, then the bigon meets the family only in its own arc
(`IsUpperBigon.family_mem_region`): a family point inside would be followed both ways to its first
exits, which lie on the open segment, giving a strictly shorter nested upper arc.

Two upper bigons at the same level whose arcs each miss the other region are disjoint
(`IsUpperBigon.disjoint_region`): the segments are disjoint intervals, the boundaries are
disjoint, each connected boundary lies outside the other region, and a common point would force
one inside into the other.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace GC.Seifert

theorem bigonRegion_eq_closure (γ : ℝ → ℝ × ℝ) (t₁ t₂ : ℝ) :
    bigonRegion γ t₁ t₂ = closure (bigonInside γ t₁ t₂) :=
  bigonPlaneEquiv.toHomeomorph.preimage_closure _

theorem isClosed_bigonRegion (γ : ℝ → ℝ × ℝ) (t₁ t₂ : ℝ) : IsClosed (bigonRegion γ t₁ t₂) :=
  isClosed_closure.preimage bigonPlaneEquiv.continuous

theorem exists_exit {F : ℝ → ℝ × ℝ} (hF : Continuous F) {I D : Set (ℝ × ℝ)} (hI : IsOpen I)
    (hD : IsClosed D) (hID : I ⊆ D) (hDb : Bornology.IsBounded D) {t₀ : ℝ}
    (hunb : ∀ R : ℝ, ∃ u, t₀ ≤ u ∧ R < ‖F u‖) (h₀ : F t₀ ∈ I) :
    ∃ t', t₀ < t' ∧ F t' ∈ D ∧ F t' ∉ I ∧ ∀ u ∈ Ico t₀ t', F u ∈ I := by
  set A := {u | t₀ ≤ u ∧ F u ∉ I}
  have hAc : IsClosed A :=
    (isClosed_le continuous_const continuous_id).inter (hI.isClosed_compl.preimage hF)
  obtain ⟨R, hR⟩ := hDb.subset_closedBall 0
  obtain ⟨u, hu, huR⟩ := hunb R
  have hAne : A.Nonempty := by
    refine ⟨u, hu, fun hI' => ?_⟩
    have := hR (hID hI')
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have hAb : BddBelow A := ⟨t₀, fun _ hv => hv.1⟩
  set t' := sInf A
  have ht'A : t' ∈ A := hAc.csInf_mem hAne hAb
  have hIco : ∀ v ∈ Ico t₀ t', F v ∈ I := by
    intro v hv
    by_contra hv'
    exact absurd (csInf_le hAb ⟨hv.1, hv'⟩) (not_le.mpr hv.2)
  have hlt : t₀ < t' := lt_of_le_of_ne ht'A.1 (fun he => ht'A.2 (he ▸ h₀))
  refine ⟨t', hlt, ?_, ht'A.2, hIco⟩
  have hcl : IsClosed (F ⁻¹' D) := hD.preimage hF
  have hsub : Ico t₀ t' ⊆ F ⁻¹' D := fun v hv => hID (hIco v hv)
  have := hcl.closure_subset_iff.mpr hsub
  rw [closure_Ico hlt.ne] at this
  exact this ⟨hlt.le, le_rfl⟩

theorem exists_exit_left {F : ℝ → ℝ × ℝ} (hF : Continuous F) {I D : Set (ℝ × ℝ)}
    (hI : IsOpen I) (hD : IsClosed D) (hID : I ⊆ D) (hDb : Bornology.IsBounded D) {t₀ : ℝ}
    (hunb : ∀ R : ℝ, ∃ u, u ≤ t₀ ∧ R < ‖F u‖) (h₀ : F t₀ ∈ I) :
    ∃ t', t' < t₀ ∧ F t' ∈ D ∧ F t' ∉ I ∧ ∀ u ∈ Ioc t' t₀, F u ∈ I := by
  obtain ⟨t', ht', hD', hI', hIco⟩ := exists_exit (F := fun u => F (-u))
    (hF.comp continuous_neg) hI hD hID hDb (t₀ := -t₀)
    (fun R => by
      obtain ⟨u, hu, huR⟩ := hunb R
      exact ⟨-u, by linarith, by simpa only [neg_neg] using huR⟩)
    (by simpa only [neg_neg] using h₀)
  refine ⟨-t', by linarith, hD', hI', fun u hu => ?_⟩
  have := hIco (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
  simpa only [neg_neg] using this

theorem abs_sub_lt_of_mem_Ioo {x₁ x₂ p q : ℝ} (hp : min x₁ x₂ < p ∧ p < max x₁ x₂)
    (hq : min x₁ x₂ < q ∧ q < max x₁ x₂) : |q - p| < |x₂ - x₁| := by
  rcases le_total x₁ x₂ with h | h
  · rw [min_eq_left h, max_eq_right h] at hp hq
    rw [abs_of_nonneg (sub_nonneg.mpr h), abs_sub_lt_iff]
    constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
  · rw [min_eq_right h, max_eq_left h] at hp hq
    rw [abs_of_nonpos (sub_nonpos.mpr h), abs_sub_lt_iff]
    constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]

namespace IsUpperBigon

variable {γ : ℝ → ℝ × ℝ} {c t₁ t₂ : ℝ}

theorem isCompact_region (h : IsUpperBigon γ c t₁ t₂) : IsCompact (bigonRegion γ t₁ t₂) := by
  have hsep := Schoenflies.jordan_curve_theorem h.jordan
  have hk : IsCompact (closure (Schoenflies.inside
      (bigonPlaneEquiv '' bigonCurveSet γ t₁ t₂))) :=
    hsep.isBounded_inside.isCompact_closure
  exact bigonPlaneEquiv.toHomeomorph.isCompact_preimage.mpr hk

theorem mem_open_segment (h : IsUpperBigon γ c t₁ t₂) {p : ℝ × ℝ}
    (hp : p ∈ bigonCurveSet γ t₁ t₂) (hpa : p ∉ γ '' Icc t₁ t₂) :
    p.2 = c ∧ min (γ t₁).1 (γ t₂).1 < p.1 ∧ p.1 < max (γ t₁).1 (γ t₂).1 := by
  rcases hp with hp | hp
  · exact absurd hp hpa
  · rw [h.segment_eq, segment_eq_uIcc] at hp
    have hp2 : p.2 = c := hp.2
    have h1 : p.1 ≠ (γ t₁).1 := fun he => hpa ⟨t₁, ⟨le_rfl, h.lt.le⟩,
      Prod.ext he.symm (h.left.trans hp2.symm)⟩
    have h2 : p.1 ≠ (γ t₂).1 := fun he => hpa ⟨t₂, ⟨h.lt.le, le_rfl⟩,
      Prod.ext he.symm (h.right.trans hp2.symm)⟩
    have hm := hp.1
    rw [uIcc, mem_Icc] at hm
    refine ⟨hp2, lt_of_le_of_ne hm.1 ?_, lt_of_le_of_ne hm.2 ?_⟩
    · intro he
      rcases min_choice (γ t₁).1 (γ t₂).1 with h' | h' <;> rw [h'] at he
      · exact h1 he.symm
      · exact h2 he.symm
    · intro he
      rcases max_choice (γ t₁).1 (γ t₂).1 with h' | h' <;> rw [h'] at he
      · exact h1 he
      · exact h2 he

theorem inside_snd (h : IsUpperBigon γ c t₁ t₂) {M : ℝ} (hM : ∀ t ∈ Icc t₁ t₂, (γ t).2 ≤ M)
    {p : ℝ × ℝ} (hp : p ∈ bigonInside γ t₁ t₂) : c < p.2 ∧ p.2 ≤ M := by
  have hpD := bigonInside_subset_region γ t₁ t₂ hp
  refine ⟨lt_of_le_of_ne (h.region_snd_ge p hpD) fun he => ?_, h.region_snd_le hM p hpD⟩
  exact Set.disjoint_left.mp (disjoint_bigonInside_curveSet γ t₁ t₂) hp
    (Or.inr (h.region_line hpD he.symm))

theorem family_mem_region {ι : Type*} {Γ : ι → ℝ → ℝ × ℝ} {i₀ : ι}
    (h : IsUpperBigon (Γ i₀) c t₁ t₂) (hM : ∀ t ∈ Icc t₁ t₂, (Γ i₀ t).2 < c + 1)
    (hl : ∀ᶠ u in 𝓝[<] t₁, (Γ i₀ u).2 < c) (hr : ∀ᶠ u in 𝓝[>] t₂, (Γ i₀ u).2 < c)
    (hΓc : ∀ i, Continuous (Γ i))
    (hinj : ∀ i j t u, Γ i t = Γ j u → i = j ∧ t = u)
    (hunb : ∀ i t (R : ℝ), (∃ u, t ≤ u ∧ R < ‖Γ i u‖) ∧ ∃ u, u ≤ t ∧ R < ‖Γ i u‖)
    (htr : ∀ i t, (Γ i t).2 = c → ∀ δ > 0, ∃ u ∈ Ioo (t - δ) (t + δ), c < (Γ i u).2)
    (hmin : ∀ i a b, a < b → (Γ i a).2 = c → (Γ i b).2 = c →
      (∀ u ∈ Ioo a b, c < (Γ i u).2 ∧ (Γ i u).2 < c + 1) →
      Γ i '' Icc a b ⊆ bigonRegion (Γ i₀) t₁ t₂ →
      |(Γ i₀ t₂).1 - (Γ i₀ t₁).1| ≤ |(Γ i b).1 - (Γ i a).1|)
    {i : ι} {t : ℝ} (ht : Γ i t ∈ bigonRegion (Γ i₀) t₁ t₂) : i = i₀ ∧ t ∈ Icc t₁ t₂ := by
  set γ := Γ i₀
  set D := bigonRegion γ t₁ t₂
  set I := bigonInside γ t₁ t₂
  have hJ := h.jordan
  have hDI : D = I ∪ bigonCurveSet γ t₁ t₂ := bigonRegion_eq_union hJ
  have hIo : IsOpen I := isOpen_bigonInside hJ
  have hDc : IsClosed D := isClosed_bigonRegion γ t₁ t₂
  have hID : I ⊆ D := bigonInside_subset_region γ t₁ t₂
  have hDb : Bornology.IsBounded D := h.isCompact_region.isBounded
  have hdisj := disjoint_bigonInside_curveSet γ t₁ t₂
  obtain ⟨tm, htm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr h.lt.le)
    h.cont.snd
  set M := (γ tm).2
  have hMle : ∀ s ∈ Icc t₁ t₂, (γ s).2 ≤ M := fun s hs => hmax hs
  have hMc : M < c + 1 := hM tm htm
  have harc : ∀ j s, Γ j s ∈ γ '' Icc t₁ t₂ → j = i₀ ∧ s ∈ Icc t₁ t₂ := by
    rintro j s ⟨s', hs', he⟩
    obtain ⟨rfl, rfl⟩ := hinj _ _ _ _ he.symm
    exact ⟨rfl, hs'⟩
  by_contra hne
  have hta : Γ i t ∉ γ '' Icc t₁ t₂ := fun ha => hne (harc i t ha)
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, Γ i t₀ ∈ I := by
    rw [hDI] at ht
    rcases ht with ht | ht
    · exact ⟨t, ht⟩
    · obtain ⟨hp2, hp1, hp1'⟩ := h.mem_open_segment ht hta
      obtain ⟨r, hr0, hball⟩ := h.upper_halfBall hp1 hp1'
      have hcont := (hΓc i).continuousAt (x := t)
      obtain ⟨δ, hδ, hδr⟩ := Metric.continuousAt_iff.mp hcont r hr0
      obtain ⟨u, hu, hcu⟩ := htr i t hp2 δ hδ
      refine ⟨u, hball _ ?_ hcu⟩
      have hd := hδr (show dist u t < δ by
        rw [Real.dist_eq, abs_sub_lt_iff]
        constructor <;> linarith [hu.1, hu.2])
      have hpt : Γ i t = ((Γ i t).1, c) := Prod.ext rfl hp2
      rwa [← hpt]
  obtain ⟨tp, htp, htpD, htpI, hIp⟩ := exists_exit (hΓc i) hIo hDc hID hDb
    (fun R => (hunb i t₀ R).1) ht₀
  obtain ⟨tq, htq, htqD, htqI, hIq⟩ := exists_exit_left (hΓc i) hIo hDc hID hDb
    (fun R => (hunb i t₀ R).2) ht₀
  have hcurve : ∀ s, Γ i s ∈ D → Γ i s ∉ I → Γ i s ∈ bigonCurveSet γ t₁ t₂ := by
    intro s hs hsI
    rw [hDI] at hs
    exact hs.resolve_left hsI
  have hnotI : ∀ s ∈ Icc t₁ t₂, γ s ∉ I := fun s hs hI' =>
    Set.disjoint_left.mp hdisj hI' (Or.inl ⟨s, hs, rfl⟩)
  have htpa : Γ i tp ∉ γ '' Icc t₁ t₂ := by
    intro ha
    obtain ⟨rfl, hs⟩ := harc i tp ha
    have ht₀a : t₀ < t₁ := by
      by_contra hle
      push Not at hle
      exact hnotI t₀ ⟨hle, (htp.trans_le hs.2).le⟩ ht₀
    have htp1 : tp = t₁ := by
      by_contra hne'
      have hlt : t₁ < tp := lt_of_le_of_ne hs.1 (Ne.symm hne')
      exact hnotI t₁ ⟨le_rfl, h.lt.le⟩ (hIp t₁ ⟨ht₀a.le, hlt⟩)
    subst htp1
    obtain ⟨u, hu1, hu2⟩ := (hl.and (Ioo_mem_nhdsLT ht₀a)).exists
    have := h.region_snd_ge _ (hID (hIp u ⟨hu2.1.le, hu2.2⟩))
    linarith
  have htqa : Γ i tq ∉ γ '' Icc t₁ t₂ := by
    intro ha
    obtain ⟨rfl, hs⟩ := harc i tq ha
    have ht₀a : t₂ < t₀ := by
      by_contra hle
      push Not at hle
      exact hnotI t₀ ⟨(hs.1.trans_lt htq).le, hle⟩ ht₀
    have htq2 : tq = t₂ := by
      by_contra hne'
      have hlt : tq < t₂ := lt_of_le_of_ne hs.2 hne'
      exact hnotI t₂ ⟨h.lt.le, le_rfl⟩ (hIq t₂ ⟨hlt, ht₀a.le⟩)
    subst htq2
    obtain ⟨u, hu1, hu2⟩ := (hr.and (Ioo_mem_nhdsGT ht₀a)).exists
    have := h.region_snd_ge _ (hID (hIq u ⟨hu2.1, hu2.2.le⟩))
    linarith
  obtain ⟨hp2, hp1⟩ := h.mem_open_segment (hcurve tp htpD htpI) htpa
  obtain ⟨hq2, hq1⟩ := h.mem_open_segment (hcurve tq htqD htqI) htqa
  have hmid : ∀ u ∈ Ioo tq tp, Γ i u ∈ I := by
    intro u hu
    rcases le_total u t₀ with hu' | hu'
    · exact hIq u ⟨hu.1, hu'⟩
    · exact hIp u ⟨hu', hu.2⟩
  have hle := hmin i tq tp (htq.trans htp) hq2 hp2
    (fun u hu => by
      obtain ⟨h1, h2⟩ := h.inside_snd hMle (hmid u hu)
      exact ⟨h1, h2.trans_lt hMc⟩)
    (by
      rintro _ ⟨u, hu, rfl⟩
      rcases eq_or_lt_of_le hu.1 with he | hlt
      · rw [← he]; exact htqD
      · rcases eq_or_lt_of_le hu.2 with he' | hlt'
        · rw [he']; exact htpD
        · exact hID (hmid u ⟨hlt, hlt'⟩))
  exact absurd hle (not_le.mpr (abs_sub_lt_of_mem_Ioo hq1 hp1))

theorem disjoint_uIcc {x₁ x₂ y₁ y₂ : ℝ} (h₁ : y₁ ∉ uIcc x₁ x₂) (h₂ : y₂ ∉ uIcc x₁ x₂)
    (h₃ : x₁ ∉ uIcc y₁ y₂) : Disjoint (uIcc x₁ x₂) (uIcc y₁ y₂) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  simp only [uIcc, mem_Icc, not_and_or, not_le] at *
  rcases le_total x₁ x₂ with hx | hx <;> rcases le_total y₁ y₂ with hy | hy <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, hx, hy] at * <;>
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rcases h₃ with h₃ | h₃ <;>
    linarith [hz.1, hz.2, hz'.1, hz'.2]

theorem disjoint_region {γ' : ℝ → ℝ × ℝ} {t₁' t₂' : ℝ} (h : IsUpperBigon γ c t₁ t₂)
    (h' : IsUpperBigon γ' c t₁' t₂')
    (hA : Disjoint (γ '' Icc t₁ t₂) (bigonRegion γ' t₁' t₂'))
    (hA' : Disjoint (γ' '' Icc t₁' t₂') (bigonRegion γ t₁ t₂)) :
    Disjoint (bigonRegion γ t₁ t₂) (bigonRegion γ' t₁' t₂') := by
  set D := bigonRegion γ t₁ t₂
  set D' := bigonRegion γ' t₁' t₂'
  set J := bigonCurveSet γ t₁ t₂
  set J' := bigonCurveSet γ' t₁' t₂'
  have hDI : D = bigonInside γ t₁ t₂ ∪ J := bigonRegion_eq_union h.jordan
  have hDI' : D' = bigonInside γ' t₁' t₂' ∪ J' := bigonRegion_eq_union h'.jordan
  have hJD : J ⊆ D := fun z hz => hDI ▸ Or.inr hz
  have hJD' : J' ⊆ D' := fun z hz => hDI' ▸ Or.inr hz
  have ha₁ : γ t₁ ∈ γ '' Icc t₁ t₂ := ⟨t₁, ⟨le_rfl, h.lt.le⟩, rfl⟩
  have ha₂ : γ t₂ ∈ γ '' Icc t₁ t₂ := ⟨t₂, ⟨h.lt.le, le_rfl⟩, rfl⟩
  have ha₁' : γ' t₁' ∈ γ' '' Icc t₁' t₂' := ⟨t₁', ⟨le_rfl, h'.lt.le⟩, rfl⟩
  have ha₂' : γ' t₂' ∈ γ' '' Icc t₁' t₂' := ⟨t₂', ⟨h'.lt.le, le_rfl⟩, rfl⟩
  have hseg : Disjoint (segment ℝ (γ t₁) (γ t₂)) (segment ℝ (γ' t₁') (γ' t₂')) := by
    have hnot : ∀ (γa : ℝ → ℝ × ℝ) (a₁ a₂ : ℝ) (Da : Set (ℝ × ℝ)) (p : ℝ × ℝ),
        p.2 = c → (γa a₁).2 = c → (γa a₂).2 = c → p ∉ Da →
        segment ℝ (γa a₁) (γa a₂) ⊆ Da → p.1 ∉ uIcc (γa a₁).1 (γa a₂).1 := by
      intro γa a₁ a₂ Da p hp h₁ h₂ hpD hsD hm
      apply hpD (hsD _)
      have e1 : γa a₁ = ((γa a₁).1, c) := Prod.ext rfl h₁
      have e2 : γa a₂ = ((γa a₂).1, c) := Prod.ext rfl h₂
      rw [e1, e2, segment_horizontal, segment_eq_uIcc]
      exact ⟨hm, hp⟩
    have hsD : segment ℝ (γ t₁) (γ t₂) ⊆ D := fun z hz => hJD (Or.inr hz)
    have hsD' : segment ℝ (γ' t₁') (γ' t₂') ⊆ D' := fun z hz => hJD' (Or.inr hz)
    have hu := disjoint_uIcc
      (hnot γ t₁ t₂ D (γ' t₁') h'.left h.left h.right
        (Set.disjoint_left.mp hA' ha₁') hsD)
      (hnot γ t₁ t₂ D (γ' t₂') h'.right h.left h.right
        (Set.disjoint_left.mp hA' ha₂') hsD)
      (hnot γ' t₁' t₂' D' (γ t₁) h.left h'.left h'.right
        (Set.disjoint_left.mp hA ha₁) hsD')
    rw [h.segment_eq, h'.segment_eq, segment_eq_uIcc, segment_eq_uIcc]
    exact Set.disjoint_prod.mpr (Or.inl hu)
  have hJJ' : Disjoint J J' := by
    rw [Set.disjoint_left]
    rintro z (hz | hz) (hz' | hz')
    · exact Set.disjoint_left.mp hA hz (hJD' (Or.inl hz'))
    · exact Set.disjoint_left.mp hA hz (hJD' (Or.inr hz'))
    · exact Set.disjoint_left.mp hA' hz' (hJD (Or.inr hz))
    · exact Set.disjoint_left.mp hseg hz hz'
  have hconnJ : ∀ (γa : ℝ → ℝ × ℝ) (a₁ a₂ : ℝ),
      Schoenflies.IsJordanCurve (bigonPlaneEquiv '' bigonCurveSet γa a₁ a₂) →
      IsPreconnected (bigonCurveSet γa a₁ a₂) := by
    intro γa a₁ a₂ hJa
    have := hJa.isConnected.isPreconnected.image _
      bigonPlaneEquiv.symm.continuous.continuousOn
    rwa [image_image, show (fun x => bigonPlaneEquiv.symm (bigonPlaneEquiv x)) = id from
      funext fun x => bigonPlaneEquiv.symm_apply_apply x, image_id] at this
  have hconnI : ∀ (γa : ℝ → ℝ × ℝ) (a₁ a₂ : ℝ),
      Schoenflies.IsJordanCurve (bigonPlaneEquiv '' bigonCurveSet γa a₁ a₂) →
      IsPreconnected (bigonInside γa a₁ a₂) := by
    intro γa a₁ a₂ hJa
    have hsep := Schoenflies.jordan_curve_theorem hJa
    have := hsep.isConnected_inside.isPreconnected.image _
      bigonPlaneEquiv.symm.continuous.continuousOn
    have he : bigonPlaneEquiv.symm '' Schoenflies.inside
        (bigonPlaneEquiv '' bigonCurveSet γa a₁ a₂) = bigonInside γa a₁ a₂ := by
      rw [ContinuousLinearEquiv.image_symm_eq_preimage]
      rfl
    rwa [he] at this
  have hJ'D : Disjoint J' D := by
    rw [hDI, Set.disjoint_union_right]
    refine ⟨?_, hJJ'.symm⟩
    rw [Set.disjoint_left]
    intro z hzJ hzI
    have hsub := subset_bigonInside_of_connected (hconnJ γ' t₁' t₂' h'.jordan) hJJ'.symm hzJ hzI
    exact Set.disjoint_left.mp hA' ha₁'
      (bigonInside_subset_region γ t₁ t₂ (hsub (Or.inl ha₁')))
  have hJD'' : Disjoint J D' := by
    rw [hDI', Set.disjoint_union_right]
    refine ⟨?_, hJJ'⟩
    rw [Set.disjoint_left]
    intro z hzJ hzI
    have hsub := subset_bigonInside_of_connected (hconnJ γ t₁ t₂ h.jordan) hJJ' hzJ hzI
    exact Set.disjoint_left.mp hA ha₁
      (bigonInside_subset_region γ' t₁' t₂' (hsub (Or.inl ha₁)))
  rw [Set.disjoint_left]
  intro z hz hz'
  have hzI : z ∈ bigonInside γ t₁ t₂ := by
    rw [hDI] at hz
    exact hz.resolve_right fun hzJ => Set.disjoint_left.mp hJD'' hzJ hz'
  have hzI' : z ∈ bigonInside γ' t₁' t₂' := by
    rw [hDI'] at hz'
    exact hz'.resolve_right fun hzJ => Set.disjoint_left.mp hJ'D hzJ hz
  have hsub := subset_bigonInside_of_connected (hconnI γ' t₁' t₂' h'.jordan)
    (Set.disjoint_of_subset_left (bigonInside_subset_region γ' t₁' t₂') hJD''.symm) hzI' hzI
  have hcl : D' ⊆ D := by
    change bigonRegion γ' t₁' t₂' ⊆ D
    rw [bigonRegion_eq_closure γ' t₁' t₂']
    exact closure_minimal (hsub.trans (bigonInside_subset_region γ t₁ t₂))
      (isClosed_bigonRegion γ t₁ t₂)
  exact Set.disjoint_left.mp hA' ha₁' (hcl (hJD' (Or.inl ha₁')))

end IsUpperBigon

end GC.Seifert
