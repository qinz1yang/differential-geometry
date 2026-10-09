import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonPush

/-!
# Jordan facts for bigons

For an arc `γ '' [t₁, t₂]` lying strictly above the horizontal line `y = c` except at its two
distinct ends on that line, the arc and the segment between the ends form a Jordan curve. Its
closed region `bigonRegion γ t₁ t₂` lies between `y = c` and the top of the arc, meets the
line only in the segment, and contains a whole upper half-disc around every interior point of
the segment. A connected set off the curve that meets the inside lies in the inside.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace GC.Seifert

theorem segment_horizontal {c x₁ x₂ : ℝ} :
    segment ℝ ((x₁, c) : ℝ × ℝ) (x₂, c) = segment ℝ x₁ x₂ ×ˢ {c} := by
  ext ⟨x, y⟩
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap]
  constructor
  · rintro ⟨s, hs, he⟩
    simp only [AffineMap.lineMap_apply_module, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul,
      Prod.mk.injEq] at he
    refine ⟨⟨s, hs, ?_⟩, ?_⟩
    · simp only [AffineMap.lineMap_apply_module, smul_eq_mul]
      exact he.1
    · change y = c
      rw [← he.2]
      ring
  · rintro ⟨⟨s, hs, he⟩, hy⟩
    refine ⟨s, hs, ?_⟩
    simp only [AffineMap.lineMap_apply_module, smul_eq_mul] at he
    simp only [AffineMap.lineMap_apply_module, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul,
      Prod.mk.injEq]
    refine ⟨he, ?_⟩
    have : y = c := hy
    rw [this]
    ring

theorem isJordanCurve_bigonCurveSet {γ : ℝ → ℝ × ℝ} {c t₁ t₂ : ℝ} (ht : t₁ < t₂)
    (hγc : ContinuousOn γ (Icc t₁ t₂)) (h₁ : (γ t₁).2 = c) (h₂ : (γ t₂).2 = c)
    (hin : ∀ t ∈ Ioo t₁ t₂, c < (γ t).2) (hinj : InjOn γ (Icc t₁ t₂)) :
    Schoenflies.IsJordanCurve (bigonPlaneEquiv '' bigonCurveSet γ t₁ t₂) := by
  set L := bigonPlaneEquiv
  have hlam : 0 < t₂ - t₁ := sub_pos.mpr ht
  have hlin : (fun s : ℝ => t₁ + (t₂ - t₁) * s) '' unitInterval = Icc t₁ t₂ := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
    · intro ht'
      refine ⟨(t - t₁) / (t₂ - t₁), ⟨div_nonneg (by linarith [ht'.1]) hlam.le,
        (div_le_one hlam).mpr (by linarith [ht'.2])⟩, ?_⟩
      field_simp
      ring
  have hne : γ t₁ ≠ γ t₂ := fun h => ht.ne (hinj ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ h)
  have hA : Schoenflies.IsArcBetween (L '' (γ '' Icc t₁ t₂)) (L (γ t₁)) (L (γ t₂)) := by
    refine ⟨fun s => L (γ (t₁ + (t₂ - t₁) * s)), ?_, ?_, ?_, ?_, ?_⟩
    · exact L.continuous.comp_continuousOn (hγc.comp (by fun_prop)
        (fun s hs => hlin ▸ mem_image_of_mem _ hs))
    · intro s hs s' hs' he
      have h1 := hinj (hlin ▸ mem_image_of_mem _ hs) (hlin ▸ mem_image_of_mem _ hs')
        (L.injective he)
      have := mul_left_cancel₀ hlam.ne' (add_left_cancel h1)
      exact this
    · rw [← hlin, image_image, image_image]
    · simp
    · simp
  have hP : Schoenflies.IsArcBetween (L '' segment ℝ (γ t₁) (γ t₂)) (L (γ t₁)) (L (γ t₂)) := by
    rw [segment_eq_image_lineMap]
    refine ⟨fun s => L (AffineMap.lineMap (γ t₁) (γ t₂) s), ?_, ?_, ?_, ?_, ?_⟩
    · exact (L.continuous.comp (AffineMap.lineMap_continuous)).continuousOn
    · intro s _ s' _ he
      have h := L.injective he
      simp only [AffineMap.lineMap_apply_module] at h
      have h' : (s - s') • (γ t₂ - γ t₁) = 0 := by
        rw [sub_smul, smul_sub, smul_sub]
        have := congrArg (fun z => z - ((1 - s') • γ t₁ + s' • γ t₂)) h
        simp only [sub_self] at this
        rw [← this]
        module
      rcases smul_eq_zero.mp h' with h0 | h0
      · linarith
      · exact absurd (sub_eq_zero.mp h0).symm hne
    · rw [image_image]
    · simp
    · simp
  unfold bigonCurveSet
  rw [image_union]
  refine Schoenflies.isJordanCurve_union hA hP ?_
  rintro _ ⟨_, ⟨t, ht', rfl⟩, rfl⟩ ⟨q, hq, hqe⟩
  have hq' : q = γ t := L.injective hqe
  have hseg : segment ℝ (γ t₁) (γ t₂) ⊆ {p : ℝ × ℝ | p.2 = c} := by
    intro p hp
    rw [segment_eq_image_lineMap] at hp
    obtain ⟨s, -, rfl⟩ := hp
    simp only [AffineMap.lineMap_apply_module, mem_ofPred_eq, Prod.snd_add, Prod.smul_snd,
      smul_eq_mul, h₁, h₂]
    ring
  have hq2 : (γ t).2 = c := hq' ▸ hseg hq
  rcases eq_or_lt_of_le ht'.1 with h | h
  · left; rw [← h]
  · rcases eq_or_lt_of_le ht'.2 with h' | h'
    · right; rw [h']
    · exact absurd hq2 (hin t ⟨h, h'⟩).ne'

def bigonInside (γ : ℝ → ℝ × ℝ) (t₁ t₂ : ℝ) : Set (ℝ × ℝ) :=
  bigonPlaneEquiv ⁻¹' Schoenflies.inside (bigonPlaneEquiv '' bigonCurveSet γ t₁ t₂)

theorem bigonRegion_eq_union {γ : ℝ → ℝ × ℝ} {t₁ t₂ : ℝ}
    (hJ : Schoenflies.IsJordanCurve (bigonPlaneEquiv '' bigonCurveSet γ t₁ t₂)) :
    bigonRegion γ t₁ t₂ = bigonInside γ t₁ t₂ ∪ bigonCurveSet γ t₁ t₂ := by
  have hsep := Schoenflies.jordan_curve_theorem hJ
  unfold bigonRegion bigonInside
  rw [closure_eq_self_union_frontier, hsep.frontier_inside, preimage_union,
    preimage_image_eq _ bigonPlaneEquiv.injective]

theorem isOpen_bigonInside {γ : ℝ → ℝ × ℝ} {t₁ t₂ : ℝ}
    (hJ : Schoenflies.IsJordanCurve (bigonPlaneEquiv '' bigonCurveSet γ t₁ t₂)) :
    IsOpen (bigonInside γ t₁ t₂) :=
  (Schoenflies.isOpen_inside hJ.isClosed).preimage bigonPlaneEquiv.continuous

theorem disjoint_bigonInside_curveSet (γ : ℝ → ℝ × ℝ) (t₁ t₂ : ℝ) :
    Disjoint (bigonInside γ t₁ t₂) (bigonCurveSet γ t₁ t₂) := by
  rw [Set.disjoint_left]
  intro x hx hxJ
  exact hx.1 (mem_image_of_mem _ hxJ)

theorem bigonInside_subset_region (γ : ℝ → ℝ × ℝ) (t₁ t₂ : ℝ) :
    bigonInside γ t₁ t₂ ⊆ bigonRegion γ t₁ t₂ :=
  fun _ hx => subset_closure hx

theorem not_mem_bigonRegion_of_connected {γ : ℝ → ℝ × ℝ} {t₁ t₂ : ℝ}
    (hJ : Schoenflies.IsJordanCurve (bigonPlaneEquiv '' bigonCurveSet γ t₁ t₂))
    {Z : Set (ℝ × ℝ)} (hZ : IsPreconnected Z) (hZJ : Disjoint Z (bigonCurveSet γ t₁ t₂))
    (hZb : ∀ R : ℝ, ∃ z ∈ Z, R < ‖z‖) {x : ℝ × ℝ} (hx : x ∈ Z) :
    x ∉ bigonRegion γ t₁ t₂ := by
  set L := bigonPlaneEquiv
  set C := L '' bigonCurveSet γ t₁ t₂
  have hsep := Schoenflies.jordan_curve_theorem hJ
  have hLZ : IsPreconnected (L '' Z) := hZ.image _ L.continuous.continuousOn
  have hLZC : L '' Z ⊆ Cᶜ := by
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    exact Set.disjoint_left.mp hZJ hz (L.injective hwz ▸ hw)
  have hout : L x ∈ Schoenflies.outside C := by
    refine ⟨hLZC (mem_image_of_mem L hx), fun hb => ?_⟩
    have hsub := hLZ.subset_connectedComponentIn (mem_image_of_mem L hx) hLZC
    have hLZb : Bornology.IsBounded (L '' Z) := hb.subset hsub
    have hZb' : Bornology.IsBounded Z := by
      have := (ContinuousLinearMap.lipschitzWith
        (L.symm : Schoenflies.Plane →L[ℝ] ℝ × ℝ)).isBounded_image hLZb
      have he : ((L.symm : Schoenflies.Plane →L[ℝ] ℝ × ℝ) : Schoenflies.Plane → ℝ × ℝ) ''
          (L '' Z) = Z := by
        change L.symm '' (L '' Z) = Z
        simp only [image_image, L.symm_apply_apply, image_id']
      rwa [he] at this
    obtain ⟨R, hR⟩ := hZb'.subset_closedBall 0
    obtain ⟨z, hz, hzR⟩ := hZb R
    have := hR hz
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  intro hreg
  have hdisj : Disjoint (Schoenflies.outside C) (closure (Schoenflies.inside C)) :=
    (Schoenflies.disjoint_inside_outside.symm).closure_right
      (Schoenflies.isOpen_outside hsep.isClosed)
  exact Set.disjoint_left.mp hdisj hout hreg

theorem subset_bigonInside_of_connected {γ : ℝ → ℝ × ℝ} {t₁ t₂ : ℝ}
    {Z : Set (ℝ × ℝ)} (hZ : IsPreconnected Z) (hZJ : Disjoint Z (bigonCurveSet γ t₁ t₂))
    {x : ℝ × ℝ} (hx : x ∈ Z) (hxi : x ∈ bigonInside γ t₁ t₂) : Z ⊆ bigonInside γ t₁ t₂ := by
  set L := bigonPlaneEquiv
  set C := L '' bigonCurveSet γ t₁ t₂
  have hLZ : IsPreconnected (L '' Z) := hZ.image _ L.continuous.continuousOn
  have hLZC : L '' Z ⊆ Cᶜ := by
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    exact Set.disjoint_left.mp hZJ hz (L.injective hwz ▸ hw)
  have hsub := hLZ.subset_connectedComponentIn (mem_image_of_mem L hx) hLZC
  intro z hz
  exact Schoenflies.connectedComponentIn_subset_inside hxi (hsub (mem_image_of_mem L hz))

theorem norm_unbounded_of_snd {Z : Set (ℝ × ℝ)} (h : ∀ y : ℝ, ∃ z ∈ Z, y ≤ |z.2|) :
    ∀ R : ℝ, ∃ z ∈ Z, R < ‖z‖ := by
  intro R
  obtain ⟨z, hz, hzR⟩ := h (R + 1)
  exact ⟨z, hz, by
    have : |z.2| ≤ ‖z‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    linarith⟩

structure IsUpperBigon (γ : ℝ → ℝ × ℝ) (c t₁ t₂ : ℝ) : Prop where
  lt : t₁ < t₂
  cont : ContinuousOn γ (Icc t₁ t₂)
  left : (γ t₁).2 = c
  right : (γ t₂).2 = c
  above : ∀ t ∈ Ioo t₁ t₂, c < (γ t).2
  injOn : InjOn γ (Icc t₁ t₂)

namespace IsUpperBigon

variable {γ : ℝ → ℝ × ℝ} {c t₁ t₂ : ℝ}

theorem jordan (h : IsUpperBigon γ c t₁ t₂) :
    Schoenflies.IsJordanCurve (bigonPlaneEquiv '' bigonCurveSet γ t₁ t₂) :=
  isJordanCurve_bigonCurveSet h.lt h.cont h.left h.right h.above h.injOn

theorem segment_eq (h : IsUpperBigon γ c t₁ t₂) :
    segment ℝ (γ t₁) (γ t₂) = segment ℝ (γ t₁).1 (γ t₂).1 ×ˢ {c} := by
  have e1 : γ t₁ = ((γ t₁).1, c) := Prod.ext rfl h.left
  have e2 : γ t₂ = ((γ t₂).1, c) := Prod.ext rfl h.right
  rw [← segment_horizontal, ← e1, ← e2]

theorem curveSet_snd_ge (h : IsUpperBigon γ c t₁ t₂) :
    ∀ p ∈ bigonCurveSet γ t₁ t₂, c ≤ p.2 := by
  rintro p (⟨t, ht, rfl⟩ | hp)
  · rcases eq_or_lt_of_le ht.1 with h' | h'
    · rw [← h', h.left]
    · rcases eq_or_lt_of_le ht.2 with h'' | h''
      · rw [h'', h.right]
      · exact (h.above t ⟨h', h''⟩).le
  · rw [h.segment_eq] at hp
    exact hp.2.symm.le

theorem curveSet_snd_eq (h : IsUpperBigon γ c t₁ t₂) {p : ℝ × ℝ}
    (hp : p ∈ bigonCurveSet γ t₁ t₂) (hc : p.2 = c) : p ∈ segment ℝ (γ t₁) (γ t₂) := by
  rcases hp with ⟨t, ht, rfl⟩ | hp
  · rcases eq_or_lt_of_le ht.1 with h' | h'
    · rw [← h']; exact left_mem_segment ℝ _ _
    · rcases eq_or_lt_of_le ht.2 with h'' | h''
      · rw [h'']; exact right_mem_segment ℝ _ _
      · exact absurd hc (h.above t ⟨h', h''⟩).ne'
  · exact hp

theorem region_snd_ge (h : IsUpperBigon γ c t₁ t₂) :
    ∀ p ∈ bigonRegion γ t₁ t₂, c ≤ p.2 := by
  intro p hp
  by_contra hlt
  push Not at hlt
  refine not_mem_bigonRegion_of_connected h.jordan (Z := {q : ℝ × ℝ | q.2 < c})
    ((convex_halfSpace_lt (f := Prod.snd) ⟨fun _ _ => rfl, fun _ _ => rfl⟩ c).isPreconnected)
    ?_ ?_ hlt hp
  · rw [Set.disjoint_left]
    intro q hq hqJ
    exact absurd (h.curveSet_snd_ge q hqJ) (not_le.mpr hq)
  · refine norm_unbounded_of_snd fun y => ⟨(0, -(|c| + |y| + 1)), ?_, ?_⟩
    · change -(|c| + |y| + 1) < c
      have := neg_abs_le c
      have := abs_nonneg y
      linarith
    · simp only
      rw [abs_neg, abs_of_pos (by positivity)]
      have := le_abs_self y
      have := abs_nonneg c
      linarith

theorem region_snd_le (h : IsUpperBigon γ c t₁ t₂) {M : ℝ}
    (hM : ∀ t ∈ Icc t₁ t₂, (γ t).2 ≤ M) : ∀ p ∈ bigonRegion γ t₁ t₂, p.2 ≤ M := by
  have hcM : c ≤ M := h.left ▸ hM t₁ ⟨le_rfl, h.lt.le⟩
  intro p hp
  by_contra hlt
  push Not at hlt
  refine not_mem_bigonRegion_of_connected h.jordan (Z := {q : ℝ × ℝ | M < q.2})
    ((convex_halfSpace_gt (f := Prod.snd) ⟨fun _ _ => rfl, fun _ _ => rfl⟩ M).isPreconnected)
    ?_ ?_ hlt hp
  · rw [Set.disjoint_left]
    rintro q hq (⟨t, ht, rfl⟩ | hqJ)
    · exact absurd (hM t ht) (not_le.mpr hq)
    · rw [h.segment_eq] at hqJ
      have : q.2 = c := hqJ.2
      change M < q.2 at hq
      linarith
  · refine norm_unbounded_of_snd fun y => ⟨(0, |M| + |y| + 1), ?_, ?_⟩
    · change M < |M| + |y| + 1
      have := le_abs_self M
      have := abs_nonneg y
      linarith
    · simp only
      rw [abs_of_pos (by positivity)]
      have := abs_nonneg M
      have := le_abs_self y
      linarith

theorem region_line (h : IsUpperBigon γ c t₁ t₂) {p : ℝ × ℝ} (hp : p ∈ bigonRegion γ t₁ t₂)
    (hc : p.2 = c) : p ∈ segment ℝ (γ t₁) (γ t₂) := by
  set x₁ := (γ t₁).1
  set x₂ := (γ t₂).1
  rw [h.segment_eq, segment_eq_uIcc]
  refine ⟨?_, hc⟩
  have hlow : IsPreconnected {q : ℝ × ℝ | q.2 < c} :=
    (convex_halfSpace_lt (f := Prod.snd) ⟨fun _ _ => rfl, fun _ _ => rfl⟩ c).isPreconnected
  have hunb (R : Set ℝ) : ∀ y : ℝ, ∃ z ∈ {q : ℝ × ℝ | q.2 < c} ∪ R ×ˢ {c}, y ≤ |z.2| := by
    intro y
    refine ⟨(0, -(|c| + |y| + 1)), Or.inl ?_, ?_⟩
    · change -(|c| + |y| + 1) < c
      have := neg_abs_le c
      have := abs_nonneg y
      linarith
    · simp only
      rw [abs_neg, abs_of_pos (by positivity)]
      have := le_abs_self y
      have := abs_nonneg c
      linarith
  have hconn (R : Set ℝ) : IsPreconnected ({q : ℝ × ℝ | q.2 < c} ∪ R ×ˢ {c}) := by
    refine hlow.subset_closure subset_union_left ?_
    rintro q (hq | ⟨-, hq⟩)
    · exact subset_closure hq
    · have hq' : q.2 = c := hq
      rw [Metric.mem_closure_iff]
      intro ε hε
      refine ⟨(q.1, c - ε / 2), ?_, ?_⟩
      · change c - ε / 2 < c
        linarith
      · rw [Prod.dist_eq, dist_self, Real.dist_eq, hq']
        rw [show c - (c - ε / 2) = ε / 2 by ring, abs_of_pos (half_pos hε)]
        simp only [max_lt_iff]
        exact ⟨hε, half_lt_self hε⟩
  have hdisj (R : Set ℝ) (hR : Disjoint R (uIcc x₁ x₂)) :
      Disjoint ({q : ℝ × ℝ | q.2 < c} ∪ R ×ˢ {c}) (bigonCurveSet γ t₁ t₂) := by
    rw [Set.disjoint_left]
    rintro q (hq | ⟨hq1, hq2⟩) hqJ
    · exact absurd (h.curveSet_snd_ge q hqJ) (not_le.mpr hq)
    · have hq2' : q.2 = c := hq2
      have hs := h.curveSet_snd_eq hqJ hq2'
      rw [h.segment_eq, segment_eq_uIcc] at hs
      exact Set.disjoint_left.mp hR hq1 hs.1
  by_contra hnot
  rw [uIcc, mem_Icc, not_and_or, not_le, not_le] at hnot
  rcases hnot with hlo | hhi
  · refine not_mem_bigonRegion_of_connected h.jordan (hconn (Iio (min x₁ x₂)))
      (hdisj _ ?_) (norm_unbounded_of_snd (hunb _)) (Or.inr ⟨hlo, hc⟩) hp
    rw [Set.disjoint_left]
    intro y hy hy'
    rw [uIcc, mem_Icc] at hy'
    exact absurd hy'.1 (not_le.mpr (mem_Iio.mp hy))
  · refine not_mem_bigonRegion_of_connected h.jordan (hconn (Ioi (max x₁ x₂)))
      (hdisj _ ?_) (norm_unbounded_of_snd (hunb _)) (Or.inr ⟨hhi, hc⟩) hp
    rw [Set.disjoint_left]
    intro y hy hy'
    rw [uIcc, mem_Icc] at hy'
    exact absurd hy'.2 (not_le.mpr (mem_Ioi.mp hy))

theorem upper_halfBall (h : IsUpperBigon γ c t₁ t₂) {x : ℝ}
    (hx₁ : min (γ t₁).1 (γ t₂).1 < x) (hx₂ : x < max (γ t₁).1 (γ t₂).1) :
    ∃ r > 0, ∀ q : ℝ × ℝ, dist q (x, c) < r → c < q.2 → q ∈ bigonInside γ t₁ t₂ := by
  set x₁ := (γ t₁).1
  set x₂ := (γ t₂).1
  set p : ℝ × ℝ := (x, c)
  have harc : IsCompact (γ '' Icc t₁ t₂) := isCompact_Icc.image_of_continuousOn h.cont
  have hparc : p ∉ γ '' Icc t₁ t₂ := by
    rintro ⟨t, ht, hte⟩
    have hs := h.curveSet_snd_eq (Or.inl ⟨t, ht, rfl⟩) (by rw [hte])
    have hpJ : p ∈ segment ℝ (γ t₁) (γ t₂) := hte ▸ hs
    rcases eq_or_lt_of_le ht.1 with h' | h'
    · rw [← h'] at hte
      have : x = x₁ := (congrArg Prod.fst hte).symm
      rw [this] at hx₁ hx₂
      rcases le_total x₁ x₂ with hle | hle
      · rw [min_eq_left hle] at hx₁; exact lt_irrefl _ hx₁
      · rw [max_eq_left hle] at hx₂; exact lt_irrefl _ hx₂
    · rcases eq_or_lt_of_le ht.2 with h'' | h''
      · rw [h''] at hte
        have : x = x₂ := (congrArg Prod.fst hte).symm
        rw [this] at hx₁ hx₂
        rcases le_total x₁ x₂ with hle | hle
        · rw [max_eq_right hle] at hx₂; exact lt_irrefl _ hx₂
        · rw [min_eq_right hle] at hx₁; exact lt_irrefl _ hx₁
      · have := h.above t ⟨h', h''⟩
        rw [hte] at this
        exact lt_irrefl _ this
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.isOpen_iff.mp harc.isClosed.isOpen_compl p hparc
  set r := min r₁ (min (x - min x₁ x₂) (max x₁ x₂ - x)) with hrdef
  have hr : 0 < r := lt_min hr₁ (lt_min (by linarith) (by linarith))
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hr₂ : r ≤ x - min x₁ x₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hr₃ : r ≤ max x₁ x₂ - x := (min_le_right _ _).trans (min_le_right _ _)
  have hline : ∀ q ∈ ball p r, q.2 = c → q ∈ bigonCurveSet γ t₁ t₂ := by
    intro q hq hqc
    right
    rw [h.segment_eq, segment_eq_uIcc]
    refine ⟨?_, hqc⟩
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq] at hq
    rw [uIcc, mem_Icc, abs_lt] at *
    constructor <;> linarith [hq.1.1, hq.1.2]
  have hnoarc : ∀ q ∈ ball p r, q ∉ γ '' Icc t₁ t₂ := fun q hq hqa =>
    hball₁ (ball_subset_ball hrr₁ hq) hqa
  have hJ := h.jordan
  have hsep := Schoenflies.jordan_curve_theorem hJ
  have hpJ : bigonPlaneEquiv p ∈ bigonPlaneEquiv '' bigonCurveSet γ t₁ t₂ :=
    mem_image_of_mem _ (hline p (mem_ball_self hr) rfl)
  rw [← hsep.frontier_inside] at hpJ
  have hnhds : bigonPlaneEquiv '' ball p r ∈ 𝓝 (bigonPlaneEquiv p) :=
    (bigonPlaneEquiv.toHomeomorph.isOpenMap _ isOpen_ball).mem_nhds (mem_image_of_mem _
      (mem_ball_self hr))
  obtain ⟨_, ⟨q, hqB, rfl⟩, hqi⟩ :=
    mem_closure_iff_nhds.mp (frontier_subset_closure hpJ) _ hnhds
  have hqi' : q ∈ bigonInside γ t₁ t₂ := hqi
  have hq2 : c < q.2 := by
    rcases lt_trichotomy q.2 c with hlt | heq | hgt
    · exact absurd (h.region_snd_ge q (bigonInside_subset_region _ _ _ hqi')) (not_le.mpr hlt)
    · exact absurd (hline q hqB heq)
        (Set.disjoint_left.mp (disjoint_bigonInside_curveSet γ t₁ t₂) hqi')
    · exact hgt
  have hBup : IsPreconnected (ball p r ∩ {z : ℝ × ℝ | c < z.2}) :=
    ((convex_ball p r).inter (convex_halfSpace_gt (f := Prod.snd)
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩ c)).isPreconnected
  have hBdisj : Disjoint (ball p r ∩ {z : ℝ × ℝ | c < z.2}) (bigonCurveSet γ t₁ t₂) := by
    rw [Set.disjoint_left]
    rintro z ⟨hzB, hzc⟩ (hza | hzs)
    · exact hnoarc z hzB hza
    · rw [h.segment_eq] at hzs
      have : z.2 = c := hzs.2
      change c < z.2 at hzc
      linarith
  have hsub := subset_bigonInside_of_connected hBup hBdisj ⟨hqB, hq2⟩ hqi'
  exact ⟨r, hr, fun z hz hzc => hsub ⟨hz, hzc⟩⟩

end IsUpperBigon

end GC.Seifert
