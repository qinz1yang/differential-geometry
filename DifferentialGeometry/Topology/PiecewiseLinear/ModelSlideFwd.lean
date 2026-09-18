import DifferentialGeometry.Topology.PiecewiseLinear.ModelSlideLong

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def slideMapFwd (d R : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.1 + slideAmountLong d R p, p.2.1, p.2.2)

def slideEndpointHalfSpace : Set (ℝ × ℝ × ℝ) := {p | 0 ≤ p.1}

def slideEndpointPlane : Set (ℝ × ℝ × ℝ) := {p | p.1 = 0}

theorem slideMapFwd_fst (d R : ℝ) (p : ℝ × ℝ × ℝ) :
    (slideMapFwd d R p).1 = p.1 + slideAmountLong d R p := rfl

theorem slideMapFwd_snd (d R : ℝ) (p : ℝ × ℝ × ℝ) : (slideMapFwd d R p).2 = p.2 := rfl

theorem slideMapFwd_eq_self_iff {d R : ℝ} {p : ℝ × ℝ × ℝ} :
    slideMapFwd d R p = p ↔ slideAmountLong d R p = 0 := by
  constructor
  · intro h
    have hfst := congrArg Prod.fst h
    rw [slideMapFwd_fst] at hfst
    linarith
  · intro h
    simp only [slideMapFwd, h, add_zero]

theorem slideMapFwd_eq_self_of_width {d R : ℝ} {p : ℝ × ℝ × ℝ} (hd : 0 ≤ d)
    (h : 1 ≤ |p.2.1| + |p.2.2|) : slideMapFwd d R p = p :=
  slideMapFwd_eq_self_iff.mpr (slideAmountLong_eq_zero_of_width hd h)

theorem slideMapFwd_eq_self_of_taper {d R : ℝ} {p : ℝ × ℝ × ℝ} (h : R ≤ |p.1|) :
    slideMapFwd d R p = p :=
  slideMapFwd_eq_self_iff.mpr (slideAmountLong_eq_zero_of_taper h)

theorem slideAmountLong_le_add' {d R : ℝ} {p q : ℝ × ℝ × ℝ} (hyz : p.2 = q.2) (hpq : p.1 ≤ q.1) :
    slideAmountLong d R p ≤ slideAmountLong d R q + (q.1 - p.1) / 2 := by
  have hc : 0 ≤ (q.1 - p.1) / 2 := by linarith
  have hw : slideWidthScaled d p = slideWidthScaled d q := by
    simp only [slideWidthScaled, hyz]
  have hab : |q.1| - |p.1| ≤ q.1 - p.1 := by
    have h := abs_sub_abs_le_abs_sub q.1 p.1
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ q.1 - p.1)] at h
  have hT : slideTaperRad R p ≤ slideTaperRad R q + (q.1 - p.1) / 2 := by
    simp only [slideTaperRad]
    linarith
  have hmin : min (slideWidthScaled d p) (slideTaperRad R p) ≤
      min (slideWidthScaled d q) (slideTaperRad R q) + (q.1 - p.1) / 2 := by
    rcases le_total (slideWidthScaled d q) (slideTaperRad R q) with h | h
    · rw [min_eq_left h]
      exact le_trans (min_le_left _ _) (by rw [hw]; linarith)
    · rw [min_eq_right h]
      exact le_trans (min_le_right _ _) (by linarith)
  have hmax : min (slideWidthScaled d q) (slideTaperRad R q) ≤ slideAmountLong d R q :=
    le_max_right _ _
  refine max_le (by linarith [slideAmountLong_nonneg d R q]) ?_
  linarith

theorem injective_slideMapFwd {d R : ℝ} : Function.Injective (slideMapFwd d R) := by
  intro p q hpq
  have h2 : p.2 = q.2 := by
    have h := congrArg Prod.snd hpq
    exact h
  have h1 : p.1 + slideAmountLong d R p = q.1 + slideAmountLong d R q := by
    have h := congrArg Prod.fst hpq
    exact h
  have hx : p.1 = q.1 := by
    rcases le_total p.1 q.1 with h | h
    · have hle := slideAmountLong_le_add' (d := d) (R := R) h2 h
      linarith
    · have hle := slideAmountLong_le_add' (d := d) (R := R) h2.symm h
      linarith
  exact Prod.ext hx h2

theorem isPiecewiseAffineOn_slideAmountLong {d R : ℝ} :
    IsPiecewiseAffineOn (slideAmountLong d R) univ := by
  have hid : IsPiecewiseAffineOn (id : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ) univ :=
    (IsLocallyPolyhedral.of_isOpen isOpen_univ).isPiecewiseAffineOn_id
  have hx : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.1) univ :=
    hid.affine_comp (LinearMap.fst ℝ ℝ (ℝ × ℝ)).toAffineMap
  have hy : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.1) univ :=
    hid.affine_comp ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap
  have hz : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.2) univ :=
    hid.affine_comp ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap
  have hconst : ∀ c : ℝ, IsPiecewiseAffineOn (fun _ : ℝ × ℝ × ℝ => c) univ := by
    intro c
    exact hid.affine_comp (AffineMap.const ℝ (ℝ × ℝ × ℝ) c)
  have hwidth : IsPiecewiseAffineOn (slideWidthScaled d) univ := by
    have h := (((hconst 1).add (hy.abs.affine_comp (-AffineMap.id ℝ ℝ))).add
      (hz.abs.affine_comp (-AffineMap.id ℝ ℝ))).affine_comp (scaleMap d)
    refine h.congr fun p _ => ?_
    change slideWidthScaled d p = scaleMap d (1 + -|p.2.1| + -|p.2.2|)
    rw [scaleMap_apply, slideWidthScaled]
    ring
  have htaper : IsPiecewiseAffineOn (slideTaperRad R) univ := by
    have h := ((hconst R).add (hx.abs.affine_comp (-AffineMap.id ℝ ℝ))).affine_comp halfMap
    refine h.congr fun p _ => ?_
    change slideTaperRad R p = halfMap (R + -|p.1|)
    rw [halfMap_apply, slideTaperRad]
    ring
  exact ((hconst 0).max (hwidth.min htaper)).congr fun _ _ => rfl

theorem isPiecewiseAffineOn_slideMapFwd {d R : ℝ} :
    IsPiecewiseAffineOn (slideMapFwd d R) univ := by
  have hid : IsPiecewiseAffineOn (id : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ) univ :=
    (IsLocallyPolyhedral.of_isOpen isOpen_univ).isPiecewiseAffineOn_id
  have hx : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.1) univ :=
    hid.affine_comp (LinearMap.fst ℝ ℝ (ℝ × ℝ)).toAffineMap
  have hy : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.1) univ :=
    hid.affine_comp ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap
  have hz : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.2) univ :=
    hid.affine_comp ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap
  exact (hx.add isPiecewiseAffineOn_slideAmountLong).prod_mk (hy.prod_mk hz)

theorem continuous_slideMapFwd {d R : ℝ} : Continuous (slideMapFwd d R) := by
  rw [← continuousOn_univ]
  exact isPiecewiseAffineOn_slideMapFwd.continuousOn

theorem surjective_slideMapFwd {d R : ℝ} (hR : 0 ≤ R) :
    Function.Surjective (slideMapFwd d R) := by
  intro w
  have hcont : Continuous fun x : ℝ => (slideMapFwd d R (x, w.2.1, w.2.2)).1 :=
    continuous_fst.comp (continuous_slideMapFwd.comp (by fun_prop))
  rcases le_or_gt |w.1| R with hle | hgt
  · have h3 : (slideMapFwd d R ((R : ℝ), w.2.1, w.2.2)).1 = R := by
      rw [slideMapFwd_eq_self_of_taper (p := ((R : ℝ), w.2.1, w.2.2))
        (by simp [abs_of_nonneg hR])]
    have hm3 : (slideMapFwd d R ((-R : ℝ), w.2.1, w.2.2)).1 = -R := by
      rw [slideMapFwd_eq_self_of_taper (p := ((-R : ℝ), w.2.1, w.2.2))
        (by simp [abs_of_nonneg hR])]
    have hmem : w.1 ∈ Icc ((slideMapFwd d R ((-R : ℝ), w.2.1, w.2.2)).1)
        ((slideMapFwd d R ((R : ℝ), w.2.1, w.2.2)).1) := by
      rw [h3, hm3]
      exact abs_le.mp hle
    obtain ⟨x, -, hgx⟩ :=
      intermediate_value_Icc (by linarith : (-R : ℝ) ≤ R) hcont.continuousOn hmem
    exact ⟨(x, w.2.1, w.2.2), Prod.ext hgx rfl⟩
  · refine ⟨(w.1, w.2.1, w.2.2), ?_⟩
    rw [slideMapFwd_eq_self_of_taper (p := (w.1, w.2.1, w.2.2)) (by simpa using hgt.le)]

theorem bijective_slideMapFwd {d R : ℝ} (hR : 0 ≤ R) : Function.Bijective (slideMapFwd d R) :=
  ⟨injective_slideMapFwd, surjective_slideMapFwd hR⟩

theorem mapsTo_slideMapFwd_prod {d R : ℝ} (T : Set (ℝ × ℝ)) :
    MapsTo (slideMapFwd d R) {p : ℝ × ℝ × ℝ | p.2 ∈ T} {p : ℝ × ℝ × ℝ | p.2 ∈ T} :=
  fun _ hp => hp

theorem bijOn_slideMapFwd_prod {d R : ℝ} (hR : 0 ≤ R) (T : Set (ℝ × ℝ)) :
    BijOn (slideMapFwd d R) {p : ℝ × ℝ × ℝ | p.2 ∈ T} {p : ℝ × ℝ × ℝ | p.2 ∈ T} := by
  refine ⟨mapsTo_slideMapFwd_prod T, injective_slideMapFwd.injOn, ?_⟩
  intro w hw
  obtain ⟨p, hp⟩ := surjective_slideMapFwd (d := d) hR w
  refine ⟨p, ?_, hp⟩
  have h2 : p.2 = w.2 := by
    rw [← slideMapFwd_snd d R p, hp]
  change p.2 ∈ T
  rw [h2]
  exact hw

theorem eqOn_slideMapFwd_id_compl {d R : ℝ} (hd : 0 ≤ d) :
    EqOn (slideMapFwd d R) id (slideSupportLong R)ᶜ := by
  intro p hp
  simp only [slideSupportLong, mem_compl_iff, mem_ofPred_eq, not_and_or, not_le] at hp
  rcases hp with h | h
  · exact slideMapFwd_eq_self_of_width hd h.le
  · exact slideMapFwd_eq_self_of_taper h.le

theorem mapsTo_slideMapFwd_slideSupportLong {d R : ℝ} :
    MapsTo (slideMapFwd d R) (slideSupportLong R) (slideSupportLong R) := by
  rintro p ⟨h1, h2⟩
  obtain ⟨hlo, hhi⟩ := abs_le.mp h2
  have hnn := slideAmountLong_nonneg d R p
  have hmax : slideAmountLong d R p ≤ max 0 (slideTaperRad R p) :=
    max_le_max (le_refl 0) (min_le_right _ _)
  have hself := le_abs_self p.1
  have hle : slideAmountLong d R p ≤ R - p.1 := by
    refine le_trans hmax (max_le (by linarith) ?_)
    simp only [slideTaperRad]
    linarith
  refine ⟨h1, ?_⟩
  have hfst : (slideMapFwd d R p).1 = p.1 + slideAmountLong d R p := rfl
  rw [hfst, abs_le]
  constructor <;> linarith

theorem mapsTo_slideMapFwd_of_subset {d R : ℝ} (hd : 0 ≤ d) {T : Set (ℝ × ℝ × ℝ)}
    (hT : slideSupportLong R ⊆ T) : MapsTo (slideMapFwd d R) T T := by
  intro p hp
  by_cases hC : p ∈ slideSupportLong R
  · exact hT (mapsTo_slideMapFwd_slideSupportLong hC)
  · rw [eqOn_slideMapFwd_id_compl hd hC]
    exact hp

theorem mapsTo_slideMapFwd_slideEndpointHalfSpace {d R : ℝ} :
    MapsTo (slideMapFwd d R) slideEndpointHalfSpace slideEndpointHalfSpace := by
  intro p hp
  have hx : (0 : ℝ) ≤ p.1 := hp
  have hnn := slideAmountLong_nonneg d R p
  change (0 : ℝ) ≤ (slideMapFwd d R p).1
  rw [slideMapFwd_fst]
  linarith

theorem slideMapFwd_mem_slideEndpointPlane_iff {d R : ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∈ slideEndpointHalfSpace) :
    slideMapFwd d R p ∈ slideEndpointPlane ↔
      p ∈ slideEndpointPlane ∧ slideMapFwd d R p = p := by
  have hx : (0 : ℝ) ≤ p.1 := hp
  have hnn := slideAmountLong_nonneg d R p
  constructor
  · intro h
    have h0 : p.1 + slideAmountLong d R p = 0 := h
    have hx0 : p.1 = 0 := by linarith
    have ha0 : slideAmountLong d R p = 0 := by linarith
    exact ⟨hx0, slideMapFwd_eq_self_iff.mpr ha0⟩
  · rintro ⟨hx0, hfix⟩
    change (slideMapFwd d R p).1 = 0
    rw [hfix]
    exact hx0

theorem slideAmountLong_eq_zero_iff_of_fst_eq_zero {d R : ℝ} {p : ℝ × ℝ × ℝ} (hd : 0 < d)
    (hR : 0 < R) (hp : p.1 = 0) : slideAmountLong d R p = 0 ↔ 1 ≤ |p.2.1| + |p.2.2| := by
  have htaper : slideTaperRad R p = R / 2 := by
    simp only [slideTaperRad, hp, abs_zero, sub_zero]
  constructor
  · intro h
    rcases le_or_gt 1 (|p.2.1| + |p.2.2|) with hcon | hcon
    · exact hcon
    · exfalso
      have hw : 0 < slideWidthScaled d p := by
        simp only [slideWidthScaled]
        exact mul_pos hd (by linarith)
      have hmin : 0 < min (slideWidthScaled d p) (slideTaperRad R p) :=
        lt_min hw (by rw [htaper]; linarith)
      have hpos : 0 < slideAmountLong d R p := by
        refine lt_of_lt_of_le hmin ?_
        exact le_max_right _ _
      linarith
  · intro h
    exact slideAmountLong_eq_zero_of_width hd.le h

theorem slideMapFwd_eq_self_iff_of_fst_eq_zero {d R : ℝ} {p : ℝ × ℝ × ℝ} (hd : 0 < d)
    (hR : 0 < R) (hp : p.1 = 0) : slideMapFwd d R p = p ↔ 1 ≤ |p.2.1| + |p.2.2| :=
  slideMapFwd_eq_self_iff.trans (slideAmountLong_eq_zero_iff_of_fst_eq_zero hd hR hp)

theorem not_mapsTo_slideMapFwd_slideEndpointPlane {d R : ℝ} (hd : 0 < d) (hR : 0 < R) :
    ¬MapsTo (slideMapFwd d R) slideEndpointPlane slideEndpointPlane := by
  intro hmaps
  have hplane : ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ slideEndpointPlane := rfl
  have hhalf : ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ slideEndpointHalfSpace := by
    change (0 : ℝ) ≤ (0 : ℝ)
    exact le_rfl
  have hfix := (slideMapFwd_mem_slideEndpointPlane_iff (d := d) (R := R) hhalf).mp (hmaps hplane)
  have hw := (slideMapFwd_eq_self_iff_of_fst_eq_zero hd hR
    (p := ((0 : ℝ), (0 : ℝ), (0 : ℝ))) rfl).mp hfix.2
  norm_num at hw

theorem le_slideMapFwd_fst_of_mem_axis {d R : ℝ} {p : ℝ × ℝ × ℝ} (hd : 0 ≤ d)
    (hy : p.2.1 = 0) (hz : p.2.2 = 0) (hx : 0 ≤ p.1) :
    min d (R / 2) ≤ (slideMapFwd d R p).1 := by
  have hw : slideWidthScaled d p = d := by
    simp only [slideWidthScaled, hy, hz, abs_zero]
    ring
  rw [slideMapFwd_fst]
  rcases le_or_gt R p.1 with hcase | hcase
  · have hhalf : min d (R / 2) ≤ R / 2 := min_le_right _ _
    have hnn := slideAmountLong_nonneg d R p
    linarith
  · have hT : slideTaperRad R p = (R - p.1) / 2 := by
      simp only [slideTaperRad, abs_of_nonneg hx]
    have hamount : slideAmountLong d R p = min d ((R - p.1) / 2) := by
      simp only [slideAmountLong, hw, hT]
      exact max_eq_right (le_min hd (by linarith))
    rw [hamount]
    rcases le_total d ((R - p.1) / 2) with h | h
    · rw [min_eq_left h]
      have hdle := min_le_left d (R / 2)
      linarith
    · rw [min_eq_right h]
      have hRle := min_le_right d (R / 2)
      linarith

theorem not_surjOn_slideMapFwd_slideEndpointHalfSpace {d R : ℝ} (hd : 0 < d) (hR : 0 < R) :
    ¬SurjOn (slideMapFwd d R) slideEndpointHalfSpace slideEndpointHalfSpace := by
  intro hsurj
  have htpos : 0 < min d (R / 2) := lt_min hd (by linarith)
  have hw : (min d (R / 2) / 2, (0 : ℝ), (0 : ℝ)) ∈ slideEndpointHalfSpace := by
    change (0 : ℝ) ≤ min d (R / 2) / 2
    linarith
  obtain ⟨p, hp, hpe⟩ := hsurj hw
  have hsnd : p.2 = ((0 : ℝ), (0 : ℝ)) := by
    rw [← slideMapFwd_snd d R p, hpe]
  have hy : p.2.1 = 0 := by rw [hsnd]
  have hz : p.2.2 = 0 := by rw [hsnd]
  have hkey := le_slideMapFwd_fst_of_mem_axis (d := d) (R := R) hd.le hy hz hp
  rw [hpe] at hkey
  have hkey' : min d (R / 2) ≤ min d (R / 2) / 2 := hkey
  linarith

theorem disjoint_slideMapFwd_image_slideBandA {d R a b c : ℝ} (hd : 0 ≤ d)
    (hR : c + 2 * d ≤ R) (hb : b < d) :
    Disjoint (slideMapFwd d R '' slideBandA c) (slideBandQ a b) := by
  rw [Set.disjoint_left]
  rintro w ⟨p, ⟨hz, -, hx0, hx1⟩, rfl⟩ ⟨hy, -, -, hw2⟩
  have hpy : p.2.1 = 0 := hy
  have hwidth : slideWidthScaled d p = d := by
    simp only [slideWidthScaled, hpy, hz, abs_zero]
    ring
  have htaper : d ≤ slideTaperRad R p := by
    simp only [slideTaperRad, abs_of_nonneg hx0]
    linarith
  have hamount : slideAmountLong d R p = d := by
    simp only [slideAmountLong, hwidth, min_eq_left htaper, max_eq_right hd]
  have hfirst : (slideMapFwd d R p).1 = p.1 + d := by
    simp only [slideMapFwd, hamount]
  rw [hfirst] at hw2
  linarith

theorem not_disjoint_image_slideBandA_of_origin_fixed {a b c : ℝ}
    {h : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ} (hc : 0 ≤ c) (ha : a ≤ 0) (hb : 0 ≤ b)
    (hfix : h ((0 : ℝ), (0 : ℝ), (0 : ℝ)) = ((0 : ℝ), (0 : ℝ), (0 : ℝ))) :
    ¬Disjoint (h '' slideBandA c) (slideBandQ a b) := by
  intro hdisj
  have hA : ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ slideBandA c := by
    refine ⟨rfl, ?_, ?_⟩
    · simp only [abs_zero]
      exact zero_le_one
    · rw [Set.mem_Icc]
      exact ⟨le_rfl, hc⟩
  have hQ : ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ slideBandQ a b := by
    refine ⟨rfl, ?_, ?_⟩
    · simp only [abs_zero]
      exact zero_le_one
    · rw [Set.mem_Icc]
      exact ⟨ha, hb⟩
  exact Set.disjoint_left.mp hdisj ⟨_, hA, hfix⟩ hQ

theorem exists_slideMapFwd_parameters (b c : ℝ) :
    ∃ d R : ℝ, 0 < d ∧ b < d ∧ c + 2 * d ≤ R :=
  ⟨max (b + 1) 1, c + 2 * max (b + 1) 1,
    lt_of_lt_of_le one_pos (le_max_right _ _),
    lt_of_lt_of_le (by linarith) (le_max_left _ _), le_refl _⟩

end DifferentialGeometry.Topology.PiecewiseLinear
