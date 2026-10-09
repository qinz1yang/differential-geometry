import DifferentialGeometry.Geometry.Metric.Approximation.CompactComparison

open Set Metric

namespace GromovHausdorff

universe u v

variable {X : Type u} {Y : Type v}
variable [MetricSpace X] [MetricSpace Y]

noncomputable def correspondenceDistortion [CompactSpace X] [CompactSpace Y]
    (r : X → Y → Prop) : ℝ :=
  sSup {d : ℝ | ∃ x y x' y', r x y ∧ r x' y' ∧ d = |dist x x' - dist y y'|}

variable [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]

omit [Nonempty X] [Nonempty Y] in
private theorem bddAbove_correspondence_distances (r : X → Y → Prop) :
    BddAbove {d : ℝ | ∃ x y x' y', r x y ∧ r x' y' ∧ d = |dist x x' - dist y y'|} := by
  refine ⟨diam (univ : Set X) + diam (univ : Set Y), ?_⟩
  rintro d ⟨x, y, x', y', _, _, rfl⟩
  have hx := dist_le_diam_of_mem (s := (univ : Set X)) isCompact_univ.isBounded
    (mem_univ x) (mem_univ x')
  have hy := dist_le_diam_of_mem (s := (univ : Set Y)) isCompact_univ.isBounded
    (mem_univ y) (mem_univ y')
  apply abs_le.mpr
  constructor <;> linarith [dist_nonneg (x := x) (y := x'), dist_nonneg (x := y) (y := y')]

omit [Nonempty X] [Nonempty Y] in
theorem dist_error_le_correspondenceDistortion (r : X → Y → Prop)
    {x x' : X} {y y' : Y} (hxy : r x y) (hx'y' : r x' y') :
    |dist x x' - dist y y'| ≤ correspondenceDistortion r :=
  le_csSup (bddAbove_correspondence_distances r) ⟨x, y, x', y', hxy, hx'y', rfl⟩

omit [Nonempty Y] in
theorem correspondenceDistortion_le (r : X → Y → Prop)
    (hleft : ∀ x, ∃ y, r x y) {D : ℝ}
    (hdist : ∀ x y x' y', r x y → r x' y' → |dist x x' - dist y y'| ≤ D) :
    correspondenceDistortion r ≤ D := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨y, hxy⟩ := hleft x
  apply csSup_le (show {d : ℝ | ∃ x y x' y', r x y ∧ r x' y' ∧
    d = |dist x x' - dist y y'|}.Nonempty from
    ⟨0, x, y, x, y, hxy, hxy, by simp⟩)
  rintro d ⟨x, y, x', y', hxy, hx'y', rfl⟩
  exact hdist x y x' y' hxy hx'y'

theorem ghDist_le_half_of_correspondence (r : X → Y → Prop)
    (hleft : ∀ x, ∃ y, r x y) (hright : ∀ y, ∃ x, r x y) {D : ℝ}
    (hdist : ∀ x y x' y', r x y → r x' y' →
      |dist x x' - dist y y'| ≤ D) :
    ghDist X Y ≤ D / 2 := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨y₀, h₀⟩ := hleft x₀
  have hD : 0 ≤ D := by simpa using hdist x₀ y₀ x₀ y₀ h₀ h₀
  let Z := {xy : X × Y // r xy.1 xy.2}
  let : Nonempty Z := ⟨⟨(x₀, y₀), h₀⟩⟩
  let l : Z → X := fun a => a.val.1
  let s : Z → Y := fun a => a.val.2
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hc : 0 < D / 2 + δ := by linarith
  have hdist' : ∀ a b : Z, |dist (l a) (l b) - dist (s a) (s b)| ≤
      2 * (D / 2 + δ) := by
    intro a b
    have h := hdist a.val.1 a.val.2 b.val.1 b.val.2 a.property b.property
    dsimp [l, s]
    linarith
  let : MetricSpace (X ⊕ Y) := glueMetricApprox l s (D / 2 + δ) hc hdist'
  have hl : Isometry (Sum.inl : X → X ⊕ Y) := Isometry.of_dist_eq fun _ _ => rfl
  have hs : Isometry (Sum.inr : Y → X ⊕ Y) := Isometry.of_dist_eq fun _ _ => rfl
  apply (ghDist_le_hausdorffDist hl hs).trans
  apply hausdorffDist_le_of_mem_dist hc.le
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hxy⟩ := hleft x
    refine ⟨Sum.inr y, mem_range_self y, ?_⟩
    exact (glueDist_glued_points l s (D / 2 + δ) ⟨(x, y), hxy⟩).le
  · rintro _ ⟨y, rfl⟩
    obtain ⟨x, hxy⟩ := hright y
    refine ⟨Sum.inl x, mem_range_self x, ?_⟩
    rw [dist_comm]
    exact (glueDist_glued_points l s (D / 2 + δ) ⟨(x, y), hxy⟩).le

theorem exists_correspondence_distortion_le_twice_ghDist :
    ∃ r : X → Y → Prop, (∀ x, ∃ y, r x y) ∧ (∀ y, ∃ x, r x y) ∧
      ∀ x y x' y', r x y → r x' y' →
        |dist x x' - dist y y'| ≤ 2 * ghDist X Y := by
  let l := optimalGHInjl X Y
  let s := optimalGHInjr X Y
  have hl : Isometry l := isometry_optimalGHInjl X Y
  have hs : Isometry s := isometry_optimalGHInjr X Y
  have hcl : IsCompact (range l) := isCompact_range hl.continuous
  have hcs : IsCompact (range s) := isCompact_range hs.continuous
  have hfin : hausdorffEDist (range l) (range s) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty l) (range_nonempty s)
      hcl.isBounded hcs.isBounded
  have hopt : hausdorffDist (range l) (range s) = ghDist X Y := hausdorffDist_optimal
  refine ⟨fun x y => dist (l x) (s y) ≤ ghDist X Y, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨z, ⟨y, rfl⟩, hz⟩ := hcs.exists_infDist_eq_dist (range_nonempty s) (l x)
    refine ⟨y, ?_⟩
    change dist (l x) (s y) ≤ ghDist X Y
    rw [← hz, ← hopt]
    exact infDist_le_hausdorffDist_of_mem (mem_range_self x) hfin
  · intro y
    obtain ⟨z, ⟨x, rfl⟩, hz⟩ := hcl.exists_infDist_eq_dist (range_nonempty l) (s y)
    refine ⟨x, ?_⟩
    change dist (l x) (s y) ≤ ghDist X Y
    rw [dist_comm, ← hz, ← hopt, hausdorffDist_comm]
    apply infDist_le_hausdorffDist_of_mem (mem_range_self y)
    simpa only [hausdorffEDist_comm] using hfin
  · intro x y x' y' hxy hx'y'
    have h1 := dist_triangle (l x) (s y) (s y')
    have h2 := dist_triangle (l x) (s y') (l x')
    have h3 := dist_triangle (s y) (l x) (l x')
    have h4 := dist_triangle (s y) (l x') (s y')
    rw [dist_comm (s y') (l x')] at h2
    rw [dist_comm (s y) (l x)] at h3
    simp only [hl.dist_eq, hs.dist_eq] at h1 h2 h3 h4
    apply abs_le.mpr
    constructor <;> linarith

theorem ghDist_le_half_iff_exists_correspondence {D : ℝ} :
    ghDist X Y ≤ D / 2 ↔
      ∃ r : X → Y → Prop, (∀ x, ∃ y, r x y) ∧ (∀ y, ∃ x, r x y) ∧
        ∀ x y x' y', r x y → r x' y' → |dist x x' - dist y y'| ≤ D := by
  constructor
  · intro h
    obtain ⟨r, hl, hr, hd⟩ := exists_correspondence_distortion_le_twice_ghDist
      (X := X) (Y := Y)
    refine ⟨r, hl, hr, fun x y x' y' hxy hx'y' => ?_⟩
    have hdist := hd x y x' y' hxy hx'y'
    linarith
  · rintro ⟨r, hl, hr, hd⟩
    exact ghDist_le_half_of_correspondence r hl hr hd

theorem exists_correspondence_distortion_eq_twice_ghDist :
    ∃ r : X → Y → Prop, (∀ x, ∃ y, r x y) ∧ (∀ y, ∃ x, r x y) ∧
      correspondenceDistortion r = 2 * ghDist X Y := by
  obtain ⟨r, hl, hr, hd⟩ := exists_correspondence_distortion_le_twice_ghDist
    (X := X) (Y := Y)
  have hu := correspondenceDistortion_le r hl hd
  have hlower := ghDist_le_half_of_correspondence r hl hr
    (fun _ _ _ _ hxy hx'y' => dist_error_le_correspondenceDistortion r hxy hx'y')
  exact ⟨r, hl, hr, by linarith⟩

theorem ghDist_eq_half_sInf_correspondenceDistortion :
    ghDist X Y = sInf {D : ℝ | ∃ r : X → Y → Prop,
      (∀ x, ∃ y, r x y) ∧ (∀ y, ∃ x, r x y) ∧ correspondenceDistortion r = D} / 2 := by
  let S := {D : ℝ | ∃ r : X → Y → Prop,
    (∀ x, ∃ y, r x y) ∧ (∀ y, ∃ x, r x y) ∧ correspondenceDistortion r = D}
  have hm : 2 * ghDist X Y ∈ S :=
    exists_correspondence_distortion_eq_twice_ghDist (X := X) (Y := Y)
  have hlow : ∀ d ∈ S, 2 * ghDist X Y ≤ d := by
    rintro d ⟨r, hl, hr, hD⟩
    have h := ghDist_le_half_of_correspondence r hl hr
      (fun _ _ _ _ hxy hx'y' => dist_error_le_correspondenceDistortion r hxy hx'y')
    rw [hD] at h
    linarith
  have heq : sInf S = 2 * ghDist X Y :=
    le_antisymm (csInf_le ⟨2 * ghDist X Y, hlow⟩ hm) (le_csInf ⟨_, hm⟩ hlow)
  change ghDist X Y = sInf S / 2
  rw [heq]
  ring

theorem exists_map_of_ghDist_lt {a : ℝ} (h : ghDist X Y < a) :
    ∃ f : X → Y, (∀ x x', |dist (f x) (f x') - dist x x'| ≤ 2 * a) ∧
      ∀ y : Y, ∃ x : X, dist y (f x) ≤ 2 * a := by
  classical
  obtain ⟨r, hl, hr, hd⟩ := exists_correspondence_distortion_le_twice_ghDist
    (X := X) (Y := Y)
  choose f hf using hl
  refine ⟨f, ?_, ?_⟩
  · intro x x'
    have hdist := hd x (f x) x' (f x') (hf x) (hf x')
    rw [abs_sub_comm] at hdist
    linarith
  · intro y
    obtain ⟨x, hxy⟩ := hr y
    have hdist := hd x y x (f x) hxy (hf x)
    simp only [dist_self, zero_sub, abs_neg, abs_of_nonneg dist_nonneg] at hdist
    exact ⟨x, by linarith⟩

end GromovHausdorff

namespace Metric

universe u v

theorem exists_approximate_inverse_of_map {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] {ε : ℝ} (f : X → Y)
    (hdist : ∀ x x', |dist (f x) (f x') - dist x x'| ≤ ε)
    (hcover : ∀ y : Y, ∃ x : X, dist y (f x) ≤ ε) :
    ∃ g : Y → X, (∀ y, dist (f (g y)) y ≤ ε) ∧
      (∀ x, dist (g (f x)) x ≤ 2 * ε) ∧
      ∀ y y', |dist (g y) (g y') - dist y y'| ≤ 3 * ε := by
  classical
  choose g hg using hcover
  refine ⟨g, ?_, ?_, ?_⟩
  · intro y
    simpa only [dist_comm] using hg y
  · intro x
    have hd := abs_le.mp (hdist (g (f x)) x)
    have h := hg (f x)
    rw [dist_comm (f x) (f (g (f x)))] at h
    linarith
  · intro y y'
    have hd := abs_le.mp (hdist (g y) (g y'))
    have h1 := dist_triangle (f (g y)) y y'
    have h2 := dist_triangle (f (g y)) y' (f (g y'))
    have h3 := dist_triangle y (f (g y)) (f (g y'))
    have h4 := dist_triangle y (f (g y')) y'
    rw [dist_comm (f (g y)) y] at h1
    rw [dist_comm (f (g y')) y'] at h4
    apply abs_le.mpr
    constructor <;> linarith [hg y, hg y']

end Metric
