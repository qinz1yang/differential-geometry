import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyPolyhedral

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def halfMap : ℝ →ᵃ[ℝ] ℝ := ((2 : ℝ)⁻¹ • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).toAffineMap

theorem halfMap_apply (t : ℝ) : halfMap t = t / 2 := by
  change (2 : ℝ)⁻¹ • t = t / 2
  rw [smul_eq_mul]
  ring

noncomputable def slideWidth (p : ℝ × ℝ × ℝ) : ℝ := 1 - |p.2.1| - |p.2.2|

noncomputable def slideTaper (p : ℝ × ℝ × ℝ) : ℝ := (3 - |p.1|) / 2

noncomputable def slideAmount (p : ℝ × ℝ × ℝ) : ℝ := max 0 (min (slideWidth p) (slideTaper p))

noncomputable def slideMap (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (p.1 - slideAmount p, p.2.1, p.2.2)

def modelBandA : Set (ℝ × ℝ × ℝ) := {p | p.2.2 = 0 ∧ |p.2.1| ≤ 1 ∧ p.1 ∈ Icc (0 : ℝ) 1}

def modelBandQ : Set (ℝ × ℝ × ℝ) :=
  {p | p.2.1 = 0 ∧ |p.2.2| ≤ 1 ∧ p.1 ∈ Icc (1 / 2 : ℝ) 2}

theorem slideAmount_nonneg (p : ℝ × ℝ × ℝ) : 0 ≤ slideAmount p := le_max_left _ _

theorem slideAmount_eq_zero_of_width {p : ℝ × ℝ × ℝ} (h : 1 ≤ |p.2.1| + |p.2.2|) :
    slideAmount p = 0 := by
  have hw : slideWidth p ≤ 0 := by
    simp only [slideWidth]
    linarith
  simp only [slideAmount, max_eq_left (le_trans (min_le_left _ _) hw)]

theorem slideAmount_eq_zero_of_taper {p : ℝ × ℝ × ℝ} (h : 3 ≤ |p.1|) :
    slideAmount p = 0 := by
  have ht : slideTaper p ≤ 0 := by
    simp only [slideTaper]
    linarith
  simp only [slideAmount, max_eq_left (le_trans (min_le_right _ _) ht)]

theorem slideMap_eq_self_of_width {p : ℝ × ℝ × ℝ} (h : 1 ≤ |p.2.1| + |p.2.2|) :
    slideMap p = p := by
  simp only [slideMap, slideAmount_eq_zero_of_width h, sub_zero]

theorem slideMap_eq_self_of_taper {p : ℝ × ℝ × ℝ} (h : 3 ≤ |p.1|) : slideMap p = p := by
  simp only [slideMap, slideAmount_eq_zero_of_taper h, sub_zero]

theorem slideAmount_le_add {p q : ℝ × ℝ × ℝ} (hyz : p.2 = q.2) (hpq : p.1 ≤ q.1) :
    slideAmount q ≤ slideAmount p + (q.1 - p.1) / 2 := by
  have hc : 0 ≤ (q.1 - p.1) / 2 := by linarith
  have hw : slideWidth q = slideWidth p := by
    simp only [slideWidth, hyz]
  have hab : |p.1| - |q.1| ≤ q.1 - p.1 := by
    have h := abs_sub_abs_le_abs_sub p.1 q.1
    rwa [abs_of_nonpos (by linarith : p.1 - q.1 ≤ 0), neg_sub] at h
  have hT : slideTaper q ≤ slideTaper p + (q.1 - p.1) / 2 := by
    simp only [slideTaper]
    linarith
  have hmin : min (slideWidth q) (slideTaper q) ≤
      min (slideWidth p) (slideTaper p) + (q.1 - p.1) / 2 := by
    rcases le_total (slideWidth p) (slideTaper p) with h | h
    · rw [min_eq_left h]
      exact le_trans (min_le_left _ _) (by rw [hw]; linarith)
    · rw [min_eq_right h]
      exact le_trans (min_le_right _ _) (by linarith)
  have hmax : min (slideWidth p) (slideTaper p) ≤ slideAmount p := le_max_right _ _
  refine max_le (by linarith [slideAmount_nonneg p]) ?_
  linarith

theorem injective_slideMap : Function.Injective slideMap := by
  intro p q hpq
  have h2 : p.2 = q.2 := by
    have h := congrArg Prod.snd hpq
    exact h
  have h1 : p.1 - slideAmount p = q.1 - slideAmount q := congrArg Prod.fst hpq
  have hx : p.1 = q.1 := by
    rcases le_total p.1 q.1 with h | h
    · have hle := slideAmount_le_add h2 h
      linarith
    · have hle := slideAmount_le_add h2.symm h
      linarith
  exact Prod.ext hx h2

theorem isPiecewiseAffineOn_slideMap : IsPiecewiseAffineOn slideMap univ := by
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
  have hwidth : IsPiecewiseAffineOn slideWidth univ := by
    have h := ((hconst 1).add (hy.abs.affine_comp (-AffineMap.id ℝ ℝ))).add
      (hz.abs.affine_comp (-AffineMap.id ℝ ℝ))
    refine h.congr fun p _ => ?_
    rw [slideWidth]
    change 1 + -|p.2.1| + -|p.2.2| = 1 - |p.2.1| - |p.2.2|
    ring
  have htaper : IsPiecewiseAffineOn slideTaper univ := by
    have h := ((hconst 3).add (hx.abs.affine_comp (-AffineMap.id ℝ ℝ))).affine_comp halfMap
    refine h.congr fun p _ => ?_
    change slideTaper p = halfMap (3 + -|p.1|)
    rw [halfMap_apply, slideTaper]
    ring
  have hamount : IsPiecewiseAffineOn slideAmount univ :=
    ((hconst 0).max (hwidth.min htaper)).congr fun _ _ => rfl
  have hfirst : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.1 - slideAmount p) univ := by
    have h := hx.add (hamount.affine_comp (-AffineMap.id ℝ ℝ))
    refine h.congr fun p _ => ?_
    change p.1 + -slideAmount p = p.1 - slideAmount p
    ring
  exact hfirst.prod_mk (hy.prod_mk hz)

theorem continuous_slideMap : Continuous slideMap := by
  rw [← continuousOn_univ]
  exact isPiecewiseAffineOn_slideMap.continuousOn

theorem surjective_slideMap : Function.Surjective slideMap := by
  intro w
  have hcont : Continuous fun x : ℝ => (slideMap (x, w.2.1, w.2.2)).1 :=
    continuous_fst.comp (continuous_slideMap.comp (by fun_prop))
  rcases le_or_gt |w.1| 3 with hle | hgt
  · have h3 : (slideMap ((3 : ℝ), w.2.1, w.2.2)).1 = 3 := by
      rw [slideMap_eq_self_of_taper (p := ((3 : ℝ), w.2.1, w.2.2)) (by norm_num)]
    have hm3 : (slideMap ((-3 : ℝ), w.2.1, w.2.2)).1 = -3 := by
      rw [slideMap_eq_self_of_taper (p := ((-3 : ℝ), w.2.1, w.2.2)) (by norm_num)]
    have hmem : w.1 ∈ Icc ((slideMap ((-3 : ℝ), w.2.1, w.2.2)).1)
        ((slideMap ((3 : ℝ), w.2.1, w.2.2)).1) := by
      rw [h3, hm3]
      exact abs_le.mp hle
    obtain ⟨x, -, hgx⟩ :=
      intermediate_value_Icc (by norm_num : (-3 : ℝ) ≤ 3) hcont.continuousOn hmem
    exact ⟨(x, w.2.1, w.2.2), Prod.ext hgx rfl⟩
  · refine ⟨(w.1, w.2.1, w.2.2), ?_⟩
    rw [slideMap_eq_self_of_taper (p := (w.1, w.2.1, w.2.2)) (by simpa using hgt.le)]

theorem bijective_slideMap : Function.Bijective slideMap :=
  ⟨injective_slideMap, surjective_slideMap⟩

theorem inter_modelBandA_modelBandQ :
    modelBandA ∩ modelBandQ = {p : ℝ × ℝ × ℝ | p.2.1 = 0 ∧ p.2.2 = 0 ∧ p.1 ∈ Icc (1 / 2 : ℝ) 1} := by
  ext p
  constructor
  · rintro ⟨⟨hz, -, hx1⟩, ⟨hy, -, hx2⟩⟩
    exact ⟨hy, hz, hx2.1, hx1.2⟩
  · rintro ⟨hy, hz, hx1, hx2⟩
    refine ⟨⟨hz, ?_, ?_, ?_⟩, hy, ?_, ?_, ?_⟩
    · rw [hy]
      simp
    · linarith
    · linarith
    · rw [hz]
      simp
    · linarith
    · linarith

theorem disjoint_slideMap_image_modelBandA :
    Disjoint (slideMap '' modelBandA) modelBandQ := by
  rw [Set.disjoint_left]
  rintro w ⟨p, ⟨hz, -, hx0, hx1⟩, rfl⟩ ⟨hy, -, hw1, -⟩
  have hpy : p.2.1 = 0 := hy
  have hwidth : slideWidth p = 1 := by
    simp only [slideWidth, hpy, hz, abs_zero]
    ring
  have htaper : 1 ≤ slideTaper p := by
    simp only [slideTaper, abs_of_nonneg hx0]
    linarith
  have hamount : slideAmount p = 1 := by
    simp only [slideAmount, hwidth, min_eq_left htaper,
      max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
  have hfirst : (slideMap p).1 = p.1 - 1 := by
    simp only [slideMap, hamount]
  rw [hfirst] at hw1
  linarith

end DifferentialGeometry.Topology.PiecewiseLinear
