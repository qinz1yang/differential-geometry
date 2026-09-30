import DifferentialGeometry.Topology.MetricSpace.GeodesicCompactness
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem exists_isometric_segment_of_dist_eq_mul {x y : X}
    {f : Icc (0 : ℝ) 1 → X}
    (hf0 : f ⟨0, by norm_num⟩ = x) (hf1 : f ⟨1, by norm_num⟩ = y)
    (hfd : ∀ s t, dist (f s) (f t) = dist x y * dist s t) :
    ∃ σ : Icc (0 : ℝ) (dist x y) → X, Isometry σ ∧
      σ ⟨0, le_rfl, dist_nonneg⟩ = x ∧ σ ⟨dist x y, dist_nonneg, le_rfl⟩ = y := by
  by_cases hxy : x = y
  · rcases hxy with rfl
    refine ⟨fun _ => x, Isometry.of_dist_eq (fun s t => ?_), rfl, rfl⟩
    have hs : (s : ℝ) = 0 := by simpa using s.property
    have ht : (t : ℝ) = 0 := by simpa using t.property
    simp [Subtype.dist_eq, hs, ht]
  have hD : 0 < dist x y := dist_pos.mpr hxy
  let g : Icc (0 : ℝ) (dist x y) → Icc (0 : ℝ) 1 := fun t =>
    ⟨(t : ℝ) / dist x y, div_nonneg t.property.1 hD.le,
      (div_le_one hD).mpr t.property.2⟩
  refine ⟨f ∘ g, Isometry.of_dist_eq (fun s t => ?_), ?_, ?_⟩
  · change dist (f (g s)) (f (g t)) = dist s t
    rw [hfd]
    change dist x y * |(s : ℝ) / dist x y - (t : ℝ) / dist x y| = |(s : ℝ) - t|
    rw [← sub_div, abs_div, abs_of_pos hD, mul_div_cancel₀ _ hD.ne']
  · simpa [g, Function.comp_def] using hf0
  · simpa [g, Function.comp_def, hD.ne'] using hf1

theorem exists_isometric_segment_concat {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {α : Icc (0 : ℝ) A → X} {β : Icc (0 : ℝ) B → X}
    (hα : Isometry α) (hβ : Isometry β)
    (hjoin : α ⟨A, hA, le_rfl⟩ = β ⟨0, le_rfl, hB⟩)
    (hend : dist (α ⟨0, le_rfl, hA⟩) (β ⟨B, hB, le_rfl⟩) = A + B) :
    ∃ σ : Icc (0 : ℝ) (A + B) → X, Isometry σ ∧
      (∀ s : Icc (0 : ℝ) A, σ ⟨s, s.property.1, by linarith [s.property.2]⟩ = α s) ∧
      (∀ t : Icc (0 : ℝ) B, σ ⟨A + t, by linarith [t.property.1],
        by linarith [t.property.2]⟩ = β t) := by
  have hcross (s : Icc (0 : ℝ) A) (t : Icc (0 : ℝ) B) :
      dist (α s) (β t) = A - s + t := by
    have h1 := dist_triangle (α s) (α ⟨A, hA, le_rfl⟩) (β t)
    rw [hα.dist_eq, hjoin, hβ.dist_eq] at h1
    have h2 := dist_triangle (α ⟨0, le_rfl, hA⟩) (α s) (β ⟨B, hB, le_rfl⟩)
    have h3 := dist_triangle (α s) (β t) (β ⟨B, hB, le_rfl⟩)
    rw [hend, hα.dist_eq] at h2
    rw [hβ.dist_eq] at h3
    simp only [Subtype.dist_eq, Real.dist_eq] at h1 h2 h3
    rw [abs_of_nonpos (sub_nonpos.mpr s.property.2), zero_sub, abs_neg,
      abs_of_nonneg t.property.1] at h1
    rw [zero_sub, abs_neg, abs_of_nonneg s.property.1] at h2
    rw [abs_of_nonpos (sub_nonpos.mpr t.property.2)] at h3
    linarith
  let σ : Icc (0 : ℝ) (A + B) → X := fun t =>
    if ht : (t : ℝ) ≤ A then α ⟨t, t.property.1, ht⟩
    else β ⟨(t : ℝ) - A, by linarith, by linarith [t.property.2]⟩
  have hleft (s : Icc (0 : ℝ) A) :
      σ ⟨s, s.property.1, by linarith [s.property.2]⟩ = α s := by
    simp [σ, s.property.2]
  have hright (t : Icc (0 : ℝ) B) :
      σ ⟨A + t, by linarith [t.property.1], by linarith [t.property.2]⟩ = β t := by
    by_cases ht : (t : ℝ) = 0
    · have ht' : t = ⟨0, le_rfl, hB⟩ := Subtype.ext ht
      subst t
      simpa [σ] using hjoin
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      simp [σ, show ¬ A + (t : ℝ) ≤ A by linarith]
  refine ⟨σ, Isometry.of_dist_eq (fun s t => ?_), hleft, hright⟩
  change dist (σ s) (σ t) = |(s : ℝ) - t|
  by_cases hs : (s : ℝ) ≤ A <;> by_cases ht : (t : ℝ) ≤ A
  · simp only [σ, dite_eq_left hs, dite_eq_left ht, hα.dist_eq, Subtype.dist_eq, Real.dist_eq]
  · simp only [σ, dite_eq_left hs, dite_eq_right ht]
    rw [hcross]
    dsimp
    rw [abs_of_nonpos (by linarith : (s : ℝ) - t ≤ 0)]
    ring
  · simp only [σ, dite_eq_right hs, dite_eq_left ht]
    rw [dist_comm, hcross]
    dsimp
    rw [abs_of_nonneg (by linarith : 0 ≤ (s : ℝ) - t)]
    ring
  · simp only [σ, dite_eq_right hs, dite_eq_right ht, hβ.dist_eq, Subtype.dist_eq, Real.dist_eq]
    congr 1
    ring

theorem metric_endpoint_iff_not_mem_segment_interior
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t) (p : X) :
    (∀ x y : X, dist x p + dist p y = dist x y → x = p ∨ y = p) ↔
      ∀ (a b : ℝ) (σ : Icc a b → X), Isometry σ →
        ∀ t : Icc a b, a < (t : ℝ) → (t : ℝ) < b → σ t ≠ p := by
  constructor
  · intro hp a b σ hσ t hat htb htp
    have hab : a ≤ b := hat.le.trans htb.le
    let s : Icc a b := ⟨a, le_rfl, hab⟩
    let u : Icc a b := ⟨b, hab, le_rfl⟩
    have hd : dist (σ s) p + dist p (σ u) = dist (σ s) (σ u) := by
      rw [← htp, hσ.dist_eq, hσ.dist_eq, hσ.dist_eq]
      change |a - (t : ℝ)| + |(t : ℝ) - b| = |a - b|
      rw [abs_of_neg (sub_neg.mpr hat), abs_of_neg (sub_neg.mpr htb),
        abs_of_nonpos (sub_nonpos.mpr hab)]
      ring
    rcases hp (σ s) (σ u) hd with hs | hu
    · have he := congrArg Subtype.val (hσ.injective (hs.trans htp.symm))
      change a = (t : ℝ) at he
      linarith
    · have he := congrArg Subtype.val (hσ.injective (hu.trans htp.symm))
      change b = (t : ℝ) at he
      linarith
  · intro hp x y hxy
    by_cases hxp : x = p
    · exact Or.inl hxp
    by_cases hyp : y = p
    · exact Or.inr hyp
    obtain ⟨f, _, hf0, hf1, hfd⟩ := hsegments x p
    obtain ⟨g, _, hg0, hg1, hgd⟩ := hsegments p y
    obtain ⟨α, hα, hα0, hα1⟩ := exists_isometric_segment_of_dist_eq_mul hf0 hf1 hfd
    obtain ⟨β, hβ, hβ0, hβ1⟩ := exists_isometric_segment_of_dist_eq_mul hg0 hg1 hgd
    obtain ⟨σ, hσ, hleft, _⟩ := exists_isometric_segment_concat
      (dist_nonneg (x := x) (y := p)) (dist_nonneg (x := p) (y := y)) hα hβ
      (hα1.trans hβ0.symm) (by rw [hα0, hβ1]; exact hxy.symm)
    have hA : 0 < dist x p := dist_pos.mpr hxp
    have hB : 0 < dist p y := dist_pos.mpr (Ne.symm hyp)
    have ht : dist x p ≤ dist x p + dist p y := by linarith
    have hcenter : σ ⟨dist x p, hA.le, ht⟩ = p :=
      (hleft ⟨dist x p, dist_nonneg, le_rfl⟩).trans hα1
    exact False.elim (hp 0 (dist x p + dist p y) σ hσ
      ⟨dist x p, hA.le, ht⟩ hA (by linarith) hcenter)

end Metric
