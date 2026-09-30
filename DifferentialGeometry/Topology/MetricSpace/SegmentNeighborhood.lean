import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem ball_eq_segment_image_of_injOn_dist {a b : ℝ} (hab : a ≤ b)
    {σ : Icc a b → X} (hσ : Isometry σ) (p : Icc a b) {r : ℝ}
    (hr : r ≤ min ((p : ℝ) - a) (b - p))
    (hinj : InjOn (fun x : X => dist (σ ⟨a, le_rfl, hab⟩) x) (ball (σ p) r)) :
    ball (σ p) r = σ '' {t | dist t p < r} := by
  apply Subset.antisymm
  · intro z hz
    let t : ℝ := a + dist (σ ⟨a, le_rfl, hab⟩) z
    have hdist : dist (σ ⟨a, le_rfl, hab⟩) (σ p) = (p : ℝ) - a := by
      rw [hσ.dist_eq]
      change |a - (p : ℝ)| = _
      rw [abs_of_nonpos (sub_nonpos.mpr p.property.1)]
      ring
    have hclose : |t - (p : ℝ)| < r := by
      have h : |dist (σ ⟨a, le_rfl, hab⟩) z -
          dist (σ ⟨a, le_rfl, hab⟩) (σ p)| ≤ dist z (σ p) := by
        simpa only [dist_comm z (σ ⟨a, le_rfl, hab⟩),
          dist_comm (σ p) (σ ⟨a, le_rfl, hab⟩)] using
          abs_dist_sub_le z (σ p) (σ ⟨a, le_rfl, hab⟩)
      rw [hdist] at h
      have heq : t - (p : ℝ) =
          dist (σ ⟨a, le_rfl, hab⟩) z - ((p : ℝ) - a) := by dsimp [t]; ring
      rw [heq]
      exact h.trans_lt hz
    have ht : t ∈ Icc a b := by
      constructor
      · dsimp [t]; linarith [dist_nonneg (x := σ ⟨a, le_rfl, hab⟩) (y := z)]
      · linarith [(abs_lt.mp hclose).2, hr.trans (min_le_right _ _)]
    let q : Icc a b := ⟨t, ht⟩
    have hqball : σ q ∈ ball (σ p) r := by
      change dist (σ q) (σ p) < r
      rw [hσ.dist_eq]
      exact hclose
    have heq : σ q = z := by
      apply hinj hqball hz
      change dist (σ ⟨a, le_rfl, hab⟩) (σ q) = dist (σ ⟨a, le_rfl, hab⟩) z
      rw [hσ.dist_eq]
      change |a - t| = _
      rw [abs_of_nonpos (sub_nonpos.mpr ht.1)]
      dsimp [t]
      ring
    exact ⟨q, hclose, heq⟩
  · rintro z ⟨t, ht, rfl⟩
    simpa [hσ.dist_eq] using ht

theorem isOpen_segment_image_of_locally_injOn_dist {a b : ℝ} (hab : a ≤ b)
    {σ : Icc a b → X} (hσ : Isometry σ)
    (hinj : ∀ p : Icc a b, a < (p : ℝ) → (p : ℝ) < b →
      ∃ r : ℝ, 0 < r ∧
        InjOn (fun x : X => dist (σ ⟨a, le_rfl, hab⟩) x) (ball (σ p) r)) :
    IsOpen (σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b}) := by
  rw [Metric.isOpen_iff]
  rintro x ⟨p, hp, rfl⟩
  obtain ⟨ε, hε, hi⟩ := hinj p hp.1 hp.2
  let r := min ε (min ((p : ℝ) - a) (b - p))
  have hr : 0 < r := lt_min hε (lt_min (sub_pos.mpr hp.1) (sub_pos.mpr hp.2))
  have hb := ball_eq_segment_image_of_injOn_dist hab hσ p (min_le_right ε _)
    (hi.mono (ball_subset_ball (min_le_left ε _)))
  refine ⟨r, hr, ?_⟩
  rw [hb]
  rintro x ⟨t, ht, rfl⟩
  refine ⟨t, ?_, rfl⟩
  change |(t : ℝ) - p| < r at ht
  have hh := abs_lt.mp ht
  constructor <;> linarith [(min_le_right ε (min ((p : ℝ) - a) (b - p))).trans
    (min_le_left _ _), (min_le_right ε (min ((p : ℝ) - a) (b - p))).trans
    (min_le_right _ _)]

private theorem segment_range_subset_of_avoids_endpoints {a b : ℝ}
    {σ : Icc a b → X} (hσ : Isometry σ)
    (ho : IsOpen (σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b}))
    {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    {f : T → X} (hf : Continuous f)
    (hmeet : (range f ∩ σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b}).Nonempty)
    (havoid : ∀ t s, f t = σ s → a < (s : ℝ) ∧ (s : ℝ) < b) :
    range f ⊆ σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b} := by
  apply (isPreconnected_range hf).subset_of_closure_inter_subset ho hmeet
  rintro x ⟨hx, t, rfl⟩
  have hclosed : IsClosed (range σ) := isCompact_range hσ.continuous |>.isClosed
  have hsub : closure (σ '' {s | a < (s : ℝ) ∧ (s : ℝ) < b}) ⊆ range σ :=
    closure_minimal (image_subset_range _ _) hclosed
  obtain ⟨s, hs⟩ := hsub hx
  exact ⟨s, havoid t s hs.symm, hs⟩

theorem ball_eq_segment_image_of_isOpen
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {a b : ℝ} {σ : Icc a b → X} (hσ : Isometry σ)
    (ho : IsOpen (σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b}))
    (p : Icc a b) {r : ℝ} (hr : r ≤ min ((p : ℝ) - a) (b - p)) :
    ball (σ p) r = σ '' {t | dist t p < r} := by
  apply Subset.antisymm
  · intro z hz
    have hz' : dist (σ p) z < r := by simpa [dist_comm] using hz
    have hrpos : 0 < r := (dist_nonneg.trans_lt hz')
    have hp : a < (p : ℝ) ∧ (p : ℝ) < b := by
      constructor <;> linarith [hr.trans (min_le_left _ _), hr.trans (min_le_right _ _)]
    obtain ⟨f, hf, hf0, hf1, hfd⟩ := hsegments (σ p) z
    have hbound (t : Icc (0 : ℝ) 1) : dist (σ p) (f t) < r := by
      rw [← hf0, hfd]
      have ht : dist (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1) t = (t : ℝ) := by
        simp [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg t.property.1]
      rw [ht]
      exact (mul_le_of_le_one_right dist_nonneg t.property.2).trans_lt hz'
    have himage : range f ⊆ σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b} := by
      apply segment_range_subset_of_avoids_endpoints hσ ho hf
      · exact ⟨σ p, ⟨⟨0, by norm_num⟩, hf0⟩, p, hp, rfl⟩
      · intro t s hts
        have hd := hbound t
        rw [hts, hσ.dist_eq] at hd
        change |(p : ℝ) - (s : ℝ)| < r at hd
        have hh := abs_lt.mp hd
        constructor <;> linarith [hr.trans (min_le_left _ _), hr.trans (min_le_right _ _)]
    obtain ⟨s, _, hs⟩ := himage ⟨⟨1, by norm_num⟩, hf1⟩
    refine ⟨s, ?_, hs⟩
    change dist s p < r
    rw [← hσ.dist_eq, hs]
    exact hz
  · rintro z ⟨t, ht, rfl⟩
    simpa [hσ.dist_eq] using ht

theorem ball_eq_segment_image_at_endpoint_of_isOpen
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {D : ℝ} (hD : 0 ≤ D) {σ : Icc (0 : ℝ) D → X} (hσ : Isometry σ)
    (ho : IsOpen (σ '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < D}))
    (hend : ∀ x y : X, dist x (σ ⟨0, le_rfl, hD⟩) + dist (σ ⟨0, le_rfl, hD⟩) y = dist x y →
      x = σ ⟨0, le_rfl, hD⟩ ∨ y = σ ⟨0, le_rfl, hD⟩)
    {r : ℝ} (hr : r ≤ D) :
    ball (σ ⟨0, le_rfl, hD⟩) r = σ '' {t | (t : ℝ) < r} := by
  let p : X := σ ⟨0, le_rfl, hD⟩
  have hdist (s t : Icc (0 : ℝ) D) : dist (σ s) (σ t) = |(s : ℝ) - t| :=
    hσ.dist_eq s t
  apply Subset.antisymm
  · intro z hz
    have hz' : dist p z < r := by simpa [p, dist_comm] using hz
    by_cases hzp : z = p
    · refine ⟨⟨0, le_rfl, hD⟩, ?_, hzp.symm⟩
      simpa [hzp] using hz'
    let a : ℝ := (D - dist p z) / 4
    have ha : 0 < a := by dsimp [a]; linarith
    have haD : a < D := by dsimp [a]; linarith [dist_nonneg (x := p) (y := z)]
    let w : Icc (0 : ℝ) D := ⟨a, ha.le, haD.le⟩
    have hwp : σ w ≠ p := by
      intro h
      have heq := congrArg Subtype.val (hσ.injective h)
      change a = 0 at heq
      linarith
    obtain ⟨f, hf, hf0, hf1, hfd⟩ := hsegments (σ w) z
    have hfstart (t : Icc (0 : ℝ) 1) :
        dist (σ w) (f t) = dist (σ w) z * (t : ℝ) := by
      rw [← hf0, hfd, hf0]
      simp [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg t.property.1]
    have hfend (t : Icc (0 : ℝ) 1) :
        dist (f t) z = dist (σ w) z * (1 - (t : ℝ)) := by
      rw [← hf1, hfd, hf1]
      simp [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr t.property.2)]
    have hfnotp (t : Icc (0 : ℝ) 1) : f t ≠ p := by
      intro h
      have hs := hfstart t
      have he := hfend t
      rw [h] at hs he
      exact (hend (σ w) z (by change dist (σ w) p + dist p z = _; nlinarith)).elim hwp hzp
    have hbound (t : Icc (0 : ℝ) 1) : dist (σ w) (f t) < D - a := by
      rw [hfstart]
      have htri := dist_triangle (σ w) p z
      have hwpdist : dist (σ w) p = a := by
        dsimp [p]
        rw [hdist]
        simp [w, abs_of_pos ha]
      rw [hwpdist] at htri
      have hm := mul_le_of_le_one_right (dist_nonneg (x := σ w) (y := z)) t.property.2
      dsimp [a] at *
      linarith
    have himage : range f ⊆ σ '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < D} := by
      apply segment_range_subset_of_avoids_endpoints hσ ho hf
      · exact ⟨σ w, ⟨⟨0, by norm_num⟩, hf0⟩, w, ⟨ha, haD⟩, rfl⟩
      · intro t s hts
        constructor
        · apply lt_of_le_of_ne s.property.1
          intro hs
          apply hfnotp t
          exact hts.trans (congrArg σ (Subtype.ext hs.symm))
        · have hd := hbound t
          rw [hts, hdist] at hd
          change |a - (s : ℝ)| < D - a at hd
          linarith [(abs_lt.mp hd).1]
    obtain ⟨s, _, hs⟩ := himage ⟨⟨1, by norm_num⟩, hf1⟩
    refine ⟨s, ?_, hs⟩
    rw [← hs] at hz'
    simpa [p, hdist, abs_of_nonneg s.property.1] using hz'
  · rintro z ⟨t, ht, rfl⟩
    change dist (σ t) (σ ⟨0, le_rfl, hD⟩) < r
    simpa [hdist, abs_of_nonneg t.property.1] using ht

theorem exists_pointed_interval_isometry_of_isOpen_segment
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {a b : ℝ} {σ : Icc a b → X} (hσ : Isometry σ)
    (ho : IsOpen (σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b}))
    (p : Icc a b) {r : ℝ} (hrpos : 0 < r)
    (hr : r ≤ min ((p : ℝ) - a) (b - p)) :
    ∃ e : Ioo (-r) r ≃ᵢ ball (σ p) r,
      (e ⟨0, by constructor <;> linarith⟩ : X) = σ p := by
  have hdom (t : Ioo (-r) r) : (p : ℝ) + t ∈ Icc a b := by
    constructor <;> linarith [t.property.1, t.property.2,
      hr.trans (min_le_left _ _), hr.trans (min_le_right _ _)]
  let F : Ioo (-r) r → ball (σ p) r := fun t =>
    ⟨σ ⟨(p : ℝ) + t, hdom t⟩, by
      change dist (σ ⟨(p : ℝ) + t, hdom t⟩) (σ p) < r
      rw [hσ.dist_eq]
      change |(p : ℝ) + t - p| < r
      simpa using abs_lt.mpr t.property⟩
  have hF : Isometry F := by
    apply Isometry.of_dist_eq
    intro s t
    change dist (σ ⟨(p : ℝ) + s, hdom s⟩) (σ ⟨(p : ℝ) + t, hdom t⟩) = dist s t
    rw [hσ.dist_eq]
    change |((p : ℝ) + s) - (p + t)| = |(s : ℝ) - t|
    congr 1
    ring
  have hsurj : Function.Surjective F := by
    intro z
    have hz := (ball_eq_segment_image_of_isOpen hsegments hσ ho p hr).subset z.property
    obtain ⟨s, hs, hsz⟩ := hz
    have ht : (s : ℝ) - p ∈ Ioo (-r) r := abs_lt.mp hs
    refine ⟨⟨(s : ℝ) - p, ht⟩, ?_⟩
    apply Subtype.ext
    change σ ⟨(p : ℝ) + ((s : ℝ) - p), _⟩ = z
    calc
      _ = σ s := congrArg σ (Subtype.ext (by dsimp; ring))
      _ = z := hsz
  let e : Ioo (-r) r ≃ᵢ ball (σ p) r :=
    ⟨Equiv.ofBijective F ⟨hF.injective, hsurj⟩, hF⟩
  refine ⟨e, ?_⟩
  change σ ⟨(p : ℝ) + 0, _⟩ = σ p
  congr 1
  apply Subtype.ext
  simp

theorem exists_pointed_half_interval_isometry_of_isOpen_segment
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {D : ℝ} (hD : 0 ≤ D) {σ : Icc (0 : ℝ) D → X} (hσ : Isometry σ)
    (ho : IsOpen (σ '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < D}))
    (hend : ∀ x y : X,
      dist x (σ ⟨0, le_rfl, hD⟩) + dist (σ ⟨0, le_rfl, hD⟩) y = dist x y →
      x = σ ⟨0, le_rfl, hD⟩ ∨ y = σ ⟨0, le_rfl, hD⟩)
    {r : ℝ} (hrpos : 0 < r) (hr : r ≤ D) :
    ∃ e : Ico (0 : ℝ) r ≃ᵢ ball (σ ⟨0, le_rfl, hD⟩) r,
      (e ⟨0, le_rfl, hrpos⟩ : X) = σ ⟨0, le_rfl, hD⟩ := by
  let F : Ico (0 : ℝ) r → ball (σ ⟨0, le_rfl, hD⟩) r := fun t =>
    ⟨σ ⟨t, t.property.1, t.property.2.le.trans hr⟩, by
      change dist (σ ⟨t, t.property.1, t.property.2.le.trans hr⟩) (σ ⟨0, le_rfl, hD⟩) < r
      rw [hσ.dist_eq]
      simpa [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg t.property.1] using t.property.2⟩
  have hF : Isometry F := by
    apply Isometry.of_dist_eq
    intro s t
    exact hσ.dist_eq _ _
  have hsurj : Function.Surjective F := by
    intro z
    have hz := (ball_eq_segment_image_at_endpoint_of_isOpen
      hsegments hD hσ ho hend hr).subset z.property
    obtain ⟨s, hs, hsz⟩ := hz
    exact ⟨⟨s, s.property.1, hs⟩, Subtype.ext hsz⟩
  exact ⟨⟨Equiv.ofBijective F ⟨hF.injective, hsurj⟩, hF⟩, rfl⟩

end Metric
