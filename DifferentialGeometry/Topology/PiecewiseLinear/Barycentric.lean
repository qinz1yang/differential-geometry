/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedra

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem mem_convexHull_iff_exists_weights {s : Finset E} {x : E} :
    x ∈ convexHull ℝ (s : Set E) ↔
      ∃ w : E → ℝ, (∀ v ∈ s, 0 ≤ w v) ∧ ∑ v ∈ s, w v = 1 ∧ ∑ v ∈ s, w v • v = x := by
  rw [Finset.mem_convexHull]
  refine exists_congr fun w => and_congr_right fun _ => and_congr_right fun hw => ?_
  rw [Finset.centerMass_eq_of_sum_1 s id hw]
  exact Iff.rfl

theorem eq_on_of_sum_smul_eq {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E))
    {w w' : E → ℝ} (hw : ∑ v ∈ s, w v = 1) (hw' : ∑ v ∈ s, w' v = 1)
    (h : ∑ v ∈ s, w v • v = ∑ v ∈ s, w' v • v) : ∀ v ∈ s, w v = w' v := by
  have hw₁ : ∑ i : s, w i = 1 := by
    rw [Finset.sum_coe_sort s w]
    exact hw
  have hw₂ : ∑ i : s, w' i = 1 := by
    rw [Finset.sum_coe_sort s w']
    exact hw'
  have key := (hs.affineCombination_eq_iff_eq (s := Finset.univ) hw₁ hw₂).mp ?_
  · intro v hv
    exact key ⟨v, hv⟩ (Finset.mem_univ _)
  · rw [Finset.affineCombination_eq_linear_combination _ _ _ hw₁,
      Finset.affineCombination_eq_linear_combination _ _ _ hw₂]
    change ∑ i : s, w i • (i : E) = ∑ i : s, w' i • (i : E)
    rw [Finset.sum_coe_sort s (fun v => w v • v), Finset.sum_coe_sort s (fun v => w' v • v)]
    exact h

theorem mem_of_mem_convexHull_of_affineIndependent {s t : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (ht : t ⊆ s) {v : E} (hv : v ∈ s)
    (h : v ∈ convexHull ℝ (t : Set E)) : v ∈ t := by
  classical
  obtain ⟨w, -, hw₁, hwx⟩ := mem_convexHull_iff_exists_weights.mp h
  let w' : E → ℝ := fun u => if u ∈ t then w u else 0
  have hw'₁ : ∑ u ∈ s, w' u = 1 := by
    simp only [w']
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr ht]
    exact hw₁
  have hw'x : ∑ u ∈ s, w' u • u = v := by
    simp only [w', ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr ht]
    exact hwx
  let δ : E → ℝ := fun u => if u = v then 1 else 0
  have hδ₁ : ∑ u ∈ s, δ u = 1 := by simp [δ, hv]
  have hδx : ∑ u ∈ s, δ u • u = v := by simp [δ, ite_smul, hv]
  have hvv := eq_on_of_sum_smul_eq hs hw'₁ hδ₁ (hw'x.trans hδx.symm) v hv
  by_contra hvt
  simp [w', δ, hvt] at hvv

def openSimplex (s : Finset E) : Set E :=
  {x | ∃ w : E → ℝ, (∀ v ∈ s, 0 < w v) ∧ ∑ v ∈ s, w v = 1 ∧ ∑ v ∈ s, w v • v = x}

theorem openSimplex_subset_convexHull (s : Finset E) :
    openSimplex s ⊆ convexHull ℝ (s : Set E) := by
  rintro x ⟨w, hw₀, hw₁, hwx⟩
  exact mem_convexHull_iff_exists_weights.mpr ⟨w, fun v hv => (hw₀ v hv).le, hw₁, hwx⟩

theorem exists_openSimplex_of_mem_convexHull {s : Finset E} {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) : ∃ t ⊆ s, t.Nonempty ∧ x ∈ openSimplex t := by
  classical
  obtain ⟨w, hw₀, hw₁, hwx⟩ := mem_convexHull_iff_exists_weights.mp hx
  refine ⟨s.filter fun v => 0 < w v, Finset.filter_subset _ _, ?_, w,
    fun v hv => (Finset.mem_filter.mp hv).2, ?_, ?_⟩
  · by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
    have h0 : ∑ v ∈ s, w v = 0 :=
      Finset.sum_eq_zero fun v hv => le_antisymm (not_lt.mp (hne hv)) (hw₀ v hv)
    linarith
  · rw [← hw₁]
    exact Finset.sum_filter_of_ne fun v hv hne => lt_of_le_of_ne (hw₀ v hv) (Ne.symm hne)
  · rw [← hwx]
    refine Finset.sum_filter_of_ne fun v hv hne => lt_of_le_of_ne (hw₀ v hv) fun h => hne ?_
    rw [← h, zero_smul]

theorem subset_convexHull_of_mem_openSimplex {s t u : Finset E}
    (ht : AffineIndependent ℝ ((↑) : t → E)) (hu : u ⊆ t)
    (hs : (s : Set E) ⊆ convexHull ℝ (t : Set E)) {x : E} (hx : x ∈ openSimplex s)
    (hxu : x ∈ convexHull ℝ (u : Set E)) : (s : Set E) ⊆ convexHull ℝ (u : Set E) := by
  classical
  obtain ⟨w, hw₀, hw₁, hwx⟩ := hx
  have hμ : ∀ v ∈ s, ∃ μ : E → ℝ, (∀ q ∈ t, 0 ≤ μ q) ∧ ∑ q ∈ t, μ q = 1 ∧ ∑ q ∈ t, μ q • q = v :=
    fun v hv => mem_convexHull_iff_exists_weights.mp (hs hv)
  choose! μ hμ₀ hμ₁ hμv using hμ
  let ν : E → ℝ := fun q => ∑ v ∈ s, w v * μ v q
  have hν₀ : ∀ q ∈ t, 0 ≤ ν q := fun q hq =>
    Finset.sum_nonneg fun v hv => mul_nonneg (hw₀ v hv).le (hμ₀ v hv q hq)
  have hν₁ : ∑ q ∈ t, ν q = 1 := by
    simp only [ν]
    rw [Finset.sum_comm, ← hw₁]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [← Finset.mul_sum, hμ₁ v hv, mul_one]
  have key : ∀ v ∈ s, ∀ (a : ℝ) (y : E), ∑ q ∈ t, μ v q • q = y →
      a • y = ∑ q ∈ t, (a * μ v q) • q := by
    rintro v _ a y rfl
    rw [Finset.smul_sum]
    simp_rw [mul_smul]
  have hνx : ∑ q ∈ t, ν q • q = x := by
    simp only [ν, Finset.sum_smul]
    rw [Finset.sum_comm, ← hwx]
    exact Finset.sum_congr rfl fun v hv => (key v hv (w v) v (hμv v hv)).symm
  obtain ⟨ω, -, hω₁, hωx⟩ := mem_convexHull_iff_exists_weights.mp hxu
  let ω' : E → ℝ := fun q => if q ∈ u then ω q else 0
  have hω'₁ : ∑ q ∈ t, ω' q = 1 := by
    simp only [ω']
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hu]
    exact hω₁
  have hω'x : ∑ q ∈ t, ω' q • q = x := by
    simp only [ω', ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hu]
    exact hωx
  have heq := eq_on_of_sum_smul_eq ht hν₁ hω'₁ (hνx.trans hω'x.symm)
  have hμzero : ∀ v ∈ s, ∀ q ∈ t, q ∉ u → μ v q = 0 := by
    intro v hv q hq hqu
    have h0 : ∑ v' ∈ s, w v' * μ v' q = 0 := by
      have := heq q hq
      simp only [ν, ω', hqu, ite_false] at this
      exact this
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun v' hv' =>
      mul_nonneg (hw₀ v' hv').le (hμ₀ v' hv' q hq)).mp h0 v hv
    rcases mul_eq_zero.mp hall with h | h
    · exact absurd h (hw₀ v hv).ne'
    · exact h
  intro v hv
  refine mem_convexHull_iff_exists_weights.mpr
    ⟨μ v, fun q hq => hμ₀ v hv q (hu hq), ?_, ?_⟩
  · exact (Finset.sum_subset hu fun q hq hqu => hμzero v hv q hq hqu).trans (hμ₁ v hv)
  · exact (Finset.sum_subset hu fun q hq hqu => by
      rw [hμzero v hv q hq hqu, zero_smul]).trans (hμv v hv)

theorem subset_of_mem_openSimplex_of_mem_convexHull {s t₁ t₂ : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (ht₁ : t₁ ⊆ s) (ht₂ : t₂ ⊆ s) {x : E}
    (hx₁ : x ∈ openSimplex t₁) (hx₂ : x ∈ convexHull ℝ (t₂ : Set E)) : t₁ ⊆ t₂ := by
  have h := subset_convexHull_of_mem_openSimplex hs ht₂
    ((subset_convexHull ℝ _).trans (convexHull_mono (Finset.coe_subset.mpr ht₁))) hx₁ hx₂
  intro v hv
  exact mem_of_mem_convexHull_of_affineIndependent hs ht₂ (ht₁ hv) (h (Finset.mem_coe.mpr hv))

theorem eq_of_mem_openSimplex_of_mem_openSimplex {s t₁ t₂ : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (ht₁ : t₁ ⊆ s) (ht₂ : t₂ ⊆ s) {x : E}
    (hx₁ : x ∈ openSimplex t₁) (hx₂ : x ∈ openSimplex t₂) : t₁ = t₂ :=
  Finset.Subset.antisymm
    (subset_of_mem_openSimplex_of_mem_convexHull hs ht₁ ht₂ hx₁
      (openSimplex_subset_convexHull _ hx₂))
    (subset_of_mem_openSimplex_of_mem_convexHull hs ht₂ ht₁ hx₂
      (openSimplex_subset_convexHull _ hx₁))

theorem exists_face_mem_openSimplex (K : Geometry.SimplicialComplex ℝ E) {x : E}
    (hx : x ∈ K.space) : ∃ t ∈ K.faces, x ∈ openSimplex t := by
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
  obtain ⟨t, hts, htne, hxt⟩ := exists_openSimplex_of_mem_convexHull hxs
  exact ⟨t, K.down_closed hs hts htne, hxt⟩

theorem face_subset_of_mem_openSimplex_of_mem_convexHull (K : Geometry.SimplicialComplex ℝ E)
    {s t : Finset E} (ht : t ∈ K.faces) (hs : s ∈ K.faces) {x : E} (hx : x ∈ openSimplex t)
    (hxs : x ∈ convexHull ℝ (s : Set E)) : t ⊆ s := by
  classical
  have hx' : x ∈ convexHull ℝ ((t ∩ s : Finset E) : Set E) := by
    rw [Finset.coe_inter]
    exact K.inter_subset_convexHull ht hs ⟨openSimplex_subset_convexHull t hx, hxs⟩
  exact (subset_of_mem_openSimplex_of_mem_convexHull (K.indep ht) (Finset.Subset.refl t)
    Finset.inter_subset_left hx hx').trans Finset.inter_subset_right

theorem face_eq_of_mem_openSimplex (K : Geometry.SimplicialComplex ℝ E) {t₁ t₂ : Finset E}
    (h₁ : t₁ ∈ K.faces) (h₂ : t₂ ∈ K.faces) {x : E} (hx₁ : x ∈ openSimplex t₁)
    (hx₂ : x ∈ openSimplex t₂) : t₁ = t₂ :=
  Finset.Subset.antisymm
    (face_subset_of_mem_openSimplex_of_mem_convexHull K h₁ h₂ hx₁
      (openSimplex_subset_convexHull _ hx₂))
    (face_subset_of_mem_openSimplex_of_mem_convexHull K h₂ h₁ hx₂
      (openSimplex_subset_convexHull _ hx₁))

open Classical in
noncomputable def weights (s : Finset E) (x : E) : E → ℝ :=
  if h : x ∈ convexHull ℝ (s : Set E) then
    Classical.choose (mem_convexHull_iff_exists_weights.mp h)
  else 0

theorem weights_spec {s : Finset E} {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) :
    (∀ v ∈ s, 0 ≤ weights s x v) ∧ ∑ v ∈ s, weights s x v = 1 ∧
      ∑ v ∈ s, weights s x v • v = x := by
  rw [weights, dite_eq_left hx]
  exact Classical.choose_spec (mem_convexHull_iff_exists_weights.mp hx)

theorem weights_nonneg {s : Finset E} {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) {v : E}
    (hv : v ∈ s) : 0 ≤ weights s x v :=
  (weights_spec hx).1 v hv

theorem sum_weights {s : Finset E} {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) :
    ∑ v ∈ s, weights s x v = 1 :=
  (weights_spec hx).2.1

theorem sum_weights_smul {s : Finset E} {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) :
    ∑ v ∈ s, weights s x v • v = x :=
  (weights_spec hx).2.2

theorem weights_eq {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E)) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) {w : E → ℝ} (hw : ∑ v ∈ s, w v = 1)
    (hwx : ∑ v ∈ s, w v • v = x) : ∀ v ∈ s, weights s x v = w v :=
  eq_on_of_sum_smul_eq hs (sum_weights hx) hw ((sum_weights_smul hx).trans hwx.symm)

theorem weights_combo {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E)) {a b : E}
    (ha : a ∈ convexHull ℝ (s : Set E)) (hb : b ∈ convexHull ℝ (s : Set E)) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hab : α + β = 1) :
    ∀ v ∈ s, weights s (α • a + β • b) v = α * weights s a v + β * weights s b v := by
  have hmem : α • a + β • b ∈ convexHull ℝ (s : Set E) :=
    (convex_convexHull ℝ _) ha hb hα hβ hab
  refine weights_eq hs hmem ?_ ?_
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_weights ha,
      sum_weights hb, mul_one, mul_one, hab]
  · simp_rw [add_smul, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, sum_weights_smul ha,
      sum_weights_smul hb]

theorem mem_openSimplex_iff_weights_pos {s t : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (ht : t ⊆ s) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) :
    x ∈ openSimplex t ↔ ∀ v ∈ s, 0 < weights s x v ↔ v ∈ t := by
  classical
  constructor
  · rintro ⟨w, hw₀, hw₁, hwx⟩ v hv
    let w' : E → ℝ := fun u => if u ∈ t then w u else 0
    have hw'₁ : ∑ u ∈ s, w' u = 1 := by
      simp only [w']
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr ht]
      exact hw₁
    have hw'x : ∑ u ∈ s, w' u • u = x := by
      simp only [w', ite_smul, zero_smul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr ht]
      exact hwx
    rw [weights_eq hs hx hw'₁ hw'x v hv]
    by_cases hvt : v ∈ t
    · simp [w', hvt, hw₀ v hvt]
    · simp [w', hvt]
  · intro h
    refine ⟨weights s x, fun v hv => (h v (ht hv)).mpr hv, ?_, ?_⟩
    · rw [← sum_weights hx]
      exact Finset.sum_subset ht fun v hv hvt =>
        le_antisymm (not_lt.mp (mt (h v hv).mp hvt)) (weights_nonneg hx hv)
    · refine (Finset.sum_subset ht fun v hv hvt => ?_).trans (sum_weights_smul hx)
      rw [le_antisymm (not_lt.mp (mt (h v hv).mp hvt)) (weights_nonneg hx hv), zero_smul]

theorem mem_openSimplex_self_iff {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E))
    {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) :
    x ∈ openSimplex s ↔ ∀ v ∈ s, 0 < weights s x v := by
  rw [mem_openSimplex_iff_weights_pos hs (Finset.Subset.refl s) hx]
  exact forall₂_congr fun v hv => ⟨fun h => h.mpr hv, fun h => ⟨fun _ => hv, fun _ => h⟩⟩

theorem weights_sum_smul {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E)) {ι : Type*}
    (S : Finset ι) {p : ι → E} (hp : ∀ i ∈ S, p i ∈ convexHull ℝ (s : Set E)) {l : ι → ℝ}
    (hl : ∀ i ∈ S, 0 ≤ l i) (hl₁ : ∑ i ∈ S, l i = 1) :
    ∀ v ∈ s, weights s (∑ i ∈ S, l i • p i) v = ∑ i ∈ S, l i * weights s (p i) v := by
  have hmem : ∑ i ∈ S, l i • p i ∈ convexHull ℝ (s : Set E) :=
    (convex_convexHull ℝ _).sum_mem hl hl₁ hp
  refine weights_eq hs hmem ?_ ?_
  · rw [Finset.sum_comm, ← hl₁]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.mul_sum, sum_weights (hp i hi), mul_one]
  · simp_rw [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.smul_sum, sum_weights_smul (hp i hi)]

theorem mem_openSimplex_image_iff [DecidableEq E] {ι : Type*} {S : Finset ι} {f : ι → E}
    (hf : Set.InjOn f S) {x : E} :
    x ∈ openSimplex (S.image f) ↔
      ∃ l : ι → ℝ, (∀ i ∈ S, 0 < l i) ∧ ∑ i ∈ S, l i = 1 ∧ ∑ i ∈ S, l i • f i = x := by
  classical
  constructor
  · rintro ⟨w, hw₀, hw₁, hwx⟩
    refine ⟨w ∘ f, fun i hi => hw₀ _ (Finset.mem_image_of_mem f hi), ?_, ?_⟩
    · rw [← hw₁, Finset.sum_image fun i hi j hj h => hf hi hj h]
      rfl
    · rw [← hwx, Finset.sum_image fun i hi j hj h => hf hi hj h]
      rfl
  · rintro ⟨l, hl₀, hl₁, hlx⟩
    let w : E → ℝ := fun p => ∑ i ∈ S.filter fun i => f i = p, l i
    have hw : ∀ i ∈ S, w (f i) = l i := by
      intro i hi
      have hfilter : (S.filter fun j => f j = f i) = {i} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_singleton]
        exact ⟨fun h => hf h.1 hi h.2, fun h => by subst h; exact ⟨hi, rfl⟩⟩
      simp only [w, hfilter, Finset.sum_singleton]
    refine ⟨w, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      rw [hw i hi]
      exact hl₀ i hi
    · rw [Finset.sum_image fun i hi j hj h => hf hi hj h, ← hl₁]
      exact Finset.sum_congr rfl fun i hi => hw i hi
    · rw [Finset.sum_image fun i hi j hj h => hf hi hj h, ← hlx]
      exact Finset.sum_congr rfl fun i hi => by rw [hw i hi]

end DifferentialGeometry.Topology.PiecewiseLinear
