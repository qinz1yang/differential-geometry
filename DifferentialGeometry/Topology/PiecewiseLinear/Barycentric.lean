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
      simp only [ν, ω', hqu, if_false] at this
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

end DifferentialGeometry.Topology.PiecewiseLinear
