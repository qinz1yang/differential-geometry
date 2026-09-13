import DifferentialGeometry.Topology.PiecewiseLinear.Cone

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexHull_inter_subset_of_affineIndependent {T τ₁ τ₂ : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (h₁ : τ₁ ⊆ T) (h₂ : τ₂ ⊆ T) :
    convexHull ℝ (τ₁ : Set E) ∩ convexHull ℝ (τ₂ : Set E) ⊆
      convexHull ℝ ((τ₁ : Set E) ∩ (τ₂ : Set E)) := by
  classical
  rintro x ⟨hx₁, hx₂⟩
  have hxT : x ∈ convexHull ℝ (T : Set E) := convexHull_mono (Finset.coe_subset.mpr h₁) hx₁
  have hzero : ∀ v ∈ T, v ∉ τ₁ ∩ τ₂ → weights T x v = 0 := by
    intro v hv hvν
    rw [Finset.mem_inter, not_and_or] at hvν
    rcases hvν with h | h
    · exact weights_eq_zero_of_subset_of_notMem hT h₁ hx₁ hv h
    · exact weights_eq_zero_of_subset_of_notMem hT h₂ hx₂ hv h
  rw [← Finset.coe_inter]
  refine mem_convexHull_iff_exists_weights.mpr ⟨weights T x,
    fun v hv => weights_nonneg hxT (h₁ (Finset.mem_of_mem_inter_left hv)), ?_, ?_⟩
  · exact (Finset.sum_subset (Finset.inter_subset_left.trans h₁) hzero).trans (sum_weights hxT)
  · refine (Finset.sum_subset (Finset.inter_subset_left.trans h₁) fun v hv hvν => ?_).trans
      (sum_weights_smul hxT)
    rw [hzero v hv hvν, zero_smul]

theorem affineIndependent_of_subset {T τ : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    (hτ : τ ⊆ T) : AffineIndependent ℝ ((↑) : τ → E) :=
  AffineIndependent.mono (t := (T : Set E)) hT (Finset.coe_subset.mpr hτ)

def boundaryFaces (T : Finset E) : Set (Finset E) := {τ | τ ⊆ T ∧ τ.Nonempty ∧ τ ≠ T}

def boundaryComplex (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) :
    Geometry.SimplicialComplex ℝ E where
  faces := boundaryFaces T
  isRelLowerSet_faces := by
    rintro τ ⟨hτT, hne, hτ⟩
    exact ⟨hne, fun u huτ hu =>
      ⟨huτ.trans hτT, hu, fun h => hτ (Finset.Subset.antisymm hτT (h ▸ huτ))⟩⟩
  indep := by
    rintro τ ⟨hτT, -, -⟩
    exact affineIndependent_of_subset hT hτT
  inter_subset_convexHull := by
    rintro τ₁ τ₂ ⟨h₁, -, -⟩ ⟨h₂, -, -⟩
    exact convexHull_inter_subset_of_affineIndependent hT h₁ h₂

theorem mem_boundaryComplex_faces_iff {T : Finset E} {hT : AffineIndependent ℝ ((↑) : T → E)}
    {τ : Finset E} : τ ∈ (boundaryComplex T hT).faces ↔ τ ⊆ T ∧ τ.Nonempty ∧ τ ≠ T := Iff.rfl

theorem boundaryComplex_faces_finite (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) :
    (boundaryComplex T hT).faces.Finite :=
  (Set.toFinite (T.powerset : Set (Finset E))).subset fun _ hτ =>
    Finset.mem_coe.mpr (Finset.mem_powerset.mpr hτ.1)

section Boundary

variable [DecidableEq E]

theorem boundaryComplex_space (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : 2 ≤ T.card) :
    (boundaryComplex T hT).space = ⋃ v ∈ T, convexHull ℝ ((T.erase v : Finset E) : Set E) := by
  ext x
  rw [Geometry.SimplicialComplex.mem_space_iff, mem_iUnion₂]
  constructor
  · rintro ⟨τ, ⟨hτT, -, hτ⟩, hx⟩
    obtain ⟨v, hvT, hvτ⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hτT, hτ⟩)
    refine ⟨v, hvT, convexHull_mono (Finset.coe_subset.mpr fun u hu => ?_) hx⟩
    exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem hu hvτ, hτT hu⟩
  · rintro ⟨v, hv, hx⟩
    refine ⟨T.erase v, ⟨Finset.erase_subset v T, ?_, ?_⟩, hx⟩
    · rw [← Finset.card_pos, Finset.card_erase_of_mem hv]
      omega
    · intro h
      have := Finset.notMem_erase v T
      rw [h] at this
      exact this hv

theorem notMem_boundary_of_mem_openSimplex {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {p : E} (hp : p ∈ openSimplex T) :
    p ∉ ⋃ v ∈ T, convexHull ℝ ((T.erase v : Finset E) : Set E) := by
  intro h
  obtain ⟨v, hv, hpv⟩ := mem_iUnion₂.mp h
  have hpT : p ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull T hp
  have hpos := (mem_openSimplex_self_iff hT hpT).mp hp v hv
  have hzero := weights_eq_zero_of_subset_of_notMem hT (Finset.erase_subset v T) hpv hv
    (Finset.notMem_erase v T)
  rw [hzero] at hpos
  exact lt_irrefl _ hpos

theorem not_radial_lt_one_boundary {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    {p : E} (hp : p ∈ openSimplex T) {x y : E}
    (hx : x ∈ ⋃ v ∈ T, convexHull ℝ ((T.erase v : Finset E) : Set E))
    (hy : y ∈ ⋃ v ∈ T, convexHull ℝ ((T.erase v : Finset E) : Set E)) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) (hyx : y = p + t • (x - p)) : False := by
  obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp hy
  obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
  have hxT : x ∈ convexHull ℝ (T : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset u T)) hxu
  have hpT : p ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull T hp
  have hyv0 : weights T y v = 0 :=
    weights_eq_zero_of_subset_of_notMem hT (Finset.erase_subset v T) hyv hv
      (Finset.notMem_erase v T)
  have hpv : 0 < weights T p v := (mem_openSimplex_self_iff hT hpT).mp hp v hv
  have hxv : 0 ≤ weights T x v := weights_nonneg hxT hv
  have hcombo := weights_combo hT hpT hxT (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring) v hv
  rw [← add_smul_sub_eq_combo, ← hyx, hyv0] at hcombo
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - t) hpv, mul_nonneg ht0.le hxv]

theorem isRadiallyInjective_boundary {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    {p : E} (hp : p ∈ openSimplex T) :
    IsRadiallyInjective p (⋃ v ∈ T, convexHull ℝ ((T.erase v : Finset E) : Set E)) := by
  intro x hx y hy t ht hyx
  rcases lt_trichotomy t 1 with h | h | h
  · exact (not_radial_lt_one_boundary hT hp hx hy ht h hyx).elim
  · rw [hyx, h, one_smul, add_sub_cancel]
  · have hxy : x = p + t⁻¹ • (y - p) := by
      rw [hyx, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_sub_cancel]
    exact (not_radial_lt_one_boundary hT hp hy hx (inv_pos.mpr ht)
      (inv_lt_one_of_one_lt₀ h) hxy).elim

theorem notMem_erase_of_mem_openSimplex {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    {p : E} (hp : p ∈ openSimplex T) {v : E} (hv : v ∈ T) : p ∉ T.erase v := by
  intro hpv
  have hpT : p ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull T hp
  have hpos := (mem_openSimplex_self_iff hT hpT).mp hp
  have hpT' : p ∈ T := Finset.mem_of_mem_erase hpv
  have hne : v ≠ p := (Finset.ne_of_mem_erase hpv).symm
  have hone : weights T p p = 1 := by
    have h := weights_eq hT hpT (w := fun u => if u = p then 1 else 0) (by simp [hpT'])
      (by simp [ite_smul, hpT']) p hpT'
    simpa using h
  have hsum := sum_weights hpT
  rw [← Finset.add_sum_erase T _ hpT'] at hsum
  have hrest : 0 < ∑ u ∈ T.erase p, weights T p u :=
    Finset.sum_pos' (fun u hu => (hpos u (Finset.mem_of_mem_erase hu)).le)
      ⟨v, Finset.mem_erase.mpr ⟨hne, hv⟩, hpos v hv⟩
  linarith

theorem exists_mem_convexHull_insert_erase {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {p : E} (hp : p ∈ openSimplex T) {x : E}
    (hx : x ∈ convexHull ℝ (T : Set E)) :
    ∃ v ∈ T, x ∈ convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E) := by
  have hpT : p ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull T hp
  have hpos : ∀ v ∈ T, 0 < weights T p v := (mem_openSimplex_self_iff hT hpT).mp hp
  have hne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := sum_weights hpT
    rw [h, Finset.sum_empty] at this
    exact zero_ne_one this
  obtain ⟨v₀, hv₀, hmin⟩ :=
    Finset.exists_min_image T (fun v => weights T x v / weights T p v) hne
  set s : ℝ := weights T x v₀ / weights T p v₀ with hs
  have hs0 : 0 ≤ s := div_nonneg (weights_nonneg hx hv₀) (hpos v₀ hv₀).le
  have ha : ∀ v ∈ T, 0 ≤ weights T x v - s * weights T p v := fun v hv => by
    have h := hmin v hv
    rw [le_div_iff₀ (hpos v hv)] at h
    linarith
  have ha₀ : weights T x v₀ - s * weights T p v₀ = 0 := by
    rw [hs, div_mul_cancel₀ _ (hpos v₀ hv₀).ne', sub_self]
  have hpv₀ : p ∉ T.erase v₀ := notMem_erase_of_mem_openSimplex hT hp hv₀
  have hsumT : ∑ v ∈ T, (weights T x v - s * weights T p v) = 1 - s := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_weights hx, sum_weights hpT, mul_one]
  have hsum_erase : ∑ v ∈ T.erase v₀, (weights T x v - s * weights T p v) = 1 - s := by
    rw [← hsumT, ← Finset.add_sum_erase T _ hv₀, ha₀, zero_add]
  have hsmulT : ∑ v ∈ T, (weights T x v - s * weights T p v) • v = x - s • p := by
    simp_rw [sub_smul, mul_smul]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, sum_weights_smul hx, sum_weights_smul hpT]
  have hsmul_erase : ∑ v ∈ T.erase v₀, (weights T x v - s * weights T p v) • v = x - s • p := by
    rw [← hsmulT, ← Finset.add_sum_erase T _ hv₀, ha₀, zero_smul, zero_add]
  set c : E → ℝ := fun u => if u = p then s else weights T x u - s * weights T p u with hc
  have hcp : c p = s := by simp only [hc, if_true]
  have hcu : ∀ u ∈ T.erase v₀, c u = weights T x u - s * weights T p u := fun u hu => by
    simp only [hc, if_neg (ne_of_mem_of_not_mem hu hpv₀)]
  refine ⟨v₀, hv₀, mem_convexHull_iff_exists_weights.mpr ⟨c, ?_, ?_, ?_⟩⟩
  · intro u hu
    rcases Finset.mem_insert.mp hu with h | h
    · rw [h, hcp]
      exact hs0
    · rw [hcu u h]
      exact ha u (Finset.mem_of_mem_erase h)
  · rw [Finset.sum_insert hpv₀, hcp, Finset.sum_congr rfl hcu, hsum_erase]
    ring
  · rw [Finset.sum_insert hpv₀, hcp, Finset.sum_congr rfl fun u hu => by rw [hcu u hu],
      hsmul_erase]
    abel

end Boundary

end DifferentialGeometry.Topology.PiecewiseLinear
