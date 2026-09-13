import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap
import DifferentialGeometry.Topology.SimplicialComplex.GeometricLink

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsRadiallyInjective (p : E) (S : Set E) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ t : ℝ, 0 < t → y = p + t • (x - p) → y = x

theorem add_smul_sub_eq_combo (p x : E) (s : ℝ) : p + s • (x - p) = (1 - s) • p + s • x := by
  simp only [sub_smul, one_smul, smul_sub]
  abel

theorem exists_ray_mem_convexHull_of_mem_convexHull_insert [DecidableEq E] {p : E}
    {τ : Finset E} {w : E} (hw : w ∈ convexHull ℝ ((insert p τ : Finset E) : Set E))
    (hwp : w ≠ p) : ∃ s : ℝ, 0 < s ∧ p + s • (w - p) ∈ convexHull ℝ (τ : Set E) := by
  by_cases hpτ : p ∈ τ
  · rw [Finset.insert_eq_of_mem hpτ] at hw
    exact ⟨1, one_pos, by rwa [one_smul, add_sub_cancel]⟩
  obtain ⟨μ, hμ₀, hμ₁, hμw⟩ := mem_convexHull_iff_exists_weights.mp hw
  rw [Finset.sum_insert hpτ] at hμ₁ hμw
  have hτ₀ : 0 ≤ ∑ v ∈ τ, μ v :=
    Finset.sum_nonneg fun v hv => hμ₀ v (Finset.mem_insert_of_mem hv)
  have hlt : μ p < 1 := by
    refine lt_of_le_of_ne (by linarith) fun h1 => hwp ?_
    have hzero : ∀ v ∈ τ, μ v = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg fun v hv =>
        hμ₀ v (Finset.mem_insert_of_mem hv)).mp ?_
      linarith
    rw [← hμw, h1, one_smul, Finset.sum_eq_zero fun v hv => by rw [hzero v hv, zero_smul],
      add_zero]
  set s : ℝ := (1 - μ p)⁻¹ with hs
  have hs_pos : 0 < s := inv_pos.mpr (by linarith)
  have hs1 : s * (1 - μ p) = 1 := inv_mul_cancel₀ (by linarith)
  refine ⟨s, hs_pos, mem_convexHull_iff_exists_weights.mpr ⟨fun v => s * μ v,
    fun v hv => mul_nonneg hs_pos.le (hμ₀ v (Finset.mem_insert_of_mem hv)), ?_, ?_⟩⟩
  · rw [← Finset.mul_sum]
    have : ∑ v ∈ τ, μ v = 1 - μ p := by linarith
    rw [this, hs1]
  · have h1 : s • (1 - μ p) • p = p := by rw [smul_smul, hs1, one_smul]
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, ← hμw]
    calc s • ∑ v ∈ τ, μ v • v
        = p - s • (1 - μ p) • p + s • ∑ v ∈ τ, μ v • v := by rw [h1, sub_self, zero_add]
      _ = p + s • (μ p • p + ∑ v ∈ τ, μ v • v - p) := by
          simp only [smul_sub, smul_add, sub_smul, one_smul]
          abel

theorem ne_of_mem_of_notMem_of_radial {p x y : E} {S : Set E} (hx : x ∈ S) (hp : p ∉ S)
    {t : ℝ} (ht : 0 < t) (hy : y = p + t • (x - p)) : y ≠ p := by
  intro hyp
  have h0 : t • (x - p) = 0 := by
    have h := congrArg (fun z => z - p) hy
    simp only [hyp, sub_self, add_sub_cancel_left] at h
    exact h.symm
  rcases smul_eq_zero.mp h0 with h | h
  · exact ht.ne' h
  · exact hp (sub_eq_zero.mp h ▸ hx)

open Classical in
noncomputable def radialRatio (p : E) (S : Set E) (w : E) : ℝ :=
  if h : ∃ t : ℝ, 0 < t ∧ p + t • (w - p) ∈ S then Classical.choose h else 1

noncomputable def radialProj (p : E) (S : Set E) (w : E) : E :=
  p + radialRatio p S w • (w - p)

theorem radialRatio_pos (p : E) (S : Set E) (w : E) : 0 < radialRatio p S w := by
  unfold radialRatio
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact one_pos

theorem radialProj_mem {p : E} {S : Set E} {w : E}
    (h : ∃ t : ℝ, 0 < t ∧ p + t • (w - p) ∈ S) : radialProj p S w ∈ S := by
  unfold radialProj radialRatio
  rw [dif_pos h]
  exact (Classical.choose_spec h).2

theorem radialProj_sub (p : E) (S : Set E) (w : E) :
    radialProj p S w - p = radialRatio p S w • (w - p) := by
  rw [radialProj, add_sub_cancel_left]

theorem IsRadiallyInjective.eq_radialProj {p : E} {S : Set E} (hS : IsRadiallyInjective p S)
    {w : E} {t : ℝ} (ht : 0 < t) (hmem : p + t • (w - p) ∈ S) :
    p + t • (w - p) = radialProj p S w := by
  have hr := radialProj_mem ⟨t, ht, hmem⟩
  have hpos := radialRatio_pos p S w
  refine hS _ hr _ hmem (t / radialRatio p S w) (div_pos ht hpos) ?_
  rw [radialProj_sub, smul_smul, div_mul_cancel₀ _ hpos.ne']

theorem IsRadiallyInjective.radialRatio_eq {p : E} {S : Set E} (hS : IsRadiallyInjective p S)
    {w : E} (hw : w ≠ p) {t : ℝ} (ht : 0 < t) (hmem : p + t • (w - p) ∈ S) :
    radialRatio p S w = t := by
  have h := hS.eq_radialProj ht hmem
  rw [radialProj, add_right_inj] at h
  have h' : (t - radialRatio p S w) • (w - p) = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h' with h0 | h0
  · exact (sub_eq_zero.mp h0).symm
  · exact absurd (sub_eq_zero.mp h0) hw

theorem IsRadiallyInjective.radialProj_eq_self {p : E} {S : Set E}
    (hS : IsRadiallyInjective p S) {w : E} (hw : w ∈ S) : radialProj p S w = w := by
  have h := hS.eq_radialProj one_pos (by rwa [one_smul, add_sub_cancel])
  rw [one_smul, add_sub_cancel] at h
  exact h.symm

structure IsConeBase (p : E) (L : Geometry.SimplicialComplex ℝ E) : Prop where
  notMem_space : p ∉ L.space
  indep : ∀ σ ∈ L.faces, AffineIndependent ℝ ((↑) : (insert p (σ : Set E) : Set E) → E)
  radial : IsRadiallyInjective p L.space

theorem mem_openSimplex_singleton (p : E) : p ∈ openSimplex ({p} : Finset E) :=
  ⟨fun _ => 1, fun _ _ => one_pos, by simp, by simp⟩

theorem mem_of_mem_convexHull_of_singleton_mem (K : Geometry.SimplicialComplex ℝ E) {p : E}
    (hp : {p} ∈ K.faces) {t : Finset E} (ht : t ∈ K.faces)
    (h : p ∈ convexHull ℝ (t : Set E)) : p ∈ t :=
  Finset.singleton_subset_iff.mp
    (face_subset_of_mem_openSimplex_of_mem_convexHull K hp ht (mem_openSimplex_singleton p) h)

theorem notMem_convexHull_of_affineIndependent_insert [DecidableEq E] {p : E} {σ : Finset E}
    (hpσ : p ∉ σ) (h : AffineIndependent ℝ ((↑) : {x // x ∈ (insert p σ : Finset E)} → E)) :
    p ∉ convexHull ℝ (σ : Set E) := fun hmem =>
  hpσ (mem_of_mem_convexHull_of_affineIndependent h (Finset.subset_insert p σ)
    (Finset.mem_insert_self p σ) hmem)

section Link

variable [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) {p : E}

theorem notMem_geometricLink_space :
    p ∉ (SimplicialComplex.geometricLink K {p}).space := by
  intro h
  obtain ⟨σ, hσ, hpσ⟩ := Geometry.SimplicialComplex.mem_space_iff.mp h
  obtain ⟨-, hpσ', hins⟩ := (SimplicialComplex.mem_geometricLink_singleton K p σ).mp hσ
  exact notMem_convexHull_of_affineIndependent_insert hpσ' (K.indep hins) hpσ

theorem mem_convexHull_insert_of_mem_geometricLink_space {x : E}
    (hx : x ∈ (SimplicialComplex.geometricLink K {p}).space) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : p + t • (x - p) ∈ K.space := by
  obtain ⟨σ, hσ, hxσ⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨-, -, hins⟩ := (SimplicialComplex.mem_geometricLink_singleton K p σ).mp hσ
  refine K.convexHull_subset_space hins ?_
  rw [add_smul_sub_eq_combo]
  refine (convex_convexHull ℝ _) (subset_convexHull ℝ _ ?_)
    (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert p σ)) hxσ)
    (by linarith) ht0 (by ring)
  exact Finset.mem_coe.mpr (Finset.mem_insert_self p σ)

theorem not_radial_lt_one_geometricLink {x y : E}
    (hx : x ∈ (SimplicialComplex.geometricLink K {p}).space)
    (hy : y ∈ (SimplicialComplex.geometricLink K {p}).space) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) (hyx : y = p + t • (x - p)) : False := by
  obtain ⟨σ, hσ, hxσ⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨σ', hσ', hyσ'⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hy
  obtain ⟨-, hpσ, hins⟩ := (SimplicialComplex.mem_geometricLink_singleton K p σ).mp hσ
  obtain ⟨-, hpσ', hins'⟩ := (SimplicialComplex.mem_geometricLink_singleton K p σ').mp hσ'
  have hpins : p ∈ convexHull ℝ ((insert p σ : Finset E) : Set E) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_self p σ))
  have hxins : x ∈ convexHull ℝ ((insert p σ : Finset E) : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert p σ)) hxσ
  have hyins : y ∈ convexHull ℝ ((insert p σ : Finset E) : Set E) := by
    rw [hyx, add_smul_sub_eq_combo]
    exact (convex_convexHull ℝ _) hpins hxins (by linarith) ht0.le (by ring)
  have hyK : y ∈ K.space := K.convexHull_subset_space hins hyins
  obtain ⟨u, hu, hyu⟩ := exists_face_mem_openSimplex K hyK
  have hu₁ : u ⊆ insert p σ :=
    face_subset_of_mem_openSimplex_of_mem_convexHull K hu hins hyu hyins
  have hu₂ : u ⊆ σ' := face_subset_of_mem_openSimplex_of_mem_convexHull K hu
    (SimplicialComplex.geometricLink_le K {p} hσ') hyu hyσ'
  have hpu : p ∉ u := fun h => hpσ' (hu₂ h)
  have huσ : u ⊆ σ := fun v hv => by
    rcases Finset.mem_insert.mp (hu₁ hv) with h | h
    · exact absurd (h ▸ hv) hpu
    · exact h
  have hyσ : y ∈ convexHull ℝ (σ : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr huσ) (openSimplex_subset_convexHull u hyu)
  have hzero : weights (insert p σ) y p = 0 :=
    weights_eq_zero_of_subset_of_notMem (K.indep hins) (Finset.subset_insert p σ) hyσ
      (Finset.mem_insert_self p σ) hpσ
  let w : E → ℝ := fun v => if v = p then 1 - t else t * weights σ x v
  have hw : ∀ v ∈ σ, w v = t * weights σ x v := fun v hv => by
    simp only [w, if_neg (ne_of_mem_of_not_mem hv hpσ)]
  have hw₁ : ∑ v ∈ insert p σ, w v = 1 := by
    rw [Finset.sum_insert hpσ, Finset.sum_congr rfl hw, ← Finset.mul_sum, sum_weights hxσ]
    simp [w]
  have hwy : ∑ v ∈ insert p σ, w v • v = y := by
    rw [Finset.sum_insert hpσ, Finset.sum_congr rfl fun v hv => by rw [hw v hv]]
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, sum_weights_smul hxσ, hyx, add_smul_sub_eq_combo]
    simp [w]
  have := weights_eq (K.indep hins) hyins hw₁ hwy p (Finset.mem_insert_self p σ)
  rw [hzero] at this
  simp only [w, if_true] at this
  linarith

theorem isRadiallyInjective_geometricLink :
    IsRadiallyInjective p (SimplicialComplex.geometricLink K {p}).space := by
  intro x hx y hy t ht hyx
  rcases lt_trichotomy t 1 with h | h | h
  · exact (not_radial_lt_one_geometricLink K hx hy ht h hyx).elim
  · rw [hyx, h, one_smul, add_sub_cancel]
  · have hxy : x = p + t⁻¹ • (y - p) := by
      rw [hyx, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_sub_cancel]
    exact (not_radial_lt_one_geometricLink K hy hx (inv_pos.mpr ht)
      (inv_lt_one_of_one_lt₀ h) hxy).elim

theorem isConeBase_geometricLink :
    IsConeBase p (SimplicialComplex.geometricLink K {p}) where
  notMem_space := notMem_geometricLink_space K
  indep σ hσ := by
    obtain ⟨-, -, hins⟩ := (SimplicialComplex.mem_geometricLink_singleton K p σ).mp hσ
    have h : AffineIndependent ℝ ((↑) : ((insert p σ : Finset E) : Set E) → E) := K.indep hins
    rwa [Finset.coe_insert] at h
  radial := isRadiallyInjective_geometricLink K

theorem exists_ray_mem_geometricLink_space_of_mem_closedStar (hp : {p} ∈ K.faces) {y : E}
    (hy : y ∈ closedStar K p) (hyp : y ≠ p) :
    ∃ s : ℝ, 0 < s ∧ p + s • (y - p) ∈ (SimplicialComplex.geometricLink K {p}).space := by
  obtain ⟨t, ⟨ht, hpt⟩, hyt⟩ := mem_iUnion₂.mp hy
  have hpt' : p ∈ t := mem_of_mem_convexHull_of_singleton_mem K hp ht hpt
  rw [← Finset.insert_erase hpt'] at hyt
  obtain ⟨s, hs, hmem⟩ := exists_ray_mem_convexHull_of_mem_convexHull_insert hyt hyp
  refine ⟨s, hs, Geometry.SimplicialComplex.mem_space_iff.mpr ⟨t.erase p, ?_, hmem⟩⟩
  refine (SimplicialComplex.mem_geometricLink_singleton K p _).mpr
    ⟨?_, Finset.notMem_erase p t, by rwa [Finset.insert_erase hpt']⟩
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  rw [hne, Finset.coe_empty, convexHull_empty] at hmem
  exact hmem

theorem exists_ray_mem_geometricLink_space [Finite K.faces] (hp : {p} ∈ K.faces) {x : E}
    (hxK : ∀ t : ℝ, 0 < t → t ≤ 1 → p + t • (x - p) ∈ K.space) (hxp : x ≠ p) :
    ∃ s : ℝ, 0 < s ∧ p + s • (x - p) ∈ (SimplicialComplex.geometricLink K {p}).space := by
  have hstar := closedStar_mem_nhdsWithin K p
  have htend : Filter.Tendsto (fun t : ℝ => p + t • (x - p)) (𝓝[>] 0) (𝓝[K.space] p) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous fun t : ℝ => p + t • (x - p) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have := hc.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      exact hxK t ht.1 ht.2.le
  obtain ⟨t, ht, hmem⟩ := (htend.eventually_mem hstar).and eventually_mem_nhdsWithin |>.exists
  have hyp : p + t • (x - p) ≠ p := by
    intro h
    have h0 : t • (x - p) = 0 := by
      have h' := congrArg (fun z => z - p) h
      simp only [sub_self, add_sub_cancel_left] at h'
      exact h'
    rcases smul_eq_zero.mp h0 with h | h
    · exact (ne_of_gt hmem) h
    · exact hxp (sub_eq_zero.mp h)
  obtain ⟨s, hs, hmem'⟩ := exists_ray_mem_geometricLink_space_of_mem_closedStar K hp ht hyp
  refine ⟨s * t, mul_pos hs hmem, ?_⟩
  rw [add_sub_cancel_left, smul_smul] at hmem'
  exact hmem'

end Link

end DifferentialGeometry.Topology.PiecewiseLinear
