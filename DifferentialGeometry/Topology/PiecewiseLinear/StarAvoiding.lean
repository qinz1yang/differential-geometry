import DifferentialGeometry.Topology.PiecewiseLinear.LinkRadial
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexAvoiding

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def starAvoiding [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) (t : Finset E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | s ∈ K.faces ∧ s ∪ t ∈ K.faces ∧ ¬ t ⊆ s}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hst, hts⟩
    refine ⟨K.nonempty_of_mem_faces hs, fun u hus hu => ⟨K.down_closed hs hus hu, ?_, ?_⟩⟩
    · exact K.down_closed hst (Finset.union_subset_union_left hus)
        (hu.mono Finset.subset_union_left)
    · exact fun h => hts (h.trans hus)
  indep hs := K.indep hs.1
  inter_subset_convexHull hs hu := K.inter_subset_convexHull hs.1 hu.1

theorem mem_starAvoiding_faces_iff [DecidableEq E] {K : Geometry.SimplicialComplex ℝ E}
    {t s : Finset E} :
    s ∈ (starAvoiding K t).faces ↔ s ∈ K.faces ∧ s ∪ t ∈ K.faces ∧ ¬ t ⊆ s := Iff.rfl

theorem starAvoiding_faces_subset [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E)
    (t : Finset E) : (starAvoiding K t).faces ⊆ K.faces := fun _ hs => hs.1

theorem starAvoiding_faces_finite [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (t : Finset E) : (starAvoiding K t).faces.Finite :=
  (Set.toFinite K.faces).subset (starAvoiding_faces_subset K t)

theorem starAvoiding_space_subset [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E)
    (t : Finset E) : (starAvoiding K t).space ⊆ K.space := by
  intro y hy
  obtain ⟨s, hs, hys⟩ := (starAvoiding K t).mem_space_iff.mp hy
  exact K.convexHull_subset_space hs.1 hys

theorem not_radial_lt_one_starAvoiding [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E)
    {t : Finset E} {x : E} (hx : x ∈ openSimplex t) {x₁ x₂ : E}
    (h₁ : x₁ ∈ (starAvoiding K t).space) (h₂ : x₂ ∈ (starAvoiding K t).space) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hx₂ : x₂ = x + r • (x₁ - x)) : False := by
  obtain ⟨s₁, hs₁, hx₁s⟩ := (starAvoiding K t).mem_space_iff.mp h₁
  obtain ⟨s₂, hs₂, hx₂s⟩ := (starAvoiding K t).mem_space_iff.mp h₂
  have hTK : s₁ ∪ t ∈ K.faces := hs₁.2.1
  have hTi : AffineIndependent ℝ ((↑) : (s₁ ∪ t : Finset E) → E) := K.indep hTK
  have hxT : x ∈ convexHull ℝ ((s₁ ∪ t : Finset E) : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right)
      (openSimplex_subset_convexHull _ hx)
  have hx₁T : x₁ ∈ convexHull ℝ ((s₁ ∪ t : Finset E) : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left) hx₁s
  have hx₂T : x₂ ∈ convexHull ℝ ((s₁ ∪ t : Finset E) : Set E) := by
    rw [hx₂, add_smul_sub_eq_combo]
    exact (convex_convexHull ℝ _) hxT hx₁T (by linarith) hr0.le (by ring)
  obtain ⟨v, hvt, hvs₂⟩ := Finset.not_subset.mp hs₂.2.2
  have hvT : v ∈ s₁ ∪ t := Finset.mem_union_right _ hvt
  have hcombo := weights_combo hTi hxT hx₁T (by linarith : (0 : ℝ) ≤ 1 - r) hr0.le (by ring) v hvT
  rw [← add_smul_sub_eq_combo, ← hx₂] at hcombo
  have hpos : 0 < weights (s₁ ∪ t) x v :=
    weights_pos_of_mem_openSimplex_of_subset hTi Finset.subset_union_right hx hvt
  have hnn : 0 ≤ weights (s₁ ∪ t) x₁ v := weights_nonneg hx₁T hvT
  have hinter : x₂ ∈ convexHull ℝ ((s₂ ∩ (s₁ ∪ t) : Finset E) : Set E) := by
    rw [Finset.coe_inter]
    exact K.inter_subset_convexHull hs₂.1 hTK ⟨hx₂s, hx₂T⟩
  have hzero : weights (s₁ ∪ t) x₂ v = 0 :=
    weights_eq_zero_of_subset_of_notMem hTi Finset.inter_subset_right hinter hvT fun h =>
      hvs₂ (Finset.mem_inter.mp h).1
  rw [hzero] at hcombo
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - r) hpos, mul_nonneg hr0.le hnn]

theorem isConeBase_starAvoiding [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E)
    {t : Finset E} (ht : t ∈ K.faces) {x : E} (hx : x ∈ openSimplex t) :
    IsConeBase x (starAvoiding K t) where
  notMem_space := by
    intro hmem
    obtain ⟨s, hs, hxs⟩ := (starAvoiding K t).mem_space_iff.mp hmem
    exact hs.2.2 (face_subset_of_mem_openSimplex_of_mem_convexHull K ht hs.1 hx hxs)
  indep s hs := by
    have h : AffineIndependent ℝ ((↑) : ((insert x s : Finset E) : Set E) → E) :=
      affineIndependent_insert_of_not_subset (K.indep hs.2.1) Finset.subset_union_right hx
        Finset.subset_union_left hs.2.2
    rwa [Finset.coe_insert] at h
  radial := by
    intro x₁ h₁ x₂ h₂ r hr hx₂
    rcases lt_trichotomy r 1 with h | h | h
    · exact (not_radial_lt_one_starAvoiding K hx h₁ h₂ hr h hx₂).elim
    · rw [hx₂, h, one_smul, add_sub_cancel]
    · have hinv : x₁ = x + r⁻¹ • (x₂ - x) := by
        rw [hx₂, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, add_sub_cancel]
      exact (not_radial_lt_one_starAvoiding K hx h₂ h₁ (inv_pos.mpr hr)
        (inv_lt_one_of_one_lt₀ h) hinv).elim

theorem exists_isPLHomeomorphOn_geometricLink_starAvoiding [FiniteDimensional ℝ E] [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {t : Finset E} (ht : t ∈ K.faces)
    {x : E} (hx : x ∈ openSimplex t) {K' : Geometry.SimplicialComplex ℝ E} [Finite K'.faces]
    (hK' : IsSubdivision K' K) (hx' : {x} ∈ K'.faces) :
    ∃ f : E → E, IsPLHomeomorphOn f (SimplicialComplex.geometricLink K' {x}).space
      (starAvoiding K t).space := by
  have : Finite (starAvoiding K t).faces := (starAvoiding_faces_finite K t).to_subtype
  refine exists_isPLHomeomorphOn_geometricLink_of_isConeBase K' hx' (starAvoiding K t)
    (isConeBase_starAvoiding K ht hx) ?_ ?_
  · intro y hy hyx
    obtain ⟨s, ⟨hs, hxs⟩, hys⟩ := mem_iUnion₂.mp (closedStar_subset_of_isSubdivision hK' x hy)
    have hts : t ⊆ s := face_subset_of_mem_openSimplex_of_mem_convexHull K ht hs hx hxs
    obtain ⟨w, hwt, hyw⟩ :=
      exists_mem_convexHull_insert_erase_of_mem_openSimplex (K.indep hs) hts hx hys
    have hne : (s.erase w).Nonempty := by
      rcases (s.erase w).eq_empty_or_nonempty with h | h
      · rw [h, Finset.insert_empty, Finset.coe_singleton, convexHull_singleton,
          Set.mem_singleton_iff] at hyw
        exact absurd hyw hyx
      · exact h
    have hunion : s.erase w ∪ t = s := by
      refine Finset.Subset.antisymm (Finset.union_subset (Finset.erase_subset w s) hts)
        fun u hu => ?_
      by_cases huw : u = w
      · refine Finset.mem_union_right _ ?_
        rw [huw]
        exact hwt
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨huw, hu⟩)
    refine ⟨s.erase w, mem_starAvoiding_faces_iff.mpr
      ⟨K.down_closed hs (Finset.erase_subset w s) hne, ?_, ?_⟩, hyw⟩
    · rw [hunion]
      exact hs
    · exact fun h => Finset.notMem_erase w s (h hwt)
  · intro y hy r hr0 hr1
    obtain ⟨s, hs, hys⟩ := (starAvoiding K t).mem_space_iff.mp hy
    rw [hK'.space_eq, add_smul_sub_eq_combo]
    refine K.convexHull_subset_space hs.2.1 ((convex_convexHull ℝ _) ?_ ?_ (by linarith) hr0.le
      (by ring))
    · exact convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right)
        (openSimplex_subset_convexHull _ hx)
    · exact convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left) hys

theorem exists_isPLHomeomorphOn_geometricLink_of_mem_openSimplex [FiniteDimensional ℝ E]
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {t : Finset E}
    (ht : t ∈ K.faces) {x y : E} (hx : x ∈ openSimplex t) (hy : y ∈ openSimplex t)
    {K₁ K₂ : Geometry.SimplicialComplex ℝ E} [Finite K₁.faces] [Finite K₂.faces]
    (hK₁ : IsSubdivision K₁ K) (hK₂ : IsSubdivision K₂ K) (hx' : {x} ∈ K₁.faces)
    (hy' : {y} ∈ K₂.faces) :
    ∃ f : E → E, IsPLHomeomorphOn f (SimplicialComplex.geometricLink K₁ {x}).space
      (SimplicialComplex.geometricLink K₂ {y}).space := by
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_geometricLink_starAvoiding K ht hx hK₁ hx'
  obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_geometricLink_starAvoiding K ht hy hK₂ hy'
  exact ⟨_, hf.trans hg.symm⟩

end DifferentialGeometry.Topology.PiecewiseLinear
