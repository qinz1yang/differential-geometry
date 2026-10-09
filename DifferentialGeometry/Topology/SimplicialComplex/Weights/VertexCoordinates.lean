import DifferentialGeometry.Topology.SimplicialComplex.Weights.ProjectiveSimplex
import DifferentialGeometry.Topology.SimplicialComplex.Stellar.HyperplaneRestriction

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry
open scoped BigOperators

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [DecidableEq E] in
theorem interpolateVertices_nonneg (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 ≤ w v) (x : K.space) :
    0 ≤ interpolateVertices K hK w x := by
  classical
  obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp x.2
  have hsub : w '' (s : Set E) ⊆ Ici 0 := by
    rintro _ ⟨v, hv, rfl⟩
    exact hw v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v))
  exact (convexHull_min hsub (convex_Ici (0 : ℝ)))
    (interpolateVertices_mem_convexHull K hK w ⟨s, hs⟩ x hx)

omit [DecidableEq E] in
theorem interpolation_zero_mem_face_filter (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 ≤ w v)
    (x : K.space) (hz : interpolateVertices K hK w x = 0)
    {s : Finset E} (hs : s ∈ K.faces) (hx : x.1 ∈ convexHull ℝ (s : Set E)) :
    x.1 ∈ convexHull ℝ ((s.filter (fun v => w v = 0) : Finset E) : Set E) := by
  classical
  obtain ⟨A, hA, hAx⟩ := interpolateVertices_affineOn K hK w ⟨s, hs⟩
  have heq : s.filter (fun v => A v = 0) = s.filter (fun v => w v = 0) :=
    Finset.filter_congr (fun v hv => by rw [hA v hv])
  rw [← heq, ← convexHull_inter_affine_zero_of_nonneg s A (fun v hv => by
    rw [hA v hv]
    exact hw v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v)))]
  exact ⟨hx, (hAx x hx).symm.trans hz⟩

omit [DecidableEq E] in
theorem interpolateVertices_eq_zero_iff (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 ≤ w v) (x : K.space) :
    interpolateVertices K hK w x = 0 ↔ x.1 ∈ (vertexRestriction K {v | w v = 0}).space := by
  classical
  constructor
  · intro hz
    obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp x.2
    obtain ⟨A, hA, hAx⟩ := interpolateVertices_affineOn K hK w ⟨s, hs⟩
    have hxs : x.1 ∈ convexHull ℝ ((s.filter (fun v => A v = 0) : Finset E) : Set E) := by
      rw [← convexHull_inter_affine_zero_of_nonneg s A (fun v hv => by
        rw [hA v hv]
        exact hw v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
          (Finset.singleton_nonempty v)))]
      exact ⟨hx, (hAx x hx).symm.trans hz⟩
    have hne : (s.filter (fun v => A v = 0)).Nonempty := by
      exact_mod_cast (convexHull_nonempty_iff.mp ⟨x.1, hxs⟩)
    exact (vertexRestriction K {v | w v = 0}).convexHull_subset_space
      ⟨K.down_closed hs (Finset.filter_subset _ _) hne, fun v hv =>
        (hA v (Finset.mem_filter.mp hv).1).symm.trans (Finset.mem_filter.mp hv).2⟩ hxs
  · intro hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact interpolateVertices_eq_affineMap K hK w ⟨s, hs.1⟩ (AffineMap.const ℝ E 0)
      (fun v hv => (hs.2 hv).symm) x hxs

omit [DecidableEq E] in
theorem interpolateVertices_pos_iff (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 ≤ w v) (x : K.space) :
    0 < interpolateVertices K hK w x ↔
      x.1 ∉ (vertexRestriction K {v | w v = 0}).space := by
  classical
  rw [← interpolateVertices_eq_zero_iff K hK w hw x]
  exact lt_iff_le_and_ne.trans (by simp [interpolateVertices_nonneg K hK w hw x, eq_comm])

omit [DecidableEq E] in
theorem normalized_interpolation_mem_face (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 ≤ w v)
    (x : K.space) (hpos : 0 < interpolateVertices K hK w x)
    {s : Finset E} (hs : s ∈ K.faces) (hxs : x.1 ∈ convexHull ℝ (s : Set E)) :
    (interpolateVertices K hK w x)⁻¹ • interpolateVertices K hK (fun v => w v • v) x ∈
      convexHull ℝ ((s.filter (fun v => w v ≠ 0) : Finset E) : Set E) := by
  classical
  obtain ⟨a, ha0, ha, hax⟩ := Finset.mem_convexHull'.mp hxs
  let D := interpolateVertices K hK w x
  let b : E → ℝ := fun v => a v * w v / D
  let t := s.filter (fun v => w v ≠ 0)
  have hb0 : ∀ v ∈ s, 0 ≤ b v := fun v hv =>
    div_nonneg (mul_nonneg (ha0 v hv) (hw v (K.down_closed hs
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)))) hpos.le
  have hzero (v : E) (hv : v ∈ s) (hnt : v ∉ t) : b v = 0 := by
    have hwv : w v = 0 := by simpa [t, hv] using hnt
    simp [b, hwv]
  have hbs : ∑ v ∈ s, b v = 1 := by
    dsimp [b]
    rw [← Finset.sum_div]
    have heq := interpolateVertices_eq_sum K hK w ⟨s, hs⟩ x a ha0 ha hax
    simp only [smul_eq_mul] at heq
    rw [← heq, div_self hpos.ne']
  have hbt : ∑ v ∈ t, b v = 1 :=
    (Finset.sum_subset (Finset.filter_subset _ _) hzero).trans hbs
  have hpoint : ∑ v ∈ t, b v • v =
      D⁻¹ • interpolateVertices K hK (fun v => w v • v) x := by
    rw [interpolateVertices_eq_sum K hK _ ⟨s, hs⟩ x a ha0 ha hax, Finset.smul_sum]
    calc
      ∑ v ∈ t, b v • v = ∑ v ∈ s, b v • v := Finset.sum_subset
        (Finset.filter_subset _ _) (fun v hv hnt => by rw [hzero v hv hnt, zero_smul])
      _ = _ := Finset.sum_congr rfl (fun v _ => by
        dsimp [b]
        simp only [smul_smul]
        congr 1
        rw [div_eq_mul_inv]
        ring)
  exact Finset.mem_convexHull'.mpr
    ⟨b, fun v hv => hb0 v (Finset.mem_filter.mp hv).1, hbt, hpoint⟩

omit [DecidableEq E] in
theorem normalized_interpolation_mem_vertexRestriction (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 ≤ w v)
    (x : K.space) (hpos : 0 < interpolateVertices K hK w x) :
    (interpolateVertices K hK w x)⁻¹ • interpolateVertices K hK (fun v => w v • v) x ∈
      (vertexRestriction K {v | w v ≠ 0}).space := by
  classical
  obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp x.2
  have hm := normalized_interpolation_mem_face K hK w hw x hpos hs hx
  have hne : (s.filter (fun v => w v ≠ 0)).Nonempty := by
    exact_mod_cast (convexHull_nonempty_iff.mp ⟨_, hm⟩)
  exact (vertexRestriction K {v | w v ≠ 0}).convexHull_subset_space
    ⟨K.down_closed hs (Finset.filter_subset _ _) hne,
      fun v hv => (Finset.mem_filter.mp hv).2⟩ hm

end DifferentialGeometry.Topology.Engulfing
