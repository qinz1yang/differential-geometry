import DifferentialGeometry.Topology.PiecewiseLinear.FaceLink
import DifferentialGeometry.Topology.PiecewiseLinear.IsomorphicSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexLink
import DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [DecidableEq E]

theorem isPLBall_geometricLink_iff_of_isSubdivision {K' K : Geometry.SimplicialComplex ℝ E}
    [Finite K'.faces] (h : IsSubdivision K' K) {p : E} (hp : {p} ∈ K.faces) {n : ℕ} :
    IsPLBall n (SimplicialComplex.geometricLink K' {p}).space ↔
      IsPLBall n (SimplicialComplex.geometricLink K {p}).space := by
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_geometricLink_of_isSubdivision h hp
  exact ⟨fun hs => hs.of_isPLHomeomorphOn hf, fun hs => hs.of_isPLHomeomorphOn hf.symm⟩

theorem isPLSphere_geometricLink_of_isPLSphere {n : ℕ} (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsPLSphere (n + 1) K.space) {u : E} (hu : {u} ∈ K.faces) :
    IsPLSphere n (SimplicialComplex.geometricLink K {u}).space := by
  classical
  obtain ⟨f, hf⟩ := hK
  obtain ⟨g, hg⟩ := isPLSphere_simplexBoundary_std (n + 1)
  have hfin₀ : Finite (simplexBoundary (stdVertices (n + 1))
      (stdVertices_affineIndependent (n + 1))).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  obtain ⟨K₀', K', φ', hK₀', hfin₀', hK', hfin', hiso, -⟩ :=
    exists_isGlueIso_of_isPLHomeomorphOn _ K (hg.symm.trans hf)
  have : Finite K₀'.faces := hfin₀'.to_subtype
  have : Finite K'.faces := hfin'.to_subtype
  have hu' : {u} ∈ K'.faces := hK'.singleton_mem hu
  have hφ'u : {φ' u} ∈ K₀'.faces := hiso.symm.singleton_mem hu'
  have hcard : (stdVertices (n + 1)).card = n + 3 := by
    have := card_stdVertices (n + 1)
    omega
  have hsph : IsPLSphere n (SimplicialComplex.geometricLink K₀' {φ' u}).space :=
    isPLSphere_geometricLink_of_isSubdivision_simplexBoundary _ hcard hK₀' hφ'u
  rw [← isPLSphere_geometricLink_iff_of_isSubdivision hK' hu]
  exact hsph.of_isPLHomeomorphOn (hiso.symm.geometricLink hu').isPLHomeomorphOn.symm

theorem isPLBall_geometricLink_iff_of_isPLHomeomorphOn_stdSimplex {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {f : (Fin (n + 2) → ℝ) → E}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) K.space) {u : E} (hu : {u} ∈ K.faces) :
    IsPLBall n (SimplicialComplex.geometricLink K {u}).space ↔
      u ∈ f '' (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space := by
  classical
  have hT := stdVertices_affineIndependent n
  have hcard : (stdVertices n).card = n + 2 := card_stdVertices n
  have hspace : (simplexComplex (stdVertices n) hT).space = stdSimplex ℝ (Fin (n + 2)) := by
    rw [simplexComplex_space _ hT (Finset.card_pos.mp (by omega)), convexHull_stdVertices]
  have hfin₀ : Finite (simplexComplex (stdVertices n) hT).faces :=
    (simplexComplex_faces_finite _ hT).to_subtype
  rw [← hspace] at hf
  obtain ⟨K₀', K', φ', hK₀', hfin₀', hK', hfin', hiso, -⟩ :=
    exists_isGlueIso_of_isPLHomeomorphOn _ K hf
  have : Finite K₀'.faces := hfin₀'.to_subtype
  have : Finite K'.faces := hfin'.to_subtype
  have hu' : {u} ∈ K'.faces := hK'.singleton_mem hu
  have hφ'u : {φ' u} ∈ K₀'.faces := hiso.symm.singleton_mem hu'
  have hfφ' : f (φ' u) = u := hiso.right _ hu' u (Finset.mem_singleton_self u)
  have hφ'K₀ : φ' u ∈ (simplexComplex (stdVertices n) hT).space := by
    rw [← hK₀'.space_eq]
    exact K₀'.convexHull_subset_space hφ'u (subset_convexHull ℝ _ (by simp))
  have hg := (hiso.symm.geometricLink hu').isPLHomeomorphOn
  have hlink : IsPLBall n (SimplicialComplex.geometricLink K {u}).space ↔
      IsPLBall n (SimplicialComplex.geometricLink K₀' {φ' u}).space := by
    rw [← isPLBall_geometricLink_iff_of_isSubdivision hK' hu]
    exact ⟨fun h => h.of_isPLHomeomorphOn hg, fun h => h.of_isPLHomeomorphOn hg.symm⟩
  rw [hlink, isPLBall_geometricLink_iff_of_isSubdivision_simplexComplex hT hcard hK₀' hφ'u]
  constructor
  · intro h
    exact ⟨φ' u, h, hfφ'⟩
  · rintro ⟨y, hy, hyu⟩
    have hyK₀ : y ∈ (simplexComplex (stdVertices n) hT).space := by
      obtain ⟨s, hs, hys⟩ := (simplexBoundary _ hT).mem_space_iff.mp hy
      exact (simplexComplex _ hT).convexHull_subset_space
        (simplexBoundary_faces_subset_simplexComplex _ hT hs) hys
    have heq : y = φ' u := hf.1.injOn hyK₀ hφ'K₀ (by rw [hyu, hfφ'])
    exact heq ▸ hy

theorem isPLSphere_geometricLink_iff_of_isPLHomeomorphOn_stdSimplex {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {f : (Fin (n + 2) → ℝ) → E}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) K.space) {u : E} (hu : {u} ∈ K.faces) :
    IsPLSphere n (SimplicialComplex.geometricLink K {u}).space ↔
      u ∉ f '' (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space := by
  classical
  have hT := stdVertices_affineIndependent n
  have hcard : (stdVertices n).card = n + 2 := card_stdVertices n
  have hspace : (simplexComplex (stdVertices n) hT).space = stdSimplex ℝ (Fin (n + 2)) := by
    rw [simplexComplex_space _ hT (Finset.card_pos.mp (by omega)), convexHull_stdVertices]
  have hfin₀ : Finite (simplexComplex (stdVertices n) hT).faces :=
    (simplexComplex_faces_finite _ hT).to_subtype
  rw [← isPLBall_geometricLink_iff_of_isPLHomeomorphOn_stdSimplex K hf hu]
  rw [← hspace] at hf
  obtain ⟨K₀', K', φ', hK₀', hfin₀', hK', hfin', hiso, -⟩ :=
    exists_isGlueIso_of_isPLHomeomorphOn _ K hf
  have : Finite K₀'.faces := hfin₀'.to_subtype
  have : Finite K'.faces := hfin'.to_subtype
  have hu' : {u} ∈ K'.faces := hK'.singleton_mem hu
  have hφ'u : {φ' u} ∈ K₀'.faces := hiso.symm.singleton_mem hu'
  have hg := (hiso.symm.geometricLink hu').isPLHomeomorphOn
  rw [← isPLBall_geometricLink_iff_of_isSubdivision hK' hu,
    ← isPLSphere_geometricLink_iff_of_isSubdivision hK' hu]
  have hball : IsPLBall n (SimplicialComplex.geometricLink K' {u}).space ↔
      IsPLBall n (SimplicialComplex.geometricLink K₀' {φ' u}).space :=
    ⟨fun h => h.of_isPLHomeomorphOn hg, fun h => h.of_isPLHomeomorphOn hg.symm⟩
  have hsph : IsPLSphere n (SimplicialComplex.geometricLink K' {u}).space ↔
      IsPLSphere n (SimplicialComplex.geometricLink K₀' {φ' u}).space :=
    ⟨fun h => h.of_isPLHomeomorphOn hg, fun h => h.of_isPLHomeomorphOn hg.symm⟩
  rw [hball, hsph, isPLBall_geometricLink_iff_of_isSubdivision_simplexComplex hT hcard hK₀' hφ'u,
    isPLSphere_geometricLink_iff_of_isSubdivision_simplexComplex hT hcard hK₀' hφ'u]

theorem isPLSphere_or_isPLBall_geometricLink_of_isPLBall {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall (n + 1) K.space) {u : E}
    (hu : {u} ∈ K.faces) :
    IsPLSphere n (SimplicialComplex.geometricLink K {u}).space ∨
      IsPLBall n (SimplicialComplex.geometricLink K {u}).space := by
  classical
  obtain ⟨f, hf⟩ := hK
  by_cases h : u ∈ f '' (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space
  · exact Or.inr ((isPLBall_geometricLink_iff_of_isPLHomeomorphOn_stdSimplex K hf hu).mpr h)
  · exact Or.inl ((isPLSphere_geometricLink_iff_of_isPLHomeomorphOn_stdSimplex K hf hu).mpr h)

theorem isPLSphere_geometricLink_faces_of_isPLSphere {m : ℕ} (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsPLSphere (m + 1) K.space) {s : Finset E} (hs : s ∈ K.faces) {k : ℕ}
    (hcard : s.card = k + 1) (hk : k ≤ m) :
    IsPLSphere (m - k) (SimplicialComplex.geometricLink K s).space := by
  induction k generalizing K m s with
  | zero =>
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
    rw [Nat.sub_zero]
    exact isPLSphere_geometricLink_of_isPLSphere K hK hs
  | succ k ih =>
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    obtain ⟨s', hvs', rfl⟩ : ∃ s', v ∉ s' ∧ s = insert v s' :=
      ⟨s.erase v, Finset.notMem_erase v s, (Finset.insert_erase hv).symm⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hcard' : s'.card = k + 1 := by
      rw [Finset.card_insert_of_notMem hvs'] at hcard
      omega
    have hv' : {v} ∈ K.faces :=
      K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hL : IsPLSphere (m' + 1) (SimplicialComplex.geometricLink K {v}).space :=
      isPLSphere_geometricLink_of_isPLSphere K hK hv'
    have hsL : s' ∈ (SimplicialComplex.geometricLink K {v}).faces :=
      (SimplicialComplex.mem_geometricLink_singleton K v s').mpr
        ⟨Finset.card_pos.mp (by omega), hvs', hs⟩
    rw [geometricLink_insert K hvs', show m' + 1 - (k + 1) = m' - k by omega]
    exact ih _ hL hsL hcard' (by omega)

theorem isPLSphere_or_isPLBall_geometricLink_faces_of_isPLBall {m : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall (m + 1) K.space)
    {s : Finset E} (hs : s ∈ K.faces) {k : ℕ} (hcard : s.card = k + 1) (hk : k ≤ m) :
    IsPLSphere (m - k) (SimplicialComplex.geometricLink K s).space ∨
      IsPLBall (m - k) (SimplicialComplex.geometricLink K s).space := by
  induction k generalizing K m s with
  | zero =>
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
    rw [Nat.sub_zero]
    exact isPLSphere_or_isPLBall_geometricLink_of_isPLBall K hK hs
  | succ k ih =>
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    obtain ⟨s', hvs', rfl⟩ : ∃ s', v ∉ s' ∧ s = insert v s' :=
      ⟨s.erase v, Finset.notMem_erase v s, (Finset.insert_erase hv).symm⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hcard' : s'.card = k + 1 := by
      rw [Finset.card_insert_of_notMem hvs'] at hcard
      omega
    have hv' : {v} ∈ K.faces :=
      K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hsL : s' ∈ (SimplicialComplex.geometricLink K {v}).faces :=
      (SimplicialComplex.mem_geometricLink_singleton K v s').mpr
        ⟨Finset.card_pos.mp (by omega), hvs', hs⟩
    rw [geometricLink_insert K hvs', show m' + 1 - (k + 1) = m' - k by omega]
    rcases isPLSphere_or_isPLBall_geometricLink_of_isPLBall K hK hv' with hL | hL
    · exact Or.inl (isPLSphere_geometricLink_faces_of_isPLSphere _ hL hsL hcard' (by omega))
    · exact ih _ hL hsL hcard' (by omega)

end DifferentialGeometry.Topology.PiecewiseLinear
