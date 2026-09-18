import DifferentialGeometry.Topology.PiecewiseLinear.BallPairSimplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem coneSet_empty (p : E) : coneSet p (∅ : Set E) = {p} := by
  ext x
  constructor
  · intro hx
    rcases mem_coneSet_iff.mp hx with rfl | ⟨z, hz, -⟩
    · rfl
    · exact absurd hz (notMem_empty z)
  · intro hx
    rw [mem_singleton_iff.mp hx]
    exact apex_mem_coneSet p ∅

theorem isPLBall_zero_singleton (z : E) : IsPLBall 0 ({z} : Set E) := by
  classical
  have h := isPLBall_convexHull_of_affineIndependent ({z} : Finset E)
    (affineIndependent_of_subsingleton ℝ _) (by simp : ({z} : Finset E).card = 0 + 1)
  rwa [Finset.coe_singleton, convexHull_singleton] at h

theorem isPLBallPair_convexHull_singleton_of_mem_openSimplex {n : ℕ} {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = n + 2) {p : E}
    (hp : p ∈ openSimplex T) :
    IsPLBallPair n 0 (convexHull ℝ (T : Set E)) {p} := by
  classical
  have h2 : 2 ≤ T.card := by omega
  have hfin : Finite (simplexBoundary T hT).faces := (simplexBoundary_faces_finite T hT).to_subtype
  have hL : IsConeBase p (simplexBoundary T hT) := isConeBase_simplexBoundary hT h2 hp
  have hsph : IsPLSphere n (simplexBoundary T hT).space := by
    rw [simplexBoundary_space T hT h2]
    exact isPLSphere_biUnion_erase T hT hcard
  have hbotspace : (⊥ : Geometry.SimplicialComplex ℝ E).space = ∅ :=
    Geometry.SimplicialComplex.space_bot
  have hball : IsPLBall 0 (coneSet p (⊥ : Geometry.SimplicialComplex ℝ E).space) := by
    rw [hbotspace, coneSet_empty]
    exact isPLBall_zero_singleton p
  have hpair := isPLBallPair_coneSet hL bot_le hsph hball
  rwa [hbotspace, coneSet_empty, ← coneComplex_space_eq_coneSet hL,
    coneComplex_simplexBoundary_space hT h2 hp] at hpair

omit [FiniteDimensional ℝ E] in
theorem convexHull_insert_inter_convexHull_insert_of_separating [DecidableEq E] {F : Finset E}
    {a b : E} (ℓ : E →ₗ[ℝ] ℝ) (hF : ∀ v ∈ F, ℓ v = 0) (ha : ℓ a < 0) (hb : 0 < ℓ b) :
    convexHull ℝ ((insert a F : Finset E) : Set E) ∩
        convexHull ℝ ((insert b F : Finset E) : Set E) = convexHull ℝ (F : Set E) := by
  have haF : a ∉ F := fun h => absurd (hF a h) (ne_of_lt ha)
  have hFzero : convexHull ℝ (F : Set E) ⊆ {x : E | ℓ x = 0} :=
    convexHull_min (fun v hv => hF v hv) (convex_hyperplane ℓ.isLinear 0)
  have hAle : convexHull ℝ ((insert a F : Finset E) : Set E) ⊆ {x : E | ℓ x ≤ 0} := by
    refine convexHull_min ?_ (convex_halfSpace_le ℓ.isLinear 0)
    intro v hv
    rw [Finset.coe_insert, Set.mem_insert_iff] at hv
    rcases hv with rfl | hv
    · exact ha.le
    · exact (hF v hv).le
  have hBge : convexHull ℝ ((insert b F : Finset E) : Set E) ⊆ {x : E | 0 ≤ ℓ x} := by
    refine convexHull_min ?_ (convex_halfSpace_ge ℓ.isLinear 0)
    intro v hv
    rw [Finset.coe_insert, Set.mem_insert_iff] at hv
    rcases hv with rfl | hv
    · exact hb.le
    · exact (hF v hv).ge
  apply Subset.antisymm
  · rintro x ⟨hxa, hxb⟩
    have hx0 : ℓ x = 0 := le_antisymm (hAle hxa) (hBge hxb)
    rcases exists_combo_of_mem_convexHull_insert haF hxa with rfl | ⟨z, hz, s, hs, hs1, rfl⟩
    · exact absurd hx0 (ne_of_lt ha)
    · have hz0 : ℓ z = 0 := hFzero hz
      have hval : ℓ (a + s • (z - a)) = (1 - s) * ℓ a := by
        rw [map_add, map_smul, map_sub, hz0, smul_eq_mul]
        ring
      rw [hval] at hx0
      rcases mul_eq_zero.mp hx0 with h | h
      · have hs' : s = 1 := by linarith
        subst hs'
        rw [one_smul, add_sub_cancel]
        exact hz
      · exact absurd h (ne_of_lt ha)
  · exact subset_inter (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert a F)))
      (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert b F)))

end DifferentialGeometry.Topology.PiecewiseLinear
