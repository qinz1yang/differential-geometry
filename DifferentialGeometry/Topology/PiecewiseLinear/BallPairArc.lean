import DifferentialGeometry.Topology.PiecewiseLinear.BallPairModel
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairSimplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineIndependent_coe_pair_set {a b : E} (h : a ≠ b) :
    AffineIndependent ℝ ((↑) : ({a, b} : Set E) → E) := by
  have hr := (affineIndependent_of_ne (k := ℝ) h).range
  have hset : Set.range ![a, b] = ({a, b} : Set E) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rwa [hset] at hr

theorem affineIndependent_coe_pair [DecidableEq E] {a b : E} (h : a ≠ b) :
    AffineIndependent ℝ ((↑) : (({a, b} : Finset E)) → E) := by
  have hr := affineIndependent_coe_pair_set h
  have hset : ((({a, b} : Finset E) : Set E)) = ({a, b} : Set E) := by simp
  rw [← hset] at hr
  exact hr

theorem simplexBoundary_pair_space [DecidableEq E] {v z : E} (h : v ≠ z) :
    (simplexBoundary ({v, z} : Finset E) (affineIndependent_coe_pair h)).space =
      ({v, z} : Set E) := by
  have hne : v ∉ ({z} : Finset E) := by simpa using h
  have hcard : 2 ≤ ({v, z} : Finset E).card := by
    rw [Finset.card_insert_of_notMem hne, Finset.card_singleton]
  have he1 : ({v, z} : Finset E).erase v = {z} := Finset.erase_insert hne
  have he2 : ({v, z} : Finset E).erase z = {v} := by
    ext y
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hy, hyv | hyz⟩
      · exact hyv
      · exact absurd hyz hy
    · rintro rfl
      exact ⟨h, Or.inl rfl⟩
  rw [simplexBoundary_space _ _ hcard]
  ext x
  simp only [mem_iUnion, exists_prop, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨u, (rfl | rfl), hx⟩
    · rw [he1, Finset.coe_singleton, convexHull_singleton] at hx
      exact Or.inr hx
    · rw [he2, Finset.coe_singleton, convexHull_singleton] at hx
      exact Or.inl hx
  · rintro (rfl | rfl)
    · exact ⟨z, Or.inr rfl, by rw [he2, Finset.coe_singleton, convexHull_singleton]; rfl⟩
    · exact ⟨v, Or.inl rfl, by rw [he1, Finset.coe_singleton, convexHull_singleton]; rfl⟩

theorem isConeBase_simplexBoundary_pair [DecidableEq E] {p v z : E} (hvz : v ≠ z) (hpv : p ≠ v)
    (hpz : p ≠ z) (hrad : IsRadiallyInjective p ({v, z} : Set E)) :
    IsConeBase p (simplexBoundary ({v, z} : Finset E) (affineIndependent_coe_pair hvz)) where
  notMem_space := by
    rw [simplexBoundary_pair_space hvz]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim hpv hpz
  indep := by
    intro σ hσ
    obtain ⟨hsub, hne, hproper⟩ := mem_simplexBoundary_faces_iff.mp hσ
    have hlt : σ.card < ({v, z} : Finset E).card :=
      Finset.card_lt_card (lt_of_le_of_ne hsub hproper)
    have hne' : v ∉ ({z} : Finset E) := by simpa using hvz
    rw [Finset.card_insert_of_notMem hne', Finset.card_singleton] at hlt
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (le_antisymm (by omega) (Finset.card_pos.mpr hne))
    have ha : a = v ∨ a = z := by simpa using hsub (Finset.mem_singleton_self a)
    rcases ha with rfl | rfl
    · rw [Finset.coe_singleton]
      exact affineIndependent_coe_pair_set hpv
    · rw [Finset.coe_singleton]
      exact affineIndependent_coe_pair_set hpz
  radial := by
    rw [simplexBoundary_pair_space hvz]
    exact hrad

theorem isPLBall_one_coneSet_pair [FiniteDimensional ℝ E] {p v z : E}
    (hvz : v ≠ z) (hpv : p ≠ v) (hpz : p ≠ z)
    (hrad : IsRadiallyInjective p ({v, z} : Set E)) :
    IsPLBall 1 (coneSet p ({v, z} : Set E)) := by
  classical
  have hJ := isConeBase_simplexBoundary_pair hvz hpv hpz hrad
  have hfin : Finite (simplexBoundary ({v, z} : Finset E) (affineIndependent_coe_pair hvz)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have h0 : IsPLSphere 0
      (simplexBoundary ({v, z} : Finset E) (affineIndependent_coe_pair hvz)).space := by
    rw [simplexBoundary_pair_space hvz]
    exact isPLSphere_zero_iff.mpr ⟨v, z, hvz, rfl⟩
  have hball := hJ.isPLBall_of_isPLSphere h0
  rwa [coneComplex_space_eq_coneSet hJ, simplexBoundary_pair_space hvz] at hball

theorem isPLBallPair_coneSet_arc_of_radial [FiniteDimensional ℝ E] {m : ℕ}
    {p v z : E} {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsConeBase p L)
    (hsph : IsPLSphere m L.space) (hvzL : ({v, z} : Set E) ⊆ L.space) (hvz : v ≠ z) (hpv : p ≠ v)
    (hpz : p ≠ z) (hrad : IsRadiallyInjective p ({v, z} : Set E)) :
    IsPLBallPair m 1 (coneSet p L.space) (segment ℝ p v ∪ segment ℝ p z) := by
  classical
  have h := isPLBallPair_coneSet hL hvzL hsph (isPLBall_one_coneSet_pair hvz hpv hpz hrad)
  rwa [coneSet_pair_eq_union_segment] at h

theorem isPLBallPair_convexHull_arc_of_radial [FiniteDimensional ℝ E] {n : ℕ} {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = n + 2) {p v z : E}
    (hp : p ∈ openSimplex T) (hvzL : ({v, z} : Set E) ⊆ (simplexBoundary T hT).space)
    (hvz : v ≠ z) (hpv : p ≠ v) (hpz : p ≠ z)
    (hrad : IsRadiallyInjective p ({v, z} : Set E)) :
    IsPLBallPair n 1 (convexHull ℝ (T : Set E)) (segment ℝ p v ∪ segment ℝ p z) := by
  classical
  have h2 : 2 ≤ T.card := by omega
  have hfin : Finite (simplexBoundary T hT).faces := (simplexBoundary_faces_finite T hT).to_subtype
  have hL : IsConeBase p (simplexBoundary T hT) := isConeBase_simplexBoundary hT h2 hp
  have hsph : IsPLSphere n (simplexBoundary T hT).space := by
    rw [simplexBoundary_space T hT h2]
    exact isPLSphere_biUnion_erase T hT hcard
  have h := isPLBallPair_coneSet_arc_of_radial hL hsph hvzL hvz hpv hpz hrad
  rwa [← coneComplex_space_eq_coneSet hL, coneComplex_simplexBoundary_space hT h2 hp] at h

end DifferentialGeometry.Topology.PiecewiseLinear
