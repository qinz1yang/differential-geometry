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

theorem isRadiallyInjective_pair_of_mem_openSegment {z d q : E} (hzd : z ≠ d)
    (hq : q ∈ openSegment ℝ z d) : IsRadiallyInjective q ({z, d} : Set E) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hq
  have hsub : d - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzd)
  have hdq : d - (a • z + b • d) = a • (d - z) := by
    rw [smul_sub]
    match_scalars <;> linarith
  have hzq : z - (a • z + b • d) = (-b) • (d - z) := by
    rw [smul_sub]
    match_scalars <;> linarith
  have hcancel : ∀ α β : ℝ, α • (d - z) = β • (d - z) → α = β := by
    intro α β h
    have h0 : (α - β) • (d - z) = 0 := by rw [sub_smul, h]; abel
    rcases smul_eq_zero.mp h0 with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hsub
  rintro x hx y hy t ht hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · exfalso
    have hstep : y - (a • x + b • y) = t • (x - (a • x + b • y)) := sub_eq_iff_eq_add'.mpr hxy
    rw [hdq, hzq, ← mul_smul] at hstep
    have hcoef : a = t * -b := hcancel _ _ hstep
    nlinarith [mul_pos ht hb]
  · exfalso
    have hstep : y - (a • y + b • x) = t • (x - (a • y + b • x)) := sub_eq_iff_eq_add'.mpr hxy
    rw [hzq, hdq, ← mul_smul] at hstep
    have hcoef : -b = t * a := hcancel _ _ hstep
    nlinarith [mul_pos ht ha]
  · rfl

theorem isRadiallyInjective_pair_of_linearIndependent {p x y : E}
    (h : LinearIndependent ℝ ![x - p, y - p]) : IsRadiallyInjective p ({x, y} : Set E) := by
  have hswap : ∀ {u v : E}, LinearIndependent ℝ ![u, v] → LinearIndependent ℝ ![v, u] := by
    intro u v hind
    rw [LinearIndependent.pair_iff] at hind ⊢
    intro sc tc hst
    obtain ⟨h1, h2⟩ := hind tc sc (by rw [← hst]; abel)
    exact ⟨h2, h1⟩
  have hcross : ∀ {u v : E}, LinearIndependent ℝ ![u, v] → ∀ t : ℝ, v ≠ t • u := by
    intro u v hind t hv
    have h0 : (-t) • u + (1 : ℝ) • v = 0 := by rw [hv]; module
    exact one_ne_zero (LinearIndependent.pair_iff.mp hind (-t) 1 h0).2
  rintro a ha b hb t ht hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact absurd (by rw [hab]; abel : b - p = t • (a - p)) (hcross h t)
  · exact absurd (by rw [hab]; abel : b - p = t • (a - p)) (hcross (hswap h) t)
  · rfl

end DifferentialGeometry.Topology.PiecewiseLinear
