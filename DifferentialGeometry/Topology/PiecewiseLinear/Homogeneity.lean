import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexCornerChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_isPLHomeomorphOn_simplex_fixing_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card)
    {p q : E} (hp : p ∈ openSimplex T) (hq : q ∈ openSimplex T) :
    ∃ f : E → E, IsPLHomeomorphOn f (convexHull ℝ (T : Set E)) (convexHull ℝ (T : Set E)) ∧
      EqOn f id (simplexBoundary T hT).space ∧ f p = q := by
  let L := simplexBoundary T hT
  let _ : Finite L.faces := (simplexBoundary_faces_finite T hT).to_subtype
  have hidpl : IsPiecewiseAffineOn (id : E → E) L.space :=
    (isPiecewiseAffineOn_id isOpen_univ).mono_of_isPolyhedron (isPolyhedron_space L) (subset_univ _)
  have hid : IsPLHomeomorphOn (id : E → E) L.space L.space :=
    ⟨bijOn_id _, hidpl, hidpl.congr fun _ hx => (bijOn_id L.space).invOn_invFunOn.1 hx⟩
  obtain ⟨f, hf, hfix, hfp, -⟩ := exists_isPLHomeomorphOn_coneComplex
    (isConeBase_simplexBoundary hT hcard hp) (isConeBase_simplexBoundary hT hcard hq) hid
  rw [coneComplex_simplexBoundary_space hT hcard hp, coneComplex_simplexBoundary_space hT hcard hq] at hf
  exact ⟨f, hf, hfix, hfp⟩

theorem exists_isPLHomeomorphOn_Icc_fixing_endpoints {p q : ℝ}
    (hp : p ∈ Ioo 0 1) (hq : q ∈ Ioo 0 1) :
    ∃ f : ℝ → ℝ, IsPLHomeomorphOn f (Icc 0 1) (Icc 0 1) ∧ f 0 = 0 ∧ f 1 = 1 ∧ f p = q := by
  classical
  let T : Finset ℝ := {0, 1}
  have hT : AffineIndependent ℝ ((↑) : T → ℝ) := by
    change AffineIndependent ℝ ((↑) : (({0, 1} : Finset ℝ) : Set ℝ) → ℝ)
    rw [Finset.coe_pair]
    have h := (affineIndependent_of_ne ℝ (zero_ne_one : (0 : ℝ) ≠ 1)).range
    rwa [Matrix.range_cons_cons_empty] at h
  have hcard : T.card = 2 := by norm_num [T]
  have hconv : convexHull ℝ (T : Set ℝ) = Icc 0 1 := by
    simp only [T, Finset.coe_pair, convexHull_pair, segment_eq_Icc zero_le_one]
  have hopen : openSimplex T = Ioo 0 1 := by
    rw [← interior_convexHull_eq_openSimplex hT (by simpa only [Module.finrank_self] using hcard),
      hconv, interior_Icc]
  obtain ⟨f, hf, hfix, hfp⟩ := exists_isPLHomeomorphOn_simplex_fixing_boundary T hT hcard.ge
    (hopen.symm ▸ hp) (hopen.symm ▸ hq)
  have hzero : (0 : ℝ) ∈ (simplexBoundary T hT).space :=
    (simplexBoundary T hT).subset_space (s := {0}) (by
      rw [mem_simplexBoundary_faces_iff]
      refine ⟨by simp [T], Finset.singleton_nonempty _, ?_⟩
      intro heq
      have h := congrArg Finset.card heq
      rw [Finset.card_singleton, hcard] at h
      omega) (Finset.mem_singleton_self 0)
  have hone : (1 : ℝ) ∈ (simplexBoundary T hT).space :=
    (simplexBoundary T hT).subset_space (s := {1}) (by
      rw [mem_simplexBoundary_faces_iff]
      refine ⟨by simp [T], Finset.singleton_nonempty _, ?_⟩
      intro heq
      have h := congrArg Finset.card heq
      rw [Finset.card_singleton, hcard] at h
      omega) (Finset.mem_singleton_self 1)
  exact ⟨f, by rwa [hconv] at hf, hfix hzero, hfix hone, hfp⟩

theorem exists_isPLHomeomorphOn_arc_fixing_endpoints
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : IsPLBall 1 A)
    {a b p q : EuclideanSpace ℝ (Fin 2)} (harc : Schoenflies.IsArcBetween A a b)
    (hp : p ∈ A \ {a, b}) (hq : q ∈ A \ {a, b}) :
    ∃ f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn f A A ∧ f a = a ∧ f b = b ∧ f p = q := by
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hA harc
  obtain ⟨s, hs, hγs⟩ := hγ.bijOn.surjOn hp.1
  obtain ⟨t, ht, hγt⟩ := hγ.bijOn.surjOn hq.1
  have hinterior {u : ℝ} (hu : u ∈ Icc 0 1) {x : EuclideanSpace ℝ (Fin 2)}
      (hγu : γ u = x) (hx : x ∉ ({a, b} : Set _)) : u ∈ Ioo 0 1 := by
    refine ⟨lt_of_le_of_ne hu.1 ?_, lt_of_le_of_ne hu.2 ?_⟩
    · intro h
      apply hx
      left
      exact hγu.symm.trans ((congrArg γ h.symm).trans hγ0)
    · intro h
      apply hx
      right
      exact hγu.symm.trans ((congrArg γ h).trans hγ1)
  obtain ⟨g, hg, hg0, hg1, hgs⟩ := exists_isPLHomeomorphOn_Icc_fixing_endpoints
    (hinterior hs hγs hp.2) (hinterior ht hγt hq.2)
  let f := γ ∘ g ∘ Function.invFunOn γ (Icc 0 1)
  have hf : IsPLHomeomorphOn f A A := hγ.symm.trans (hg.trans hγ)
  have hvalue (u : ℝ) (hu : u ∈ Icc 0 1) : f (γ u) = γ (g u) := by
    change γ (g (Function.invFunOn γ (Icc 0 1) (γ u))) = γ (g u)
    rw [hγ.bijOn.invOn_invFunOn.1 hu]
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · rw [← hγ0, hvalue 0 (left_mem_Icc.mpr zero_le_one), hg0]
  · rw [← hγ1, hvalue 1 (right_mem_Icc.mpr zero_le_one), hg1]
  · rw [← hγs, hvalue s hs, hgs, hγt]


theorem exists_isPLHomeomorphOn_simplex_vertex_star_map_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : 3 ≤ T.card) (hspan : affineSpan ℝ (T : Set E) = ⊤)
    {a p q : E} (ha : a ∈ T) (hp : p ∈ openStar (simplexBoundary T hT) a)
    (hq : q ∈ openStar (simplexBoundary T hT) a)
    {U : Set E} (hU : IsOpen U) (hTU : convexHull ℝ (T : Set E) ⊆ U) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧
      h '' convexHull ℝ (T : Set E) = convexHull ℝ (T : Set E) ∧ h p = q ∧ EqOn h id Uᶜ := by
  classical
  let F := T.erase a
  let hF := affineIndependent_of_subset hT (Finset.erase_subset a T)
  let L := starComplex (simplexBoundary T hT) a
  let B := simplexBoundary F hF
  let g := simplicialMap L (Function.update id a (F.centroid ℝ id))
  have hg : IsPLHomeomorphOn g L.space (convexHull ℝ (F : Set E)) :=
    isPLHomeomorphOn_simplicialMap_simplex_vertex_star T hT hcard ha
  have hgfix : EqOn g id B.space := eqOn_simplicialMap_simplex_vertex_star_boundary T hT ha
  have hBL : B.space ⊆ L.space := by
    rw [show L = simplexAvoiding T hT {T.erase a} from
      (simplexAvoiding_erase_eq_starComplex T hT ha).symm]
    exact space_mono_of_faces_subset (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a)
  have hopen : openStar (simplexBoundary T hT) a = L.space \ B.space :=
    openStar_simplexBoundary_eq_sdiff_boundary T hT (by omega) ha
  have hgopen {x : E} (hx : x ∈ openStar (simplexBoundary T hT) a) : g x ∈ openSimplex F := by
    rw [hopen] at hx
    rw [openSimplex_eq_sdiff_simplexBoundary F hF]
    refine ⟨hg.bijOn.mapsTo hx.1, ?_⟩
    intro hxB
    have heq : g (g x) = g x := hgfix hxB
    have hxx : g x = x := hg.bijOn.injOn (hBL hxB) hx.1 heq
    exact hx.2 (hxx ▸ hxB)
  have hFcard : 2 ≤ F.card := by
    dsimp [F]
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨f, hf, hfix, hfp⟩ := exists_isPLHomeomorphOn_simplex_fixing_boundary F hF hFcard
    (hgopen hp) (hgopen hq)
  obtain ⟨h, hh, hC, hhf, hhU⟩ := exists_isPLHomeomorphOn_simplex_vertex_star_conjugate
    T hT hcard hspan ha hf hfix hU hTU
  refine ⟨h, hh, hC, ?_, hhU⟩
  rw [hopen] at hp hq
  rw [hhf hp.1]
  change Function.invFunOn g L.space (f (g p)) = q
  rw [hfp]
  exact hg.bijOn.invOn_invFunOn.1 hq.1

theorem exists_isPLHomeomorphOn_simplex_boundary_mem_vertices
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : 3 ≤ T.card) (hspan : affineSpan ℝ (T : Set E) = ⊤)
    {p : E} (hp : p ∈ (simplexBoundary T hT).space)
    {U : Set E} (hU : IsOpen U) (hTU : convexHull ℝ (T : Set E) ⊆ U) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧
      h '' convexHull ℝ (T : Set E) = convexHull ℝ (T : Set E) ∧ h p ∈ T ∧ EqOn h id Uᶜ := by
  classical
  obtain ⟨a, ha, hpstar⟩ := exists_vertex_mem_openStar (simplexBoundary T hT) hp
  have haT : a ∈ T := ha.1 (Finset.mem_singleton_self a)
  have hastar : a ∈ openStar (simplexBoundary T hT) a :=
    (mem_openStar_iff (simplexBoundary T hT) ha).mpr (Or.inl rfl)
  obtain ⟨h, hh, hC, hpa, hU⟩ := exists_isPLHomeomorphOn_simplex_vertex_star_map_eq
    T hT hcard hspan haT hpstar hastar hU hTU
  exact ⟨h, hh, hC, hpa.symm ▸ haT, hU⟩
end DifferentialGeometry.Topology.PiecewiseLinear
