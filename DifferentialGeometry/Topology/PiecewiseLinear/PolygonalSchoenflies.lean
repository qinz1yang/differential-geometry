import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension
import DifferentialGeometry.External.Schoenflies.JordanClosed

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convex_openSimplex (s : Finset E) : Convex ℝ (openSimplex s) := by
  rintro x ⟨u, hu, hu₁, hux⟩ y ⟨v, hv, hv₁, hvy⟩ a b ha hb hab
  refine ⟨fun w => a * u w + b * v w, ?_, ?_, ?_⟩
  · intro w hw
    rcases ha.eq_or_lt with rfl | ha'
    · have hb' : b = 1 := by simpa using hab
      simpa [hb'] using hv w hw
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hu w hw)) (mul_nonneg hb (hv w hw).le)
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hu₁, hv₁]
    simpa using hab
  · simp_rw [add_smul, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hux, hvy]

theorem IsCompact.exists_isPolyhedron_superset [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsCompact C) : ∃ Q : Set E, IsPolyhedron Q ∧ C ⊆ interior Q := by
  choose P hP hPU hPn using fun x : E =>
    exists_isHPolytope_subset_mem_nhds (x := x) (U := univ) Filter.univ_mem
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun x => interior (P x))
    (fun _ => isOpen_interior) (fun x _ => mem_iUnion.mpr ⟨x, mem_interior_iff_mem_nhds.mpr (hPn x)⟩)
  refine ⟨⋃ x : s, P x, IsPolyhedron.iUnion (fun x => (hP x).isPolyhedron), ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
  exact interior_mono (subset_iUnion (fun z : s => P z) ⟨y, hy⟩) hxy

theorem convexHull_subset_closure_of_mem_openSimplex_of_frontier_subcomplex
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces) {U : Set E}
    (hU : IsOpen U) (hL : L.space = frontier U) {s : Finset E} (hs : s ∈ K.faces)
    {x : E} (hxs : x ∈ openSimplex s) (hxU : x ∈ U) :
    convexHull ℝ (s : Set E) ⊆ closure U := by
  have havoid : Disjoint (openSimplex s) (frontier U) := by
    refine Set.disjoint_left.mpr fun z hzs hzU => ?_
    rw [← hL] at hzU
    obtain ⟨t, ht, hzt⟩ := L.mem_space_iff.mp hzU
    have hst := face_subset_of_mem_openSimplex_of_mem_convexHull K hs (hLK ht) hzs hzt
    have hxL := L.convexHull_subset_space ht
      (convexHull_mono (Finset.coe_subset.mpr hst) (openSimplex_subset_convexHull s hxs))
    rw [hL, hU.frontier_eq] at hxL
    exact hxL.2 hxU
  have hcover : openSimplex s ⊆ U ∪ (closure U)ᶜ := by
    intro z hz
    by_cases hzU : z ∈ U
    · exact Or.inl hzU
    · refine Or.inr fun hzcl => Set.disjoint_left.mp havoid hz ?_
      rw [hU.frontier_eq]
      exact ⟨hzcl, hzU⟩
  have hsplit := IsPreconnected.subset_or_subset hU isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr fun _ hz hz' => hz' (subset_closure hz)) hcover
    (convex_openSimplex s).isPreconnected
  have hopen : openSimplex s ⊆ U := hsplit.resolve_right fun h => h hxs (subset_closure hxU)
  exact (convexHull_subset_closure_openSimplex (K.nonempty_of_mem_faces hs)).trans
    (closure_mono hopen)

theorem restrict_closure_space_of_frontier_subcomplex [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hLK : L.faces ⊆ K.faces)
    {U : Set E} (hU : IsOpen U) (hUK : U ⊆ K.space) (hL : L.space = frontier U) :
    (restrict K (closure U)).space = closure U := by
  have : Finite (restrict K (closure U)).faces := (restrict_faces_finite K (closure U)).to_subtype
  apply Subset.antisymm (restrict_space_subset K (closure U))
  refine closure_minimal ?_ (isPolyhedron_space (restrict K (closure U))).isClosed
  intro x hx
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K (hUK hx)
  exact (restrict K (closure U)).convexHull_subset_space
    ⟨hs, convexHull_subset_closure_of_mem_openSimplex_of_frontier_subcomplex K L hLK hU hL hs hxs hx⟩
    (openSimplex_subset_convexHull s hxs)

theorem isPolyhedron_closure_of_isPolyhedron_frontier [FiniteDimensional ℝ E] {U : Set E}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hfr : IsPolyhedron (frontier U)) :
    IsPolyhedron (closure U) := by
  obtain ⟨Q, hQ, hUQ⟩ := IsCompact.exists_isPolyhedron_superset hUb.isCompact_closure
  obtain ⟨K, hKfin, hK⟩ := hQ.exists_simplicialComplex
  have : Finite K.faces := hKfin.to_subtype
  have hfrK : frontier U ⊆ K.space := by
    rw [hK]
    exact frontier_subset_closure.trans (hUQ.trans interior_subset)
  obtain ⟨R, hR, hRfin, hfrR⟩ := exists_isSubdivision_restrict_space K hfr hfrK
  have : Finite R.faces := hRfin.to_subtype
  have hUR : U ⊆ R.space := by
    rw [hR.space_eq, hK]
    exact subset_closure.trans (hUQ.trans interior_subset)
  have hcl := restrict_closure_space_of_frontier_subcomplex R (restrict R (frontier U))
    (restrict_faces_subset R (frontier U)) hU hUR hfrR
  have : Finite (restrict R (closure U)).faces := (restrict_faces_finite R (closure U)).to_subtype
  rw [← hcl]
  exact isPolyhedron_space _

noncomputable def stdTriangleLoop (t : ℝ) : Fin 3 → ℝ :=
  if t ≤ 1 / 3 then ![1 - 3 * t, 3 * t, 0]
  else if t ≤ 2 / 3 then ![0, 2 - 3 * t, 3 * t - 1]
  else ![3 * t - 2, 0, 3 - 3 * t]

theorem continuous_stdTriangleLoop : Continuous stdTriangleLoop := by
  have h₁ : Continuous fun t : ℝ => (![1 - 3 * t, 3 * t, 0] : Fin 3 → ℝ) := by fun_prop
  have h₂ : Continuous fun t : ℝ => (![0, 2 - 3 * t, 3 * t - 1] : Fin 3 → ℝ) := by fun_prop
  have h₃ : Continuous fun t : ℝ => (![3 * t - 2, 0, 3 - 3 * t] : Fin 3 → ℝ) := by fun_prop
  have h₂₃ : Continuous fun t : ℝ =>
      if t ≤ 2 / 3 then (![0, 2 - 3 * t, 3 * t - 1] : Fin 3 → ℝ)
      else ![3 * t - 2, 0, 3 - 3 * t] :=
    h₂.if_le h₃ continuous_id continuous_const (by intro t ht; subst t; norm_num)
  exact h₁.if_le h₂₃ continuous_id continuous_const (by intro t ht; subst t; norm_num)

theorem stdTriangleLoop_image : stdTriangleLoop '' Icc 0 1 = stdSimplexBoundary 2 := by
  apply Subset.antisymm
  · rintro x ⟨t, ⟨ht₀, ht₁⟩, rfl⟩
    unfold stdTriangleLoop
    split_ifs with h₁ h₂
    · refine ⟨⟨?_, ?_⟩, 2, rfl⟩
      · intro i; fin_cases i <;> dsimp <;> linarith
      · norm_num [Fin.sum_univ_succ]
    · refine ⟨⟨?_, ?_⟩, 0, rfl⟩
      · intro i; fin_cases i <;> dsimp <;> linarith
      · norm_num [Fin.sum_univ_succ]
    · refine ⟨⟨?_, ?_⟩, 1, rfl⟩
      · intro i; fin_cases i <;> dsimp <;> linarith
      · norm_num [Fin.sum_univ_succ]
  · rintro x ⟨⟨hx₀, hx₁⟩, i, hi⟩
    have hxsum : x 0 + x 1 + x 2 = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hx₁
    have h0 := hx₀ 0
    have h1 := hx₀ 1
    have h2 := hx₀ 2
    fin_cases i
    · refine ⟨(x 2 + 1) / 3, ⟨by linarith, by linarith⟩, ?_⟩
      unfold stdTriangleLoop
      split_ifs with ha hb <;> funext j <;> fin_cases j <;>
        dsimp at * <;> linarith
    · refine ⟨(x 0 + 2) / 3, ⟨by linarith, by linarith⟩, ?_⟩
      unfold stdTriangleLoop
      split_ifs with ha hb <;> funext j <;> fin_cases j <;>
        dsimp at * <;> linarith
    · refine ⟨x 1 / 3, ⟨by linarith, by linarith⟩, ?_⟩
      unfold stdTriangleLoop
      split_ifs with ha hb <;> funext j <;> fin_cases j <;>
        dsimp at * <;> linarith

theorem injOn_stdTriangleLoop : InjOn stdTriangleLoop (Ico 0 1) := by
  intro s hs t ht hst
  have h0 := congrFun hst 0
  have h1 := congrFun hst 1
  have h2 := congrFun hst 2
  simp only [stdTriangleLoop] at h0 h1 h2
  split_ifs at h0 h1 h2 <;>
    dsimp at h0 h1 h2 <;>
    linarith [hs.1, hs.2, ht.1, ht.2]

theorem isJordanCurve_of_isPLSphere_one {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLSphere 1 J) : Schoenflies.IsJordanCurve J := by
  obtain ⟨f, hf⟩ := hJ
  have hmap : MapsTo stdTriangleLoop (Icc 0 1) (stdSimplexBoundary 2) :=
    fun t ht => stdTriangleLoop_image.subset ⟨t, ht, rfl⟩
  refine ⟨f ∘ stdTriangleLoop, ⟨hf.isPiecewiseAffineOn.continuousOn.comp
    continuous_stdTriangleLoop.continuousOn hmap, ?_, ?_⟩, ?_⟩
  · norm_num [stdTriangleLoop]
  · intro s hs t ht hst
    exact injOn_stdTriangleLoop hs ht
      (hf.bijOn.injOn (hmap ⟨hs.1, hs.2.le⟩) (hmap ⟨ht.1, ht.2.le⟩) hst)
  · change (fun t : ℝ => f (stdTriangleLoop t)) '' Icc 0 1 = J
    rw [← image_image f stdTriangleLoop (Icc (0 : ℝ) 1), stdTriangleLoop_image, hf.image_eq]

theorem exists_polyhedral_region_of_isPLSphere_one {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLSphere 1 J) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧
      frontier U = J ∧ IsPolyhedron (closure U) ∧
      ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)),
        K.faces.Finite ∧ K.space = closure U ∧ (restrict K J).space = J := by
  have hsep := Schoenflies.jordan_curve_theorem (isJordanCurve_of_isPLSphere_one hJ)
  have hpoly : IsPolyhedron (closure (Schoenflies.inside J)) :=
    isPolyhedron_closure_of_isPolyhedron_frontier hsep.isOpen_inside hsep.isBounded_inside
      (hsep.frontier_inside.symm ▸ hJ.isPolyhedron)
  obtain ⟨L, hLfin, hL⟩ := hpoly.exists_simplicialComplex
  have : Finite L.faces := hLfin.to_subtype
  have hJL : J ⊆ L.space := by
    calc
      J = frontier (Schoenflies.inside J) := hsep.frontier_inside.symm
      _ ⊆ closure (Schoenflies.inside J) := frontier_subset_closure
      _ = L.space := hL.symm
  obtain ⟨K, hK, hKfin, hJK⟩ := exists_isSubdivision_restrict_space L hJ.isPolyhedron hJL
  exact ⟨_, hsep.isOpen_inside, hsep.isConnected_inside, hsep.isBounded_inside,
    hsep.frontier_inside, hpoly, K, hKfin, hK.space_eq.trans hL, hJK⟩

end DifferentialGeometry.Topology.PiecewiseLinear
