import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial
import DifferentialGeometry.Topology.PlanarJordan.Regions
import DifferentialGeometry.External.Schoenflies.FaceCyclesProof

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

theorem convexHull_subset_closure_of_mem_openSimplex_of_frontier_subset_subcomplex
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces) {U : Set E}
    (hU : IsOpen U) (hL : frontier U ⊆ L.space) (hUL : Disjoint U L.space)
    {s : Finset E} (hs : s ∈ K.faces)
    {x : E} (hxs : x ∈ openSimplex s) (hxU : x ∈ U) :
    convexHull ℝ (s : Set E) ⊆ closure U := by
  have havoid : Disjoint (openSimplex s) (frontier U) := by
    refine Set.disjoint_left.mpr fun z hzs hzU => ?_
    obtain ⟨t, ht, hzt⟩ := L.mem_space_iff.mp (hL hzU)
    have hst := face_subset_of_mem_openSimplex_of_mem_convexHull K hs (hLK ht) hzs hzt
    have hxL := L.convexHull_subset_space ht
      (convexHull_mono (Finset.coe_subset.mpr hst) (openSimplex_subset_convexHull s hxs))
    exact Set.disjoint_left.mp hUL hxU hxL
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

theorem convexHull_subset_closure_of_mem_openSimplex_of_frontier_subcomplex
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces) {U : Set E}
    (hU : IsOpen U) (hL : L.space = frontier U) {s : Finset E} (hs : s ∈ K.faces)
    {x : E} (hxs : x ∈ openSimplex s) (hxU : x ∈ U) :
    convexHull ℝ (s : Set E) ⊆ closure U := by
  have hUL : Disjoint U L.space := by
    refine Set.disjoint_left.mpr fun z hz hzL => ?_
    rw [hL, hU.frontier_eq] at hzL
    exact hzL.2 hz
  exact convexHull_subset_closure_of_mem_openSimplex_of_frontier_subset_subcomplex K L hLK hU
    hL.symm.subset hUL hs hxs hxU

theorem restrict_closure_space_of_frontier_subset_subcomplex [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hLK : L.faces ⊆ K.faces)
    {U : Set E} (hU : IsOpen U) (hUK : U ⊆ K.space) (hL : frontier U ⊆ L.space)
    (hUL : Disjoint U L.space) :
    (restrict K (closure U)).space = closure U := by
  have : Finite (restrict K (closure U)).faces := (restrict_faces_finite K (closure U)).to_subtype
  apply Subset.antisymm (restrict_space_subset K (closure U))
  refine closure_minimal ?_ (isPolyhedron_space (restrict K (closure U))).isClosed
  intro x hx
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K (hUK hx)
  exact (restrict K (closure U)).convexHull_subset_space
    ⟨hs, convexHull_subset_closure_of_mem_openSimplex_of_frontier_subset_subcomplex
      K L hLK hU hL hUL hs hxs hx⟩
    (openSimplex_subset_convexHull s hxs)

theorem restrict_closure_space_of_frontier_subcomplex [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hLK : L.faces ⊆ K.faces)
    {U : Set E} (hU : IsOpen U) (hUK : U ⊆ K.space) (hL : L.space = frontier U) :
    (restrict K (closure U)).space = closure U := by
  have hUL : Disjoint U L.space := by
    refine Set.disjoint_left.mpr fun z hz hzL => ?_
    rw [hL, hU.frontier_eq] at hzL
    exact hzL.2 hz
  exact restrict_closure_space_of_frontier_subset_subcomplex K L hLK hU hUK hL.symm.subset hUL

theorem ncard_faces_card_restrict_lt_of_isOpen [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {U Q : Set E}
    (hU : IsOpen U) (hUne : U.Nonempty) (hUK : U ⊆ K.space) (hUQ : Disjoint U Q) :
    {s ∈ (restrict K Q).faces | s.card = Module.finrank ℝ E + 1}.ncard <
      {s ∈ K.faces | s.card = Module.finrank ℝ E + 1}.ncard := by
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨s, hs, hcard, hxs⟩ := exists_face_card_eq_finrank_succ_of_mem_closure K hU hUK
    (subset_closure hxU)
  apply Set.ncard_lt_ncard _ ((Set.toFinite K.faces).subset (Set.sep_subset _ _))
  refine ssubset_iff_subset_ne.mpr ⟨fun t ht => ⟨ht.1.1, ht.2⟩, ?_⟩
  intro heq
  have hsQ : s ∈ {s ∈ (restrict K Q).faces | s.card = Module.finrank ℝ E + 1} :=
    heq.symm ▸ ⟨hs, hcard⟩
  exact Set.disjoint_left.mp hUQ hxU (hsQ.1.2 hxs)

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

theorem isPiecewiseAffineOn_stdTriangleLoop : IsPiecewiseAffineOn stdTriangleLoop (Icc 0 1) := by
  have h₁ : IsPiecewiseAffineOn stdTriangleLoop (Icc 0 (1 / 3)) := by
    refine (isPiecewiseAffineOn_of_affine_of_isHPolytope
      (AffineMap.lineMap (![1, 0, 0] : Fin 3 → ℝ) ![-2, 3, 0]) isHPolytope_Icc).congr ?_
    intro t ht
    rw [stdTriangleLoop, if_pos ht.2, AffineMap.lineMap_apply_module]
    funext i; fin_cases i <;> dsimp <;> ring
  have h₂ : IsPiecewiseAffineOn stdTriangleLoop (Icc (1 / 3) (2 / 3)) := by
    refine (isPiecewiseAffineOn_of_affine_of_isHPolytope
      (AffineMap.lineMap (![0, 2, -1] : Fin 3 → ℝ) ![0, -1, 2]) isHPolytope_Icc).congr ?_
    intro t ht
    rw [stdTriangleLoop, AffineMap.lineMap_apply_module]
    split_ifs with ha hb <;> funext i <;> fin_cases i <;> dsimp <;> linarith [ht.1, ht.2]
  have h₃ : IsPiecewiseAffineOn stdTriangleLoop (Icc (2 / 3) 1) := by
    refine (isPiecewiseAffineOn_of_affine_of_isHPolytope
      (AffineMap.lineMap (![-2, 0, 3] : Fin 3 → ℝ) ![1, 0, 0]) isHPolytope_Icc).congr ?_
    intro t ht
    rw [stdTriangleLoop, AffineMap.lineMap_apply_module]
    split_ifs with ha hb <;> funext i <;> fin_cases i <;> dsimp <;> linarith [ht.1, ht.2]
  have h₁₂ := h₁.union_of_isClosed h₂ isClosed_Icc isClosed_Icc
  rw [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at h₁₂
  have h := h₁₂.union_of_isClosed h₃ isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at h

theorem exists_piecewiseAffine_loop_of_isPLSphere_one {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLSphere 1 J) :
    ∃ γ : ℝ → EuclideanSpace ℝ (Fin 2), Schoenflies.IsLoop γ ∧
      IsPiecewiseAffineOn γ (Icc 0 1) ∧ γ '' Icc 0 1 = J := by
  obtain ⟨f, hf⟩ := hJ
  have hmap : MapsTo stdTriangleLoop (Icc 0 1) (stdSimplexBoundary 2) :=
    fun t ht => stdTriangleLoop_image.subset ⟨t, ht, rfl⟩
  refine ⟨f ∘ stdTriangleLoop, ⟨hf.isPiecewiseAffineOn.continuousOn.comp
    continuous_stdTriangleLoop.continuousOn hmap, ?_, ?_⟩, ?_, ?_⟩
  · norm_num [stdTriangleLoop]
  · intro s hs t ht hst
    exact injOn_stdTriangleLoop hs ht
      (hf.bijOn.injOn (hmap ⟨hs.1, hs.2.le⟩) (hmap ⟨ht.1, ht.2.le⟩) hst)
  · have h := hf.isPiecewiseAffineOn.comp isPiecewiseAffineOn_stdTriangleLoop
    have hsub : Icc (0 : ℝ) 1 ⊆ stdTriangleLoop ⁻¹' stdSimplexBoundary (1 + 1) := hmap
    rwa [inter_eq_left.mpr hsub] at h
  · change (fun t : ℝ => f (stdTriangleLoop t)) '' Icc 0 1 = J
    rw [← image_image f stdTriangleLoop (Icc (0 : ℝ) 1), stdTriangleLoop_image, hf.image_eq]

theorem isJordanCurve_of_isPLSphere_one {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLSphere 1 J) : Schoenflies.IsJordanCurve J := by
  obtain ⟨γ, hγ, -, hγJ⟩ := exists_piecewiseAffine_loop_of_isPLSphere_one hJ
  exact ⟨γ, hγ, hγJ⟩

open Classical in
theorem boundaryComplex_space_eq_of_isPLBall_of_frontier
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) [Finite K.faces]
    (hK : IsPLBall 2 K.space) {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLSphere 1 J) (hfrontier : frontier K.space = J) :
    (boundaryComplex 2 K).space = J := by
  have hman : IsCombinatorialManifoldWithBoundary (1 + 1) K :=
    hK.isCombinatorialManifoldWithBoundary
  have hsub : (boundaryComplex 2 K).space ⊆ frontier K.space :=
    boundaryComplex_space_subset_frontier_of_finrank (n := 1) (by simp) K hman
  exact DifferentialGeometry.Topology.PlanarJordan.eq_of_isJordanCurve_of_subset
    (isJordanCurve_of_isPLSphere_one (isPLSphere_boundaryComplex_space_of_isPLBall K hK))
    (isJordanCurve_of_isPLSphere_one hJ)
    (hsub.trans hfrontier.subset)

theorem isPLBall_segment [FiniteDimensional ℝ E] {a b : E} (hab : a ≠ b) :
    IsPLBall 1 (segment ℝ a b) := by
  classical
  have hi : AffineIndependent ℝ ((↑) : ({a, b} : Finset E) → E) := by
    change AffineIndependent ℝ ((↑) : (({a, b} : Finset E) : Set E) → E)
    rw [Finset.coe_pair]
    have h := (affineIndependent_of_ne ℝ hab).range
    rw [Matrix.range_cons_cons_empty] at h
    exact h
  have h := isPLBall_convexHull_of_affineIndependent ({a, b} : Finset E) hi
    (n := 1) (by simp [hab])
  simpa only [Finset.coe_pair, convexHull_pair] using h

theorem isPLBall_Icc {a b : ℝ} (hab : a < b) : IsPLBall 1 (Icc a b) := by
  simpa only [segment_eq_Icc hab.le] using isPLBall_segment hab.ne

theorem exists_isPLHomeomorphOn_Icc_of_isPLBall_one [FiniteDimensional ℝ E] {A : Set E}
    (hA : IsPLBall 1 A) : ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc 0 1) A := by
  obtain ⟨f, hf⟩ := isPLBall_Icc (by norm_num : (0 : ℝ) < 1)
  obtain ⟨g, hg⟩ := hA
  exact ⟨_, hf.symm.trans hg⟩

theorem isPLBall_image_Icc_of_isPiecewiseAffineOn [FiniteDimensional ℝ E] {γ : ℝ → E}
    {a b : ℝ} (hab : a < b) (hγ : IsPiecewiseAffineOn γ (Icc a b)) (hi : InjOn γ (Icc a b)) :
    IsPLBall 1 (γ '' Icc a b) := by
  obtain ⟨K, hKfin, hK⟩ := (isHPolytope_Icc (a := a) (b := b)).isPolyhedron.exists_simplicialComplex
  have : Finite K.faces := hKfin.to_subtype
  obtain ⟨L, -, hL, hf⟩ := exists_isPLHomeomorphOn_image K (hK.symm ▸ hγ) (hK.symm ▸ hi)
  rw [hK] at hL hf
  rw [← hL]
  exact (isPLBall_Icc hab).of_isPLHomeomorphOn hf

theorem isPiecewiseAffineOn_subarc {γ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hγ : IsPiecewiseAffineOn γ (Icc 0 1)) {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    IsPiecewiseAffineOn (Schoenflies.subarc γ a b) (Icc 0 1) := by
  have hA : IsPiecewiseAffineOn (Schoenflies.reparam a b) (Icc 0 1) := by
    refine (isPiecewiseAffineOn_of_affine_of_isHPolytope (AffineMap.lineMap a b)
      isHPolytope_Icc).congr fun t _ => ?_
    simp only [Schoenflies.reparam, AffineMap.lineMap_apply_module, smul_eq_mul]
    ring
  have hsub : Icc (0 : ℝ) 1 ⊆ Schoenflies.reparam a b ⁻¹' Icc 0 1 :=
    fun t ht => Schoenflies.uIcc_subset_I ha hb (Schoenflies.mapsTo_reparam ht)
  have h := hγ.comp hA
  rw [inter_eq_left.mpr hsub] at h
  exact h

theorem isPiecewiseAffineOn_concatenate {γ η : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hγ : IsPiecewiseAffineOn γ (Icc 0 1)) (hη : IsPiecewiseAffineOn η (Icc 0 1))
    (hmid : γ 1 = η 0) : IsPiecewiseAffineOn (Schoenflies.concatenate γ η) (Icc 0 1) := by
  have h₁ : IsPiecewiseAffineOn (Schoenflies.concatenate γ η) (Icc 0 (1 / 2)) := by
    let A : ℝ →ᵃ[ℝ] ℝ := AffineMap.lineMap 0 2
    have hA : ∀ t, A t = 2 * t := by
      intro t
      simp [A, AffineMap.lineMap_apply_module, mul_comm]
    have hsub : Icc (0 : ℝ) (1 / 2) ⊆ A ⁻¹' Icc 0 1 := by
      intro t ht
      rw [mem_preimage, hA]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h := hγ.comp (isPiecewiseAffineOn_of_affine_of_isHPolytope A
      (isHPolytope_Icc (a := 0) (b := 1 / 2)))
    rw [inter_eq_left.mpr hsub] at h
    refine h.congr fun t ht => ?_
    rw [Function.comp_apply, hA, Schoenflies.concatenate_of_le ht.2]
  have h₂ : IsPiecewiseAffineOn (Schoenflies.concatenate γ η) (Icc (1 / 2) 1) := by
    let A : ℝ →ᵃ[ℝ] ℝ := AffineMap.lineMap (-1) 1
    have hA : ∀ t, A t = 2 * t - 1 := by
      intro t
      simp only [A, AffineMap.lineMap_apply_module, smul_eq_mul]
      ring
    have hsub : Icc (1 / 2 : ℝ) 1 ⊆ A ⁻¹' Icc 0 1 := by
      intro t ht
      rw [mem_preimage, hA]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h := hη.comp (isPiecewiseAffineOn_of_affine_of_isHPolytope A
      (isHPolytope_Icc (a := 1 / 2) (b := 1)))
    rw [inter_eq_left.mpr hsub] at h
    refine h.congr fun t ht => ?_
    rw [Function.comp_apply, hA, Schoenflies.concatenate_upperHalf hmid ht]
  have h := h₁.union_of_isClosed h₂ isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at h

theorem isPLBall_outside_subarcs {γ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hγ : Schoenflies.IsLoop γ) (hPL : IsPiecewiseAffineOn γ (Icc 0 1))
    {s t : ℝ} (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (ht1 : t < 1) (hst : s < t) :
    IsPLBall 1 (γ '' Icc 0 s ∪ γ '' Icc t 1) := by
  have ht0 : 0 < t := lt_of_le_of_lt hs.1 hst
  have hs1 : s ≠ 1 := (hst.trans ht1).ne
  have hback : IsPLBall 1 (γ '' Icc t 1) :=
    isPLBall_image_Icc_of_isPiecewiseAffineOn ht1
      (hPL.mono_of_isPolyhedron isHPolytope_Icc.isPolyhedron (Icc_subset_Icc ht.1 le_rfl))
      (hγ.injective_on_back ht ht0)
  rcases hs.1.eq_or_lt with hs0 | hs0
  · have hfront : γ '' Icc 0 s = {γ 1} := by
      rw [← hs0, Icc_self, image_singleton, hγ.closes]
    have hone : γ 1 ∈ γ '' Icc t 1 := ⟨1, ⟨ht.2, le_rfl⟩, rfl⟩
    simpa only [hfront, singleton_union, insert_eq_of_mem hone] using hback
  · let f := Schoenflies.subarc γ t 1
    let g := Schoenflies.subarc γ 0 s
    have hf : InjOn f (Icc 0 1) := by
      apply Schoenflies.injOn_subarc _ ht1.ne
      simpa only [uIcc_of_le ht.2] using hγ.injective_on_back ht ht0
    have hg : InjOn g (Icc 0 1) := by
      apply Schoenflies.injOn_subarc _ hs0.ne
      simpa only [uIcc_of_le hs.1] using hγ.injective_on_front hs hs1
    have hmid : f 1 = g 0 := by simpa [f, g] using hγ.closes.symm
    have hfimage : f '' Icc 0 1 = γ '' Icc t 1 := by
      simpa only [f, uIcc_of_le ht.2] using Schoenflies.subarc_image (f := γ) (a := t) (b := 1)
    have hgimage : g '' Icc 0 1 = γ '' Icc 0 s := by
      simpa only [g, uIcc_of_le hs.1] using Schoenflies.subarc_image (f := γ) (a := 0) (b := s)
    have hmeet : ∀ z ∈ f '' Icc 0 1, z ∈ g '' Icc 0 1 → z = f 1 := by
      rw [hfimage, hgimage]
      intro z hz hz'
      simpa [f] using hγ.back_meet_front hs ht hs1 hst hz hz'
    have h := isPLBall_image_Icc_of_isPiecewiseAffineOn (by norm_num : (0 : ℝ) < 1)
      (isPiecewiseAffineOn_concatenate (isPiecewiseAffineOn_subarc hPL ht ⟨zero_le_one, le_rfl⟩)
        (isPiecewiseAffineOn_subarc hPL ⟨le_rfl, zero_le_one⟩ hs) hmid)
      (Schoenflies.injOn_concatenate hf hg hmid hmeet)
    rw [Schoenflies.image_concatenate hmid, hfimage, hgimage, union_comm] at h
    exact h

theorem exists_isPLHomeomorphOn_Icc_of_isArcBetween {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hPL : IsPLBall 1 A) {p q : EuclideanSpace ℝ (Fin 2)}
    (hA : Schoenflies.IsArcBetween A p q) :
    ∃ γ : ℝ → EuclideanSpace ℝ (Fin 2), IsPLHomeomorphOn γ (Icc 0 1) A ∧ γ 0 = p ∧ γ 1 = q := by
  have hpq : p ≠ q := by
    intro hpq
    obtain ⟨f, -, hi, -, hf0, hf1⟩ := hA
    exact zero_ne_one (hi Schoenflies.zero_mem_I Schoenflies.one_mem_I
      (hf0.trans (hpq.trans hf1.symm)))
  obtain ⟨γ, hγ⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hPL
  obtain ⟨s, hs, hγs⟩ := hγ.bijOn.surjOn hA.left_mem
  obtain ⟨t, ht, hγt⟩ := hγ.bijOn.surjOn hA.right_mem
  have hst : s ≠ t := fun h => hpq (hγs.symm.trans ((congrArg γ h).trans hγt))
  have hsubarc := Schoenflies.isArcBetween_subarc_of_injOn_I
    hγ.isPiecewiseAffineOn.continuousOn hγ.bijOn.injOn hs ht hst
  rw [hγs, hγt] at hsubarc
  have hsub : uIcc s t ⊆ Icc 0 1 := Schoenflies.uIcc_subset_I hs ht
  have himage : γ '' uIcc s t = A :=
    hA.eq_of_subset hsubarc ((image_mono hsub).trans hγ.image_eq.subset)
  have hcover : Icc (0 : ℝ) 1 ⊆ uIcc s t := by
    intro u hu
    obtain ⟨v, hv, hγv⟩ := himage.symm.subset (hγ.bijOn.mapsTo hu)
    exact (hγ.bijOn.injOn (hsub hv) hu hγv) ▸ hv
  have h0 := hcover (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
  have h1 := hcover (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  rcases hst.lt_or_gt with hst | hts
  · rw [uIcc_of_le hst.le] at h0 h1
    have hs0 : s = 0 := le_antisymm h0.1 hs.1
    have ht1 : t = 1 := le_antisymm ht.2 h1.2
    exact ⟨γ, hγ, hs0 ▸ hγs, ht1 ▸ hγt⟩
  · rw [uIcc_of_ge hts.le] at h0 h1
    have ht0 : t = 0 := le_antisymm h0.1 ht.1
    have hs1 : s = 1 := le_antisymm hs.2 h1.2
    have hrevPL := isPiecewiseAffineOn_subarc hγ.isPiecewiseAffineOn
      (show (1 : ℝ) ∈ Icc 0 1 by norm_num) (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    have hrevInj : InjOn (Schoenflies.subarc γ 1 0) (Icc 0 1) :=
      Schoenflies.injOn_subarc (by simpa using hγ.bijOn.injOn) one_ne_zero
    have hrevImage : Schoenflies.subarc γ 1 0 '' Icc 0 1 = A := by
      rw [Schoenflies.subarc_image, uIcc_of_ge zero_le_one, hγ.image_eq]
    refine ⟨Schoenflies.subarc γ 1 0,
      isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
        hrevPL (hrevImage ▸ hrevInj.bijOn_image), ?_, ?_⟩
    · simpa using hs1 ▸ hγs
    · simpa using ht0 ▸ hγt

theorem exists_isPLHomeomorphOn_of_isArcBetween {A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : IsPLBall 1 A) (hB : IsPLBall 1 B) {p q r s : EuclideanSpace ℝ (Fin 2)}
    (hApq : Schoenflies.IsArcBetween A p q) (hBrs : Schoenflies.IsArcBetween B r s) :
    ∃ f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn f A B ∧ f p = r ∧ f q = s := by
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hA hApq
  obtain ⟨η, hη, hη0, hη1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hB hBrs
  refine ⟨_, hγ.symm.trans hη, ?_, ?_⟩
  · change η (Function.invFunOn γ (Icc 0 1) p) = r
    rw [← hγ0, hγ.bijOn.invOn_invFunOn.1 (by norm_num), hη0]
  · change η (Function.invFunOn γ (Icc 0 1) q) = s
    rw [← hγ1, hγ.bijOn.invOn_invFunOn.1 (by norm_num), hη1]

theorem exists_isCutPair_isPLBall_of_isPLSphere_one {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLSphere 1 J) {p q : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ J) (hq : q ∈ J)
    (hpq : p ≠ q) :
    ∃ A B, Schoenflies.IsCutPair J p q A B ∧ IsPLBall 1 A ∧ IsPLBall 1 B := by
  obtain ⟨γ, hγ, hPL, hγJ⟩ := exists_piecewiseAffine_loop_of_isPLSphere_one hJ
  rw [← hγJ] at hp hq ⊢
  obtain ⟨s, hs, hs1, rfl⟩ := hγ.parameter_before_finish hp
  obtain ⟨t, ht, ht1, rfl⟩ := hγ.parameter_before_finish hq
  have hstne : s ≠ t := fun h => hpq (congrArg γ h)
  have hsplit : ∀ {s t : ℝ}, s ∈ Icc 0 1 → t ∈ Icc 0 1 → t < 1 → s < t →
      ∃ A B, Schoenflies.IsCutPair (γ '' Icc 0 1) (γ s) (γ t) A B ∧
        IsPLBall 1 A ∧ IsPLBall 1 B := by
    intro a b ha hb hb1 hab
    refine ⟨γ '' Icc a b, γ '' Icc 0 a ∪ γ '' Icc b 1, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · exact hγ.middle_IsArcBetween ha hb hb1.ne hab
    · exact (hγ.outside_IsArcBetween ha hb (hab.trans hb1).ne hb1.ne hab).reverse
    · exact Schoenflies.IsLoop.pieces_cover ha hb
    · exact hγ.pieces_meet_at_ends ha hb (hab.trans hb1).ne hb1.ne hab
    · exact isPLBall_image_Icc_of_isPiecewiseAffineOn hab
        (hPL.mono_of_isPolyhedron isHPolytope_Icc.isPolyhedron (Icc_subset_Icc ha.1 hb.2))
        (hγ.injective_on_middle ha hb hb1.ne)
    · exact isPLBall_outside_subarcs hγ hPL ha hb hb1 hab
  rcases hstne.lt_or_gt with hst | hts
  · exact hsplit hs ht (lt_of_le_of_ne ht.2 ht1) hst
  · obtain ⟨A, B, hcut, hA, hB⟩ := hsplit ht hs (lt_of_le_of_ne hs.2 hs1) hts
    refine ⟨A, B, ⟨hcut.fst.reverse, hcut.snd.reverse, hcut.union_eq, ?_⟩, hA, hB⟩
    rw [hcut.inter_eq, pair_comm]

theorem exists_isCutPair_of_isArcBetween_subset_isPLSphere
    {J A : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J)
    {p q : EuclideanSpace ℝ (Fin 2)} (hA : Schoenflies.IsArcBetween A p q) (hAJ : A ⊆ J) :
    ∃ B, Schoenflies.IsCutPair J p q A B ∧ IsPLBall 1 A ∧ IsPLBall 1 B := by
  have hpq : p ≠ q := by
    intro hpq
    obtain ⟨f, -, hi, -, hf0, hf1⟩ := hA
    exact zero_ne_one (hi Schoenflies.zero_mem_I Schoenflies.one_mem_I
      (hf0.trans (hpq.trans hf1.symm)))
  obtain ⟨B, C, hcut, hB, hC⟩ := exists_isCutPair_isPLBall_of_isPLSphere_one hJ
    (hAJ hA.left_mem) (hAJ hA.right_mem) hpq
  rcases DifferentialGeometry.Topology.PlanarJordan.eq_or_eq_of_isArcBetween_subset_isCutPair
    hcut hA hAJ with hABeq | hACeq
  · exact ⟨C, hABeq.symm ▸ hcut, hABeq.symm ▸ hB, hC⟩
  · exact ⟨B, hACeq.symm ▸ hcut.symm, hACeq.symm ▸ hC, hB⟩

theorem isPLBall_of_isArc_subset_isPLSphere {J A : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLSphere 1 J) (hA : Schoenflies.IsArc A) (hAJ : A ⊆ J) : IsPLBall 1 A := by
  obtain ⟨p, q, hpq⟩ := hA.exists_isArcBetween
  obtain ⟨-, -, hball, -⟩ := exists_isCutPair_of_isArcBetween_subset_isPLSphere hJ hpq hAJ
  exact hball

theorem isPLBall_compl_openArc_of_isPLSphere_one {J A : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLSphere 1 J) {p q : EuclideanSpace ℝ (Fin 2)}
    (hA : Schoenflies.IsArcBetween A p q) (hAJ : A ⊆ J) :
    IsPLBall 1 (J \ (A \ {p, q})) := by
  obtain ⟨B, hcut, -, hB⟩ := exists_isCutPair_of_isArcBetween_subset_isPLSphere hJ hA hAJ
  have heq : J \ (A \ {p, q}) = B := by
    rw [← hcut.union_eq]
    ext x
    have hx : (x ∈ A ∧ x ∈ B) ↔ x ∈ ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) := by
      change x ∈ A ∩ B ↔ _
      rw [hcut.inter_eq]
    simp only [mem_sdiff, mem_union]
    tauto
  rwa [heq]

open Classical in
theorem exists_isPLHomeomorphOn_of_isCutPair_of_isPLBall
    {J J' A B A' B' : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : IsPLBall 1 A) (hB : IsPLBall 1 B) (hA' : IsPLBall 1 A') (hB' : IsPLBall 1 B')
    {p q p' q' : EuclideanSpace ℝ (Fin 2)}
    (hcut : Schoenflies.IsCutPair J p q A B) (hcut' : Schoenflies.IsCutPair J' p' q' A' B') :
    ∃ f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn f J J' ∧ IsPLHomeomorphOn f A A' ∧ IsPLHomeomorphOn f B B' ∧
        f p = p' ∧ f q = q' := by
  obtain ⟨f, hf, hfp, hfq⟩ := exists_isPLHomeomorphOn_of_isArcBetween hA hA' hcut.fst hcut'.fst
  obtain ⟨g, hg, hgp, hgq⟩ := exists_isPLHomeomorphOn_of_isArcBetween hB hB' hcut.snd hcut'.snd
  have hfg : EqOn f g (A ∩ B) := by
    rw [hcut.inter_eq]
    rintro x (rfl | rfl)
    · exact hfp.trans hgp.symm
    · exact hfq.trans hgq.symm
  have hmeet : f '' (A ∩ B) = A' ∩ B' := by
    rw [hcut.inter_eq, hcut'.inter_eq, image_pair, hfp, hfq]
  have h := hf.piecewise hg hA.isPolyhedron hB.isPolyhedron hfg hmeet
  rw [hcut.union_eq, hcut'.union_eq] at h
  have hleft : EqOn (A.piecewise f g) f A := A.piecewise_eqOn f g
  have hright : EqOn (A.piecewise f g) g B := by
    intro x hx
    by_cases hxA : x ∈ A
    · rw [A.piecewise_eq_of_mem f g hxA, hfg ⟨hxA, hx⟩]
    · exact A.piecewise_eq_of_notMem f g hxA
  exact ⟨_, h, hf.congr hleft, hg.congr hright,
    (hleft hcut.fst.left_mem).trans hfp, (hleft hcut.fst.right_mem).trans hfq⟩

theorem exists_isPLHomeomorphOn_of_isCutPair
    {J J' A B A' B' : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLSphere 1 J) (hJ' : IsPLSphere 1 J')
    {p q p' q' : EuclideanSpace ℝ (Fin 2)}
    (hcut : Schoenflies.IsCutPair J p q A B) (hcut' : Schoenflies.IsCutPair J' p' q' A' B') :
    ∃ f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn f J J' ∧ IsPLHomeomorphOn f A A' ∧ IsPLHomeomorphOn f B B' ∧
        f p = p' ∧ f q = q' :=
  exists_isPLHomeomorphOn_of_isCutPair_of_isPLBall
    (isPLBall_of_isArc_subset_isPLSphere hJ hcut.fst.isArc hcut.fst_subset)
    (isPLBall_of_isArc_subset_isPLSphere hJ hcut.snd.isArc hcut.snd_subset)
    (isPLBall_of_isArc_subset_isPLSphere hJ' hcut'.fst.isArc hcut'.fst_subset)
    (isPLBall_of_isArc_subset_isPLSphere hJ' hcut'.snd.isArc hcut'.snd_subset) hcut hcut'

open Classical in
theorem exists_isPLHomeomorphOn_eqOn_arc_of_isPLSphere_one
    {J J' A A' : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J) (hJ' : IsPLSphere 1 J')
    {p q : EuclideanSpace ℝ (Fin 2)} (hA : Schoenflies.IsArcBetween A p q) (hAJ : A ⊆ J)
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hg : IsPLHomeomorphOn g A A') (hA'J' : A' ⊆ J') :
    ∃ G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn G J J' ∧ EqOn G g A := by
  obtain ⟨B, hcut, hAball, hBball⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere hJ hA hAJ
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hAball hA
  have hγg := hγ.trans hg
  have hA' : Schoenflies.IsArcBetween A' (g p) (g q) :=
    ⟨g ∘ γ, hγg.isPiecewiseAffineOn.continuousOn, hγg.bijOn.injOn, hγg.image_eq,
      congrArg g hγ0, congrArg g hγ1⟩
  obtain ⟨B', hcut', -, hB'ball⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere hJ' hA' hA'J'
  obtain ⟨f, hf, hfp, hfq⟩ :=
    exists_isPLHomeomorphOn_of_isArcBetween hBball hB'ball hcut.snd hcut'.snd
  have hgf : EqOn g f (A ∩ B) := by
    rw [hcut.inter_eq]
    rintro x (rfl | rfl)
    · exact hfp.symm
    · exact hfq.symm
  have hmeet : g '' (A ∩ B) = A' ∩ B' := by
    rw [hcut.inter_eq, hcut'.inter_eq, image_pair]
  have h := hg.piecewise hf hAball.isPolyhedron hBball.isPolyhedron hgf hmeet
  rw [hcut.union_eq, hcut'.union_eq] at h
  exact ⟨_, h, A.piecewise_eqOn g f⟩

open Classical in
theorem exists_isPLHomeomorphOn_eqOn_arc_of_boundaryComplex
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    [Finite K.faces] [Finite L.faces] (hK : IsPLBall 2 K.space) (hL : IsPLBall 2 L.space)
    {A B : Set (EuclideanSpace ℝ (Fin 2))} {p q : EuclideanSpace ℝ (Fin 2)}
    (hA : Schoenflies.IsArcBetween A p q) (hAK : A ⊆ (boundaryComplex 2 K).space)
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hg : IsPLHomeomorphOn g A B) (hBL : B ⊆ (boundaryComplex 2 L).space) :
    ∃ G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn G K.space L.space ∧ EqOn G g A := by
  have hKboundary : IsPLSphere 1 (boundaryComplex 2 K).space :=
    isPLSphere_boundaryComplex_space_of_isPLBall (n := 1) K hK
  have hLboundary : IsPLSphere 1 (boundaryComplex 2 L).space :=
    isPLSphere_boundaryComplex_space_of_isPLBall (n := 1) L hL
  obtain ⟨f, hf, hfg⟩ := exists_isPLHomeomorphOn_eqOn_arc_of_isPLSphere_one
    hKboundary hLboundary hA hAK hg hBL
  obtain ⟨G, hG, hGf⟩ := exists_isPLHomeomorphOn_of_boundaryComplex (n := 1) K L hK hL hf
  exact ⟨G, hG, (hGf.mono hAK).trans hfg⟩

open Classical in
theorem exists_isPLBall_pair_with_segment_inter :
    ∃ K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)),
      K.faces.Finite ∧ L.faces.Finite ∧ IsPLBall 2 K.space ∧ IsPLBall 2 L.space ∧
        IsPLBall 2 (K.space ∪ L.space) ∧
        ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧ K.space ∩ L.space = segment ℝ p q ∧
          segment ℝ p q ⊆ (boundaryComplex 2 K).space ∧
          segment ℝ p q ⊆ (boundaryComplex 2 L).space := by
  obtain ⟨T, hT, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (E := EuclideanSpace ℝ (Fin 2)) (n := 1) (by simp) 0 (U := univ) Filter.univ_mem
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  have hecard : (T.erase a).card = 2 := by rw [Finset.card_erase_of_mem ha, hcard]
  obtain ⟨b, c, hbc, he⟩ := Finset.card_eq_two.mp hecard
  have hb : b ∈ T.erase a := by rw [he]; simp
  have hc : c ∈ T.erase a := by rw [he]; simp
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have hca : c ≠ a := (Finset.mem_erase.mp hc).1
  have hbT : b ∈ T := Finset.mem_of_mem_erase hb
  have hcT : c ∈ T := Finset.mem_of_mem_erase hc
  have hTeq : T = {a, b, c} := by rw [← Finset.insert_erase ha, he]
  have hTb : T.erase b = {a, c} := by
    rw [hTeq]
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hTc : T.erase c = {a, b} := by
    rw [hTeq]
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  let p := (T.erase a).centroid ℝ id
  have hp : p ∈ openSimplex (T.erase a) := centroid_mem_openSimplex ⟨b, hb⟩
  have hpb : p ∉ T.erase b := notMem_erase_of_mem_openSimplex_erase hT hp hb
  have hpc : p ∉ T.erase c := notMem_erase_of_mem_openSimplex_erase hT hp hc
  have hpa : p ≠ a := fun h => hpb (h.symm ▸ Finset.mem_erase.mpr ⟨hba.symm, ha⟩)
  have hB : AffineIndependent ℝ
      ((↑) : (insert p (T.erase b) : Finset _) → EuclideanSpace ℝ (Fin 2)) :=
    affineIndependent_insert_erase_far hT hp hb
  have hC : AffineIndependent ℝ
      ((↑) : (insert p (T.erase c) : Finset _) → EuclideanSpace ℝ (Fin 2)) :=
    affineIndependent_insert_erase_far hT hp hc
  have hBcard : (insert p (T.erase b)).card = 3 := by
    rw [Finset.card_insert_of_notMem hpb, Finset.card_erase_of_mem hbT, hcard]
  have hCcard : (insert p (T.erase c)).card = 3 := by
    rw [Finset.card_insert_of_notMem hpc, Finset.card_erase_of_mem hcT, hcard]
  let K := simplexComplex (insert p (T.erase b)) hB
  let L := simplexComplex (insert p (T.erase c)) hC
  have hK : K.space = convexHull ℝ ((insert p (T.erase b) : Finset _) : Set (EuclideanSpace ℝ (Fin 2))) :=
    simplexComplex_space _ hB (Finset.insert_nonempty _ _)
  have hL : L.space = convexHull ℝ ((insert p (T.erase c) : Finset _) : Set (EuclideanSpace ℝ (Fin 2))) :=
    simplexComplex_space _ hC (Finset.insert_nonempty _ _)
  have hKball : IsPLBall 2 K.space := by
    rw [hK]
    exact isPLBall_convexHull_of_affineIndependent _ hB hBcard
  have hLball : IsPLBall 2 L.space := by
    rw [hL]
    exact isPLBall_convexHull_of_affineIndependent _ hC hCcard
  have hpT : p ∈ convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2))) :=
    mem_convexHull_of_mem_openSimplex_erase hp
  have hsub : ∀ v, convexHull ℝ ((insert p (T.erase v) : Finset _) : Set (EuclideanSpace ℝ (Fin 2))) ⊆
      convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro v
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    rintro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hpT
    · exact subset_convexHull ℝ _ (Finset.mem_of_mem_erase hx)
  have hunion : K.space ∪ L.space = convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [hK, hL]
    refine Subset.antisymm (union_subset (hsub b) (hsub c)) fun x hx => ?_
    obtain ⟨v, hv, hxv⟩ := exists_mem_convexHull_insert_erase_far hT ha hp hx
    rw [he, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Or.inl hxv
    · exact Or.inr hxv
  have hcone := isConeBase_far hT ha hp (by omega)
  have hface : ∀ v ∈ T.erase a,
      T.erase v ∈ (starComplex (simplexBoundary T hT) a).faces := by
    intro v hv
    have hvT := Finset.mem_of_mem_erase hv
    have hav : a ∈ T.erase v := Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hv).1.symm, ha⟩
    have hf : T.erase v ∈ (simplexBoundary T hT).faces :=
      ⟨Finset.erase_subset _ _, ⟨a, hav⟩, fun h => Finset.notMem_erase v T (h.symm ▸ hvT)⟩
    exact ⟨hf, by rwa [Finset.insert_eq_of_mem hav]⟩
  have hBface : insert p (T.erase b) ∈ (coneComplex hcone).faces :=
    Or.inr (Or.inr ⟨T.erase b, hface b hb, rfl⟩)
  have hCface : insert p (T.erase c) ∈ (coneComplex hcone).faces :=
    Or.inr (Or.inr ⟨T.erase c, hface c hc, rfl⟩)
  have hmeet : (insert p (T.erase b)) ∩ (insert p (T.erase c)) = {p, a} := by
    rw [hTb, hTc]
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hinter : K.space ∩ L.space = segment ℝ p a := by
    rw [hK, hL, (coneComplex hcone).convexHull_inter_convexHull hBface hCface,
      ← Finset.coe_inter, hmeet, Finset.coe_pair, convexHull_pair]
  have hedge : ∀ (S : Finset (EuclideanSpace ℝ (Fin 2)))
      (hS : AffineIndependent ℝ ((↑) : S → EuclideanSpace ℝ (Fin 2))), S.card = 3 →
      {p, a} ⊆ S → segment ℝ p a ⊆ (boundaryComplex 2 (simplexComplex S hS)).space := by
    intro S hS hScard hpaS
    rw [boundaryComplex_simplexComplex (n := 1) hS hScard, ← convexHull_pair]
    have hne : ({p, a} : Finset _) ≠ S := by
      intro h
      have hsize : ({p, a} : Finset _).card = 2 := by simp [hpa]
      rw [h, hScard] at hsize
      omega
    simpa only [Finset.coe_pair] using (simplexBoundary S hS).convexHull_subset_space
      ⟨hpaS, Finset.insert_nonempty _ _, hne⟩
  refine ⟨K, L, simplexComplex_faces_finite _ hB, simplexComplex_faces_finite _ hC,
    hKball, hLball, ?_, p, a, hpa, hinter, ?_, ?_⟩
  · rw [hunion]
    exact isPLBall_convexHull_of_affineIndependent _ hT hcard
  · exact hedge _ hB hBcard (by rw [hTb]; exact Finset.insert_subset_insert _ (by simp))
  · exact hedge _ hC hCcard (by rw [hTc]; exact Finset.insert_subset_insert _ (by simp))

theorem isPLSphere_one_of_isCutPair {J A B : Set (EuclideanSpace ℝ (Fin 2))}
    {p q : EuclideanSpace ℝ (Fin 2)} (hcut : Schoenflies.IsCutPair J p q A B)
    (hA : IsPLBall 1 A) (hB : IsPLBall 1 B) : IsPLSphere 1 J := by
  classical
  obtain ⟨K, -, hKfin, -, hK, -, -, r, s, hrs, -, hsub, -⟩ :=
    exists_isPLBall_pair_with_segment_inter
  have : Finite K.faces := hKfin.to_subtype
  have hboundary : IsPLSphere 1 (boundaryComplex 2 K).space :=
    isPLSphere_boundaryComplex_space_of_isPLBall (n := 1) K hK
  obtain ⟨C, D, hcut', hC, hD⟩ := exists_isCutPair_isPLBall_of_isPLSphere_one hboundary
    (hsub (left_mem_segment ℝ r s)) (hsub (right_mem_segment ℝ r s)) hrs
  obtain ⟨f, hf, -, -, -, -⟩ :=
    exists_isPLHomeomorphOn_of_isCutPair_of_isPLBall hA hB hC hD hcut hcut'
  exact hboundary.of_isPLHomeomorphOn hf.symm

theorem isPLSphere_one_union_of_isCrosscut {J P A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLSphere 1 J) (hP : IsPLBall 1 P) {p q : EuclideanSpace ℝ (Fin 2)}
    (h : Schoenflies.IsCrosscut J P p q) (hcut : Schoenflies.IsCutPair J p q A B) :
    IsPLSphere 1 (A ∪ P) := by
  have hmeet : A ∩ P = {p, q} := by
    refine Subset.antisymm (fun x hx => h.inter_eq.subset ⟨hx.2, hcut.fst_subset hx.1⟩) ?_
    exact pair_subset ⟨hcut.fst.left_mem, h.arc.left_mem⟩ ⟨hcut.fst.right_mem, h.arc.right_mem⟩
  exact isPLSphere_one_of_isCutPair ⟨hcut.fst, h.arc, rfl, hmeet⟩
    (isPLBall_of_isArc_subset_isPLSphere hJ hcut.fst.isArc hcut.fst_subset) hP

theorem isCrosscut_segment_of_mem_faces
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : Schoenflies.IsJordanCurve J)
    (hK : K.space = closure (Schoenflies.inside J)) (hJK : (restrict K J).space = J)
    {p q : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q) (hp : p ∈ J) (hq : q ∈ J)
    (hpqK : {p, q} ∈ K.faces) (hpqJ : {p, q} ∉ (restrict K J).faces) :
    Schoenflies.IsCrosscut J (segment ℝ p q) p q := by
  classical
  refine ⟨hJ, Schoenflies.isArcBetween_segment hpq, Schoenflies.isPolygonal_segment p q, hp, hq, ?_⟩
  rintro x ⟨hx, hxpq⟩
  have hxconv : x ∈ convexHull ℝ (({p, q} : Finset (EuclideanSpace ℝ (Fin 2))) : Set _) := by
    simpa only [Finset.coe_pair, convexHull_pair] using hx
  obtain ⟨s, hspq, hsne, hxs⟩ := exists_openSimplex_of_mem_convexHull hxconv
  have hs : s = {p, q} := by
    by_contra hsne'
    have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hspq, hsne'⟩)
    have hpaircard : ({p, q} : Finset (EuclideanSpace ℝ (Fin 2))).card = 2 := by simp [hpq]
    have hspos := Finset.card_pos.mpr hsne
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
    have hxr : x = r := by simpa [hr] using openSimplex_subset_convexHull s hxs
    have hrpq : r ∈ ({p, q} : Finset (EuclideanSpace ℝ (Fin 2))) := hspq (by simp [hr])
    exact hxpq (by simpa [hxr] using hrpq)
  have hxnot : x ∉ J := by
    rw [← hJK]
    exact notMem_space_of_notMem_faces (restrict_faces_subset K J) hpqK hpqJ (hs ▸ hxs)
  have hxcl := hK ▸ K.convexHull_subset_space hpqK hxconv
  rw [(Schoenflies.IsRegionOf.inside J).closure_eq (Schoenflies.jordan_curve_theorem hJ)] at hxcl
  exact hxcl.resolve_right hxnot

theorem exists_triangle_with_boundary_edge
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) [Finite K.faces]
    {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J)
    (hK : K.space = closure (Schoenflies.inside J)) (hJK : (restrict K J).space = J) :
    ∃ s ∈ (restrict K J).faces, s.card = 2 ∧ ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3 := by
  have : Finite (restrict K J).faces := (restrict_faces_finite K J).to_subtype
  obtain ⟨s, hs, hcard⟩ := exists_face_card_two_of_isPLSphere_one (restrict K J) (hJK.symm ▸ hJ)
  have hsep := Schoenflies.jordan_curve_theorem (isJordanCurve_of_isPLSphere_one hJ)
  obtain ⟨t, ht, hst, htcard⟩ := exists_face_superset_card_eq_finrank_succ K hsep.isOpen_inside hK hs.1
  exact ⟨s, hs, hcard, t, ht, hst, by simpa using htcard⟩

theorem restrict_arc_space_of_isCutPair
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {J A B : Set (EuclideanSpace ℝ (Fin 2))} (hJK : (restrict K J).space = J)
    {p q : EuclideanSpace ℝ (Fin 2)} (hp : {p} ∈ K.faces) (hq : {q} ∈ K.faces)
    (hcut : Schoenflies.IsCutPair J p q A B) : (restrict K A).space = A := by
  refine Subset.antisymm (restrict_space_subset _ _) fun x hxA => ?_
  have hxJ : x ∈ (restrict K J).space := hJK.symm ▸ hcut.fst_subset hxA
  obtain ⟨t, ht, hxt⟩ := (restrict K J).mem_space_iff.mp hxJ
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K (K.convexHull_subset_space ht.1 hxt)
  have hsJ : convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ J :=
    (convexHull_mono (Finset.coe_subset.mpr
      (face_subset_of_mem_openSimplex_of_mem_convexHull K hs ht.1 hxs hxt))).trans ht.2
  have hsA : convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ A := by
    by_cases hsmall : s.card ≤ 1
    · have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
      have hxa : x = a := by simpa using openSimplex_subset_convexHull _ hxs
      subst x
      simpa using hxA
    have hnot : ∀ z, {z} ∈ K.faces → z ∉ openSimplex s := by
      intro z hz hzs
      have hsz := face_subset_of_mem_openSimplex_of_mem_convexHull K hs hz hzs
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self z)))
      have hcard := Finset.card_le_card hsz
      exact hsmall (by simpa using hcard)
    have havoid : Disjoint (openSimplex s) ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) := by
      refine Set.disjoint_left.mpr fun z hz hzpq => ?_
      rcases hzpq with rfl | rfl
      · exact hnot _ hp hz
      · exact hnot _ hq hz
    have hcover : openSimplex s ⊆ Aᶜ ∪ Bᶜ := by
      intro z hz
      by_cases hzA : z ∈ A
      · exact Or.inr fun hzB => Set.disjoint_left.mp havoid hz (hcut.inter_eq.subset ⟨hzA, hzB⟩)
      · exact Or.inl hzA
    have hxBc : x ∈ Bᶜ := fun hxB =>
      Set.disjoint_left.mp havoid hxs (hcut.inter_eq.subset ⟨hxA, hxB⟩)
    have hopen : openSimplex s ⊆ A := by
      intro z hz
      by_contra hzA
      obtain ⟨y, hy, hyA, hyB⟩ := (convex_openSimplex s).isPreconnected _ _
        hcut.fst.isArc.isClosed.isOpen_compl hcut.snd.isArc.isClosed.isOpen_compl
        hcover ⟨z, hz, hzA⟩ ⟨x, hxs, hxBc⟩
      exact (hcut.union_eq.symm.subset (hsJ (openSimplex_subset_convexHull s hy))).elim hyA hyB
    exact (convexHull_subset_closure_openSimplex (K.nonempty_of_mem_faces hs)).trans
      (closure_minimal hopen hcut.fst.isArc.isClosed)
  exact (restrict K A).convexHull_subset_space ⟨hs, hsA⟩ (openSimplex_subset_convexHull s hxs)

theorem restrict_closure_inside_boundary_space_of_isCrosscut
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {J P A B : Set (EuclideanSpace ℝ (Fin 2))} (hJK : (restrict K J).space = J)
    (hPK : (restrict K P).space = P) {p q : EuclideanSpace ℝ (Fin 2)}
    (hp : {p} ∈ K.faces) (hq : {q} ∈ K.faces) (h : Schoenflies.IsCrosscut J P p q)
    (hcut : Schoenflies.IsCutPair J p q A B) :
    (restrict (restrict K (closure (Schoenflies.inside (A ∪ P)))) (A ∪ P)).space = A ∪ P := by
  have hj : ∀ S, Schoenflies.IsJordanCurve S → Schoenflies.IsSeparating S :=
    fun _ => Schoenflies.jordan_curve_theorem
  have hsub : A ∪ P ⊆ closure (Schoenflies.inside (A ∪ P)) :=
    (h.frontier_side hj hcut).symm.subset.trans frontier_subset_closure
  rw [restrict_restrict, inter_eq_right.mpr hsub]
  exact restrict_union_space (restrict_arc_space_of_isCutPair K hJK hp hq hcut) hPK

theorem restrict_closure_inside_space_of_isCrosscut
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) [Finite K.faces]
    {J P A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : K.space = closure (Schoenflies.inside J))
    (hbarrier : (restrict K (J ∪ P)).space = J ∪ P)
    {p q : EuclideanSpace ℝ (Fin 2)} (h : Schoenflies.IsCrosscut J P p q)
    (hcut : Schoenflies.IsCutPair J p q A B) :
    (restrict K (closure (Schoenflies.inside (A ∪ P)))).space =
      closure (Schoenflies.inside (A ∪ P)) := by
  have hj : ∀ S, Schoenflies.IsJordanCurve S → Schoenflies.IsSeparating S :=
    fun _ => Schoenflies.jordan_curve_theorem
  have hsub : Schoenflies.inside (A ∪ P) ⊆ K.space := by
    rw [hK]
    exact fun x hx => subset_closure (h.side_subset hj hcut hx).1
  have hfrontier : frontier (Schoenflies.inside (A ∪ P)) ⊆ (restrict K (J ∪ P)).space := by
    rw [h.frontier_side hj hcut, hbarrier]
    exact union_subset_union_left P hcut.fst_subset
  have hdisj : Disjoint (Schoenflies.inside (A ∪ P)) (restrict K (J ∪ P)).space := by
    rw [hbarrier]
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    have hx' := h.side_subset hj hcut hx
    rcases hy with hy | hy
    · exact Schoenflies.inside_subset_compl hx'.1 hy
    · exact hx'.2 hy
  exact restrict_closure_space_of_frontier_subset_subcomplex K (restrict K (J ∪ P))
    (restrict_faces_subset K _) (h.isOpen_side hj hcut) hsub hfrontier hdisj

theorem restrict_closure_inside_union_of_isCrosscut
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) [Finite K.faces]
    {J P A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : K.space = closure (Schoenflies.inside J))
    (hbarrier : (restrict K (J ∪ P)).space = J ∪ P)
    {p q : EuclideanSpace ℝ (Fin 2)} (h : Schoenflies.IsCrosscut J P p q)
    (hcut : Schoenflies.IsCutPair J p q A B) :
    (restrict K (closure (Schoenflies.inside (A ∪ P)))).space ∪
      (restrict K (closure (Schoenflies.inside (B ∪ P)))).space = K.space := by
  rw [restrict_closure_inside_space_of_isCrosscut K hK hbarrier h hcut,
    restrict_closure_inside_space_of_isCrosscut K hK hbarrier h hcut.symm,
    PlanarJordan.closure_inside_union_of_isCrosscut h hcut, hK]

theorem restrict_closure_inside_inter_of_isCrosscut
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) [Finite K.faces]
    {J P A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : K.space = closure (Schoenflies.inside J))
    (hbarrier : (restrict K (J ∪ P)).space = J ∪ P)
    {p q : EuclideanSpace ℝ (Fin 2)} (h : Schoenflies.IsCrosscut J P p q)
    (hcut : Schoenflies.IsCutPair J p q A B) :
    (restrict K (closure (Schoenflies.inside (A ∪ P)))).space ∩
      (restrict K (closure (Schoenflies.inside (B ∪ P)))).space = P := by
  rw [restrict_closure_inside_space_of_isCrosscut K hK hbarrier h hcut,
    restrict_closure_inside_space_of_isCrosscut K hK hbarrier h hcut.symm,
    PlanarJordan.closure_inside_inter_of_isCrosscut h hcut]

theorem ncard_faces_card_restrict_closure_inside_lt_of_isCrosscut
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) [Finite K.faces]
    {J P A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : K.space = closure (Schoenflies.inside J))
    {p q : EuclideanSpace ℝ (Fin 2)} (h : Schoenflies.IsCrosscut J P p q)
    (hcut : Schoenflies.IsCutPair J p q A B) :
    {s ∈ (restrict K (closure (Schoenflies.inside (A ∪ P)))).faces | s.card = 3}.ncard <
      {s ∈ K.faces | s.card = 3}.ncard := by
  have hj : ∀ S, Schoenflies.IsJordanCurve S → Schoenflies.IsSeparating S :=
    fun _ => Schoenflies.jordan_curve_theorem
  have hUK : Schoenflies.inside (B ∪ P) ⊆ K.space := by
    intro x hx
    rw [hK]
    exact subset_closure (h.side_subset hj hcut.symm hx).1
  have hdisj : Disjoint (Schoenflies.inside (B ∪ P))
      (closure (Schoenflies.inside (A ∪ P))) := by
    refine Set.disjoint_left.mpr fun x hxB hxA => ?_
    have hxP := (PlanarJordan.closure_inside_inter_of_isCrosscut h hcut).subset
      ⟨hxA, subset_closure hxB⟩
    exact (h.side_subset hj hcut.symm hxB).2 hxP
  simpa using ncard_faces_card_restrict_lt_of_isOpen K (h.isOpen_side hj hcut.symm)
    (h.side_nonempty hj hcut.symm) hUK hdisj

open Classical in
theorem isPLBall_union_of_boundary_arc
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    [Finite K.faces] [Finite L.faces] (hK : IsPLBall 2 K.space) (hL : IsPLBall 2 L.space)
    (hArc : Schoenflies.IsArc (K.space ∩ L.space))
    (hAK : K.space ∩ L.space ⊆ (boundaryComplex 2 K).space)
    (hAL : K.space ∩ L.space ⊆ (boundaryComplex 2 L).space) :
    IsPLBall 2 (K.space ∪ L.space) := by
  obtain ⟨a, b, hArc⟩ := hArc.exists_isArcBetween
  obtain ⟨P, Q, hPfin, hQfin, hP, hQ, hPQ, p, q, hpq, hinter, hBP, hBQ⟩ :=
    exists_isPLBall_pair_with_segment_inter
  have : Finite P.faces := hPfin.to_subtype
  have : Finite Q.faces := hQfin.to_subtype
  have hboundary : IsPLSphere 1 (boundaryComplex 2 K).space :=
    isPLSphere_boundaryComplex_space_of_isPLBall (n := 1) K hK
  have hball : IsPLBall 1 (K.space ∩ L.space) :=
    isPLBall_of_isArc_subset_isPLSphere hboundary hArc.isArc hAK
  obtain ⟨g, hg, -, -⟩ := exists_isPLHomeomorphOn_of_isArcBetween hball
    (isPLBall_segment hpq) hArc (Schoenflies.isArcBetween_segment hpq)
  obtain ⟨f₁, hf₁, hf₁g⟩ :=
    exists_isPLHomeomorphOn_eqOn_arc_of_boundaryComplex K P hK hP hArc hAK hg hBP
  obtain ⟨f₂, hf₂, hf₂g⟩ :=
    exists_isPLHomeomorphOn_eqOn_arc_of_boundaryComplex L Q hL hQ hArc hAL hg hBQ
  have hfg : EqOn f₁ f₂ (K.space ∩ L.space) := hf₁g.trans hf₂g.symm
  have himage : f₁ '' (K.space ∩ L.space) = P.space ∩ Q.space :=
    hf₁g.image_eq.trans (hg.image_eq.trans hinter.symm)
  have h := hf₁.piecewise hf₂ hK.isPolyhedron hL.isPolyhedron hfg himage
  exact hPQ.of_isPLHomeomorphOn h.symm

theorem isPolyhedron_closure_inside_of_isPLSphere_one {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLSphere 1 J) : IsPolyhedron (closure (Schoenflies.inside J)) := by
  have hsep := Schoenflies.jordan_curve_theorem (isJordanCurve_of_isPLSphere_one hJ)
  exact isPolyhedron_closure_of_isPolyhedron_frontier hsep.isOpen_inside hsep.isBounded_inside
    (hsep.frontier_inside.symm ▸ hJ.isPolyhedron)

theorem frontier_closure_inside_of_isPLSphere_one {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLSphere 1 J) : frontier (closure (Schoenflies.inside J)) = J :=
  PlanarJordan.frontier_closure_inside (isJordanCurve_of_isPLSphere_one hJ)

theorem isPLBall_closure_inside_of_isCrosscut {J P A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLSphere 1 J) (hP : IsPLBall 1 P) {p q : EuclideanSpace ℝ (Fin 2)}
    (h : Schoenflies.IsCrosscut J P p q) (hcut : Schoenflies.IsCutPair J p q A B)
    (hA : IsPLBall 2 (closure (Schoenflies.inside (A ∪ P))))
    (hB : IsPLBall 2 (closure (Schoenflies.inside (B ∪ P)))) :
    IsPLBall 2 (closure (Schoenflies.inside J)) := by
  classical
  have hAP := isPLSphere_one_union_of_isCrosscut hJ hP h hcut
  have hBP := isPLSphere_one_union_of_isCrosscut hJ hP h hcut.symm
  obtain ⟨K, hKfin, hKA⟩ := hA.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hLfin, hLB⟩ := hB.isPolyhedron.exists_simplicialComplex
  have : Finite K.faces := hKfin.to_subtype
  have : Finite L.faces := hLfin.to_subtype
  have hK : IsPLBall 2 K.space := hKA.symm ▸ hA
  have hL : IsPLBall 2 L.space := hLB.symm ▸ hB
  have hBK : (boundaryComplex 2 K).space = A ∪ P :=
    boundaryComplex_space_eq_of_isPLBall_of_frontier K hK hAP (by
      rw [hKA]
      exact frontier_closure_inside_of_isPLSphere_one hAP)
  have hBL : (boundaryComplex 2 L).space = B ∪ P :=
    boundaryComplex_space_eq_of_isPLBall_of_frontier L hL hBP (by
      rw [hLB]
      exact frontier_closure_inside_of_isPLSphere_one hBP)
  have hinter : K.space ∩ L.space = P := by
    rw [hKA, hLB]
    exact PlanarJordan.closure_inside_inter_of_isCrosscut h hcut
  have hball := isPLBall_union_of_boundary_arc K L hK hL
    (hinter.symm ▸ h.arc.isArc)
    (by rw [hinter, hBK]; exact subset_union_right)
    (by rw [hinter, hBL]; exact subset_union_right)
  rwa [hKA, hLB, PlanarJordan.closure_inside_union_of_isCrosscut h hcut] at hball

theorem exists_triangulation_closure_inside_of_isPLSphere_one
    {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)),
      K.faces.Finite ∧ K.space = closure (Schoenflies.inside J) ∧ (restrict K J).space = J := by
  have hsep := Schoenflies.jordan_curve_theorem (isJordanCurve_of_isPLSphere_one hJ)
  obtain ⟨L, hLfin, hL⟩ := (isPolyhedron_closure_inside_of_isPLSphere_one hJ).exists_simplicialComplex
  have : Finite L.faces := hLfin.to_subtype
  have hJL : J ⊆ L.space :=
    hsep.frontier_inside.symm.subset.trans (frontier_subset_closure.trans hL.symm.subset)
  obtain ⟨K, hK, hKfin, hJK⟩ := exists_isSubdivision_restrict_space L hJ.isPolyhedron hJL
  exact ⟨K, hKfin, hK.space_eq.trans hL, hJK⟩

theorem exists_polyhedral_region_of_isPLSphere_one {J : Set (EuclideanSpace ℝ (Fin 2))}
    (hJ : IsPLSphere 1 J) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧
      frontier U = J ∧ IsPolyhedron (closure U) ∧
      ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)),
        K.faces.Finite ∧ K.space = closure U ∧ (restrict K J).space = J := by
  have hsep := Schoenflies.jordan_curve_theorem (isJordanCurve_of_isPLSphere_one hJ)
  have hpoly := isPolyhedron_closure_inside_of_isPLSphere_one hJ
  obtain ⟨K, hKfin, hK, hJK⟩ := exists_triangulation_closure_inside_of_isPLSphere_one hJ
  exact ⟨_, hsep.isOpen_inside, hsep.isConnected_inside, hsep.isBounded_inside,
    hsep.frontier_inside, hpoly, K, hKfin, hK, hJK⟩

end DifferentialGeometry.Topology.PiecewiseLinear
