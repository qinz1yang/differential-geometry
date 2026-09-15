import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import DifferentialGeometry.External.Schoenflies.JordanClosed
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
  have hsub : A \ {p, q} ⊆ Bᶜ ∪ Cᶜ := by
    intro z hz
    by_cases hzB : z ∈ B
    · refine Or.inr fun hzC => hz.2 ?_
      exact hcut.inter_eq.subset ⟨hzB, hzC⟩
    · exact Or.inl hzB
  have hnone : ¬ ((A \ {p, q}) ∩ (Bᶜ ∩ Cᶜ)).Nonempty := by
    rintro ⟨z, hz, hzB, hzC⟩
    exact ((hcut.union_eq.symm.subset (hAJ hz.1))).elim hzB hzC
  have hends : ∀ D : Set (EuclideanSpace ℝ (Fin 2)), p ∈ D → q ∈ D →
      A \ {p, q} ⊆ D → A ⊆ D := by
    intro D hpD hqD hD z hz
    by_cases hzp : z ∈ ({p, q} : Set (EuclideanSpace ℝ (Fin 2)))
    · rcases hzp with rfl | rfl
      · exact hpD
      · exact hqD
    · exact hD ⟨hz, hzp⟩
  have hsplit : A ⊆ B ∨ A ⊆ C := by
    by_cases hmeet : ((A \ {p, q}) ∩ Bᶜ).Nonempty
    · refine Or.inr (hends C hcut.snd.left_mem hcut.snd.right_mem fun z hz => ?_)
      by_contra hzC
      exact hnone (hA.isPreconnected_diff _ _ hB.isPolyhedron.isClosed.isOpen_compl
        hC.isPolyhedron.isClosed.isOpen_compl hsub hmeet ⟨z, hz, hzC⟩)
    · refine Or.inl (hends B hcut.fst.left_mem hcut.fst.right_mem fun z hz => ?_)
      by_contra hzB
      exact hmeet ⟨z, hz, hzB⟩
  rcases hsplit with hAB | hAC
  · have hABeq : A = B := hcut.fst.eq_of_subset hA hAB
    exact ⟨C, hABeq.symm ▸ hcut, hABeq.symm ▸ hB, hC⟩
  · have hACeq : A = C := hcut.snd.eq_of_subset hA hAC
    exact ⟨B, hACeq.symm ▸ hcut.symm, hACeq.symm ▸ hC, hB⟩

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
