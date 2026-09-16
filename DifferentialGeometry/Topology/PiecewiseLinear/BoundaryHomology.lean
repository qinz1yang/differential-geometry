import DifferentialGeometry.Topology.PiecewiseLinear.OrderedChainCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.BettiPolyhedra
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSphereRecognition

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace DifferentialGeometry.Topology.SimplicialComplex

universe u
variable {k ι : Type u} [Field k]

def faceSubtypeEquivFacesOfCard (K : PreAbstractSimplicialComplex ι) [Finite K.faces] (m : ℕ) :
    {s : Finset ι // s ∈ K ∧ s.card = m} ≃ {s : Finset ι // s ∈ facesOfCard K m} where
  toFun s := ⟨s.1, (mem_facesOfCard K).mpr s.2⟩
  invFun s := ⟨s.1, (mem_facesOfCard K).mp s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem orderedNormalizedBoundary_boundary [LinearOrder ι]
    (K : PreAbstractSimplicialComplex ι) [Finite K.faces] (n : ℕ)
    (c : {s : Finset ι // s ∈ K ∧ s.card = n + 3} → k) :
    orderedNormalizedBoundary (k := k) K n
      (orderedNormalizedBoundary (k := k) K (n + 1) c) = 0 := by
  let C := (orderedSimplicialSet K).normalizedChainComplex (ModuleCat.of k k)
  let x := (orderedNormalizedChainEquiv (k := k) K (n + 2)).symm c
  have hdd : C.d (n + 1) n (C.d (n + 2) (n + 1) x) = 0 :=
    congrArg (fun f : C.X (n + 2) ⟶ C.X n => f x)
      (C.d_comp_d (n + 2) (n + 1) n)
  simpa [orderedNormalizedBoundary, C, x] using
    congrArg (orderedNormalizedChainEquiv (k := k) K n) hdd

end DifferentialGeometry.Topology.SimplicialComplex

namespace DifferentialGeometry.ShortComplex

universe v
variable {k : Type} [Field k]

theorem finrank_ker_eq_homology_add_range
    (S : CategoryTheory.ShortComplex (ModuleCat.{v} k)) [FiniteDimensional k S.X₂] :
    Module.finrank k (LinearMap.ker S.g.hom) = Module.finrank k S.homology +
      Module.finrank k (LinearMap.range S.f.hom) := by
  have h := finrank_eq_homology_add_range S
  have hr := S.g.hom.finrank_range_add_finrank_ker
  omega

end DifferentialGeometry.ShortComplex

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E k : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Field k]

noncomputable def facePoint (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) : K.space :=
  ⟨s.centroid ℝ id, K.convexHull_subset_space hs
    (openSimplex_subset_convexHull s
      (centroid_mem_openSimplex (K.nonempty_of_mem_faces hs)))⟩

noncomputable def connectedComponentOfFace (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) : ConnectedComponents K.space :=
  ConnectedComponents.mk (facePoint K hs)

open Classical in
theorem mem_connectedComponentComplex_connectedComponentOfFace
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces) :
    s ∈ (connectedComponentComplex K (connectedComponentOfFace K hs)).faces := by
  rw [connectedComponentOfFace, connectedComponentComplex_mk, mem_restrict_faces_iff]
  refine ⟨hs, ?_⟩
  exact (convex_convexHull ℝ (s : Set E)).isPreconnected.subset_connectedComponentIn
    (openSimplex_subset_convexHull s
      (centroid_mem_openSimplex (K.nonempty_of_mem_faces hs)))
    (K.convexHull_subset_space hs)

open Classical in
theorem connectedComponentOfFace_eq_of_mem
    (K : Geometry.SimplicialComplex ℝ E) (c : ConnectedComponents K.space)
    {s : Finset E} (hs : s ∈ K.faces)
    (hsc : s ∈ (connectedComponentComplex K c).faces) :
    connectedComponentOfFace K hs = c := by
  have hpC : (facePoint K hs : E) ∈ (connectedComponentComplex K c).space :=
    (connectedComponentComplex K c).convexHull_subset_space hsc
      (openSimplex_subset_convexHull s
        (centroid_mem_openSimplex (K.nonempty_of_mem_faces hs)))
  rw [connectedComponentComplex_space] at hpC
  obtain ⟨q, hq, hqp⟩ := hpC
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hq
  have hpq : facePoint K hs = q := Subtype.ext hqp.symm
  rw [connectedComponentOfFace, hpq]
  exact hq

open Classical in
theorem connectedComponentOfFace_eq_of_subset
    (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hts : t ⊆ s) :
    connectedComponentOfFace K ht = connectedComponentOfFace K hs := by
  let c := connectedComponentOfFace K hs
  have hsC := mem_connectedComponentComplex_connectedComponentOfFace K hs
  have htC : t ∈ (connectedComponentComplex K c).faces :=
    (connectedComponentComplex K c).down_closed hsC hts (K.nonempty_of_mem_faces ht)
  exact connectedComponentOfFace_eq_of_mem K c ht htC

open Classical in
theorem mem_connectedComponentComplex_faces_iff_connectedComponentOfFace_eq
    (K : Geometry.SimplicialComplex ℝ E) (c : ConnectedComponents K.space)
    {s : Finset E} (hs : s ∈ K.faces) :
    s ∈ (connectedComponentComplex K c).faces ↔ connectedComponentOfFace K hs = c := by
  constructor
  · exact connectedComponentOfFace_eq_of_mem K c hs
  · intro h
    have hm := mem_connectedComponentComplex_connectedComponentOfFace K hs
    simpa only [h] using hm

open Classical in
theorem exists_face_card_three_in_connectedComponent
    [FiniteDimensional ℝ E]
    (B : Geometry.SimplicialComplex ℝ E) [Finite B.faces]
    (hB : IsCombinatorialManifold 2 B) (c : ConnectedComponents B.space) :
    ∃ t : {t : Finset E // t ∈ B.faces ∧ t.card = 3},
      connectedComponentOfFace B t.2.1 = c := by
  let C := connectedComponentComplex B c
  let _ : Finite C.faces := (connectedComponentComplex_faces_finite B c).to_subtype
  have hC : IsCombinatorialManifoldWithBoundary 2 C :=
    hB.isCombinatorialManifoldWithBoundary.connectedComponentComplex c
  obtain ⟨p, hp⟩ := ConnectedComponents.surjective_coe c
  have hpC : (p : E) ∈ C.space := by
    change (p : E) ∈ (connectedComponentComplex B c).space
    rw [connectedComponentComplex_space]
    exact ⟨p, by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hp, rfl⟩
  obtain ⟨s, hsC, -⟩ := C.mem_space_iff.mp hpC
  obtain ⟨t, htC, -, htcard⟩ := hC.exists_face_superset_card_eq hsC
  have htB : t ∈ B.faces := by
    exact htC.1
  exact ⟨⟨t, htB, htcard⟩, connectedComponentOfFace_eq_of_mem B c htB htC⟩

open Classical in
theorem faceEulerChar_eq_sum_connectedComponentComplex
    [FiniteDimensional ℝ E]
    (B : Geometry.SimplicialComplex ℝ E) [Finite B.faces]
    (c₀ : ConnectedComponents B.space) :
    let _ : Fintype (ConnectedComponents B.space) :=
      @Fintype.ofFinite (ConnectedComponents B.space) (finite_connectedComponents_space B)
    SimplicialComplex.faceEulerChar B.toPreAbstractSimplicialComplex =
      ∑ c : ConnectedComponents B.space,
        let _ : Finite (connectedComponentComplex B c).faces :=
          (connectedComponentComplex_faces_finite B c).to_subtype
        SimplicialComplex.faceEulerChar
          (connectedComponentComplex B c).toPreAbstractSimplicialComplex := by
  dsimp
  let _ : Finite (ConnectedComponents B.space) := finite_connectedComponents_space B
  let _ : Fintype (ConnectedComponents B.space) := Fintype.ofFinite _
  let S := (Set.toFinite B.faces).toFinset
  let g : Finset E → ConnectedComponents B.space := fun s =>
    if hs : s ∈ B.faces then connectedComponentOfFace B hs else c₀
  let f : Finset E → ℤ := fun s => -(-1 : ℤ) ^ s.card
  unfold SimplicialComplex.faceEulerChar
  rw [← Finset.sum_fiberwise S g f]
  apply Finset.sum_congr rfl
  intro c _
  let C := connectedComponentComplex B c
  let _ : Finite C.faces := (connectedComponentComplex_faces_finite B c).to_subtype
  apply Finset.sum_congr
  · ext s
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, S]
    constructor
    · rintro ⟨hsB, hg⟩
      have hcomp : connectedComponentOfFace B hsB = c := by
        simpa only [g, dif_pos hsB] using hg
      exact (mem_connectedComponentComplex_faces_iff_connectedComponentOfFace_eq
        B c hsB).mpr hcomp
    · intro hsC
      have hsB : s ∈ B.faces := hsC.1
      refine ⟨hsB, ?_⟩
      have hcomp := connectedComponentOfFace_eq_of_mem B c hsB hsC
      simpa only [g, dif_pos hsB] using hcomp
  · intro s _
    rfl

open Classical in
theorem faceEulerChar_lt_two_mul_card_of_component_not_sphere
    [FiniteDimensional ℝ E]
    (B : Geometry.SimplicialComplex ℝ E) [Finite B.faces]
    (hB : IsCombinatorialManifold 2 B)
    (c₀ : ConnectedComponents B.space)
    (hnot : ¬ IsPLSphere 2 (connectedComponentComplex B c₀).space) :
    SimplicialComplex.faceEulerChar B.toPreAbstractSimplicialComplex <
      (2 : ℤ) * Nat.card (ConnectedComponents B.space) := by
  let _ : Finite (ConnectedComponents B.space) := finite_connectedComponents_space B
  let _ : Fintype (ConnectedComponents B.space) := Fintype.ofFinite _
  rw [faceEulerChar_eq_sum_connectedComponentComplex B c₀]
  calc
    (∑ c : ConnectedComponents B.space,
        let _ : Finite (connectedComponentComplex B c).faces :=
          (connectedComponentComplex_faces_finite B c).to_subtype
        SimplicialComplex.faceEulerChar
          (connectedComponentComplex B c).toPreAbstractSimplicialComplex) <
        ∑ _c : ConnectedComponents B.space, (2 : ℤ) := by
      apply Finset.sum_lt_sum
      · intro c _
        let _ : Finite (connectedComponentComplex B c).faces :=
          (connectedComponentComplex_faces_finite B c).to_subtype
        exact (hB.connectedComponentComplex c).faceEulerChar_le_two
          (connectedComponentComplex B c)
          (isConnected_connectedComponentComplex_space B c)
      · refine ⟨c₀, Finset.mem_univ _, ?_⟩
        let _ : Finite (connectedComponentComplex B c₀).faces :=
          (connectedComponentComplex_faces_finite B c₀).to_subtype
        have hle := (hB.connectedComponentComplex c₀).faceEulerChar_le_two
          (connectedComponentComplex B c₀)
          (isConnected_connectedComponentComplex_space B c₀)
        have hne : SimplicialComplex.faceEulerChar
            (connectedComponentComplex B c₀).toPreAbstractSimplicialComplex ≠ 2 := by
          intro heq
          exact hnot ((hB.connectedComponentComplex c₀).isPLSphere_two_of_faceEulerChar_eq_two
            (connectedComponentComplex B c₀)
            (isConnected_connectedComponentComplex_space B c₀) heq)
        change SimplicialComplex.faceEulerChar
          (connectedComponentComplex B c₀).toPreAbstractSimplicialComplex < 2
        omega
    _ = (2 : ℤ) * Nat.card (ConnectedComponents B.space) := by
      rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
      simp [mul_comm]

theorem orderedNormalizedBoundary_intCast_apply
    (r : LinearOrder E) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (n : ℕ) (c : Finset E → ℤ)
    (t : {t : Finset E // t ∈ K.faces ∧ t.card = n + 1}) :
    let _ := r
    SimplicialComplex.orderedNormalizedBoundary (k := k) K.toPreAbstractSimplicialComplex n
        (fun s => (c s.1 : k)) t =
      (orientedBoundary r K (n + 1) c t.1 : k) := by
  dsimp
  let _ := r
  classical
  let _ : Finite {s : Finset E // s ∈ K.faces ∧ s.card = n + 2} :=
    Finite.of_injective
      (fun s => (⟨s.1, s.2.1⟩ : K.faces))
      (fun _ _ h => Subtype.ext (congrArg (fun x : K.faces => x.1) h))
  let _ : Fintype {s : Finset E // s ∈ K.faces ∧ s.card = n + 2} := Fintype.ofFinite _
  rw [SimplicialComplex.orderedNormalizedBoundary_apply, finsum_eq_sum_of_fintype,
    orientedBoundary]
  push_cast
  let e := SimplicialComplex.faceSubtypeEquivFacesOfCard
    K.toPreAbstractSimplicialComplex (n + 2)
  calc
    (∑ s : {s : Finset E // s ∈ K.faces ∧ s.card = n + 2},
        (c s.1 : k) * (simplexBoundaryCoefficient r s.1 t.1 : k)) =
      ∑ s : {s : Finset E // s ∈ SimplicialComplex.facesOfCard
          K.toPreAbstractSimplicialComplex (n + 2)},
        (c s.1 : k) * (simplexBoundaryCoefficient r s.1 t.1 : k) := by
      exact e.sum_comp
        (fun s : {s : Finset E // s ∈ SimplicialComplex.facesOfCard
          K.toPreAbstractSimplicialComplex (n + 2)} =>
          (c s.1 : k) * (simplexBoundaryCoefficient r s.1 t.1 : k))
    _ = ∑ s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex (n + 2),
        (c s : k) * (simplexBoundaryCoefficient r s t.1 : k) := by
      exact Finset.sum_coe_sort
        (SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex (n + 2))
        (fun s : Finset E => (c s : k) * (simplexBoundaryCoefficient r s t.1 : k))

theorem orderedNormalizedBoundary_apply_eq_sum_faceCofaces
    (r : LinearOrder E) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (n : ℕ) (c : Finset E → k)
    (t : {t : Finset E // t ∈ K.faces ∧ t.card = n + 1}) :
    let _ := r
    SimplicialComplex.orderedNormalizedBoundary (k := k) K.toPreAbstractSimplicialComplex n
        (fun s => c s.1) t =
      ∑ s ∈ faceCofaces K t.1 (n + 2),
        c s * (simplexBoundaryCoefficient r s t.1 : k) := by
  dsimp
  let _ := r
  classical
  let _ : Finite {s : Finset E // s ∈ K.faces ∧ s.card = n + 2} :=
    Finite.of_injective
      (fun s => (⟨s.1, s.2.1⟩ : K.faces))
      (fun _ _ h => Subtype.ext (congrArg (fun x : K.faces => x.1) h))
  let _ : Fintype {s : Finset E // s ∈ K.faces ∧ s.card = n + 2} := Fintype.ofFinite _
  rw [SimplicialComplex.orderedNormalizedBoundary_apply, finsum_eq_sum_of_fintype]
  let e := SimplicialComplex.faceSubtypeEquivFacesOfCard
    K.toPreAbstractSimplicialComplex (n + 2)
  calc
    (∑ s : {s : Finset E // s ∈ K.faces ∧ s.card = n + 2},
        c s.1 * (simplexBoundaryCoefficient r s.1 t.1 : k)) =
      ∑ s : {s : Finset E // s ∈ SimplicialComplex.facesOfCard
          K.toPreAbstractSimplicialComplex (n + 2)},
        c s.1 * (simplexBoundaryCoefficient r s.1 t.1 : k) := by
      exact e.sum_comp
        (fun s : {s : Finset E // s ∈ SimplicialComplex.facesOfCard
          K.toPreAbstractSimplicialComplex (n + 2)} =>
          c s.1 * (simplexBoundaryCoefficient r s.1 t.1 : k))
    _ = ∑ s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex (n + 2),
        c s * (simplexBoundaryCoefficient r s t.1 : k) := by
      exact Finset.sum_coe_sort
        (SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex (n + 2))
        (fun s : Finset E => c s * (simplexBoundaryCoefficient r s t.1 : k))
    _ = ∑ s ∈ faceCofaces K t.1 (n + 2),
        c s * (simplexBoundaryCoefficient r s t.1 : k) := by
      symm
      apply Finset.sum_subset
      · intro s hs
        exact (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mpr
          ⟨((mem_faceCofaces K).mp hs).1, ((mem_faceCofaces K).mp hs).2.1⟩
      · intro s hs hst
        suffices simplexBoundaryCoefficient r s t.1 = 0 by rw [this, Int.cast_zero, mul_zero]
        rw [simplexBoundaryCoefficient]
        apply Finset.sum_eq_zero
        intro v hv
        rw [if_neg]
        intro herase
        apply hst
        apply (mem_faceCofaces K).mpr
        refine ⟨((SimplicialComplex.mem_facesOfCard
          K.toPreAbstractSimplicialComplex).mp hs).1,
          ((SimplicialComplex.mem_facesOfCard
            K.toPreAbstractSimplicialComplex).mp hs).2, ?_⟩
        rw [← herase]
        exact Finset.erase_subset v s

open Classical in
noncomputable def componentOrientationChain
    (B : Geometry.SimplicialComplex ℝ E) [Finite B.faces]
    (o : CoherentOrientation 2 B) (c : ConnectedComponents B.space) : Finset E → ℤ :=
  fun s => if hs : s ∈ B.faces ∧ s.card = 3 then
    if connectedComponentOfFace B hs.1 = c then o.sign s else 0 else 0

open Classical in
noncomputable def boundaryComponentCycle
    (B : Geometry.SimplicialComplex ℝ E) [Finite B.faces]
    (o : CoherentOrientation 2 B) (c : ConnectedComponents B.space) :
    {s : Finset E // s ∈ B.faces ∧ s.card = 3} → ℚ :=
  fun s => (componentOrientationChain B o c s.1 : ℚ)

open Classical in
theorem orientedBoundary_componentOrientationChain
    (B : Geometry.SimplicialComplex ℝ E) [Finite B.faces]
    (o : CoherentOrientation 2 B) (c : ConnectedComponents B.space)
    (t : {t : Finset E // t ∈ B.faces ∧ t.card = 2}) :
    orientedBoundary o.vertexOrder B 2 (componentOrientationChain B o c) t.1 =
      if connectedComponentOfFace B t.2.1 = c then
        orientedBoundary o.vertexOrder B 2 o.sign t.1 else 0 := by
  rw [orientedBoundary_eq_sum_faceCofaces, orientedBoundary_eq_sum_faceCofaces]
  by_cases htc : connectedComponentOfFace B t.2.1 = c
  · rw [if_pos htc]
    apply Finset.sum_congr rfl
    intro s hs
    obtain ⟨hsB, hscard, hts⟩ := (mem_faceCofaces B).mp hs
    have hcomp := connectedComponentOfFace_eq_of_subset B hsB t.2.1 hts
    have hcard : s.card = 3 := by omega
    have hsc : connectedComponentOfFace B hsB = c := hcomp.symm.trans htc
    simp [componentOrientationChain, hsB, hcard, hsc]
  · rw [if_neg htc]
    apply Finset.sum_eq_zero
    intro s hs
    obtain ⟨hsB, hscard, hts⟩ := (mem_faceCofaces B).mp hs
    have hcomp := connectedComponentOfFace_eq_of_subset B hsB t.2.1 hts
    have hcard : s.card = 3 := by omega
    have hsc : connectedComponentOfFace B hsB ≠ c := fun h => htc (hcomp.trans h)
    simp [componentOrientationChain, hsB, hcard, hsc]

open Classical in
theorem orderedNormalizedBoundary_boundaryComponentCycle
    [FiniteDimensional ℝ E]
    (B : Geometry.SimplicialComplex ℝ E) [Finite B.faces]
    (hB : IsCombinatorialManifold 2 B) (o : CoherentOrientation 2 B)
    (c : ConnectedComponents B.space) :
    let _ := o.vertexOrder
    SimplicialComplex.orderedNormalizedBoundary (k := ℚ) B.toPreAbstractSimplicialComplex 1
      (boundaryComponentCycle B o c) = 0 := by
  dsimp
  let _ := o.vertexOrder
  ext t
  rw [show boundaryComponentCycle B o c =
      fun s => (componentOrientationChain B o c s.1 : ℚ) from rfl]
  change SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
    B.toPreAbstractSimplicialComplex 1
      (fun s => (componentOrientationChain B o c s.1 : ℚ)) t = 0
  rw [orderedNormalizedBoundary_intCast_apply o.vertexOrder B 1
    (componentOrientationChain B o c) t]
  rw [orientedBoundary_componentOrientationChain B o c t]
  have hzero := o.coherent t.1 t.2.1 t.2.2 (by
    rw [hB.card_faceCofaces_eq_two B t.2.1 t.2.2]
    omega)
  by_cases htc : connectedComponentOfFace B t.2.1 = c
  · rw [if_pos htc, hzero]
    norm_num
  · rw [if_neg htc]
    norm_num

abbrev OtherBoundaryComponent
    (B : Geometry.SimplicialComplex ℝ E) (c₀ : ConnectedComponents B.space) :=
  {c : ConnectedComponents B.space // c ≠ c₀}

open Classical in
noncomputable def boundaryComponentCombinationCoeff
    (B : Geometry.SimplicialComplex ℝ E) [Finite B.faces]
    (o : CoherentOrientation 2 B) (c₀ : ConnectedComponents B.space)
    (a : OtherBoundaryComponent B c₀ → ℚ) : Finset E → ℚ :=
  fun s => if hs : s ∈ B.faces ∧ s.card = 3 then
    if hc : connectedComponentOfFace B hs.1 ≠ c₀ then
      a ⟨connectedComponentOfFace B hs.1, hc⟩ * (o.sign s : ℚ)
    else 0 else 0

open Classical in
noncomputable def boundaryComponentCombination
    (B : Geometry.SimplicialComplex ℝ E) [Finite B.faces]
    (o : CoherentOrientation 2 B) (c₀ : ConnectedComponents B.space) :
    (OtherBoundaryComponent B c₀ → ℚ) →ₗ[ℚ]
      ({s : Finset E // s ∈ B.faces ∧ s.card = 3} → ℚ) where
  toFun a s := boundaryComponentCombinationCoeff B o c₀ a s.1
  map_add' a b := by
    ext s
    change boundaryComponentCombinationCoeff B o c₀ (a + b) s.1 =
      boundaryComponentCombinationCoeff B o c₀ a s.1 +
        boundaryComponentCombinationCoeff B o c₀ b s.1
    by_cases hc : connectedComponentOfFace B s.2.1 = c₀
    · simp [boundaryComponentCombinationCoeff, s.2.1, s.2.2, hc]
    · simp [boundaryComponentCombinationCoeff, s.2.1, s.2.2, hc, add_mul]
  map_smul' q a := by
    ext s
    change boundaryComponentCombinationCoeff B o c₀ (q • a) s.1 =
      q • boundaryComponentCombinationCoeff B o c₀ a s.1
    by_cases hc : connectedComponentOfFace B s.2.1 = c₀
    · simp [boundaryComponentCombinationCoeff, s.2.1, s.2.2, hc]
    · simp [boundaryComponentCombinationCoeff, s.2.1, s.2.2, hc, mul_assoc]

open Classical in
theorem orderedNormalizedBoundary_boundaryComponentCombination
    [FiniteDimensional ℝ E]
    (B : Geometry.SimplicialComplex ℝ E) [Finite B.faces]
    (hB : IsCombinatorialManifold 2 B) (o : CoherentOrientation 2 B)
    (c₀ : ConnectedComponents B.space) (a : OtherBoundaryComponent B c₀ → ℚ) :
    let _ := o.vertexOrder
    SimplicialComplex.orderedNormalizedBoundary (k := ℚ) B.toPreAbstractSimplicialComplex 1
      (boundaryComponentCombination B o c₀ a) = 0 := by
  dsimp
  let _ := o.vertexOrder
  ext t
  change SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
    B.toPreAbstractSimplicialComplex 1
      (fun s => boundaryComponentCombinationCoeff B o c₀ a s.1) t = 0
  rw [orderedNormalizedBoundary_apply_eq_sum_faceCofaces o.vertexOrder B 1
    (boundaryComponentCombinationCoeff B o c₀ a) t]
  let d := connectedComponentOfFace B t.2.1
  by_cases hd : d = c₀
  · apply Finset.sum_eq_zero
    intro s hs
    obtain ⟨hsB, hscard, hts⟩ := (mem_faceCofaces B).mp hs
    have hcard : s.card = 3 := by omega
    have hcomp := connectedComponentOfFace_eq_of_subset B hsB t.2.1 hts
    have hsbase : connectedComponentOfFace B hsB = c₀ := hcomp.symm.trans hd
    simp [boundaryComponentCombinationCoeff, hsB, hcard, hsbase]
  · let d' : OtherBoundaryComponent B c₀ := ⟨d, hd⟩
    have hzero := o.coherent t.1 t.2.1 t.2.2 (by
      rw [hB.card_faceCofaces_eq_two B t.2.1 t.2.2]
      omega)
    calc
      (∑ s ∈ faceCofaces B t.1 (1 + 2),
          boundaryComponentCombinationCoeff B o c₀ a s *
            (simplexBoundaryCoefficient o.vertexOrder s t.1 : ℚ)) =
        ∑ s ∈ faceCofaces B t.1 3,
          a d' * ((o.sign s : ℚ) *
            (simplexBoundaryCoefficient o.vertexOrder s t.1 : ℚ)) := by
          apply Finset.sum_congr rfl
          intro s hs
          obtain ⟨hsB, hscard, hts⟩ := (mem_faceCofaces B).mp hs
          have hcard : s.card = 3 := by omega
          have hcomp := connectedComponentOfFace_eq_of_subset B hsB t.2.1 hts
          have hsc : connectedComponentOfFace B hsB = d := hcomp.symm
          have hsnot : connectedComponentOfFace B hsB ≠ c₀ := hsc.trans_ne hd
          have hsub : (⟨connectedComponentOfFace B hsB, hsnot⟩ :
              OtherBoundaryComponent B c₀) = d' := Subtype.ext hsc
          simp [boundaryComponentCombinationCoeff, hsB, hcard, hsnot, hsub]
          ring
      _ = a d' * ∑ s ∈ faceCofaces B t.1 3,
          (o.sign s : ℚ) *
            (simplexBoundaryCoefficient o.vertexOrder s t.1 : ℚ) := by
          rw [Finset.mul_sum]
      _ = a d' * (orientedBoundary o.vertexOrder B 2 o.sign t.1 : ℚ) := by
          rw [orientedBoundary_eq_sum_faceCofaces]
          push_cast
          rfl
      _ = 0 := by rw [hzero, Int.cast_zero, mul_zero]

open Classical in
noncomputable def boundaryComponentCombinationIn
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space) :
    (OtherBoundaryComponent (boundaryComplex 3 K) c₀ → ℚ) →ₗ[ℚ]
      ({s : Finset E // s ∈ K.faces ∧ s.card = 3} → ℚ) where
  toFun a s := boundaryComponentCombinationCoeff (boundaryComplex 3 K)
    (o.boundary K hK) c₀ a s.1
  map_add' a b := by
    ext s
    change boundaryComponentCombinationCoeff (boundaryComplex 3 K)
        (o.boundary K hK) c₀ (a + b) s.1 =
      boundaryComponentCombinationCoeff (boundaryComplex 3 K)
          (o.boundary K hK) c₀ a s.1 +
        boundaryComponentCombinationCoeff (boundaryComplex 3 K)
          (o.boundary K hK) c₀ b s.1
    by_cases hs : s.1 ∈ (boundaryComplex 3 K).faces
    · have hscard : s.1.card = 3 := s.2.2
      by_cases hc : connectedComponentOfFace (boundaryComplex 3 K) hs = c₀
      · simp [boundaryComponentCombinationCoeff, hs, hscard, hc]
      · simp [boundaryComponentCombinationCoeff, hs, hscard, hc, add_mul]
    · simp [boundaryComponentCombinationCoeff, hs]
  map_smul' q a := by
    ext s
    change boundaryComponentCombinationCoeff (boundaryComplex 3 K)
        (o.boundary K hK) c₀ (q • a) s.1 =
      q • boundaryComponentCombinationCoeff (boundaryComplex 3 K)
        (o.boundary K hK) c₀ a s.1
    by_cases hs : s.1 ∈ (boundaryComplex 3 K).faces
    · have hscard : s.1.card = 3 := s.2.2
      by_cases hc : connectedComponentOfFace (boundaryComplex 3 K) hs = c₀
      · simp [boundaryComponentCombinationCoeff, hs, hscard, hc]
      · simp [boundaryComponentCombinationCoeff, hs, hscard, hc, mul_assoc]
    · simp [boundaryComponentCombinationCoeff, hs]

open Classical in
theorem orderedNormalizedBoundary_boundaryComponentCombinationIn
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space)
    (a : OtherBoundaryComponent (boundaryComplex 3 K) c₀ → ℚ) :
    let _ := o.vertexOrder
    SimplicialComplex.orderedNormalizedBoundary (k := ℚ) K.toPreAbstractSimplicialComplex 1
      (boundaryComponentCombinationIn K hK o c₀ a) = 0 := by
  dsimp
  let B : Geometry.SimplicialComplex ℝ E := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  let oB : CoherentOrientation 2 B := o.boundary K hK
  have hB : IsCombinatorialManifold 2 B := isCombinatorialManifold_boundaryComplex K hK
  have hBK : B.faces ⊆ K.faces := by
    simpa only [B] using boundaryComplex_faces_subset 3 K
  let _ := o.vertexOrder
  ext t
  change SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
    K.toPreAbstractSimplicialComplex 1
      (fun s => boundaryComponentCombinationCoeff B oB c₀ a s.1) t = 0
  rw [orderedNormalizedBoundary_apply_eq_sum_faceCofaces o.vertexOrder K 1
    (boundaryComponentCombinationCoeff B oB c₀ a) t]
  by_cases htB : t.1 ∈ B.faces
  · let tB : {t : Finset E // t ∈ B.faces ∧ t.card = 2} := ⟨t.1, htB, t.2.2⟩
    have hcycle := congrFun
      (orderedNormalizedBoundary_boundaryComponentCombination B hB oB c₀ a) tB
    change SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
      B.toPreAbstractSimplicialComplex 1
        (fun s => boundaryComponentCombinationCoeff B oB c₀ a s.1) tB = 0 at hcycle
    rw [orderedNormalizedBoundary_apply_eq_sum_faceCofaces o.vertexOrder B 1
      (boundaryComponentCombinationCoeff B oB c₀ a) tB] at hcycle
    rw [← hcycle]
    symm
    apply Finset.sum_subset
    · intro s hs
      obtain ⟨hsB, hscard, hts⟩ := (mem_faceCofaces B).mp hs
      exact (mem_faceCofaces K).mpr
        ⟨hBK hsB, hscard, hts⟩
    · intro s hsK hsB
      obtain ⟨hsKface, hscard, hts⟩ := (mem_faceCofaces K).mp hsK
      have hsnot : s ∉ B.faces := by
        intro hs
        apply hsB
        exact (mem_faceCofaces B).mpr ⟨hs, hscard, hts⟩
      simp [boundaryComponentCombinationCoeff, hsnot]
  · apply Finset.sum_eq_zero
    intro s hs
    obtain ⟨hsK, hscard, hts⟩ := (mem_faceCofaces K).mp hs
    have hsnot : s ∉ B.faces := by
      intro hsB
      apply htB
      exact B.down_closed hsB hts (K.nonempty_of_mem_faces t.2.1)
    simp [boundaryComponentCombinationCoeff, hsnot]

open Classical in
noncomputable def orientedTopChainCoeff
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (o : CoherentOrientation 3 K)
    (x : {s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ) : Finset E → ℚ :=
  fun s => if hs : s ∈ K.faces ∧ s.card = 4 then
    x ⟨s, hs⟩ * (o.sign s : ℚ) else 0

open Classical in
noncomputable def orientedTopChain
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (o : CoherentOrientation 3 K) :
    ({s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ) →ₗ[ℚ]
      ({s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ) where
  toFun x s := orientedTopChainCoeff K o x s.1
  map_add' x y := by
    ext s
    simp [orientedTopChainCoeff, s.2.1, s.2.2, add_mul]
  map_smul' q x := by
    ext s
    simp [orientedTopChainCoeff, s.2.1, s.2.2, mul_assoc]

theorem orderedNormalizedBoundary_orientedTopChain_apply_of_faceCofaces_eq_singleton
    (r : LinearOrder E) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (o : CoherentOrientation 3 K)
    (x : {s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ)
    (t : {t : Finset E // t ∈ K.faces ∧ t.card = 3})
    (s : {s : Finset E // s ∈ K.faces ∧ s.card = 4}) :
    let _ := r
    faceCofaces K t.1 4 = {s.1} →
    SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
        K.toPreAbstractSimplicialComplex 2 (orientedTopChain K o x) t =
      x s * (o.sign s.1 : ℚ) *
        (simplexBoundaryCoefficient r s.1 t.1 : ℚ) := by
  dsimp
  let _ := r
  intro hcofaces
  change SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
      K.toPreAbstractSimplicialComplex 2
        (fun s => orientedTopChainCoeff K o x s.1) t = _
  rw [orderedNormalizedBoundary_apply_eq_sum_faceCofaces r K 2
    (orientedTopChainCoeff K o x) t, hcofaces]
  simp [orientedTopChainCoeff, s.2.1, s.2.2]

theorem orderedNormalizedBoundary_orientedTopChain_apply_of_faceCofaces_eq_pair
    (r : LinearOrder E) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (o : CoherentOrientation 3 K)
    (x : {s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ)
    (f : {f : Finset E // f ∈ K.faces ∧ f.card = 3})
    (s t : {s : Finset E // s ∈ K.faces ∧ s.card = 4}) (hst : s.1 ≠ t.1) :
    let _ := r
    faceCofaces K f.1 4 = {s.1, t.1} →
    SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
        K.toPreAbstractSimplicialComplex 2 (orientedTopChain K o x) f =
      x s * (o.sign s.1 : ℚ) *
          (simplexBoundaryCoefficient r s.1 f.1 : ℚ) +
        x t * (o.sign t.1 : ℚ) *
          (simplexBoundaryCoefficient r t.1 f.1 : ℚ) := by
  dsimp
  let _ := r
  intro hcofaces
  change SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
      K.toPreAbstractSimplicialComplex 2
        (fun s => orientedTopChainCoeff K o x s.1) f = _
  rw [orderedNormalizedBoundary_apply_eq_sum_faceCofaces r K 2
    (orientedTopChainCoeff K o x) f, hcofaces]
  simp [orientedTopChainCoeff, s.2.1, s.2.2, t.2.1, t.2.2, hst]

open Classical in
theorem orientedTopChain_coeff_eq_of_boundary_apply_eq_zero
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (o : CoherentOrientation 3 K)
    (x : {s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ)
    (f : {f : Finset E // f ∈ K.faces ∧ f.card = 3})
    (s t : {s : Finset E // s ∈ K.faces ∧ s.card = 4}) (hst : s.1 ≠ t.1)
    (hcofaces : faceCofaces K f.1 4 = {s.1, t.1})
    (hzero : let _ := o.vertexOrder
      SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
          K.toPreAbstractSimplicialComplex 2 (orientedTopChain K o x) f = 0) :
    x s = x t := by
  have hsco : s.1 ∈ faceCofaces K f.1 4 := by
    rw [hcofaces]
    exact Finset.mem_insert_self _ _
  have htco : t.1 ∈ faceCofaces K f.1 4 := by
    rw [hcofaces]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨-, -, hfs⟩ := (mem_faceCofaces K).mp hsco
  obtain ⟨-, -, hft⟩ := (mem_faceCofaces K).mp htco
  have hcancel := o.pair_cancel_of_faceCofaces_eq f.2.1 f.2.2 hst hcofaces
  let _ := o.vertexOrder
  have hsco' : s.1 ∈ faceCofaces K f.1 4 :=
    (mem_faceCofaces K).mpr ⟨s.2.1, s.2.2, hfs⟩
  have htco' : t.1 ∈ faceCofaces K f.1 4 :=
    (mem_faceCofaces K).mpr ⟨t.2.1, t.2.2, hft⟩
  have hsub : ({s.1, t.1} : Finset (Finset E)) ⊆ faceCofaces K f.1 4 := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hsco', htco'⟩
  have htwo : (faceCofaces K f.1 4).card = 2 :=
    (hK.card_faceCofaces_eq_one_or_two K f.2.1 f.2.2).resolve_left (by
      have hge := Finset.card_le_card hsub
      rw [Finset.card_pair hst] at hge
      intro hone
      rw [hone] at hge
      omega)
  have hcofaces' : faceCofaces K f.1 4 = {s.1, t.1} := by
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [htwo, Finset.card_pair hst]
  have hvalue := orderedNormalizedBoundary_orientedTopChain_apply_of_faceCofaces_eq_pair
    o.vertexOrder K o x f s t hst hcofaces'
  dsimp at hzero hvalue
  have hcancelQ :
      (o.sign s.1 : ℚ) * (simplexBoundaryCoefficient o.vertexOrder s.1 f.1 : ℚ) +
        (o.sign t.1 : ℚ) * (simplexBoundaryCoefficient o.vertexOrder t.1 f.1 : ℚ) = 0 := by
    exact_mod_cast hcancel
  rw [hvalue] at hzero
  let A : ℚ := (o.sign s.1 : ℚ) *
    (simplexBoundaryCoefficient o.vertexOrder s.1 f.1 : ℚ)
  let B : ℚ := (o.sign t.1 : ℚ) *
    (simplexBoundaryCoefficient o.vertexOrder t.1 f.1 : ℚ)
  have hAne : A ≠ 0 := by
    apply mul_ne_zero
    · rcases o.sign_top s.1 s.2.1 s.2.2 with h | h <;> simp [h]
    · rcases simplexBoundaryCoefficient_eq_one_or_neg_one o.vertexOrder hfs
        (by omega) with h | h <;> simp [h]
  have hAB : A + B = 0 := by simpa only [A, B] using hcancelQ
  have hB : B = -A := by linarith only [hAB]
  have hprod : (x s - x t) * A = 0 := by
    calc
      (x s - x t) * A = x s * A + x t * B := by rw [hB]; ring
      _ = 0 := by simpa only [A, B, mul_assoc] using hzero
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hAne)

open Classical in
noncomputable def topBoundaryAndBoundaryComponents
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space) :
    (({s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ) ×
      (OtherBoundaryComponent (boundaryComplex 3 K) c₀ → ℚ)) →ₗ[ℚ]
        ({s : Finset E // s ∈ K.faces ∧ s.card = 3} → ℚ) := by
  let _ := o.vertexOrder
  exact {
    toFun := fun z =>
      SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
          K.toPreAbstractSimplicialComplex 2 (orientedTopChain K o z.1) +
        boundaryComponentCombinationIn K hK o c₀ z.2
    map_add' := by
      intro x y
      simp only [Prod.fst_add, Prod.snd_add, map_add]
      abel
    map_smul' := by
      intro q x
      simp }

open Classical in
theorem orderedNormalizedBoundary_topBoundaryAndBoundaryComponents
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space)
    (z : ({s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ) ×
      (OtherBoundaryComponent (boundaryComplex 3 K) c₀ → ℚ)) :
    let _ := o.vertexOrder
    SimplicialComplex.orderedNormalizedBoundary (k := ℚ) K.toPreAbstractSimplicialComplex 1
      (topBoundaryAndBoundaryComponents K hK o c₀ z) = 0 := by
  dsimp
  let _ := o.vertexOrder
  rw [show topBoundaryAndBoundaryComponents K hK o c₀ z =
    SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
        K.toPreAbstractSimplicialComplex 2 (orientedTopChain K o z.1) +
      boundaryComponentCombinationIn K hK o c₀ z.2 from rfl]
  rw [map_add, SimplicialComplex.orderedNormalizedBoundary_boundary,
    orderedNormalizedBoundary_boundaryComponentCombinationIn, zero_add]

open Classical in
theorem topBoundaryAndBoundaryComponents_fst_eq_of_dualGraph_adj
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space)
    (z : ({s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ) ×
      (OtherBoundaryComponent (boundaryComplex 3 K) c₀ → ℚ))
    (hz : topBoundaryAndBoundaryComponents K hK o c₀ z = 0)
    {s t : {s : Finset E // s ∈ K.faces ∧ s.card = 4}}
    (hadj : (dualGraph 3 K).Adj s t) :
    z.1 s = z.1 t := by
  obtain ⟨hne, f, hf, hfcard, hfs, hft⟩ := hadj
  have hst : s.1 ≠ t.1 := fun h => hne (Subtype.ext h)
  have hsco : s.1 ∈ faceCofaces K f 4 :=
    (mem_faceCofaces K).mpr ⟨s.2.1, s.2.2, hfs⟩
  have htco : t.1 ∈ faceCofaces K f 4 :=
    (mem_faceCofaces K).mpr ⟨t.2.1, t.2.2, hft⟩
  have hsub : ({s.1, t.1} : Finset (Finset E)) ⊆ faceCofaces K f 4 := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hsco, htco⟩
  have htwo : (faceCofaces K f 4).card = 2 :=
    (hK.card_faceCofaces_eq_one_or_two K hf hfcard).resolve_left (by
      have hge := Finset.card_le_card hsub
      rw [Finset.card_pair hst] at hge
      intro hone
      rw [hone] at hge
      omega)
  have hpair : faceCofaces K f 4 = {s.1, t.1} := by
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [htwo, Finset.card_pair hst]
  have hfnot : f ∉ (boundaryComplex 3 K).faces := by
    intro hfB
    have hone := (hK.mem_boundaryComplex_iff_card_cofaces_eq_one K hf hfcard).mp hfB
    rw [hpair, Finset.card_pair hst] at hone
    omega
  let f' : {f : Finset E // f ∈ K.faces ∧ f.card = 3} := ⟨f, hf, hfcard⟩
  have hD : let _ := o.vertexOrder
      SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
        K.toPreAbstractSimplicialComplex 2 (orientedTopChain K o z.1) f' = 0 := by
    dsimp
    let B : Geometry.SimplicialComplex ℝ E := boundaryComplex 3 K
    let oB : CoherentOrientation 2 B := o.boundary K hK
    let _ := o.vertexOrder
    have hb : boundaryComponentCombinationIn K hK o c₀ z.2 f' = 0 := by
      change boundaryComponentCombinationCoeff B oB c₀ z.2 f = 0
      simp [boundaryComponentCombinationCoeff, B, hfnot]
    have hzval := congrFun hz f'
    rw [show topBoundaryAndBoundaryComponents K hK o c₀ z =
      SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
          K.toPreAbstractSimplicialComplex 2 (orientedTopChain K o z.1) +
        boundaryComponentCombinationIn K hK o c₀ z.2 from rfl] at hzval
    simpa only [Pi.add_apply, hb, add_zero, Pi.zero_apply] using hzval
  exact orientedTopChain_coeff_eq_of_boundary_apply_eq_zero
    K hK o z.1 f' s t hst hpair hD

open Classical in
theorem topBoundaryAndBoundaryComponents_fst_eq_of_dualGraph_reachable
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space)
    (z : ({s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ) ×
      (OtherBoundaryComponent (boundaryComplex 3 K) c₀ → ℚ))
    (hz : topBoundaryAndBoundaryComponents K hK o c₀ z = 0)
    {s t : {s : Finset E // s ∈ K.faces ∧ s.card = 4}}
    (hreach : (dualGraph 3 K).Reachable s t) :
    z.1 s = z.1 t := by
  obtain ⟨w⟩ := hreach
  induction w with
  | nil => rfl
  | cons h _ ih =>
      exact (topBoundaryAndBoundaryComponents_fst_eq_of_dualGraph_adj
        K hK o c₀ z hz h).trans ih

open Classical in
theorem topBoundaryAndBoundaryComponents_fst_eq_zero_of_base_boundary_face
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space)
    (z : ({s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ) ×
      (OtherBoundaryComponent (boundaryComplex 3 K) c₀ → ℚ))
    (hz : topBoundaryAndBoundaryComponents K hK o c₀ z = 0)
    (t : {t : Finset E // t ∈ K.faces ∧ t.card = 3})
    (htB : t.1 ∈ (boundaryComplex 3 K).faces)
    (hcomp : connectedComponentOfFace (boundaryComplex 3 K) htB = c₀)
    (s : {s : Finset E // s ∈ K.faces ∧ s.card = 4})
    (hcofaces : faceCofaces K t.1 4 = {s.1}) :
    z.1 s = 0 := by
  have hsco : s.1 ∈ faceCofaces K t.1 4 := by
    rw [hcofaces]
    exact Finset.mem_singleton_self _
  obtain ⟨-, -, hts⟩ := (mem_faceCofaces K).mp hsco
  let B : Geometry.SimplicialComplex ℝ E := boundaryComplex 3 K
  let oB : CoherentOrientation 2 B := o.boundary K hK
  let F : Finset (Finset E) := faceCofaces K t.1 4
  let S : Finset (Finset E) := {s.1}
  have hFS : F = S := hcofaces
  let _ := o.vertexOrder
  have hcurF : faceCofaces K t.1 4 = F := by
    apply Finset.ext
    intro u
    simp only [mem_faceCofaces, F]
  have hScur : S = ({s.1} : Finset (Finset E)) := by
    apply Finset.ext
    intro u
    simp only [S, Finset.mem_singleton]
  have hcofaces' : faceCofaces K t.1 4 = {s.1} := hcurF.trans (hFS.trans hScur)
  have hb : boundaryComponentCombinationIn K hK o c₀ z.2 t = 0 := by
    change boundaryComponentCombinationCoeff B oB c₀ z.2 t.1 = 0
    simp [boundaryComponentCombinationCoeff, B, htB, t.2.2, hcomp]
  have hD : SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
      K.toPreAbstractSimplicialComplex 2 (orientedTopChain K o z.1) t = 0 := by
    have hzval := congrFun hz t
    rw [show topBoundaryAndBoundaryComponents K hK o c₀ z =
      SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
          K.toPreAbstractSimplicialComplex 2 (orientedTopChain K o z.1) +
        boundaryComponentCombinationIn K hK o c₀ z.2 from rfl] at hzval
    simpa only [Pi.add_apply, hb, add_zero, Pi.zero_apply] using hzval
  have hvalue := orderedNormalizedBoundary_orientedTopChain_apply_of_faceCofaces_eq_singleton
    o.vertexOrder K o z.1 t s hcofaces'
  dsimp at hvalue
  rw [hvalue] at hD
  have hsign : (o.sign s.1 : ℚ) ≠ 0 := by
    rcases o.sign_top s.1 s.2.1 s.2.2 with h | h <;> simp [h]
  have hcoefficient : (simplexBoundaryCoefficient o.vertexOrder s.1 t.1 : ℚ) ≠ 0 := by
    rcases simplexBoundaryCoefficient_eq_one_or_neg_one o.vertexOrder hts
      (by omega) with h | h <;> simp [h]
  have hprod : z.1 s * ((o.sign s.1 : ℚ) *
      (simplexBoundaryCoefficient o.vertexOrder s.1 t.1 : ℚ)) = 0 := by
    simpa only [mul_assoc] using hD
  exact (mul_eq_zero.mp hprod).resolve_right (mul_ne_zero hsign hcoefficient)

open Classical in
theorem topBoundaryAndBoundaryComponents_fst_eq_zero
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hconn : IsConnected K.space)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space)
    (z : ({s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ) ×
      (OtherBoundaryComponent (boundaryComplex 3 K) c₀ → ℚ))
    (hz : topBoundaryAndBoundaryComponents K hK o c₀ z = 0) :
    z.1 = 0 := by
  let B : Geometry.SimplicialComplex ℝ E := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hB : IsCombinatorialManifold 2 B := isCombinatorialManifold_boundaryComplex K hK
  obtain ⟨tB, htcomp⟩ := exists_face_card_three_in_connectedComponent B hB c₀
  let t : {t : Finset E // t ∈ K.faces ∧ t.card = 3} :=
    ⟨tB.1, boundaryComplex_faces_subset 3 K tB.2.1, tB.2.2⟩
  have hone := (hK.mem_boundaryComplex_iff_card_cofaces_eq_one K t.2.1 t.2.2).mp tB.2.1
  obtain ⟨s, hcofaces⟩ := Finset.card_eq_one.mp hone
  have hsco : s ∈ faceCofaces K t.1 4 := by
    rw [hcofaces]
    exact Finset.mem_singleton_self _
  obtain ⟨hsK, hscard, -⟩ := (mem_faceCofaces K).mp hsco
  let s₀ : {s : Finset E // s ∈ K.faces ∧ s.card = 4} := ⟨s, hsK, hscard⟩
  have hs₀zero : z.1 s₀ = 0 :=
    topBoundaryAndBoundaryComponents_fst_eq_zero_of_base_boundary_face
      K hK o c₀ z hz t tB.2.1 htcomp s₀ hcofaces
  funext q
  have hreach : (dualGraph 3 K).Reachable s₀ q :=
    hK.dualGraph_preconnected hconn.isPreconnected s₀ q
  have heq := topBoundaryAndBoundaryComponents_fst_eq_of_dualGraph_reachable
    K hK o c₀ z hz hreach
  exact heq.symm.trans hs₀zero

open Classical in
theorem topBoundaryAndBoundaryComponents_snd_apply_eq_zero_of_fst_eq_zero
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space)
    (z : ({s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ) ×
      (OtherBoundaryComponent (boundaryComplex 3 K) c₀ → ℚ))
    (hz : topBoundaryAndBoundaryComponents K hK o c₀ z = 0)
    (hfst : z.1 = 0) (c : OtherBoundaryComponent (boundaryComplex 3 K) c₀) :
    z.2 c = 0 := by
  let B : Geometry.SimplicialComplex ℝ E := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  let oB : CoherentOrientation 2 B := o.boundary K hK
  have hB : IsCombinatorialManifold 2 B := isCombinatorialManifold_boundaryComplex K hK
  obtain ⟨tB, htcomp⟩ := exists_face_card_three_in_connectedComponent B hB c.1
  let t : {t : Finset E // t ∈ K.faces ∧ t.card = 3} :=
    ⟨tB.1, boundaryComplex_faces_subset 3 K tB.2.1, tB.2.2⟩
  have htop : let _ := o.vertexOrder
      SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
        K.toPreAbstractSimplicialComplex 2 (orientedTopChain K o z.1) t = 0 := by
    dsimp
    let _ := o.vertexOrder
    rw [hfst, map_zero, map_zero]
    rfl
  have hbc : boundaryComponentCombinationIn K hK o c₀ z.2 t = 0 := by
    let _ := o.vertexOrder
    have hzval := congrFun hz t
    rw [show topBoundaryAndBoundaryComponents K hK o c₀ z =
      SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
          K.toPreAbstractSimplicialComplex 2 (orientedTopChain K o z.1) +
        boundaryComponentCombinationIn K hK o c₀ z.2 from rfl] at hzval
    dsimp at htop
    simpa only [Pi.add_apply, htop, zero_add, Pi.zero_apply] using hzval
  have hcnot : connectedComponentOfFace B tB.2.1 ≠ c₀ := htcomp.trans_ne c.2
  have hcsub : (⟨connectedComponentOfFace B tB.2.1, hcnot⟩ :
      OtherBoundaryComponent B c₀) = c := Subtype.ext htcomp
  change boundaryComponentCombinationCoeff B oB c₀ z.2 tB.1 = 0 at hbc
  simp only [boundaryComponentCombinationCoeff, tB.2.1, tB.2.2, and_self,
    dite_true, hcsub] at hbc
  by_cases hc : connectedComponentOfFace B tB.2.1 ≠ c₀
  · rw [dif_pos hc] at hbc
    have hsign : (oB.sign tB.1 : ℚ) ≠ 0 := by
      rcases oB.sign_top tB.1 tB.2.1 tB.2.2 with h | h <;> simp [h]
    exact (mul_eq_zero.mp hbc).resolve_right hsign
  · exact (hc hcnot).elim

open Classical in
theorem topBoundaryAndBoundaryComponents_eq_zero
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hconn : IsConnected K.space)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space)
    (z : ({s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ) ×
      (OtherBoundaryComponent (boundaryComplex 3 K) c₀ → ℚ))
    (hz : topBoundaryAndBoundaryComponents K hK o c₀ z = 0) :
    z = 0 := by
  have hfst := topBoundaryAndBoundaryComponents_fst_eq_zero K hK hconn o c₀ z hz
  apply Prod.ext hfst
  funext c
  exact topBoundaryAndBoundaryComponents_snd_apply_eq_zero_of_fst_eq_zero
    K hK o c₀ z hz hfst c

open Classical in
theorem topBoundaryAndBoundaryComponents_injective
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hconn : IsConnected K.space)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space) :
    Function.Injective (topBoundaryAndBoundaryComponents K hK o c₀) := by
  intro z w hzw
  apply sub_eq_zero.mp
  apply topBoundaryAndBoundaryComponents_eq_zero K hK hconn o c₀
  rw [map_sub, hzw, sub_self]

open Classical in
noncomputable def topBoundaryAndBoundaryComponentsToCycles
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space) :
    let B := boundaryComplex 3 K
    let _ := o.vertexOrder
    (({s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ) ×
      (OtherBoundaryComponent B c₀ → ℚ)) →ₗ[ℚ]
      LinearMap.ker
        (((SimplicialComplex.orderedSimplicialSet K.toPreAbstractSimplicialComplex).normalizedChainComplex
          (ModuleCat.of ℚ ℚ)).d 2 1).hom := by
  dsimp
  let _ := o.vertexOrder
  let X := SimplicialComplex.orderedSimplicialSet K.toPreAbstractSimplicialComplex
  let C := X.normalizedChainComplex (ModuleCat.of ℚ ℚ)
  let e₁ := SimplicialComplex.orderedNormalizedChainEquiv (k := ℚ)
    K.toPreAbstractSimplicialComplex 1
  let e₂ := SimplicialComplex.orderedNormalizedChainEquiv (k := ℚ)
    K.toPreAbstractSimplicialComplex 2
  let L := topBoundaryAndBoundaryComponents K hK o c₀
  exact {
    toFun := fun z => ⟨e₂.symm (L z), by
      have hcoord := orderedNormalizedBoundary_topBoundaryAndBoundaryComponents
        K hK o c₀ z
      dsimp at hcoord
      have heq : e₁ (C.d 2 1 (e₂.symm (L z))) = 0 := by
        simpa [SimplicialComplex.orderedNormalizedBoundary, X, C, e₁, e₂, L] using hcoord
      exact e₁.injective (by simpa using heq)⟩
    map_add' := by
      intro z w
      apply Subtype.ext
      simp [e₂, L]
    map_smul' := by
      intro q z
      apply Subtype.ext
      simp [e₂, L] }

open Classical in
theorem topBoundaryAndBoundaryComponentsToCycles_injective
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hconn : IsConnected K.space)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space) :
    let _ := o.vertexOrder
    Function.Injective (topBoundaryAndBoundaryComponentsToCycles K hK o c₀) := by
  dsimp
  let _ := o.vertexOrder
  let e₂ := SimplicialComplex.orderedNormalizedChainEquiv (k := ℚ)
    K.toPreAbstractSimplicialComplex 2
  intro z w hzw
  apply topBoundaryAndBoundaryComponents_injective K hK hconn o c₀
  apply e₂.symm.injective
  exact congrArg Subtype.val hzw

open Classical in
theorem card_otherBoundaryComponent_le_bettiNumber_two
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hconn : IsConnected K.space)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space) :
    Nat.card (OtherBoundaryComponent (boundaryComplex 3 K) c₀) ≤
      Homology.bettiNumber ℚ (TopCat.of K.space) 2 := by
  let B : Geometry.SimplicialComplex ℝ E := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  let _ : Finite (ConnectedComponents B.space) := finite_connectedComponents_space B
  let _ : Fintype (ConnectedComponents B.space) := Fintype.ofFinite _
  let _ : Fintype (OtherBoundaryComponent B c₀) := Fintype.ofFinite _
  let Top := {s : Finset E // s ∈ K.faces ∧ s.card = 4}
  let _ : Finite Top := Finite.of_injective
    (fun s => (⟨s.1, s.2.1⟩ : K.faces))
    (fun _ _ h => Subtype.ext (congrArg (fun x : K.faces => x.1) h))
  let _ : Fintype Top := Fintype.ofFinite _
  let _ := o.vertexOrder
  let X := SimplicialComplex.orderedSimplicialSet K.toPreAbstractSimplicialComplex
  let R := ModuleCat.of ℚ ℚ
  let C := X.normalizedChainComplex R
  let _ : FiniteDimensional ℚ (C.X 2) :=
    DifferentialGeometry.SSet.finiteDimensional_normalizedChainComplex_X X R 2
  let _ : FiniteDimensional ℚ (C.X 3) :=
    DifferentialGeometry.SSet.finiteDimensional_normalizedChainComplex_X X R 3
  let _ : FiniteDimensional ℚ (C.sc' 3 2 1).X₂ := by
    change FiniteDimensional ℚ (C.X 2)
    infer_instance
  let J := topBoundaryAndBoundaryComponentsToCycles K hK o c₀
  have hJ : Function.Injective J :=
    topBoundaryAndBoundaryComponentsToCycles_injective K hK hconn o c₀
  have hinj := LinearMap.finrank_le_finrank_of_injective hJ
  have hdomain : Module.finrank ℚ (Top → ℚ) +
      Module.finrank ℚ (OtherBoundaryComponent B c₀ → ℚ) ≤
      Module.finrank ℚ (LinearMap.ker (C.d 2 1).hom) := by
    simpa [J, Top, B, C, X, R, Module.finrank_prod] using hinj
  have hker := DifferentialGeometry.ShortComplex.finrank_ker_eq_homology_add_range
    (C.sc' 3 2 1)
  change Module.finrank ℚ (LinearMap.ker (C.d 2 1).hom) =
    Module.finrank ℚ (C.sc' 3 2 1).homology +
      Module.finrank ℚ (LinearMap.range (C.d 3 2).hom) at hker
  have hsc := (CategoryTheory.ShortComplex.homologyMapIso
    (C.isoSc' 3 2 1 (by simp) (by simp))).toLinearEquiv.finrank_eq
  change Module.finrank ℚ (C.homology 2) =
    Module.finrank ℚ (C.sc' 3 2 1).homology at hsc
  have hrange := LinearMap.finrank_range_le (C.d 3 2).hom
  let e₃ := SimplicialComplex.orderedNormalizedChainEquiv (k := ℚ)
    K.toPreAbstractSimplicialComplex 3
  have hC3 : Module.finrank ℚ (C.X 3) = Fintype.card Top := by
    have he := e₃.finrank_eq
    change Module.finrank ℚ (C.X 3) = Module.finrank ℚ (Top → ℚ) at he
    rw [Module.finrank_pi] at he
    exact he
  have hnorm := (isoOfQuasiIsoAt (X.toNormalizedChainComplex R) 2).toLinearEquiv.finrank_eq
  change Module.finrank ℚ ((X.chainComplex R).homology 2) =
    Module.finrank ℚ (C.homology 2) at hnorm
  have hreal := (DifferentialGeometry.SSet.realizationHomologyIso R X 2).toLinearEquiv.finrank_eq
  let F := (singularHomologyFunctor (ModuleCat ℚ) 2).obj R
  let e : _root_.SSet.toTop.obj X ≅ TopCat.of K.space :=
    TopCat.isoOfHomeo (by simpa [X] using
      SimplicialComplex.geometricRealizationHomeomorphism K)
  have hhomeo := (F.mapIso e).toLinearEquiv.finrank_eq
  have hbetti : Module.finrank ℚ (C.homology 2) =
      Homology.bettiNumber ℚ (TopCat.of K.space) 2 := by
    calc
      Module.finrank ℚ (C.homology 2) =
          Module.finrank ℚ ((X.chainComplex R).homology 2) := hnorm.symm
      _ = Module.finrank ℚ (((singularHomologyFunctor (ModuleCat ℚ) 2).obj R).obj
          (_root_.SSet.toTop.obj X)) := hreal
      _ = Module.finrank ℚ (((singularHomologyFunctor (ModuleCat ℚ) 2).obj R).obj
          (TopCat.of K.space)) := by simpa [F, X] using hhomeo
      _ = Homology.bettiNumber ℚ (TopCat.of K.space) 2 := rfl
  rw [Module.finrank_pi, Module.finrank_pi] at hdomain
  rw [← hsc, hbetti] at hker
  rw [hC3] at hrange
  change Nat.card (OtherBoundaryComponent B c₀) ≤
    Homology.bettiNumber ℚ (TopCat.of K.space) 2
  rw [Nat.card_eq_fintype_card]
  omega

open Classical in
theorem orientedTopChain_involutive
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (o : CoherentOrientation 3 K)
    (x : {s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ) :
    orientedTopChain K o (orientedTopChain K o x) = x := by
  funext s
  rcases o.sign_top s.1 s.2.1 s.2.2 with h | h <;>
    simp [orientedTopChain, orientedTopChainCoeff, s.2.1, s.2.2, h]

open Classical in
theorem orientedTopChain_injective
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (o : CoherentOrientation 3 K) : Function.Injective (orientedTopChain K o) := by
  intro x y hxy
  calc
    x = orientedTopChain K o (orientedTopChain K o x) :=
      (orientedTopChain_involutive K o x).symm
    _ = orientedTopChain K o (orientedTopChain K o y) := congrArg (orientedTopChain K o) hxy
    _ = y := orientedTopChain_involutive K o y

open Classical in
theorem orderedNormalizedBoundary_two_injective
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hconn : IsConnected K.space)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space) :
    let _ := o.vertexOrder
    Function.Injective
      (SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
        K.toPreAbstractSimplicialComplex 2) := by
  dsimp
  let B := boundaryComplex 3 K
  let L := topBoundaryAndBoundaryComponents K hK o c₀
  let Q := boundaryComponentCombinationIn K hK o c₀
  have hLzero : ∀ z, L z = 0 → z = 0 := by
    intro z hz
    exact topBoundaryAndBoundaryComponents_eq_zero K hK hconn o c₀ z hz
  let _ := o.vertexOrder
  intro u v huv
  let a := orientedTopChain K o (u - v)
  let z : ({s : Finset E // s ∈ K.faces ∧ s.card = 4} → ℚ) ×
      (OtherBoundaryComponent B c₀ → ℚ) := (a, 0)
  have hz : L z = 0 := by
    change SimplicialComplex.orderedNormalizedBoundary (k := ℚ)
          K.toPreAbstractSimplicialComplex 2 (orientedTopChain K o a) +
        Q 0 = 0
    rw [orientedTopChain_involutive]
    simp only [map_sub, huv, sub_self, map_zero, add_zero]
  have hzzero := hLzero z hz
  have ha : a = 0 := congrArg Prod.fst hzzero
  apply sub_eq_zero.mp
  apply orientedTopChain_injective K o
  simpa only [a, map_zero] using ha

open Classical in
theorem normalizedChainDifferential_three_two_injective
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hconn : IsConnected K.space)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space) :
    let _ := o.vertexOrder
    Function.Injective
      (((SimplicialComplex.orderedSimplicialSet K.toPreAbstractSimplicialComplex).normalizedChainComplex
        (ModuleCat.of ℚ ℚ)).d 3 2).hom := by
  dsimp
  have hcoord := orderedNormalizedBoundary_two_injective K hK hconn o c₀
  let _ := o.vertexOrder
  let X := SimplicialComplex.orderedSimplicialSet K.toPreAbstractSimplicialComplex
  let C := X.normalizedChainComplex (ModuleCat.of ℚ ℚ)
  let e₂ := SimplicialComplex.orderedNormalizedChainEquiv (k := ℚ)
    K.toPreAbstractSimplicialComplex 2
  let e₃ := SimplicialComplex.orderedNormalizedChainEquiv (k := ℚ)
    K.toPreAbstractSimplicialComplex 3
  intro x y hxy
  apply e₃.injective
  apply hcoord
  have heq := congrArg e₂ hxy
  simpa [SimplicialComplex.orderedNormalizedBoundary, X, C, e₂, e₃] using heq

open Classical in
theorem bettiNumber_three_eq_zero_of_coherentOrientation
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hconn : IsConnected K.space)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space) :
    Homology.bettiNumber ℚ (TopCat.of K.space) 3 = 0 := by
  have hinj₀ := normalizedChainDifferential_three_two_injective K hK hconn o c₀
  let _ := o.vertexOrder
  let X := SimplicialComplex.orderedSimplicialSet K.toPreAbstractSimplicialComplex
  let R := ModuleCat.of ℚ ℚ
  let C := X.normalizedChainComplex R
  let _ : FiniteDimensional ℚ (C.X 3) :=
    DifferentialGeometry.SSet.finiteDimensional_normalizedChainComplex_X X R 3
  let _ : FiniteDimensional ℚ (C.sc' 4 3 2).X₂ := by
    change FiniteDimensional ℚ (C.X 3)
    infer_instance
  have hinj : Function.Injective (C.d 3 2).hom := hinj₀
  have hker : Module.finrank ℚ (LinearMap.ker (C.d 3 2).hom) = 0 := by
    rw [LinearMap.ker_eq_bot.mpr hinj, finrank_bot]
  have hrank := DifferentialGeometry.ShortComplex.finrank_ker_eq_homology_add_range
    (C.sc' 4 3 2)
  change Module.finrank ℚ (LinearMap.ker (C.d 3 2).hom) =
    Module.finrank ℚ (C.sc' 4 3 2).homology +
      Module.finrank ℚ (LinearMap.range (C.d 4 3).hom) at hrank
  have hsc := (CategoryTheory.ShortComplex.homologyMapIso
    (C.isoSc' 4 3 2 (by simp) (by simp))).toLinearEquiv.finrank_eq
  change Module.finrank ℚ (C.homology 3) =
    Module.finrank ℚ (C.sc' 4 3 2).homology at hsc
  have hCzero : Module.finrank ℚ (C.homology 3) = 0 := by
    rw [hker, ← hsc] at hrank
    omega
  have hnorm := (isoOfQuasiIsoAt (X.toNormalizedChainComplex R) 3).toLinearEquiv.finrank_eq
  change Module.finrank ℚ ((X.chainComplex R).homology 3) =
    Module.finrank ℚ (C.homology 3) at hnorm
  have hreal := (DifferentialGeometry.SSet.realizationHomologyIso R X 3).toLinearEquiv.finrank_eq
  let F := (singularHomologyFunctor (ModuleCat ℚ) 3).obj R
  let e : _root_.SSet.toTop.obj X ≅ TopCat.of K.space :=
    TopCat.isoOfHomeo (by simpa [X] using
      SimplicialComplex.geometricRealizationHomeomorphism K)
  have hhomeo := (F.mapIso e).toLinearEquiv.finrank_eq
  change Module.finrank ℚ (((singularHomologyFunctor (ModuleCat ℚ) 3).obj R).obj
    (TopCat.of K.space)) = 0
  calc
    Module.finrank ℚ (((singularHomologyFunctor (ModuleCat ℚ) 3).obj R).obj
        (TopCat.of K.space)) =
        Module.finrank ℚ (((singularHomologyFunctor (ModuleCat ℚ) 3).obj R).obj
          (_root_.SSet.toTop.obj X)) := by simpa [F, X] using hhomeo.symm
    _ = Module.finrank ℚ ((X.chainComplex R).homology 3) := hreal.symm
    _ = Module.finrank ℚ (C.homology 3) := hnorm
    _ = 0 := hCzero

open Classical in
theorem eulerChar_eq_one_sub_bettiOne_add_bettiTwo_of_coherentOrientation
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hconn : IsConnected K.space)
    (o : CoherentOrientation 3 K)
    (c₀ : ConnectedComponents (boundaryComplex 3 K).space) :
    eulerChar K = 1 - (Homology.bettiOne K.space : ℤ) +
      (Homology.bettiNumber ℚ (TopCat.of K.space) 2 : ℤ) := by
  have hb₀ := bettiNumber_zero_of_isConnected K ℚ hconn
  have hb₃ := bettiNumber_three_eq_zero_of_coherentOrientation K hK hconn o c₀
  rw [eulerChar_eq_sum_bettiNumber K ℚ 3 (fun s hs => hK.card_le K hs)]
  norm_num [Finset.sum_range_succ, Homology.bettiOne, hb₀, hb₃]
  ring

end DifferentialGeometry.Topology.PiecewiseLinear
