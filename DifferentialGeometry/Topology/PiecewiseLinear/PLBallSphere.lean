import DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import DifferentialGeometry.Topology.SimplicialComplex.GeometricEulerCharacteristic
import DifferentialGeometry.Topology.SimplicialComplex.Simplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def IsPLHomeomorphOn.homeomorph [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {P : Set E} {Q : Set F} (h : IsPLHomeomorphOn f P Q) : P ≃ₜ Q where
  toFun x := ⟨f x, h.bijOn.mapsTo x.2⟩
  invFun y := ⟨Function.invFunOn f P y, h.bijOn.surjOn.mapsTo_invFunOn y.2⟩
  left_inv x := Subtype.ext (h.bijOn.invOn_invFunOn.1 x.2)
  right_inv y := Subtype.ext (h.bijOn.invOn_invFunOn.2 y.2)
  continuous_toFun :=
    (continuousOn_iff_continuous_domRestrict.mp h.isPiecewiseAffineOn.continuousOn).subtype_mk _
  continuous_invFun :=
    (continuousOn_iff_continuous_domRestrict.mp
      h.isPiecewiseAffineOn_invFunOn.continuousOn).subtype_mk _

theorem IsPLSphere.isPolyhedron [FiniteDimensional ℝ E] {n : ℕ} {P : Set E}
    (hP : IsPLSphere n P) : IsPolyhedron P := by
  obtain ⟨f, hf⟩ := hP
  obtain ⟨g, hg⟩ := isPLSphere_simplexBoundary_std n
  have : Finite (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have h := hg.symm.trans hf
  rw [← h.image_eq]
  exact IsPolyhedron.image_of_isPiecewiseAffineOn (isPolyhedron_space _)
    h.isPiecewiseAffineOn h.bijOn.injOn

theorem isConnected_stdSimplexBoundary (n : ℕ) : IsConnected (stdSimplexBoundary (n + 2)) := by
  classical
  let C : Fin (n + 3) → Set (Fin (n + 3) → ℝ) :=
    fun i => {x | x ∈ stdSimplex ℝ (Fin (n + 3)) ∧ x i = 0}
  have hthird : ∀ i j : Fin (n + 3), ∃ k : Fin (n + 3), k ≠ i ∧ k ≠ j := by
    intro i j
    by_contra! h
    have hall : ∀ k : Fin (n + 3), k.val = i.val ∨ k.val = j.val := by
      intro k
      by_cases hki : k = i
      · exact Or.inl (congrArg Fin.val hki)
      · exact Or.inr (congrArg Fin.val (h k hki))
    have h0 : (0 : ℕ) = i.val ∨ 0 = j.val := hall ⟨0, by omega⟩
    have h1 : (1 : ℕ) = i.val ∨ 1 = j.val := hall ⟨1, by omega⟩
    have h2 : (2 : ℕ) = i.val ∨ 2 = j.val := hall ⟨2, by omega⟩
    omega
  have hmem : ∀ i j : Fin (n + 3), j ≠ i → Pi.single j (1 : ℝ) ∈ C i := by
    intro i j hji
    exact ⟨single_mem_stdSimplex ℝ j, by simp only [Pi.single_eq_of_ne (Ne.symm hji)]⟩
  have hconv : ∀ i, Convex ℝ (C i) := fun i =>
    (convex_stdSimplex ℝ (Fin (n + 3))).inter
      ((convex_singleton (0 : ℝ)).linear_preimage (LinearMap.proj i : (Fin (n + 3) → ℝ) →ₗ[ℝ] ℝ))
  have hcover : stdSimplexBoundary (n + 2) = ⋃ i, C i := by
    ext x
    rw [mem_iUnion]
    change (x ∈ stdSimplex ℝ (Fin (n + 3)) ∧ ∃ i, x i = 0) ↔
      ∃ i, x ∈ stdSimplex ℝ (Fin (n + 3)) ∧ x i = 0
    constructor
    · rintro ⟨hx, i, hi⟩
      exact ⟨i, hx, hi⟩
    · rintro ⟨i, hx, hi⟩
      exact ⟨hx, i, hi⟩
  rw [hcover]
  apply IsConnected.iUnion_of_reflTransGen
  · intro i
    obtain ⟨j, hji, -⟩ := hthird i i
    exact (hconv i).isConnected ⟨Pi.single j 1, hmem i j hji⟩
  · intro i j
    obtain ⟨k, hki, hkj⟩ := hthird i j
    exact Relation.ReflTransGen.single ⟨Pi.single k 1, hmem i k hki, hmem j k hkj⟩

theorem IsPLBall.isConnected {n : ℕ} {P : Set E} (hP : IsPLBall n P) : IsConnected P := by
  obtain ⟨f, hf⟩ := hP
  rw [← hf.image_eq]
  exact ((convex_stdSimplex ℝ (Fin (n + 1))).isConnected
    ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩).image f hf.isPiecewiseAffineOn.continuousOn

theorem IsPLSphere.isConnected {n : ℕ} {P : Set E} (hP : IsPLSphere (n + 1) P) : IsConnected P := by
  obtain ⟨f, hf⟩ := hP
  rw [← hf.image_eq]
  exact (isConnected_stdSimplexBoundary n).image f hf.isPiecewiseAffineOn.continuousOn

theorem eulerChar_stdSimplex (n : ℕ) :
    Homology.eulerChar ℚ (TopCat.of (stdSimplex ℝ (Fin (n + 1)))) = 1 := by
  have : ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
      ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n + 1))⟩
  exact Homology.eulerChar_of_contractible ℚ

theorem simplexBoundary_toPreAbstractSimplicialComplex {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) :
    (simplexBoundary T hT).toPreAbstractSimplicialComplex = SimplicialComplex.boundarySimplex T := by
  ext s
  change s ⊆ T ∧ s.Nonempty ∧ s ≠ T ↔ s.Nonempty ∧ s ⊂ T
  rw [Finset.ssubset_iff_subset_ne]
  tauto

theorem faceEulerChar_congr {ι : Type*} {K₁ K₂ : PreAbstractSimplicialComplex ι}
    [Finite K₁.faces] [Finite K₂.faces] (h : K₁ = K₂) :
    SimplicialComplex.faceEulerChar K₁ = SimplicialComplex.faceEulerChar K₂ := by
  subst h
  rfl

theorem faceEulerChar_simplexBoundary {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    [Finite (simplexBoundary T hT).faces] (hne : T.Nonempty) :
    SimplicialComplex.faceEulerChar (simplexBoundary T hT).toPreAbstractSimplicialComplex =
      1 + (-1 : ℤ) ^ T.card :=
  (faceEulerChar_congr (simplexBoundary_toPreAbstractSimplicialComplex hT)).trans
    (SimplicialComplex.faceEulerChar_boundarySimplex hne)

theorem eulerChar_stdSimplexBoundary (n : ℕ) :
    Homology.eulerChar ℚ (TopCat.of (stdSimplexBoundary (n + 1))) = 1 + (-1 : ℤ) ^ n := by
  obtain ⟨f, hf⟩ := isPLSphere_simplexBoundary_std n
  have hfin :=
    (simplexBoundary_faces_finite (stdVertices n) (stdVertices_affineIndependent n)).to_subtype
  have hne : (stdVertices n).Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le two_pos (two_le_card_stdVertices n))
  rw [Homology.eulerChar_eq_of_homeomorph ℚ (X := TopCat.of (stdSimplexBoundary (n + 1)))
    (Y := TopCat.of (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space)
    hf.homeomorph, SimplicialComplex.eulerChar_geometricSpace_eq_faceEulerChar,
    faceEulerChar_simplexBoundary _ hne, card_stdVertices, pow_succ, pow_succ]
  ring

theorem not_isPLHomeomorphOn_stdSimplex_stdSimplexBoundary (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → (Fin (n + 2) → ℝ)) :
    ¬ IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 1))) (stdSimplexBoundary (n + 1)) := by
  intro hf
  have h := Homology.eulerChar_eq_of_homeomorph ℚ
    (X := TopCat.of (stdSimplex ℝ (Fin (n + 1))))
    (Y := TopCat.of (stdSimplexBoundary (n + 1))) hf.homeomorph
  rw [eulerChar_stdSimplex, eulerChar_stdSimplexBoundary] at h
  have hzero : ((-1 : ℤ) ^ n) = 0 := by linarith
  exact pow_ne_zero n (by norm_num) hzero

theorem IsPLBall.not_isPLSphere [FiniteDimensional ℝ E] {n : ℕ} {P : Set E} (hB : IsPLBall n P)
    (hS : IsPLSphere n P) : False := by
  obtain ⟨f, hf⟩ := hB
  obtain ⟨g, hg⟩ := hS
  exact not_isPLHomeomorphOn_stdSimplex_stdSimplexBoundary n _ (hf.trans hg.symm)

theorem IsPLSphere.not_isPLBall [FiniteDimensional ℝ E] {n : ℕ} {P : Set E} (hS : IsPLSphere n P)
    (hB : IsPLBall n P) : False :=
  hB.not_isPLSphere hS

end DifferentialGeometry.Topology.PiecewiseLinear
