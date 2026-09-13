import DifferentialGeometry.Topology.PiecewiseLinear.ConeExtension
import DifferentialGeometry.Topology.PiecewiseLinear.LinkEuclidean

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Std

variable (n : ℕ)

noncomputable def stdVertices : Finset (Fin (n + 2) → ℝ) :=
  Finset.univ.image fun i : Fin (n + 2) => (Pi.single i (1 : ℝ) : Fin (n + 2) → ℝ)

noncomputable def stdCenter : Fin (n + 2) → ℝ := fun _ => ((n : ℝ) + 2)⁻¹

theorem stdVertex_injective :
    Function.Injective fun i : Fin (n + 2) => (Pi.single i (1 : ℝ) : Fin (n + 2) → ℝ) := by
  intro i j h
  by_contra hij
  have h1 : (Pi.single i (1 : ℝ) : Fin (n + 2) → ℝ) i = (Pi.single j (1 : ℝ) : Fin (n + 2) → ℝ) i :=
    congrFun h i
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hij] at h1
  exact one_ne_zero h1

theorem coe_stdVertices :
    ((stdVertices n : Finset (Fin (n + 2) → ℝ)) : Set (Fin (n + 2) → ℝ)) =
      Set.range fun i : Fin (n + 2) => (Pi.single i (1 : ℝ) : Fin (n + 2) → ℝ) := by
  rw [stdVertices, Finset.coe_image, Finset.coe_univ, Set.image_univ]

theorem stdVertices_affineIndependent :
    AffineIndependent ℝ ((↑) : stdVertices n → (Fin (n + 2) → ℝ)) := by
  have hlin : LinearIndependent ℝ fun i : Fin (n + 2) => (Pi.single i (1 : ℝ) : Fin (n + 2) → ℝ) := by
    have h := (Pi.basisFun ℝ (Fin (n + 2))).linearIndependent
    have heq : (⇑(Pi.basisFun ℝ (Fin (n + 2))) : Fin (n + 2) → Fin (n + 2) → ℝ) =
        fun i => Pi.single i 1 := funext fun i => by simp
    rwa [heq] at h
  have h := hlin.affineIndependent.range
  rwa [← coe_stdVertices] at h

theorem card_stdVertices : (stdVertices n).card = n + 2 := by
  rw [stdVertices, Finset.card_image_of_injective _ (stdVertex_injective n), Finset.card_univ,
    Fintype.card_fin]

theorem two_le_card_stdVertices : 2 ≤ (stdVertices n).card := by
  rw [card_stdVertices]
  omega

theorem convexHull_stdVertices :
    convexHull ℝ ((stdVertices n : Finset (Fin (n + 2) → ℝ)) : Set (Fin (n + 2) → ℝ)) =
      stdSimplex ℝ (Fin (n + 2)) := by
  have hfun : (fun i : Fin (n + 2) => (Pi.single i (1 : ℝ) : Fin (n + 2) → ℝ)) =
      fun i j => if i = j then (1 : ℝ) else 0 := by
    funext i j
    rw [Pi.single_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  rw [coe_stdVertices, hfun, convexHull_basis_eq_stdSimplex]

theorem stdCenter_mem_openSimplex : stdCenter n ∈ openSimplex (stdVertices n) := by
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  refine ⟨fun _ => ((n : ℝ) + 2)⁻¹, fun _ _ => inv_pos.mpr (by positivity), ?_, ?_⟩
  · rw [Finset.sum_const, card_stdVertices, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat,
      mul_inv_cancel₀ hn2]
  · rw [stdVertices, Finset.sum_image fun i _ j _ h => stdVertex_injective n h]
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl

theorem isConeBase_std :
    IsConeBase (stdCenter n) (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)) :=
  isConeBase_simplexBoundary _ (two_le_card_stdVertices n) (stdCenter_mem_openSimplex n)

theorem coneComplex_std_space :
    (coneComplex (isConeBase_std n)).space = stdSimplex ℝ (Fin (n + 2)) := by
  rw [← convexHull_stdVertices]
  ext x
  rw [mem_coneComplex_space_iff]
  constructor
  · rintro (hxp | ⟨z, hz, s, hs, hs', rfl⟩)
    · rw [hxp]
      exact openSimplex_subset_convexHull _ (stdCenter_mem_openSimplex n)
    · rw [simplexBoundary_space _ _ (two_le_card_stdVertices n)] at hz
      obtain ⟨v, -, hzv⟩ := mem_iUnion₂.mp hz
      have hzT : z ∈ convexHull ℝ ((stdVertices n : Finset _) : Set _) :=
        convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset v _)) hzv
      rw [add_smul_sub_eq_combo]
      exact (convex_convexHull ℝ _) (openSimplex_subset_convexHull _ (stdCenter_mem_openSimplex n))
        hzT (by linarith) hs.le (by ring)
  · intro hx
    obtain ⟨v, hv, hxv⟩ := exists_mem_convexHull_insert_erase (stdVertices_affineIndependent n)
      (stdCenter_mem_openSimplex n) hx
    rcases exists_combo_of_mem_convexHull_insert
      (notMem_erase_of_mem_openSimplex (stdVertices_affineIndependent n)
        (stdCenter_mem_openSimplex n) hv) hxv with
      hxp | ⟨z, hz, s, hs, hs', rfl⟩
    · exact Or.inl hxp
    · refine Or.inr ⟨z, ?_, s, hs, hs', rfl⟩
      exact Geometry.SimplicialComplex.mem_space_iff.mpr
        ⟨_, erase_mem_simplexBoundary_faces _ (two_le_card_stdVertices n) hv, hz⟩

theorem isPLSphere_simplexBoundary_std :
    IsPLSphere n (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space := by
  rw [simplexBoundary_space _ _ (two_le_card_stdVertices n)]
  exact isPLSphere_biUnion_erase _ (stdVertices_affineIndependent n) (card_stdVertices n)

end Std

theorem IsConeBase.isPLBall_of_isPLSphere [FiniteDimensional ℝ E] [DecidableEq E] {p : E}
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsConeBase p L) {n : ℕ}
    (hsph : IsPLSphere n L.space) : IsPLBall (n + 1) (coneComplex hL).space := by
  obtain ⟨f, hf⟩ := hsph
  obtain ⟨f₀, hf₀⟩ := isPLSphere_simplexBoundary_std n
  have hfin : Finite (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hhomeo := hf₀.symm.trans hf
  obtain ⟨g, hg, -, -, -⟩ := exists_isPLHomeomorphOn_coneComplex (isConeBase_std n) hL hhomeo
  rw [coneComplex_std_space] at hg
  exact ⟨g, hg⟩

theorem isPLBall_closedStar [FiniteDimensional ℝ E] [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {p : E} (hp : {p} ∈ K.faces) {n : ℕ}
    (hsph : IsPLSphere n (SimplicialComplex.geometricLink K {p}).space) :
    IsPLBall (n + 1) (closedStar K p) := by
  rw [closedStar_eq_coneComplex_space K hp]
  exact (isConeBase_geometricLink K).isPLBall_of_isPLSphere hsph

theorem IsCombinatorialManifold.isPLBall_closedStar [FiniteDimensional ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold (n + 1) K) {p : E} (hp : {p} ∈ K.faces) :
    IsPLBall (n + 1) (closedStar K p) := by
  classical
  exact PiecewiseLinear.isPLBall_closedStar K hp (by convert hK p hp)

end DifferentialGeometry.Topology.PiecewiseLinear
