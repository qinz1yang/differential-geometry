/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssemblyWitness
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBall
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Weights

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem nonneg_apply_of_mem_convexHull {T : Finset E} (φ : E →ₗ[ℝ] ℝ)
    (hT : ∀ v ∈ T, 0 ≤ φ v) {x : E} (hx : x ∈ convexHull ℝ (T : Set E)) : 0 ≤ φ x := by
  obtain ⟨c, hc0, -, hcx⟩ := mem_convexHull_iff_exists_weights.mp hx
  rw [← hcx, map_sum]
  refine Finset.sum_nonneg fun v hv => ?_
  rw [map_smul, smul_eq_mul]
  exact mul_nonneg (hc0 v hv) (hT v hv)

theorem mem_convexHull_erase_of_apply_eq_zero [DecidableEq E] {T : Finset E} {k : E} (hk : k ∈ T)
    (φ : E →ₗ[ℝ] ℝ) (hzero : ∀ v ∈ T, v ≠ k → φ v = 0) (hk0 : φ k ≠ 0) {x : E}
    (hx : x ∈ convexHull ℝ (T : Set E)) (hxz : φ x = 0) :
    x ∈ convexHull ℝ ((T.erase k : Finset E) : Set E) := by
  obtain ⟨c, hc0, hc1, hcx⟩ := mem_convexHull_iff_exists_weights.mp hx
  have hsingle : ∑ v ∈ T, φ (c v • v) = φ (c k • k) :=
    Finset.sum_eq_single_of_mem k hk fun v hv hvk => by
      rw [map_smul, smul_eq_mul, hzero v hv hvk, mul_zero]
  have hck : c k = 0 := by
    have hval : φ x = c k * φ k := by
      rw [← hcx, map_sum, hsingle, map_smul, smul_eq_mul]
    rw [hxz] at hval
    rcases mul_eq_zero.mp hval.symm with h | h
    · exact h
    · exact absurd h hk0
  refine mem_convexHull_iff_exists_weights.mpr
    ⟨c, fun v hv => hc0 v (Finset.mem_of_mem_erase hv), ?_, ?_⟩
  · rw [← Finset.add_sum_erase T c hk, hck, zero_add] at hc1
    exact hc1
  · rw [← Finset.add_sum_erase T (fun v => c v • v) hk, hck, zero_smul, zero_add] at hcx
    exact hcx

end Weights

section BentIndex

theorem subset_pos_or_neg_of_not_subset {J : Finset (Fin 5)}
    (hJ : ¬ ({3, 4} : Finset (Fin 5)) ⊆ J) :
    J ⊆ ({0, 1, 2, 3} : Finset (Fin 5)) ∨ J ⊆ ({0, 1, 2, 4} : Finset (Fin 5)) := by
  obtain ⟨i, hi, hiJ⟩ := Finset.not_subset.mp hJ
  have hi' : i = 3 ∨ i = 4 := by simpa using hi
  rcases hi' with rfl | rfl
  · right
    intro k hk
    have hk3 : k ≠ 3 := fun h => hiJ (h ▸ hk)
    fin_cases k <;> revert hk3 <;> decide
  · left
    intro k hk
    have hk4 : k ≠ 4 := fun h => hiJ (h ▸ hk)
    fin_cases k <;> revert hk4 <;> decide

theorem card_le_four_of_not_subset {J : Finset (Fin 5)}
    (hJ : ¬ ({3, 4} : Finset (Fin 5)) ⊆ J) : J.card ≤ 4 := by
  rcases subset_pos_or_neg_of_not_subset hJ with h | h
  · exact le_trans (Finset.card_le_card h) (by decide)
  · exact le_trans (Finset.card_le_card h) (by decide)

end BentIndex

section BentFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexHull_image_inter_of_subset {w : Fin 5 → E} (hw : Function.Injective w)
    {S I J : Finset (Fin 5)}
    (hS : AffineIndependent ℝ ((↑) : ↥(w '' (S : Set (Fin 5))) → E))
    (hI : I ⊆ S) (hJ : J ⊆ S) :
    convexHull ℝ (w '' (I : Set (Fin 5))) ∩ convexHull ℝ (w '' (J : Set (Fin 5))) =
      convexHull ℝ (w '' ((I ∩ J : Finset (Fin 5)) : Set (Fin 5))) := by
  classical
  have hS' : AffineIndependent ℝ ((↑) : ↥((S.image w : Finset E) : Set E) → E) :=
    hS.mono (Finset.coe_image (f := w) (s := S)).subset
  have h := hS'.convexHull_inter (t₁ := I.image w) (t₂ := J.image w)
    (Finset.image_subset_image hI) (Finset.image_subset_image hJ)
  simp only [Finset.coe_image] at h
  rw [← Set.image_inter hw, ← Finset.coe_inter] at h
  exact h.symm

theorem convexHull_image_inter_of_cross {w : Fin 5 → E} (hw : Function.Injective w)
    (φ : E →ₗ[ℝ] ℝ)
    (hS : AffineIndependent ℝ ((↑) : ↥(w '' ((({0, 1, 2, 3} : Finset (Fin 5)))
      : Set (Fin 5))) → E))
    (hbase : ∀ i ∈ ({0, 1, 2} : Finset (Fin 5)), φ (w i) = 0)
    (h3 : 0 < φ (w 3)) (h4 : φ (w 4) < 0) {I J : Finset (Fin 5)}
    (hI : I ⊆ ({0, 1, 2, 3} : Finset (Fin 5))) (hJ : J ⊆ ({0, 1, 2, 4} : Finset (Fin 5))) :
    convexHull ℝ (w '' (I : Set (Fin 5))) ∩ convexHull ℝ (w '' (J : Set (Fin 5))) =
      convexHull ℝ (w '' ((I ∩ J : Finset (Fin 5)) : Set (Fin 5))) := by
  classical
  refine Subset.antisymm ?_ ?_
  · rintro x ⟨hxI, hxJ⟩
    have hxIT : x ∈ convexHull ℝ ((I.image w : Finset E) : Set E) := by
      rwa [Finset.coe_image]
    have hxJT : x ∈ convexHull ℝ ((J.image w : Finset E) : Set E) := by
      rwa [Finset.coe_image]
    have hIbase : ∀ i ∈ I, i ≠ 3 → φ (w i) = 0 := by
      intro i hi hi3
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simpa using hI hi
      rcases hi' with rfl | rfl | rfl | rfl
      · exact hbase 0 (by decide)
      · exact hbase 1 (by decide)
      · exact hbase 2 (by decide)
      · exact absurd rfl hi3
    have hJbase : ∀ i ∈ J, i ≠ 4 → φ (w i) = 0 := by
      intro i hi hi4
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4 := by simpa using hJ hi
      rcases hi' with rfl | rfl | rfl | rfl
      · exact hbase 0 (by decide)
      · exact hbase 1 (by decide)
      · exact hbase 2 (by decide)
      · exact absurd rfl hi4
    have hpos : 0 ≤ φ x := by
      refine nonneg_apply_of_mem_convexHull φ (fun v hv => ?_) hxIT
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      rcases eq_or_ne i 3 with rfl | hi3
      · exact h3.le
      · exact (hIbase i hi hi3).ge
    have hneg : φ x ≤ 0 := by
      have hmap : 0 ≤ (-φ) x := by
        refine nonneg_apply_of_mem_convexHull (-φ) (fun v hv => ?_) hxJT
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
        rcases eq_or_ne i 4 with rfl | hi4
        · simpa using h4.le
        · simp [hJbase i hi hi4]
      simpa using hmap
    have hzero : φ x = 0 := le_antisymm hneg hpos
    have hxI' : x ∈ convexHull ℝ (w '' ((I.erase 3 : Finset (Fin 5)) : Set (Fin 5))) := by
      by_cases h3I : (3 : Fin 5) ∈ I
      · have hkey := mem_convexHull_erase_of_apply_eq_zero (T := I.image w) (k := w 3)
          (Finset.mem_image_of_mem w h3I) φ (fun v hv hvk => by
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
            exact hIbase i hi fun h => hvk (by rw [h])) h3.ne' hxIT hzero
        rwa [← Finset.image_erase hw, Finset.coe_image] at hkey
      · rwa [Finset.erase_eq_of_notMem h3I]
    have hxJ' : x ∈ convexHull ℝ (w '' ((J.erase 4 : Finset (Fin 5)) : Set (Fin 5))) := by
      by_cases h4J : (4 : Fin 5) ∈ J
      · have hkey := mem_convexHull_erase_of_apply_eq_zero (T := J.image w) (k := w 4)
          (Finset.mem_image_of_mem w h4J) φ (fun v hv hvk => by
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
            exact hJbase i hi fun h => hvk (by rw [h])) h4.ne hxJT hzero
        rwa [← Finset.image_erase hw, Finset.coe_image] at hkey
      · rwa [Finset.erase_eq_of_notMem h4J]
    have hIsub : I.erase 3 ⊆ ({0, 1, 2, 3} : Finset (Fin 5)) :=
      (Finset.erase_subset 3 I).trans hI
    have hJsub : J.erase 4 ⊆ ({0, 1, 2, 3} : Finset (Fin 5)) := by
      intro k hk
      have hkJ : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 4 := by
        simpa using hJ (Finset.mem_of_mem_erase hk)
      have hk4 : k ≠ 4 := Finset.ne_of_mem_erase hk
      rcases hkJ with rfl | rfl | rfl | rfl
      · decide
      · decide
      · decide
      · exact absurd rfl hk4
    have hIJ : (I.erase 3) ∩ (J.erase 4) = I ∩ J := by
      ext k
      simp only [Finset.mem_inter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨-, hkI⟩, -, hkJ⟩
        exact ⟨hkI, hkJ⟩
      · rintro ⟨hkI, hkJ⟩
        refine ⟨⟨?_, hkI⟩, ?_, hkJ⟩
        · rintro rfl
          exact absurd (hJ hkJ) (by decide)
        · rintro rfl
          exact absurd (hI hkI) (by decide)
    have hfin := convexHull_image_inter_of_subset hw hS hIsub hJsub
    rw [hIJ] at hfin
    exact hfin.subset ⟨hxI', hxJ'⟩
  · exact subset_inter
      (convexHull_mono (image_mono (Finset.coe_subset.mpr Finset.inter_subset_left)))
      (convexHull_mono (image_mono (Finset.coe_subset.mpr Finset.inter_subset_right)))

theorem convexHull_image_inter_of_bent {w : Fin 5 → E} (hw : Function.Injective w)
    (φ : E →ₗ[ℝ] ℝ)
    (hpos : AffineIndependent ℝ ((↑) : ↥(w '' ((({0, 1, 2, 3} : Finset (Fin 5)))
      : Set (Fin 5))) → E))
    (hneg : AffineIndependent ℝ ((↑) : ↥(w '' ((({0, 1, 2, 4} : Finset (Fin 5)))
      : Set (Fin 5))) → E))
    (hbase : ∀ i ∈ ({0, 1, 2} : Finset (Fin 5)), φ (w i) = 0)
    (h3 : 0 < φ (w 3)) (h4 : φ (w 4) < 0) {I J : Finset (Fin 5)}
    (hI : ¬ ({3, 4} : Finset (Fin 5)) ⊆ I) (hJ : ¬ ({3, 4} : Finset (Fin 5)) ⊆ J) :
    convexHull ℝ (w '' (I : Set (Fin 5))) ∩ convexHull ℝ (w '' (J : Set (Fin 5))) =
      convexHull ℝ (w '' ((I ∩ J : Finset (Fin 5)) : Set (Fin 5))) := by
  rcases subset_pos_or_neg_of_not_subset hI with hI' | hI' <;>
    rcases subset_pos_or_neg_of_not_subset hJ with hJ' | hJ'
  · exact convexHull_image_inter_of_subset hw hpos hI' hJ'
  · exact convexHull_image_inter_of_cross hw φ hpos hbase h3 h4 hI' hJ'
  · rw [inter_comm, Finset.inter_comm]
    exact convexHull_image_inter_of_cross hw φ hpos hbase h3 h4 hJ' hI'
  · exact convexHull_image_inter_of_subset hw hneg hI' hJ'

theorem image_stdSimplexBoundary_eq_biUnion_erase [FiniteDimensional ℝ E] {w : Fin 5 → E}
    (hw : Function.Injective w) {I : Finset (Fin 5)}
    (hI : AffineIndependent ℝ ((↑) : ↥(w '' (I : Set (Fin 5))) → E)) {d : ℕ}
    (hcard : I.card = d + 1) {f : (Fin (d + 1) → ℝ) → E}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1)))
      (convexHull ℝ (w '' (I : Set (Fin 5))))) :
    f '' stdSimplexBoundary d =
      ⋃ i ∈ I, convexHull ℝ (w '' ((I.erase i : Finset (Fin 5)) : Set (Fin 5))) := by
  classical
  have hcoe : ((I.image w : Finset E) : Set E) = w '' (I : Set (Fin 5)) := Finset.coe_image
  have hT : AffineIndependent ℝ ((↑) : ↥(I.image w : Finset E) → E) := hI.mono hcoe.subset
  have hTcard : (I.image w).card = d + 1 := by
    rw [Finset.card_image_of_injective _ hw]
    exact hcard
  cases d with
  | zero =>
      rw [stdSimplexBoundary_zero, image_empty, eq_comm, eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      have hempty : I.erase i = ∅ := by
        rw [← Finset.card_eq_zero, Finset.card_erase_of_mem hi, hcard]
      rw [hempty] at hxi
      simp at hxi
  | succ n =>
      have hf' : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)))
          (convexHull ℝ ((I.image w : Finset E) : Set E)) := by
        rw [hcoe]
        exact hf
      have hspace := image_stdSimplexBoundary_of_isPLHomeomorphOn_convexHull hT hTcard hf'
      rw [hspace, simplexBoundary_space _ hT (by omega)]
      refine Subset.antisymm (iUnion₂_subset fun v hv => ?_) (iUnion₂_subset fun i hi => ?_)
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
        rw [← Finset.image_erase hw, Finset.coe_image]
        exact subset_iUnion₂ (s := fun j (_ : j ∈ I) =>
          convexHull ℝ (w '' ((I.erase j : Finset (Fin 5)) : Set (Fin 5)))) i hi
      · rw [← Finset.coe_image, Finset.image_erase hw]
        exact subset_iUnion₂ (s := fun v (_ : v ∈ I.image w) =>
          convexHull ℝ (((I.image w).erase v : Finset E) : Set E)) (w i)
          (Finset.mem_image_of_mem w hi)

end BentFamily

section Model

theorem isPLHomeomorphInto_id_of_isPolyhedron {P : Set (EuclideanSpace ℝ (Fin 3))}
    (hP : IsPolyhedron P) :
    IsPLHomeomorphInto 3 (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) P := by
  have hpl : IsPLOn 3 3 (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) P :=
    isPLOn_iff_isPiecewiseAffineOn.mpr hP.isPLHomeomorphOn_id.isPiecewiseAffineOn
  refine ⟨hpl, injOn_id _, fun y hy => ⟨id, ?_, fun x _ => rfl⟩⟩
  rw [image_id] at hy ⊢
  exact hpl y hy

theorem linearIndependent_euclideanSingleTriple {d₀ d₁ d₂ : ℝ} (h₀ : d₀ ≠ 0) (h₁ : d₁ ≠ 0)
    (h₂ : d₂ ≠ 0) :
    LinearIndependent ℝ ![(EuclideanSpace.single 0 d₀ : EuclideanSpace ℝ (Fin 3)),
      EuclideanSpace.single 1 d₁, EuclideanSpace.single 2 d₂] := by
  have hbase : LinearIndependent ℝ
      (fun i : Fin 3 => (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 3))) := by
    have heq : (fun i : Fin 3 => (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 3))) =
        ⇑(EuclideanSpace.basisFun (Fin 3) ℝ).toBasis :=
      funext fun i => (EuclideanSpace.basisFun_apply (𝕜 := ℝ) (ι := Fin 3) i).symm
    rw [heq]
    exact (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.linearIndependent
  have hunits := hbase.units_smul ![Units.mk0 d₀ h₀, Units.mk0 d₁ h₁, Units.mk0 d₂ h₂]
  have hfun : (![Units.mk0 d₀ h₀, Units.mk0 d₁ h₁, Units.mk0 d₂ h₂] •
      fun i : Fin 3 => (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 3))) =
      ![(EuclideanSpace.single 0 d₀ : EuclideanSpace ℝ (Fin 3)),
        EuclideanSpace.single 1 d₁, EuclideanSpace.single 2 d₂] := by
    funext i
    fin_cases i <;> ext j <;>
      simp [Pi.smul_apply', Units.smul_def, PiLp.single_apply, mul_ite]
  rwa [hfun] at hunits

theorem affineIndependent_euclideanQuadruple {S : Set (EuclideanSpace ℝ (Fin 3))}
    (c : EuclideanSpace ℝ (Fin 3)) {d₀ d₁ d₂ : ℝ} (h₀ : d₀ ≠ 0) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0)
    (hS : S = {c, EuclideanSpace.single 0 d₀ + c, EuclideanSpace.single 1 d₁ + c,
      EuclideanSpace.single 2 d₂ + c}) :
    AffineIndependent ℝ ((↑) : ↥S → EuclideanSpace ℝ (Fin 3)) := by
  have hrange : (Set.range ![(EuclideanSpace.single 0 d₀ : EuclideanSpace ℝ (Fin 3)),
      EuclideanSpace.single 1 d₁, EuclideanSpace.single 2 d₂]) =
      ({EuclideanSpace.single 0 d₀, EuclideanSpace.single 1 d₁, EuclideanSpace.single 2 d₂} :
        Set (EuclideanSpace ℝ (Fin 3))) := by
    ext x
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.mem_union,
      Set.mem_singleton_iff, Set.mem_insert_iff]
  have hne : ∀ v ∈ ({EuclideanSpace.single 0 d₀, EuclideanSpace.single 1 d₁,
      EuclideanSpace.single 2 d₂} : Set (EuclideanSpace ℝ (Fin 3))), v ≠ (0 : _) := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · simpa using h₀
    · simpa using h₁
    · simpa using h₂
  have hli := (linearIndependent_euclideanSingleTriple h₀ h₁ h₂).linearIndepOn_id' hrange
  have haff := (linearIndependent_set_iff_affineIndependent_vadd_union_singleton ℝ hne c).mp hli
  refine haff.mono ?_
  rw [hS]
  rintro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Set.mem_union_left _ rfl
  · exact Set.mem_union_right _ ⟨_, Or.inl rfl, rfl⟩
  · exact Set.mem_union_right _ ⟨_, Or.inr (Or.inl rfl), rfl⟩
  · exact Set.mem_union_right _ ⟨_, Or.inr (Or.inr rfl), rfl⟩

end Model

section Vertices

noncomputable def bentTetrahedraVertex : Fin 5 → EuclideanSpace ℝ (Fin 3)
  | 0 => 0
  | 1 => EuclideanSpace.single 0 1
  | 2 => EuclideanSpace.single 1 1
  | 3 => EuclideanSpace.single 2 1
  | 4 => EuclideanSpace.single 2 (-1)

noncomputable def bentTetrahedraTargetVertex : Fin 5 → EuclideanSpace ℝ (Fin 3)
  | 0 => EuclideanSpace.single 0 4
  | 1 => EuclideanSpace.single 0 1 + EuclideanSpace.single 0 4
  | 2 => EuclideanSpace.single 1 1 + EuclideanSpace.single 0 4
  | 3 => EuclideanSpace.single 2 1 + EuclideanSpace.single 0 4
  | 4 => EuclideanSpace.single 2 (-2) + EuclideanSpace.single 0 4

theorem fin_five_eq_cases (i : Fin 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  revert i
  decide

theorem bentTetrahedraVertex_injective : Function.Injective bentTetrahedraVertex := by
  intro i j hij
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) hij
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) hij
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hij
  clear hij
  rcases fin_five_eq_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin_five_eq_cases j with rfl | rfl | rfl | rfl | rfl
  all_goals
    first
      | rfl
      | (exfalso
         simp [bentTetrahedraVertex] at h0 h1 h2
         try norm_num at h0 h1 h2)

theorem bentTetrahedraTargetVertex_injective :
    Function.Injective bentTetrahedraTargetVertex := by
  intro i j hij
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) hij
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) hij
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hij
  clear hij
  rcases fin_five_eq_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin_five_eq_cases j with rfl | rfl | rfl | rfl | rfl
  all_goals
    first
      | rfl
      | (exfalso
         simp [bentTetrahedraTargetVertex] at h0 h1 h2
         try norm_num at h0 h1 h2)

theorem bentTetrahedraVertex_height_base (i : Fin 5) (hi : i ∈ ({0, 1, 2} : Finset (Fin 5))) :
    (EuclideanSpace.proj (2 : Fin 3)).toLinearMap (bentTetrahedraVertex i) = 0 := by
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by simpa using hi
  rcases hi' with rfl | rfl | rfl <;>
    simp [bentTetrahedraVertex]

theorem bentTetrahedraVertex_height_pos :
    0 < (EuclideanSpace.proj (2 : Fin 3)).toLinearMap (bentTetrahedraVertex 3) := by
  simp [bentTetrahedraVertex]

theorem bentTetrahedraVertex_height_neg :
    (EuclideanSpace.proj (2 : Fin 3)).toLinearMap (bentTetrahedraVertex 4) < 0 := by
  simp [bentTetrahedraVertex]

theorem bentTetrahedraTargetVertex_height_base (i : Fin 5)
    (hi : i ∈ ({0, 1, 2} : Finset (Fin 5))) :
    (EuclideanSpace.proj (2 : Fin 3)).toLinearMap (bentTetrahedraTargetVertex i) = 0 := by
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by simpa using hi
  rcases hi' with rfl | rfl | rfl <;>
    simp [bentTetrahedraTargetVertex]

theorem bentTetrahedraTargetVertex_height_pos :
    0 < (EuclideanSpace.proj (2 : Fin 3)).toLinearMap (bentTetrahedraTargetVertex 3) := by
  simp [bentTetrahedraTargetVertex]

theorem bentTetrahedraTargetVertex_height_neg :
    (EuclideanSpace.proj (2 : Fin 3)).toLinearMap (bentTetrahedraTargetVertex 4) < 0 := by
  simp [bentTetrahedraTargetVertex]

theorem bentTetrahedraVertex_affineIndependent_pos :
    AffineIndependent ℝ ((↑) : ↥(bentTetrahedraVertex ''
      ((({0, 1, 2, 3} : Finset (Fin 5))) : Set (Fin 5))) → EuclideanSpace ℝ (Fin 3)) := by
  refine affineIndependent_euclideanQuadruple (d₀ := 1) (d₁ := 1) (d₂ := 1) 0 one_ne_zero
    one_ne_zero one_ne_zero ?_
  simp [bentTetrahedraVertex, Set.image_insert_eq]

theorem bentTetrahedraVertex_affineIndependent_neg :
    AffineIndependent ℝ ((↑) : ↥(bentTetrahedraVertex ''
      ((({0, 1, 2, 4} : Finset (Fin 5))) : Set (Fin 5))) → EuclideanSpace ℝ (Fin 3)) := by
  refine affineIndependent_euclideanQuadruple (d₀ := 1) (d₁ := 1) (d₂ := -1) 0 one_ne_zero
    one_ne_zero (by norm_num) ?_
  simp [bentTetrahedraVertex, Set.image_insert_eq]

theorem bentTetrahedraTargetVertex_affineIndependent_pos :
    AffineIndependent ℝ ((↑) : ↥(bentTetrahedraTargetVertex ''
      ((({0, 1, 2, 3} : Finset (Fin 5))) : Set (Fin 5))) → EuclideanSpace ℝ (Fin 3)) := by
  refine affineIndependent_euclideanQuadruple (d₀ := 1) (d₁ := 1) (d₂ := 1)
    (EuclideanSpace.single 0 4) one_ne_zero one_ne_zero one_ne_zero ?_
  simp [bentTetrahedraTargetVertex, Set.image_insert_eq]

theorem bentTetrahedraTargetVertex_affineIndependent_neg :
    AffineIndependent ℝ ((↑) : ↥(bentTetrahedraTargetVertex ''
      ((({0, 1, 2, 4} : Finset (Fin 5))) : Set (Fin 5))) → EuclideanSpace ℝ (Fin 3)) := by
  refine affineIndependent_euclideanQuadruple (d₀ := 1) (d₁ := 1) (d₂ := -2)
    (EuclideanSpace.single 0 4) one_ne_zero one_ne_zero (by norm_num) ?_
  simp [bentTetrahedraTargetVertex, Set.image_insert_eq]

end Vertices

section Labels

abbrev BentTetrahedraLabel : Type :=
  {J : Finset (Fin 5) // J.Nonempty ∧ ¬ ({3, 4} : Finset (Fin 5)) ⊆ J}

def bentTetrahedraDim (l : BentTetrahedraLabel) : ℕ := l.1.card - 1

def bentTetrahedraFace (l : BentTetrahedraLabel) : Set BentTetrahedraLabel := {m | m.1 ⊆ l.1}

noncomputable def bentTetrahedraSourceCell (l : BentTetrahedraLabel) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  convexHull ℝ (bentTetrahedraVertex '' ((l.1 : Finset (Fin 5)) : Set (Fin 5)))

noncomputable def bentTetrahedraTargetCell (l : BentTetrahedraLabel) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  convexHull ℝ (bentTetrahedraTargetVertex '' ((l.1 : Finset (Fin 5)) : Set (Fin 5)))

theorem card_bentTetrahedraLabel : Fintype.card BentTetrahedraLabel = 23 := by decide

theorem bentTetrahedraDim_le_three (l : BentTetrahedraLabel) : bentTetrahedraDim l ≤ 3 := by
  have h := card_le_four_of_not_subset l.2.2
  simp only [bentTetrahedraDim]
  omega

theorem bentTetrahedraDim_add_one (l : BentTetrahedraLabel) :
    bentTetrahedraDim l + 1 = l.1.card := by
  have h : 1 ≤ l.1.card := Finset.card_pos.mpr l.2.1
  simp only [bentTetrahedraDim]
  omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem biUnion_convexHull_image_erase (w : Fin 5 → E) (l : BentTetrahedraLabel) :
    (⋃ i ∈ l.1, convexHull ℝ (w '' ((l.1.erase i : Finset (Fin 5)) : Set (Fin 5)))) =
      ⋃ m ∈ bentTetrahedraFace l \ {l},
        convexHull ℝ (w '' ((m.1 : Finset (Fin 5)) : Set (Fin 5))) := by
  refine Subset.antisymm (iUnion₂_subset fun i hi => ?_) (iUnion₂_subset fun m hm => ?_)
  · rcases Finset.eq_empty_or_nonempty (l.1.erase i) with he | hne
    · rw [he]
      simp
    · have hval : ¬ ({3, 4} : Finset (Fin 5)) ⊆ l.1.erase i := fun h =>
        l.2.2 (h.trans (Finset.erase_subset i l.1))
      refine subset_iUnion₂ (s := fun m (_ : m ∈ bentTetrahedraFace l \ {l}) =>
          convexHull ℝ (w '' ((m.1 : Finset (Fin 5)) : Set (Fin 5))))
        (⟨l.1.erase i, hne, hval⟩ : BentTetrahedraLabel)
        ⟨Finset.erase_subset i l.1, ?_⟩
      intro hmem
      have heq : l.1.erase i = l.1 := congrArg Subtype.val (Set.mem_singleton_iff.mp hmem)
      rw [← heq] at hi
      exact Finset.notMem_erase i l.1 hi
  · have hsub : m.1 ⊆ l.1 := hm.1
    have hne : m.1 ≠ l.1 := fun h => hm.2 (Set.mem_singleton_iff.mpr (Subtype.ext h))
    obtain ⟨i, hi, hin⟩ :=
      Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    refine subset_trans (convexHull_mono (image_mono ?_))
      (subset_iUnion₂ (s := fun j (_ : j ∈ l.1) =>
        convexHull ℝ (w '' ((l.1.erase j : Finset (Fin 5)) : Set (Fin 5)))) i hi)
    exact Finset.coe_subset.mpr fun k hk => Finset.mem_erase.mpr ⟨fun h => hin (h ▸ hk), hsub hk⟩

theorem biUnion_convexHull_image_face_inter (w : Fin 5 → E) (l m : BentTetrahedraLabel) :
    (⋃ k ∈ bentTetrahedraFace l ∩ bentTetrahedraFace m,
        convexHull ℝ (w '' ((k.1 : Finset (Fin 5)) : Set (Fin 5)))) =
      convexHull ℝ (w '' ((l.1 ∩ m.1 : Finset (Fin 5)) : Set (Fin 5))) := by
  refine Subset.antisymm (iUnion₂_subset fun k hk => ?_) ?_
  · exact convexHull_mono (image_mono (Finset.coe_subset.mpr (Finset.subset_inter hk.1 hk.2)))
  · rcases Finset.eq_empty_or_nonempty (l.1 ∩ m.1) with he | hne
    · rw [he]
      simp
    · have hval : ¬ ({3, 4} : Finset (Fin 5)) ⊆ l.1 ∩ m.1 := fun h =>
        l.2.2 (h.trans Finset.inter_subset_left)
      exact subset_iUnion₂ (s := fun k (_ : k ∈ bentTetrahedraFace l ∩ bentTetrahedraFace m) =>
          convexHull ℝ (w '' ((k.1 : Finset (Fin 5)) : Set (Fin 5))))
        (⟨l.1 ∩ m.1, hne, hval⟩ : BentTetrahedraLabel)
        ⟨Finset.inter_subset_left, Finset.inter_subset_right⟩

end Labels

section Assembly

theorem bentTetrahedraSourceCell_affineIndependent (l : BentTetrahedraLabel) :
    AffineIndependent ℝ ((↑) : ↥(bentTetrahedraVertex ''
      ((l.1 : Finset (Fin 5)) : Set (Fin 5))) → EuclideanSpace ℝ (Fin 3)) := by
  rcases subset_pos_or_neg_of_not_subset l.2.2 with h | h
  · exact bentTetrahedraVertex_affineIndependent_pos.mono
      (image_mono (Finset.coe_subset.mpr h))
  · exact bentTetrahedraVertex_affineIndependent_neg.mono
      (image_mono (Finset.coe_subset.mpr h))

theorem bentTetrahedraTargetCell_affineIndependent (l : BentTetrahedraLabel) :
    AffineIndependent ℝ ((↑) : ↥(bentTetrahedraTargetVertex ''
      ((l.1 : Finset (Fin 5)) : Set (Fin 5))) → EuclideanSpace ℝ (Fin 3)) := by
  rcases subset_pos_or_neg_of_not_subset l.2.2 with h | h
  · exact bentTetrahedraTargetVertex_affineIndependent_pos.mono
      (image_mono (Finset.coe_subset.mpr h))
  · exact bentTetrahedraTargetVertex_affineIndependent_neg.mono
      (image_mono (Finset.coe_subset.mpr h))

theorem isPLBall_bentTetrahedraSourceCell (l : BentTetrahedraLabel) :
    IsPLBall (bentTetrahedraDim l) (bentTetrahedraSourceCell l) := by
  classical
  have hcard : (l.1.image bentTetrahedraVertex).card = bentTetrahedraDim l + 1 := by
    rw [Finset.card_image_of_injective _ bentTetrahedraVertex_injective,
      bentTetrahedraDim_add_one l]
  have hT : AffineIndependent ℝ
      ((↑) : ↥(l.1.image bentTetrahedraVertex : Finset (EuclideanSpace ℝ (Fin 3))) →
        EuclideanSpace ℝ (Fin 3)) :=
    (bentTetrahedraSourceCell_affineIndependent l).mono
      (Finset.coe_image (f := bentTetrahedraVertex) (s := l.1)).subset
  have h := isPLBall_convexHull_of_affineIndependent _ hT hcard
  rwa [Finset.coe_image] at h

theorem isPLBall_bentTetrahedraTargetCell (l : BentTetrahedraLabel) :
    IsPLBall (bentTetrahedraDim l) (bentTetrahedraTargetCell l) := by
  classical
  have hcard : (l.1.image bentTetrahedraTargetVertex).card = bentTetrahedraDim l + 1 := by
    rw [Finset.card_image_of_injective _ bentTetrahedraTargetVertex_injective,
      bentTetrahedraDim_add_one l]
  have hT : AffineIndependent ℝ
      ((↑) : ↥(l.1.image bentTetrahedraTargetVertex : Finset (EuclideanSpace ℝ (Fin 3))) →
        EuclideanSpace ℝ (Fin 3)) :=
    (bentTetrahedraTargetCell_affineIndependent l).mono
      (Finset.coe_image (f := bentTetrahedraTargetVertex) (s := l.1)).subset
  have h := isPLBall_convexHull_of_affineIndependent _ hT hcard
  rwa [Finset.coe_image] at h

theorem bentTetrahedraSourceCell_inter (l m : BentTetrahedraLabel) :
    bentTetrahedraSourceCell l ∩ bentTetrahedraSourceCell m =
      ⋃ k ∈ bentTetrahedraFace l ∩ bentTetrahedraFace m, bentTetrahedraSourceCell k := by
  simp only [bentTetrahedraSourceCell]
  rw [biUnion_convexHull_image_face_inter bentTetrahedraVertex l m]
  exact convexHull_image_inter_of_bent bentTetrahedraVertex_injective
    (EuclideanSpace.proj (2 : Fin 3)).toLinearMap bentTetrahedraVertex_affineIndependent_pos
    bentTetrahedraVertex_affineIndependent_neg bentTetrahedraVertex_height_base
    bentTetrahedraVertex_height_pos bentTetrahedraVertex_height_neg l.2.2 m.2.2

theorem bentTetrahedraTargetCell_inter (l m : BentTetrahedraLabel) :
    bentTetrahedraTargetCell l ∩ bentTetrahedraTargetCell m =
      ⋃ k ∈ bentTetrahedraFace l ∩ bentTetrahedraFace m, bentTetrahedraTargetCell k := by
  simp only [bentTetrahedraTargetCell]
  rw [biUnion_convexHull_image_face_inter bentTetrahedraTargetVertex l m]
  exact convexHull_image_inter_of_bent bentTetrahedraTargetVertex_injective
    (EuclideanSpace.proj (2 : Fin 3)).toLinearMap
    bentTetrahedraTargetVertex_affineIndependent_pos
    bentTetrahedraTargetVertex_affineIndependent_neg bentTetrahedraTargetVertex_height_base
    bentTetrahedraTargetVertex_height_pos bentTetrahedraTargetVertex_height_neg l.2.2 m.2.2

theorem exists_isPLHomeomorphInto_bentTetrahedra :
    ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphInto 3 f (⋃ l, bentTetrahedraSourceCell l) ∧
        ∀ l, f '' bentTetrahedraSourceCell l = bentTetrahedraTargetCell l := by
  classical
  choose r hr using isPLBall_bentTetrahedraSourceCell
  choose s hs using isPLBall_bentTetrahedraTargetCell
  refine exists_isPLHomeomorphInto_of_labelledCells bentTetrahedraDim bentTetrahedraFace
    bentTetrahedraSourceCell bentTetrahedraTargetCell r s (fun _ => id) (fun _ => id)
    bentTetrahedraSourceCell bentTetrahedraTargetCell bentTetrahedraDim_le_three hr hs
    (fun l => isPLHomeomorphInto_id_of_isPolyhedron (IsPLBall.isPolyhedron ⟨r l, hr l⟩))
    (fun l => isPLHomeomorphInto_id_of_isPolyhedron (IsPLBall.isPolyhedron ⟨s l, hs l⟩))
    (fun l => (image_id _).symm) (fun l => (image_id _).symm) ?_ ?_ ?_
    bentTetrahedraSourceCell_inter bentTetrahedraTargetCell_inter
    (fun x _ => ⟨univ, Filter.univ_mem, Set.toFinite _⟩)
    (fun y _ => ⟨univ, Filter.univ_mem, Set.toFinite _⟩)
  · intro l m hm
    rcases eq_or_ne m.1 l.1 with h | h
    · exact Or.inl (Subtype.ext h)
    · refine Or.inr ?_
      have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hm, h⟩)
      have h1 : 1 ≤ m.1.card := Finset.card_pos.mpr m.2.1
      simp only [bentTetrahedraDim]
      omega
  · intro l
    rw [image_id]
    simp only [bentTetrahedraSourceCell]
    rw [← biUnion_convexHull_image_erase bentTetrahedraVertex l]
    exact image_stdSimplexBoundary_eq_biUnion_erase bentTetrahedraVertex_injective
      (bentTetrahedraSourceCell_affineIndependent l) (bentTetrahedraDim_add_one l).symm (hr l)
  · intro l
    rw [image_id]
    simp only [bentTetrahedraTargetCell]
    rw [← biUnion_convexHull_image_erase bentTetrahedraTargetVertex l]
    exact image_stdSimplexBoundary_eq_biUnion_erase bentTetrahedraTargetVertex_injective
      (bentTetrahedraTargetCell_affineIndependent l) (bentTetrahedraDim_add_one l).symm (hs l)

end Assembly

section NonDegeneracy

theorem exists_bentTetrahedra_top_cells_inter_eq :
    ∃ l m k : BentTetrahedraLabel, l ≠ m ∧ bentTetrahedraDim l = 3 ∧ bentTetrahedraDim m = 3 ∧
      bentTetrahedraDim k = 2 ∧
      bentTetrahedraSourceCell l ∩ bentTetrahedraSourceCell m = bentTetrahedraSourceCell k := by
  refine ⟨⟨{0, 1, 2, 3}, by decide⟩, ⟨{0, 1, 2, 4}, by decide⟩, ⟨{0, 1, 2}, by decide⟩,
    by decide, by decide, by decide, by decide, ?_⟩
  have h := convexHull_image_inter_of_bent (w := bentTetrahedraVertex)
    bentTetrahedraVertex_injective (EuclideanSpace.proj (2 : Fin 3)).toLinearMap
    bentTetrahedraVertex_affineIndependent_pos bentTetrahedraVertex_affineIndependent_neg
    bentTetrahedraVertex_height_base bentTetrahedraVertex_height_pos
    bentTetrahedraVertex_height_neg
    (I := ({0, 1, 2, 3} : Finset (Fin 5))) (J := ({0, 1, 2, 4} : Finset (Fin 5)))
    (by decide) (by decide)
  have hinter : ({0, 1, 2, 3} : Finset (Fin 5)) ∩ {0, 1, 2, 4} = {0, 1, 2} := by decide
  simp only [bentTetrahedraSourceCell]
  rw [h, hinter]

theorem not_exists_affineMap_image_eq_bentTetrahedraTargetCell :
    ¬ ∃ F : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
      ∀ l : BentTetrahedraLabel, bentTetrahedraDim l = 0 →
        F '' bentTetrahedraSourceCell l = bentTetrahedraTargetCell l := by
  rintro ⟨F, hF⟩
  have hcell : ∀ i : Fin 5, ∀ h : ({i} : Finset (Fin 5)).Nonempty ∧
      ¬ ({3, 4} : Finset (Fin 5)) ⊆ {i}, F (bentTetrahedraVertex i) =
        bentTetrahedraTargetVertex i := by
    intro i h
    have hi := hF ⟨{i}, h⟩ (by simp [bentTetrahedraDim])
    simp only [bentTetrahedraSourceCell, bentTetrahedraTargetCell, Finset.coe_singleton,
      Set.image_singleton, convexHull_singleton] at hi
    exact (Set.singleton_eq_singleton_iff.mp hi)
  have h0 := hcell 0 (by decide)
  have h3 := hcell 3 (by decide)
  have h4 := hcell 4 (by decide)
  have hline : bentTetrahedraVertex 4 =
      AffineMap.lineMap (bentTetrahedraVertex 0) (bentTetrahedraVertex 3) (-1 : ℝ) := by
    rw [AffineMap.lineMap_apply]
    change (EuclideanSpace.single 2 (-1) : EuclideanSpace ℝ (Fin 3)) =
      (-1 : ℝ) • (EuclideanSpace.single 2 1 -ᵥ (0 : EuclideanSpace ℝ (Fin 3))) +ᵥ
        (0 : EuclideanSpace ℝ (Fin 3))
    rw [vsub_eq_sub, sub_zero, vadd_eq_add, add_zero, neg_one_smul, ← PiLp.single_neg]
  have hkey : bentTetrahedraTargetVertex 4 =
      AffineMap.lineMap (bentTetrahedraTargetVertex 0) (bentTetrahedraTargetVertex 3)
        (-1 : ℝ) := by
    rw [← h4, hline, AffineMap.apply_lineMap, h0, h3]
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at hkey
  have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hkey
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hcoord
  rw [show (bentTetrahedraTargetVertex 4) 2 = -2 from by
      simp [bentTetrahedraTargetVertex],
    show (bentTetrahedraTargetVertex 3) 2 = 1 from by
      simp [bentTetrahedraTargetVertex],
    show (bentTetrahedraTargetVertex 0) 2 = 0 from by
      simp [bentTetrahedraTargetVertex]] at hcoord
  norm_num at hcoord

end NonDegeneracy

end DifferentialGeometry.Topology.PiecewiseLinear
