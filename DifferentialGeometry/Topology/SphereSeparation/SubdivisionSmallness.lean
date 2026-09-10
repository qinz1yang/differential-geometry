import DifferentialGeometry.Topology.SphereSeparation.SubdivisionOperator
import DifferentialGeometry.Topology.SphereSeparation.SpecializedDuality
import DifferentialGeometry.Topology.SphereSeparation.LocallyNilpotentHomotopy
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open CategoryTheory
open CategoryTheory.Limits
open Simplicial
open scoped Simplicial

namespace DifferentialGeometry.Topology.SphereSeparation




abbrev BarycentricWord (n k : ℕ) :=
  Fin k → Equiv.Perm (Fin (n + 1))

noncomputable def iteratedBarycentricSimplexMap (n : ℕ) :
    (k : ℕ) → BarycentricWord n k →
      C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 1))) :=
  Nat.rec (motive := fun k ↦ BarycentricWord n k →
      C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 1))))
    (fun _ ↦ ContinuousMap.id _)
    (fun k previous w ↦
      (previous (fun i ↦ w i.castSucc)).comp
        (barycentricPermutationSimplexMap (w (Fin.last k))))

@[simp]
theorem iteratedBarycentricSimplexMap_zero
    (n : ℕ) (w : BarycentricWord n 0) :
    iteratedBarycentricSimplexMap n 0 w = ContinuousMap.id _ :=
  rfl

theorem iteratedBarycentricSimplexMap_succ
    (n k : ℕ) (w : BarycentricWord n (k + 1)) :
    iteratedBarycentricSimplexMap n (k + 1) w =
      (iteratedBarycentricSimplexMap n k (fun i ↦ w i.castSucc)).comp
        (barycentricPermutationSimplexMap (w (Fin.last k))) :=
  rfl

theorem range_iteratedBarycentricSimplexMap_succ_subset
    (n k : ℕ) (w : BarycentricWord n (k + 1)) :
    Set.range (iteratedBarycentricSimplexMap n (k + 1) w) ⊆
      Set.range (iteratedBarycentricSimplexMap n k
        (fun i ↦ w i.castSucc)) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨barycentricPermutationSimplexMap (w (Fin.last k)) x, rfl⟩


noncomputable def singularSimplexIteratedBarycentricPiece
    {X : Type} [TopologicalSpace X] {n k : ℕ}
    (s : C(stdSimplex ℝ (Fin (n + 1)), X))
    (w : BarycentricWord n k) :
    C(stdSimplex ℝ (Fin (n + 1)), X) :=
  s.comp (iteratedBarycentricSimplexMap n k w)

theorem range_singularSimplexIteratedBarycentricPiece_subset
    {X : Type} [TopologicalSpace X] {n k : ℕ}
    (s : C(stdSimplex ℝ (Fin (n + 1)), X))
    (w : BarycentricWord n k) :
    Set.range (singularSimplexIteratedBarycentricPiece s w) ⊆
      Set.range s := by
  rintro _ ⟨x, rfl⟩
  exact ⟨iteratedBarycentricSimplexMap n k w x, rfl⟩

theorem singularSimplexIteratedBarycentricPiece_smallFor_twoSets
    {X : Type} [TopologicalSpace X] {n k : ℕ}
    (V W : Set X) (s : C(stdSimplex ℝ (Fin (n + 1)), X))
    (w : BarycentricWord n k)
    (hs : SingularSimplexSmallFor V W s) :
    SingularSimplexSmallFor V W
      (singularSimplexIteratedBarycentricPiece s w) :=
  hs.imp
    ((range_singularSimplexIteratedBarycentricPiece_subset s w).trans)
    ((range_singularSimplexIteratedBarycentricPiece_subset s w).trans)



noncomputable def barycentricResidual {n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    stdSimplex ℝ (Fin (n + 1)) := by
  let b := nonemptyFaceBarycenter (barycentricPrefix σ k)
    (barycentricPrefix_nonempty σ k)
  let e : stdSimplex ℝ (Fin (n + 1)) :=
    stdSimplex.vertex (S := ℝ) (σ 0)
  let a : ℝ := ((n : ℝ) + 1)⁻¹
  let q : ℝ := barycentricContractionFactor n
  have hq : 0 < q := div_pos (Nat.cast_pos.2 hn) (by positivity)
  refine ⟨fun i ↦ (b i - a * e i) / q, ?_⟩
  constructor
  · intro i
    apply div_nonneg _ hq.le
    by_cases hi : i = σ 0
    · subst i
      simp only [b, a, barycentricPrefixBarycenter_apply,
        Equiv.symm_apply_apply, Fin.zero_le, ↓reduceIte]
      have he : e (σ 0) = 1 := by simp [e]
      rw [he, mul_one]
      apply sub_nonneg.2
      apply (inv_le_inv₀ (by positivity) (by positivity)).2
      exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt_succ k.isLt) 1
    · have hvertex : e i = 0 := by
        simp [e, hi]
      rw [hvertex, mul_zero, sub_zero]
      exact (stdSimplex.zero_le b i)
  · simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
      stdSimplex.sum_eq_one, stdSimplex.sum_eq_one e, mul_one]
    dsimp only [q, a, barycentricContractionFactor]
    field_simp
    ring

theorem barycentricPrefixBarycenter_eq_common_add_residual
    {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    (nonemptyFaceBarycenter (barycentricPrefix σ k)
        (barycentricPrefix_nonempty σ k) : Fin (n + 1) → ℝ) =
      fun i ↦ ((n : ℝ) + 1)⁻¹ * stdSimplex.vertex (σ 0) i +
        barycentricContractionFactor n * barycentricResidual hn σ k i := by
  funext i
  change _ = ((n : ℝ) + 1)⁻¹ * stdSimplex.vertex (σ 0) i +
    barycentricContractionFactor n *
      ((nonemptyFaceBarycenter (barycentricPrefix σ k)
        (barycentricPrefix_nonempty σ k) i -
          ((n : ℝ) + 1)⁻¹ * stdSimplex.vertex (σ 0) i) /
            barycentricContractionFactor n)
  have hq : barycentricContractionFactor n ≠ 0 :=
    ne_of_gt (div_pos (Nat.cast_pos.2 hn) (by positivity))
  field_simp
  ring

theorem affineStandardSimplexMap_barycentricPrefixBarycenter
    {n : ℕ} (hn : 0 < n)
    (v : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)))
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    (affineStandardSimplexMap v
      (nonemptyFaceBarycenter (barycentricPrefix σ k)
        (barycentricPrefix_nonempty σ k)) : Fin (n + 1) → ℝ) =
      fun i ↦ ((n : ℝ) + 1)⁻¹ * v (σ 0) i +
        barycentricContractionFactor n *
          affineStandardSimplexMap v (barycentricResidual hn σ k) i := by
  classical
  funext i
  rw [affineStandardSimplexMap_apply]
  simp_rw [congr_fun
    (barycentricPrefixBarycenter_eq_common_add_residual hn σ k)]
  calc
    (∑ j, (((n : ℝ) + 1)⁻¹ * stdSimplex.vertex (σ 0) j +
        barycentricContractionFactor n * barycentricResidual hn σ k j) *
          v j i) =
      ((n : ℝ) + 1)⁻¹ *
          ∑ j, stdSimplex.vertex (σ 0) j * v j i +
        barycentricContractionFactor n *
          ∑ j, barycentricResidual hn σ k j * v j i := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = ((n : ℝ) + 1)⁻¹ * v (σ 0) i +
        barycentricContractionFactor n *
          affineStandardSimplexMap v (barycentricResidual hn σ k) i := by
      rw [← affineStandardSimplexMap_apply,
        affineStandardSimplexMap_vertex,
        affineStandardSimplexMap_apply]

theorem dist_affineStandardSimplexMap_barycentricVertices_le
    {n : ℕ} (hn : 0 < n)
    (v : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)))
    (σ : Equiv.Perm (Fin (n + 1))) (k l : Fin (n + 1)) :
    dist
        (affineStandardSimplexMap v
          (nonemptyFaceBarycenter (barycentricPrefix σ k)
            (barycentricPrefix_nonempty σ k)))
        (affineStandardSimplexMap v
          (nonemptyFaceBarycenter (barycentricPrefix σ l)
            (barycentricPrefix_nonempty σ l))) ≤
      barycentricContractionFactor n *
        Metric.diam (Set.range (affineStandardSimplexMap v)) := by
  let f := affineStandardSimplexMap v
  let q := barycentricContractionFactor n
  let a : ℝ := ((n : ℝ) + 1)⁻¹
  let zk := barycentricResidual hn σ k
  let zl := barycentricResidual hn σ l
  have hq : 0 ≤ q := barycentricContractionFactor_nonneg n
  have hk := affineStandardSimplexMap_barycentricPrefixBarycenter hn v σ k
  have hl := affineStandardSimplexMap_barycentricPrefixBarycenter hn v σ l
  have hdist : dist (f zk) (f zl) ≤ Metric.diam (Set.range f) :=
    Metric.dist_le_diam_of_mem (isCompact_range f.continuous).isBounded
      ⟨zk, rfl⟩ ⟨zl, rfl⟩
  rw [Subtype.dist_eq]
  change dist
    (affineStandardSimplexMap v
      (nonemptyFaceBarycenter (barycentricPrefix σ k)
        (barycentricPrefix_nonempty σ k)) : Fin (n + 1) → ℝ)
    (affineStandardSimplexMap v
      (nonemptyFaceBarycenter (barycentricPrefix σ l)
        (barycentricPrefix_nonempty σ l)) : Fin (n + 1) → ℝ) ≤ _
  rw [hk, hl]
  change dist (fun i ↦ a * v (σ 0) i + q * f zk i)
      (fun i ↦ a * v (σ 0) i + q * f zl i) ≤ q * Metric.diam (Set.range f)
  have heq : dist (fun i ↦ a * v (σ 0) i + q * f zk i)
      (fun i ↦ a * v (σ 0) i + q * f zl i) = q * dist (f zk) (f zl) := by
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    have hfun :
        (fun i ↦ a * v (σ 0) i + q * f zk i -
          (a * v (σ 0) i + q * f zl i)) =
        q • ((f zk : Fin (n + 1) → ℝ) - (f zl : Fin (n + 1) → ℝ)) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      ring
    change ‖(fun i ↦ a * v (σ 0) i + q * f zk i -
      (a * v (σ 0) i + q * f zl i))‖ =
        q * ‖(f zk : Fin (n + 1) → ℝ) - (f zl : Fin (n + 1) → ℝ)‖
    rw [hfun, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
  rw [heq]
  exact mul_le_mul_of_nonneg_left hdist hq

theorem affineStandardSimplexMap_comp
    {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (v : κ → stdSimplex ℝ μ) (u : ι → stdSimplex ℝ κ) :
    (affineStandardSimplexMap v).comp (affineStandardSimplexMap u) =
      affineStandardSimplexMap (fun i ↦ affineStandardSimplexMap v (u i)) := by
  classical
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  funext a
  simp only [ContinuousMap.comp_apply]
  calc
    (∑ j, (∑ i, x i * u i j) * v j a) =
        ∑ j, ∑ i, (x i * u i j) * v j a := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, (x i * u i j) * v j a := Finset.sum_comm
    _ = ∑ i, x i * ∑ j, u i j * v j a := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring


theorem affineStandardSimplexMap_vertex_eq_id
    {ι : Type} [Fintype ι] [DecidableEq ι] :
    affineStandardSimplexMap
        (fun i : ι ↦ stdSimplex.vertex (S := ℝ) i) =
      ContinuousMap.id (stdSimplex ℝ ι) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  funext a
  change (∑ i, x i * stdSimplex.vertex (S := ℝ) i a) = x a
  classical
  rw [Finset.sum_eq_single a]
  · simp [stdSimplex.vertex]
  · intro b _ hba
    simp [stdSimplex.vertex, hba]
  · simp


theorem exists_affineStandardSimplexMap_eq_iterated
    (n k : ℕ) (w : BarycentricWord n k) :
    ∃ v : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)),
      iteratedBarycentricSimplexMap n k w = affineStandardSimplexMap v := by
  induction k with
  | zero =>
      refine ⟨fun i ↦ stdSimplex.vertex (S := ℝ) i, ?_⟩
      rw [iteratedBarycentricSimplexMap_zero,
        affineStandardSimplexMap_vertex_eq_id]
  | succ k ih =>
      obtain ⟨v, hv⟩ := ih (fun i ↦ w i.castSucc)
      refine ⟨fun i ↦ affineStandardSimplexMap v
        (nonemptyFaceBarycenter
          (barycentricPrefix (w (Fin.last k)) i)
          (barycentricPrefix_nonempty (w (Fin.last k)) i)), ?_⟩
      rw [iteratedBarycentricSimplexMap_succ, hv]
      change (affineStandardSimplexMap v).comp
          (affineStandardSimplexMap (fun i ↦
            nonemptyFaceBarycenter
              (barycentricPrefix (w (Fin.last k)) i)
              (barycentricPrefix_nonempty (w (Fin.last k)) i))) = _
      rw [affineStandardSimplexMap_comp]

theorem diam_range_affineStandardSimplexMap_comp_barycentric_le
    {n : ℕ} (hn : 0 < n)
    (v : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)))
    (σ : Equiv.Perm (Fin (n + 1))) :
    Metric.diam (Set.range ((affineStandardSimplexMap v).comp
      (barycentricPermutationSimplexMap σ))) ≤
        barycentricContractionFactor n *
          Metric.diam (Set.range (affineStandardSimplexMap v)) := by
  let r := barycentricContractionFactor n *
    Metric.diam (Set.range (affineStandardSimplexMap v))
  have hr : 0 ≤ r := mul_nonneg (barycentricContractionFactor_nonneg n)
    Metric.diam_nonneg
  rw [show barycentricPermutationSimplexMap σ =
      affineStandardSimplexMap (fun k ↦
        nonemptyFaceBarycenter (barycentricPrefix σ k)
          (barycentricPrefix_nonempty σ k)) by rfl,
    affineStandardSimplexMap_comp]
  apply Metric.diam_le_of_forall_dist_le hr
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  apply dist_affineStandardSimplexMap_le_of_pairwise _ hr
  intro k l i
  have hkl := dist_affineStandardSimplexMap_barycentricVertices_le
    hn v σ k l
  rw [Subtype.dist_eq] at hkl
  exact (dist_pi_le_iff hr).1 hkl i

private theorem diam_univ_stdSimplex_le (ι : Type) [Fintype ι] :
    Metric.diam (Set.univ : Set (stdSimplex ℝ ι)) ≤ 1 := by
  apply Metric.diam_le_of_forall_dist_le zero_le_one
  intro x _ y _
  rw [Subtype.dist_eq]
  exact (Metric.dist_le_diam_of_mem (bounded_stdSimplex (ι := ι))
    x.property y.property).trans diam_stdSimplex_le

theorem diam_range_iteratedBarycentricSimplexMap_le
    (n k : ℕ) (w : BarycentricWord n k) :
    Metric.diam (Set.range (iteratedBarycentricSimplexMap n k w)) ≤
      barycentricContractionFactor n ^ k := by
  by_cases hn : n = 0
  · subst n
    rw [Metric.diam_subsingleton (s :=
      Set.range (iteratedBarycentricSimplexMap 0 k w)) (by
        intro x _ y _
        exact Subsingleton.elim x y)]
    exact pow_nonneg (barycentricContractionFactor_nonneg 0) k
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    induction k with
    | zero =>
        rw [pow_zero]
        exact (Metric.diam_mono (Set.subset_univ _)
          isCompact_univ.isBounded).trans
            (diam_univ_stdSimplex_le (Fin (n + 1)))
    | succ k ih =>
        let w' : BarycentricWord n k := fun i ↦ w i.castSucc
        obtain ⟨v, hv⟩ :=
          exists_affineStandardSimplexMap_eq_iterated n k w'
        rw [iteratedBarycentricSimplexMap_succ, hv]
        calc
          Metric.diam (Set.range ((affineStandardSimplexMap v).comp
              (barycentricPermutationSimplexMap (w (Fin.last k))))) ≤
              barycentricContractionFactor n *
                Metric.diam (Set.range (affineStandardSimplexMap v)) :=
            diam_range_affineStandardSimplexMap_comp_barycentric_le
              hnpos v _
          _ ≤ barycentricContractionFactor n *
                barycentricContractionFactor n ^ k := by
            apply mul_le_mul_of_nonneg_left _
              (barycentricContractionFactor_nonneg n)
            rw [← hv]
            exact ih w'
          _ = barycentricContractionFactor n ^ (k + 1) := by
            rw [pow_succ]
            ring

theorem exists_pow_barycentricContractionFactor_lt
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, barycentricContractionFactor n ^ k < ε :=
  exists_pow_lt_of_lt_one hε (barycentricContractionFactor_lt_one n)

theorem standardSimplex_openCover_lebesgueNumber
    {n : ℕ} {ι : Sort*} (U : ι → Set (stdSimplex ℝ (Fin (n + 1))))
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : Set.univ ⊆ ⋃ i, U i) :
    ∃ δ > 0, ∀ x : stdSimplex ℝ (Fin (n + 1)),
      ∃ i, Metric.ball x δ ⊆ U i := by
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hUopen hUcover
  exact ⟨δ, hδ, fun x ↦ hball x (Set.mem_univ x)⟩

theorem subset_openCover_of_diam_lt_lebesgueNumber
    {Y : Type} [PseudoMetricSpace Y] {ι : Sort*}
    (U : ι → Set Y) {K : Set Y} (hK : K.Nonempty)
    (hKbounded : Bornology.IsBounded K)
    {δ : ℝ} (_hδ : 0 < δ)
    (hball : ∀ x ∈ K, ∃ i, Metric.ball x δ ⊆ U i)
    (hdiam : Metric.diam K < δ) :
    ∃ i, K ⊆ U i := by
  obtain ⟨x, hx⟩ := hK
  obtain ⟨i, hi⟩ := hball x hx
  refine ⟨i, fun y hy ↦ hi ?_⟩
  rw [Metric.mem_ball]
  rw [dist_comm]
  exact (Metric.dist_le_diam_of_mem hKbounded hx hy).trans_lt hdiam


theorem isCompact_range_iteratedBarycentricSimplexMap
    (n k : ℕ) (w : BarycentricWord n k) :
    IsCompact (Set.range (iteratedBarycentricSimplexMap n k w)) :=
  isCompact_range (iteratedBarycentricSimplexMap n k w).continuous

theorem iteratedBarycentricSimplexMap_subordinate_of_diam_lt
    {n k : ℕ} {ι : Sort*}
    (U : ι → Set (stdSimplex ℝ (Fin (n + 1))))
    (w : BarycentricWord n k) {δ : ℝ} (_hδ : 0 < δ)
    (hball : ∀ x : stdSimplex ℝ (Fin (n + 1)),
      ∃ i, Metric.ball x δ ⊆ U i)
    (hdiam : Metric.diam
      (Set.range (iteratedBarycentricSimplexMap n k w)) < δ) :
    ∃ i, Set.range (iteratedBarycentricSimplexMap n k w) ⊆ U i := by
  apply subset_openCover_of_diam_lt_lebesgueNumber U
    (Set.range_nonempty _) (isCompact_range_iteratedBarycentricSimplexMap n k w).isBounded
    _hδ (fun x _ ↦ hball x) hdiam

theorem singularSimplexIteratedBarycentricPiece_subordinate_of_diam_lt
    {X : Type} [TopologicalSpace X] {n : ℕ} {ι : Sort*}
    (U : ι → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (s : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ δ > 0, ∀ (k : ℕ) (w : BarycentricWord n k),
      Metric.diam (Set.range (iteratedBarycentricSimplexMap n k w)) < δ →
        ∃ i, Set.range (singularSimplexIteratedBarycentricPiece s w) ⊆ U i := by
  obtain ⟨δ, hδ, hball⟩ := standardSimplex_openCover_lebesgueNumber
    (fun i ↦ s ⁻¹' U i) (fun i ↦ (hUopen i).preimage s.continuous) (by
      intro x _
      have hx : s x ∈ ⋃ i, U i := hUcover (Set.mem_univ _)
      simpa only [Set.mem_iUnion, Set.mem_preimage] using hx)
  refine ⟨δ, hδ, fun k w hdiam ↦ ?_⟩
  obtain ⟨i, hi⟩ := iteratedBarycentricSimplexMap_subordinate_of_diam_lt
    (fun i ↦ s ⁻¹' U i) w hδ hball hdiam
  refine ⟨i, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact hi ⟨x, rfl⟩

theorem exists_iterate_singularSimplex_subordinate_openCover
    {X : Type} [TopologicalSpace X] {n : ℕ} {ι : Sort*}
    (U : ι → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (s : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ k : ℕ, ∀ w : BarycentricWord n k,
      ∃ i, Set.range (singularSimplexIteratedBarycentricPiece s w) ⊆ U i := by
  obtain ⟨δ, hδ, hsubordinate⟩ :=
    singularSimplexIteratedBarycentricPiece_subordinate_of_diam_lt
      U hUopen hUcover s
  obtain ⟨k, hk⟩ := exists_pow_barycentricContractionFactor_lt n hδ
  refine ⟨k, fun w ↦ hsubordinate k w ?_⟩
  exact (diam_range_iteratedBarycentricSimplexMap_le n k w).trans_lt hk

theorem exists_iterate_singularSimplex_smallFor_twoSetCover
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (V W : Set X) (hV : IsOpen V) (hW : IsOpen W)
    (hcover : V ∪ W = Set.univ)
    (s : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ k : ℕ, ∀ w : BarycentricWord n k,
      SingularSimplexSmallFor V W
        (singularSimplexIteratedBarycentricPiece s w) := by
  let U : Fin 2 → Set X := Fin.cases V (fun _ ↦ W)
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    fin_cases i
    · exact hV
    · exact hW
  have hUcover : Set.univ ⊆ ⋃ i, U i := by
    intro x _
    have hx : x ∈ V ∪ W := by rw [hcover]; exact Set.mem_univ x
    rcases hx with hx | hx
    · exact Set.mem_iUnion.2 ⟨0, hx⟩
    · exact Set.mem_iUnion.2 ⟨1, hx⟩
  obtain ⟨k, hk⟩ := exists_iterate_singularSimplex_subordinate_openCover
    U hUopen hUcover s
  refine ⟨k, fun w ↦ ?_⟩
  obtain ⟨i, hi⟩ := hk w
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr hi



noncomputable def iteratedBarycentricPieceOfSingularSimplex
    (X : TopCat) {n k : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) (w : BarycentricWord n k) :
    (TopCat.toSSet.obj X) _⦋n⦌ :=
  (X.toSSetObjEquiv _).symm
    (singularSimplexIteratedBarycentricPiece (X.toSSetObjEquiv _ s) w)

@[simp]
theorem toSSetObjEquiv_iteratedBarycentricPieceOfSingularSimplex
    (X : TopCat) {n k : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) (w : BarycentricWord n k) :
    X.toSSetObjEquiv _
        (iteratedBarycentricPieceOfSingularSimplex X s w) =
      singularSimplexIteratedBarycentricPiece (X.toSSetObjEquiv _ s) w :=
  Equiv.apply_symm_apply _ _

@[simp]
theorem iteratedBarycentricPieceOfSingularSimplex_zero
    (X : TopCat) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) (w : BarycentricWord n 0) :
    iteratedBarycentricPieceOfSingularSimplex X s w = s := by
  apply (X.toSSetObjEquiv _).injective
  simp [iteratedBarycentricPieceOfSingularSimplex,
    singularSimplexIteratedBarycentricPiece]

theorem iteratedBarycentricPieceOfSingularSimplex_succ
    (X : TopCat) {n k : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌)
    (w : BarycentricWord n (k + 1)) :
    iteratedBarycentricPieceOfSingularSimplex X s w =
      barycentricPieceOfSingularSimplex X
        (iteratedBarycentricPieceOfSingularSimplex X s
          (fun i ↦ w i.castSucc)) (w (Fin.last k)) := by
  apply (X.toSSetObjEquiv _).injective
  simp only [iteratedBarycentricPieceOfSingularSimplex,
    Equiv.apply_symm_apply, singularSimplexIteratedBarycentricPiece,
    iteratedBarycentricSimplexMap_succ,
    toSSetObjEquiv_barycentricPieceOfSingularSimplex,
    ContinuousMap.comp_assoc]

def barycentricWordSign {n k : ℕ} (w : BarycentricWord n k) : ℤ :=
  ∏ i, (Equiv.Perm.sign (w i) : ℤ)

@[simp]
theorem barycentricWordSign_zero {n : ℕ} (w : BarycentricWord n 0) :
    barycentricWordSign w = 1 := by
  simp [barycentricWordSign]

theorem barycentricWordSign_snoc {n k : ℕ}
    (w : BarycentricWord n k) (σ : Equiv.Perm (Fin (n + 1))) :
    barycentricWordSign (Fin.snoc w σ) =
      barycentricWordSign w * (Equiv.Perm.sign σ : ℤ) := by
  simp [barycentricWordSign, Fin.prod_univ_castSucc]

theorem ιChainComplex_singularBarycentricSubdivisionIterate
    (X : TopCat) {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n⦌)
    (k : ℕ) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s ≫
        (singularBarycentricSubdivisionIterate X k).f n =
      ∑ w : BarycentricWord n k,
        barycentricWordSign w •
          (TopCat.toSSet.obj X).ιChainComplex
            (R := ModuleCat.of ℤ ℤ)
            (iteratedBarycentricPieceOfSingularSimplex X s w) := by
  classical
  induction k with
  | zero =>
      rw [singularBarycentricSubdivisionIterate_zero]
      simp only [HomologicalComplex.id_f,
        Fintype.sum_unique, barycentricWordSign_zero, one_smul,
        iteratedBarycentricPieceOfSingularSimplex_zero]
      exact Category.comp_id _
  | succ k ih =>
      rw [singularBarycentricSubdivisionIterate_succ,
        HomologicalComplex.comp_f]
      erw [← Category.assoc, ih]
      change (∑ w : BarycentricWord n k,
          barycentricWordSign w •
            (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              (iteratedBarycentricPieceOfSingularSimplex X s w)) ≫
            barycentricSubdivisionDegreeMap X n =
        ∑ w : BarycentricWord n (k + 1),
          barycentricWordSign w •
            (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              (iteratedBarycentricPieceOfSingularSimplex X s w)
      rw [Preadditive.sum_comp]
      simp only [Preadditive.zsmul_comp,
        ιChainComplex_barycentricSubdivisionDegreeMap]
      rw [← Equiv.sum_comp
        (Fin.snocEquiv (fun _ : Fin (k + 1) ↦
          Equiv.Perm (Fin (n + 1)))), Fintype.sum_prod_type,
        Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      have hsnoc :
          (Fin.snocEquiv (fun _ : Fin (k + 1) ↦
            Equiv.Perm (Fin (n + 1)))) (σ, w) = Fin.snoc w σ := by
        rfl
      rw [smul_smul, hsnoc, barycentricWordSign_snoc,
        iteratedBarycentricPieceOfSingularSimplex_succ]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem mem_smallSingularSubcomplex_of_smallFor
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌)
    (hs : SingularSimplexSmallFor V W (X.toSSetObjEquiv _ s)) :
    s ∈ (smallSingularSubcomplex X V W).obj
      (Opposite.op (SimplexCategory.mk n)) := by
  rcases hs with hs | hs
  · apply Or.inl
    let t := topologicalSingularSimplexLift (X.toSSetObjEquiv _ s) V hs
    let u := ((TopCat.of V).toSSetObjEquiv _).symm t
    refine ⟨u, ?_⟩
    apply (X.toSSetObjEquiv _).injective
    ext x
    rfl
  · apply Or.inr
    let t := topologicalSingularSimplexLift (X.toSSetObjEquiv _ s) W hs
    let u := ((TopCat.of W).toSSetObjEquiv _).symm t
    refine ⟨u, ?_⟩
    apply (X.toSSetObjEquiv _).injective
    ext x
    rfl

theorem smallFor_of_mem_smallSingularSubcomplex
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌)
    (hs : s ∈ (smallSingularSubcomplex X V W).obj
      (Opposite.op (SimplexCategory.mk n))) :
    SingularSimplexSmallFor V W (X.toSSetObjEquiv _ s) := by
  rcases hs with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · left
    rintro _ ⟨x, rfl⟩
    change (((TopCat.of V).toSSetObjEquiv _ u x : V) : X) ∈ V
    exact ((TopCat.of V).toSSetObjEquiv _ u x).property
  · right
    rintro _ ⟨x, rfl⟩
    change (((TopCat.of W).toSSetObjEquiv _ u x : W) : X) ∈ W
    exact ((TopCat.of W).toSSetObjEquiv _ u x).property

noncomputable def smallIteratedBarycentricSimplex
    (X : TopCat) (V W : Set X) {n k : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) (w : BarycentricWord n k)
    (hw : SingularSimplexSmallFor V W
      (singularSimplexIteratedBarycentricPiece (X.toSSetObjEquiv _ s) w)) :
    (smallSingularSubcomplex X V W : SSet) _⦋n⦌ :=
  ⟨iteratedBarycentricPieceOfSingularSimplex X s w,
    mem_smallSingularSubcomplex_of_smallFor X V W _ (by
      simpa only [toSSetObjEquiv_iteratedBarycentricPieceOfSingularSimplex]
        using hw)⟩

noncomputable def smallChainLiftOfSubdivisionGenerator
    (X : TopCat) (V W : Set X) {n k : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌)
    (hsmall : ∀ w : BarycentricWord n k,
      SingularSimplexSmallFor V W
        (singularSimplexIteratedBarycentricPiece (X.toSSetObjEquiv _ s) w)) :
    ModuleCat.of ℤ ℤ ⟶ (smallSingularChainComplex X V W).X n :=
  ∑ w : BarycentricWord n k,
    barycentricWordSign w •
      (smallSingularSubcomplex X V W : SSet).ιChainComplex
        (R := ModuleCat.of ℤ ℤ)
        (smallIteratedBarycentricSimplex X V W s w (hsmall w))

theorem smallChainLiftOfSubdivisionGenerator_comp_inclusion
    (X : TopCat) (V W : Set X) {n k : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌)
    (hsmall : ∀ w : BarycentricWord n k,
      SingularSimplexSmallFor V W
        (singularSimplexIteratedBarycentricPiece (X.toSSetObjEquiv _ s) w)) :
    smallChainLiftOfSubdivisionGenerator X V W s hsmall ≫
        (smallSingularChainInclusion X V W).f n =
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s ≫
        (singularBarycentricSubdivisionIterate X k).f n := by
  rw [ιChainComplex_singularBarycentricSubdivisionIterate]
  unfold smallChainLiftOfSubdivisionGenerator
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro w _
  rw [Preadditive.zsmul_comp]
  change barycentricWordSign w •
      ((smallSingularSubcomplex X V W : SSet).ιChainComplex
          (R := ModuleCat.of ℤ ℤ)
          (smallIteratedBarycentricSimplex X V W s w (hsmall w)) ≫
        (SSet.chainComplexMap (smallSingularSubcomplex X V W).ι
          (ModuleCat.of ℤ ℤ)).f n) = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

theorem exists_iterate_generator_factors_smallSingularChainInclusion
    (X : TopCat) (V W : Set X) (hV : IsOpen V) (hW : IsOpen W)
    (hcover : V ∪ W = Set.univ) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    ∃ (k : ℕ)
      (lift : ModuleCat.of ℤ ℤ ⟶ (smallSingularChainComplex X V W).X n),
      lift ≫ (smallSingularChainInclusion X V W).f n =
        (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s ≫
          (singularBarycentricSubdivisionIterate X k).f n := by
  obtain ⟨k, hsmall⟩ := exists_iterate_singularSimplex_smallFor_twoSetCover
    V W hV hW hcover (X.toSSetObjEquiv _ s)
  exact ⟨k, smallChainLiftOfSubdivisionGenerator X V W s hsmall,
    smallChainLiftOfSubdivisionGenerator_comp_inclusion X V W s hsmall⟩

theorem exists_iterate_generator_factors_largerSmallSingularChainInclusion
    (X : TopCat) {V₀ W₀ V W : Set X}
    (hV₀ : IsOpen V₀) (hW₀ : IsOpen W₀)
    (hcover : V₀ ∪ W₀ = Set.univ)
    (hV : V₀ ⊆ V) (hW : W₀ ⊆ W) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    ∃ (k : ℕ)
      (lift : ModuleCat.of ℤ ℤ ⟶ (smallSingularChainComplex X V W).X n),
      lift ≫ (smallSingularChainInclusion X V W).f n =
        (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s ≫
          (singularBarycentricSubdivisionIterate X k).f n := by
  obtain ⟨k, hsmall₀⟩ :=
    exists_iterate_singularSimplex_smallFor_twoSetCover
      V₀ W₀ hV₀ hW₀ hcover (X.toSSetObjEquiv _ s)
  have hsmall : ∀ w : BarycentricWord n k,
      SingularSimplexSmallFor V W
        (singularSimplexIteratedBarycentricPiece
          (X.toSSetObjEquiv _ s) w) := fun w ↦
    (hsmall₀ w).imp (fun h ↦ h.trans hV) (fun h ↦ h.trans hW)
  exact ⟨k, smallChainLiftOfSubdivisionGenerator X V W s hsmall,
    smallChainLiftOfSubdivisionGenerator_comp_inclusion X V W s hsmall⟩

noncomputable def singularChainGeneratorSet (X : TopCat) (n : ℕ) :
    Set ((((TopCat.toSSet.obj X).chainComplex
      (ModuleCat.of ℤ ℤ)).X n) : Type) :=
  Set.range fun s : (TopCat.toSSet.obj X) _⦋n⦌ ↦
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s (1 : ℤ)

theorem span_singularChainGeneratorSet_eq_top (X : TopCat) (n : ℕ) :
    Submodule.span ℤ (singularChainGeneratorSet X n) = ⊤ := by
  let M : ModuleCat ℤ :=
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X n
  let P : Submodule ℤ M := Submodule.span ℤ (singularChainGeneratorSet X n)
  apply top_unique
  intro x _
  let _ : Module ℤ (M ⧸ P) := Submodule.Quotient.module P
  have hzero : ModuleCat.ofHom P.mkQ = 0 := by
    apply SSet.chainComplex_hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change P.mkQ
      ((TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) s z) = 0
    have hz :
        (TopCat.toSSet.obj X).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) s z =
          (show ℤ from z) • (TopCat.toSSet.obj X).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) s (1 : ℤ) := by
      change
        ((TopCat.toSSet.obj X).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s).hom z =
          (show ℤ from z) • ((TopCat.toSSet.obj X).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) s).hom (1 : ℤ)
      simpa using
        ((TopCat.toSSet.obj X).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s).hom.toAddMonoidHom.map_zsmul z (1 : ℤ)
    rw [hz]
    have hgen :
        P.mkQ ((TopCat.toSSet.obj X).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s (1 : ℤ)) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨s, rfl⟩
    have hgen' :
        P.mkQ.toAddMonoidHom ((TopCat.toSSet.obj X).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s (1 : ℤ)) = 0 := hgen
    exact (P.mkQ.toAddMonoidHom.map_zsmul
      z ((TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) s (1 : ℤ))).trans (by
          rw [hgen']
          exact zsmul_zero z)
  rw [← Submodule.Quotient.mk_eq_zero (p := P)]
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hzero) x

theorem singularBarycentricSubdivisionIterate_f_apply
    (X : TopCat) (n k : ℕ)
    (x : (integerSingularChainComplex X).X n) :
    (singularBarycentricSubdivisionIterate X k).f n x =
      (((singularBarycentricSubdivision X).f n)^[k]) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [singularBarycentricSubdivisionIterate_succ,
        HomologicalComplex.comp_f]
      change
        (singularBarycentricSubdivision X).f n
            ((singularBarycentricSubdivisionIterate X k).f n x) = _
      rw [Function.iterate_succ_apply', ih]



theorem kernel_persists_under_iterate
    {M Q : ModuleCat ℤ} (f : M ⟶ M) (q : M ⟶ Q)
    (hstable : ∀ x : M, q x = 0 → q (f x) = 0) :
    ∀ (k : ℕ) (x : M), q x = 0 → q ((f^[k]) x) = 0 := by
  intro k
  induction k with
  | zero =>
      intro x hx
      exact hx
  | succ k ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      exact hstable _ (ih x hx)

theorem ModuleEndomorphism.iterate_zsmul
    {M : ModuleCat ℤ} (f : M ⟶ M) (k : ℕ) (r : ℤ) (x : M) :
    (f^[k]) (r • x) = r • (f^[k]) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      calc
        (f^[k + 1]) (r • x) = f ((f^[k]) (r • x)) :=
          Function.iterate_succ_apply' f k (r • x)
        _ = f (r • (f^[k]) x) := congrArg (fun y ↦ f y) (ih x)
        _ = r • f ((f^[k]) x) :=
          f.hom.toAddMonoidHom.map_zsmul r _
        _ = r • (f^[k + 1]) x := congrArg (fun y ↦ r • y)
          (Function.iterate_succ_apply' f k x).symm

def eventuallyKernelSubmodule
    {M Q : ModuleCat ℤ} (f : M ⟶ M) (q : M ⟶ Q)
    (hstable : ∀ x : M, q x = 0 → q (f x) = 0) :
    Submodule ℤ M where
  carrier := {x | ∃ k : ℕ, q ((f^[k]) x) = 0}
  zero_mem' := by
    refine ⟨0, ?_⟩
    exact q.hom.map_zero
  add_mem' {x y} hx hy := by
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hy
    refine ⟨k + l, ?_⟩
    rw [ModuleEndomorphism.iterate_add, map_add]
    have hx' : q ((f^[k + l]) x) = 0 := by
      rw [Nat.add_comm, Function.iterate_add_apply]
      exact kernel_persists_under_iterate f q hstable l _ hk
    have hy' : q ((f^[k + l]) y) = 0 := by
      rw [Function.iterate_add_apply]
      exact kernel_persists_under_iterate f q hstable k _ hl
    rw [hx', hy', add_zero]
  smul_mem' r x hx := by
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, ?_⟩
    have hiter := ModuleEndomorphism.iterate_zsmul f k r x
    have hz : q ((f^[k]) (r • x)) = 0 := by
      calc
        q ((f^[k]) (r • x)) = q (r • (f^[k]) x) :=
          congrArg (fun y ↦ q y) hiter
        _ = r • q ((f^[k]) x) := q.hom.toAddMonoidHom.map_zsmul r _
        _ = r • 0 := congrArg (fun y ↦ r • y) hk
        _ = 0 := zsmul_zero r
    exact (congrArg (fun y : M ↦ q ((f^[k]) y))
      (int_smul_eq_zsmul (by infer_instance : Module ℤ M) r x)).trans hz

@[simp]
theorem mem_eventuallyKernelSubmodule_iff
    {M Q : ModuleCat ℤ} (f : M ⟶ M) (q : M ⟶ Q)
    (hstable : ∀ x : M, q x = 0 → q (f x) = 0) (x : M) :
    x ∈ eventuallyKernelSubmodule f q hstable ↔
      ∃ k : ℕ, q ((f^[k]) x) = 0 :=
  Iff.rfl

theorem eventually_kernel_of_span
    {M Q : ModuleCat ℤ} (f : M ⟶ M) (q : M ⟶ Q)
    (hstable : ∀ x : M, q x = 0 → q (f x) = 0)
    (S : Set M) (hspan : Submodule.span ℤ S = ⊤)
    (hS : ∀ x ∈ S, ∃ k : ℕ, q ((f^[k]) x) = 0) :
    ∀ x : M, ∃ k : ℕ, q ((f^[k]) x) = 0 := by
  intro x
  have hle : Submodule.span ℤ S ≤
      eventuallyKernelSubmodule f q hstable :=
    Submodule.span_le.2 (fun y hy ↦ hS y hy)
  exact hle (by rw [hspan]; exact Submodule.mem_top)

theorem subdivision_eventually_maps_chain_to_zero
    (X : TopCat) {V₀ W₀ V W : Set X}
    (hV₀ : IsOpen V₀) (hW₀ : IsOpen W₀)
    (hcover : V₀ ∪ W₀ = Set.univ)
    (hV : V₀ ⊆ V) (hW : W₀ ⊆ W) (n : ℕ)
    {Q : ModuleCat ℤ}
    (q : (integerSingularChainComplex X).X n ⟶ Q)
    (hq : (smallSingularChainInclusion X V W).f n ≫ q = 0)
    (hstable : ∀ x : (integerSingularChainComplex X).X n,
      q x = 0 → q ((singularBarycentricSubdivision X).f n x) = 0) :
    ∀ x : (integerSingularChainComplex X).X n, ∃ k : ℕ,
      q ((((singularBarycentricSubdivision X).f n)^[k]) x) = 0 := by
  apply eventually_kernel_of_span
    ((singularBarycentricSubdivision X).f n) q hstable
    (singularChainGeneratorSet X n)
    (span_singularChainGeneratorSet_eq_top X n)
  intro x hx
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨k, lift, hfactor⟩ :=
    exists_iterate_generator_factors_largerSmallSingularChainInclusion
      X hV₀ hW₀ hcover hV hW s
  refine ⟨k, ?_⟩
  have hfactorApply := DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom hfactor) (1 : ℤ)
  have hfactorAfterQ := congrArg (fun y ↦ q y) hfactorApply
  have hleft :
      q ((smallSingularChainInclusion X V W).f n (lift (1 : ℤ))) = 0 := by
    simpa using DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hq)
      (lift (1 : ℤ))
  have hright :
      q ((singularBarycentricSubdivisionIterate X k).f n
        ((TopCat.toSSet.obj X).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s (1 : ℤ))) = 0 :=
    hfactorAfterQ.symm.trans hleft
  let g : (integerSingularChainComplex X).X n :=
    (TopCat.toSSet.obj X).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) s (1 : ℤ)
  have hrightG :
      q ((singularBarycentricSubdivisionIterate X k).f n g) = 0 := by
    simpa [g] using hright
  rw [singularBarycentricSubdivisionIterate_f_apply X n k g] at hrightG
  exact hrightG

theorem subdivision_eventually_zero_in_smallChainCokernel
    (X : TopCat) {V₀ W₀ V W : Set X}
    (hV₀ : IsOpen V₀) (hW₀ : IsOpen W₀)
    (hcover : V₀ ∪ W₀ = Set.univ)
    (hV : V₀ ⊆ V) (hW : W₀ ⊆ W) (n : ℕ)
    (hstable : ∀ x : (integerSingularChainComplex X).X n,
      (cokernel.π (smallSingularChainInclusion X V W)).f n x = 0 →
        (cokernel.π (smallSingularChainInclusion X V W)).f n
          ((singularBarycentricSubdivision X).f n x) = 0) :
    ∀ x : (integerSingularChainComplex X).X n, ∃ k : ℕ,
      (cokernel.π (smallSingularChainInclusion X V W)).f n
        ((((singularBarycentricSubdivision X).f n)^[k]) x) = 0 := by
  apply subdivision_eventually_maps_chain_to_zero X
    hV₀ hW₀ hcover hV hW n
    ((cokernel.π (smallSingularChainInclusion X V W)).f n)
    (HomologicalComplex.congr_hom
      (cokernel.condition (smallSingularChainInclusion X V W)) n)
    hstable

end DifferentialGeometry.Topology.SphereSeparation
