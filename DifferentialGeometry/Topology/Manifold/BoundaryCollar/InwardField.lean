import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Coorientation
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

open Set Function Topology Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.BoundaryCollar

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

private def chartInwardField (p : BoundaryManifold (𝓡∂ n) M)
    (y : M) : TangentSpace (𝓡∂ n) y :=
  (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡∂ n)) (p : M)).symm y
    (EuclideanSpace.single (0 : Fin n) (1 : ℝ))

private theorem contMDiffOn_chartInwardField (p : BoundaryManifold (𝓡∂ n) M) :
    ContMDiffOn (𝓡∂ n) (𝓡∂ n).tangent ∞
      (fun y => (⟨y, chartInwardField p y⟩ : TangentBundle (𝓡∂ n) M))
      (chartAt (EuclideanHalfSpace n) (p : M)).source := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡∂ n)) (p : M)
  apply (e.contMDiffOn_section_baseSet_iff (IB := 𝓡∂ n) (n := ∞)).mpr
  apply (contMDiffOn_const (c := EuclideanSpace.single (0 : Fin n) (1 : ℝ))).congr
  intro y hy
  exact congrArg Prod.snd (e.apply_mk_symm hy (EuclideanSpace.single (0 : Fin n) (1 : ℝ)))

theorem exists_smooth_inwardField [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ n).boundary M)) :
    ∃ V : (y : M) → TangentSpace (𝓡∂ n) y,
      ContMDiff (𝓡∂ n) (𝓡∂ n).tangent ∞
        (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ n) M)) ∧
      IsCompact (tsupport V) ∧
      ∀ y : BoundaryManifold (𝓡∂ n) M,
        0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (V y) ∧
          V y ∉ (boundaryInclusionMfderiv y).range := by
  classical
  let _ : LocallyCompactSpace (EuclideanHalfSpace n) := (𝓡∂ n).locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanHalfSpace n) M
  obtain ⟨W, hW, hKW, _, hWc⟩ := exists_open_between_and_isCompact_closure
    hK isOpen_univ (subset_univ _)
  let D : BoundaryManifold (𝓡∂ n) M → Set M := fun p =>
    (chartAt (EuclideanHalfSpace n) (p : M)).source ∩ W
  have hD (p : BoundaryManifold (𝓡∂ n) M) : IsOpen (D p) :=
    (chartAt (EuclideanHalfSpace n) (p : M)).open_source.inter hW
  have hcover : (𝓡∂ n).boundary M ⊆ ⋃ p, D p := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, mem_chart_source (EuclideanHalfSpace n) y, hKW hy⟩
  obtain ⟨a, ha⟩ := hK.elim_finite_subcover D hD hcover
  let A := ↥a
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓡∂ n)
    hK.isClosed (fun i : A => D i.1) (fun i => hD i.1) (by
      intro y hy
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (ha hy)
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hyi⟩)
  let V : (y : M) → TangentSpace (𝓡∂ n) y :=
    fun y => ∑ i : A, ρ i y • chartInwardField i.1 y
  have hV : ContMDiff (𝓡∂ n) (𝓡∂ n).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ n) M)) := by
    apply ContMDiff.sum_section
    intro i _
    exact ContMDiffOn.smul_section_of_tsupport (ρ i).contMDiff.contMDiffOn
      (hD i.1) (hρ i) ((contMDiffOn_chartInwardField i.1).mono inter_subset_left)
  have hsupp : Function.support V ⊆ W := by
    intro y hy
    by_contra hn
    apply hy
    apply Finset.sum_eq_zero
    intro i _
    have hh : ρ i y = 0 := image_eq_zero_of_notMem_tsupport (fun hi => hn (hρ i hi).2)
    rw [hh, zero_smul]
    rfl
  refine ⟨V, hV, hWc.of_isClosed_subset (isClosed_tsupport V) (closure_mono hsupp), ?_⟩
  intro y
  let L : TangentSpace (𝓡∂ n) (y : M) →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)
  have hpos : 0 < L (V y) := by
    change 0 < L (∑ i : A, ρ i (y : M) • chartInwardField i.1 y)
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul]
    have hp (i : A) (hi : 0 < ρ i (y : M)) : 0 < L (chartInwardField i.1 y) :=
      proj_inwardCoordAt_pos i.1 y (hρ i (subset_tsupport _ (ne_of_gt hi))).1
    apply Finset.sum_pos'
    · intro i _
      by_cases hi : ρ i (y : M) = 0
      · rw [hi, zero_mul]
      · exact mul_nonneg (ρ.nonneg _ _) (hp i (lt_of_le_of_ne (ρ.nonneg _ _) (Ne.symm hi))).le
    · obtain ⟨i, hi⟩ := ρ.exists_pos_of_mem y.2
      exact ⟨i, Finset.mem_univ _, mul_pos hi (hp i hi)⟩
  refine ⟨hpos, ?_⟩
  rw [range_boundaryInclusionMfderiv_eq_ker_proj]
  exact ne_of_gt hpos

end DifferentialGeometry.Manifold.BoundaryCollar
