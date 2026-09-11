import DifferentialGeometry.Topology.Manifold.BoundaryCollar.ChartField

open Set Function Topology Filter Manifold WithLp
open scoped ContDiff
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.BoundaryCollar


def normalSplit (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ]
    (ℝ × EuclideanSpace ℝ (Fin n)) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun v => (v 0, toLp 2 (fun i => v i.succ))
      invFun := fun p => toLp 2 (Fin.cons p.1 (ofLp p.2))
      left_inv := by
        intro v
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      right_inv := by intro p; rfl
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl }


@[simp] theorem normalSplit_fst (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    (normalSplit n v).1 = v 0 := rfl


@[simp] theorem normalSplit_symm_zero (n : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    (normalSplit n).symm p 0 = p.1 := rfl


theorem normalSplit_symm_mem_range_iff (n : ℕ) (q : ℝ × EuclideanSpace ℝ (Fin n)) :
    (normalSplit n).symm q ∈ range (𝓡∂ (n + 1)) ↔ 0 ≤ q.1 := by
  rw [range_modelWithCornersEuclideanHalfSpace]
  rfl

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]


def normalChartField (p : M) (V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y) :
    (ℝ × EuclideanSpace ℝ (Fin n)) → ℝ × EuclideanSpace ℝ (Fin n) :=
  fun q => normalSplit n (chartField (𝓡∂ (n + 1)) p V ((normalSplit n).symm q))


theorem normalSplit_extChartAt_boundary [IsManifold (𝓡∂ (n + 1)) 1 M]
    {p : M} (hp : (𝓡∂ (n + 1)).IsBoundaryPoint p) :
    normalSplit n (extChartAt (𝓡∂ (n + 1)) p p) =
      (0, (normalSplit n (extChartAt (𝓡∂ (n + 1)) p p)).2) := by
  apply Prod.ext
  · exact (chartHeight_eq_zero_iff p (mem_chart_source _ p)).mpr hp
  · rfl

theorem exists_normalChartField_neighborhood [IsManifold (𝓡∂ (n + 1)) ∞ M]
    {p : M} (hp : (𝓡∂ (n + 1)).IsBoundaryPoint p)
    {V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y}
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hpos : 0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p)) :
    ∃ U : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsOpen U ∧
      (0, (normalSplit n (extChartAt (𝓡∂ (n + 1)) p p)).2) ∈ U ∧
      ContDiffOn ℝ ∞ (normalChartField p V)
        ((Ici (0 : ℝ) ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n)))) ∩ U) ∧
      (∀ q ∈ (Ici (0 : ℝ) ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n)))) ∩ U,
        (normalSplit n).symm q ∈ (extChartAt (𝓡∂ (n + 1)) p).target) ∧
      0 < (normalChartField p V
        (0, (normalSplit n (extChartAt (𝓡∂ (n + 1)) p p)).2)).1 := by
  let I := 𝓡∂ (n + 1)
  let a := extChartAt I p p
  have ha := normalSplit_extChartAt_boundary hp
  obtain ⟨B, hB, hBT⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
    (extChartAt_target_mem_nhdsWithin (I := I) p)
  obtain ⟨O, hOB, hO, haO⟩ := mem_nhds_iff.mp hB
  let U := (normalSplit n).symm ⁻¹' O
  have hU : IsOpen U := hO.preimage (normalSplit n).symm.continuous
  have h0U : (0, (normalSplit n a).2) ∈ U := by
    rw [← ha]
    change (normalSplit n).symm (normalSplit n a) ∈ O
    simpa only [(normalSplit n).symm_apply_apply] using haO
  have hmaps : MapsTo (normalSplit n).symm
      ((Ici (0 : ℝ) ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n)))) ∩ U)
      (extChartAt I p).target := by
    intro q hq
    exact hBT ⟨hOB hq.2, (normalSplit_symm_mem_range_iff n q).mpr hq.1.1⟩
  refine ⟨U, hU, h0U, ?_, hmaps, ?_⟩
  · exact (normalSplit n).contDiff.comp_contDiffOn
      ((contDiffOn_chartField I p hV).comp (normalSplit n).symm.contDiff.contDiffOn hmaps)
  · rw [← ha]
    change 0 < (normalSplit n (chartField I p V ((normalSplit n).symm (normalSplit n a)))).1
    rw [(normalSplit n).symm_apply_apply, normalSplit_fst, chartField_self]
    exact hpos

end DifferentialGeometry.Manifold.BoundaryCollar
