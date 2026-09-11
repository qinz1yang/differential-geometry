import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderScalarNormalization


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

local notation "SphereTwo" => SpatialNeckSphere
local notation "sphereMetric" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

private local instance cylinderScalarNativeDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
private local instance cylinderScalarNativeSphereC1 : IsManifold (𝓡 2) 1 SphereTwo :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance cylinderScalarNativeCylinderC1 :
    IsManifold SpatialNeckCylinderModel 1 SpatialNeckCylinder :=
  IsManifold.of_le (n := ∞) (by decide)

private def cylinder_scalar_basis {Idx : Type*} {x : SphereTwo}
    (b : Module.Basis Idx ℝ (TangentSpace (𝓡 2) x)) (s : ℝ) :
    Module.Basis (Idx ⊕ Unit) ℝ (TangentSpace SpatialNeckCylinderModel (x, s)) := by
  with_unfolding_all exact b.prod (Module.Basis.singleton Unit ℝ)

private theorem cylinder_scalar_basis_inl {Idx : Type*} {x : SphereTwo}
    (b : Module.Basis Idx ℝ (TangentSpace (𝓡 2) x)) (s : ℝ) (i : Idx) :
    cylinder_scalar_basis b s (Sum.inl i) = (b i, 0) :=
  Prod.ext (b.prod_apply_inl_fst (Module.Basis.singleton Unit ℝ) i)
    (b.prod_apply_inl_snd (Module.Basis.singleton Unit ℝ) i)

private theorem cylinder_scalar_basis_inr {Idx : Type*} {x : SphereTwo}
    (b : Module.Basis Idx ℝ (TangentSpace (𝓡 2) x)) (s : ℝ) (i : Unit) :
    cylinder_scalar_basis b s (Sum.inr i) = (0, 1) :=
  Prod.ext (b.prod_apply_inr_fst (Module.Basis.singleton Unit ℝ) i)
    ((b.prod_apply_inr_snd (Module.Basis.singleton Unit ℝ) i).trans
      (Module.Basis.singleton_apply Unit ℝ i))


theorem doubleSphereCylinderMetric_scalar_native (p : SpatialNeckCylinder) :
    metricScalarAt doubleSphereCylinderMetric p = 1 := by
  classical
  rcases p with ⟨x, s⟩
  let h := scaleMetric 2 (by norm_num) sphereMetric
  let gP := doubleSphereCylinderMetric
  have hproduct (y : SphereTwo) (z : ℝ)
      (v w : TangentSpace (𝓡 2) y) (a c : ℝ) :
      gP.inner (y, z) (v, a) (w, c) = h.inner y v w + a * c := by
    rw [scaleMetric_inner]
    exact doubleSphereCylinderMetric_inner y z v w a c
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := 𝓡 2) h x
  let Idx := Fin (Module.finrank ℝ (TangentSpace (𝓡 2) x))
  let bP := cylinder_scalar_basis b s
  have hbP : ∀ i j, gP.inner (x, s) (bP i) (bP j) =
      if i = j then (1 : ℝ) else 0 := by
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [bP, cylinder_scalar_basis_inl, Sum.inl.injEq]
      exact (hproduct x s (b i) (b j) 0 0).trans
        (by simpa only [zero_mul, add_zero] using hb i j)
    · simp only [bP, cylinder_scalar_basis_inl, cylinder_scalar_basis_inr,
        Sum.inl_ne_inr, ↓reduceIte]
      exact (hproduct x s (b i) 0 0 1).trans (by simp)
    · simp only [bP, cylinder_scalar_basis_inl, cylinder_scalar_basis_inr,
        Sum.inr_ne_inl, ↓reduceIte]
      exact (hproduct x s 0 (b j) 1 0).trans (by simp)
    · simp only [bP, cylinder_scalar_basis_inr, Subsingleton.elim i j, ↓reduceIte]
      exact (hproduct x s 0 0 1 1).trans (by simp)
  have hRm (i j : Idx ⊕ Unit) :
      metricRm04At gP (x, s) (vec4 (bP j) (bP i) (bP i) (bP j)) =
        metricRm04At h x (vec4 (bP j).1 (bP i).1 (bP i).1 (bP j).1) := by
    change metricRm04StandardAt gP (x, s) (bP j) (bP i) (bP i) (bP j) =
      metricRm04StandardAt h x (bP j).1 (bP i).1 (bP i).1 (bP j).1
    have hc := shrinkingCylinder_metricRm04StdAt 0 (by norm_num) (x, s)
      (bP j) (bP i) (bP i) (bP j)
    rw [scalarOneShrinkingCylinderMetric_zero] at hc
    have hh := metricRmStandard_scale (I := 𝓡 2) 2 (by norm_num) sphereMetric x
      (bP j).1 (bP i).1 (bP i).1 (bP j).1
    exact hc.trans (by simpa only [sub_zero, mul_one] using hh.symm)
  have htrace : metricScalarAt gP (x, s) = metricScalarAt h x := by
    rw [metricScalarAt_eq_sum_sum_rm04_of_orthonormal gP bP hbP,
      metricScalarAt_eq_sum_sum_rm04_of_orthonormal h b hb]
    rw [← Fintype.sum_prod_type (fun q : (Idx ⊕ Unit) × (Idx ⊕ Unit) =>
      metricRm04At gP (x, s) (vec4 (bP q.2) (bP q.1) (bP q.1) (bP q.2))),
      ← Fintype.sum_prod_type (fun q : Idx × Idx =>
        metricRm04At h x (vec4 (b q.2) (b q.1) (b q.1) (b q.2)))]
    let e : Idx × Idx → (Idx ⊕ Unit) × (Idx ⊕ Unit) :=
      fun q => (Sum.inl q.1, Sum.inl q.2)
    have he : Function.Injective e := by
      intro p q hpq
      exact Prod.ext (Sum.inl_injective (congrArg Prod.fst hpq))
        (Sum.inl_injective (congrArg Prod.snd hpq))
    symm
    refine Fintype.sum_of_injective e he _ _ ?_ ?_
    · rintro ⟨i, j⟩ hnot
      rw [hRm]
      rcases i with i | i <;> rcases j with j | j
      · exact False.elim (hnot ⟨(i, j), rfl⟩)
      · apply (metricRm04At h x).map_coord_zero 0
        change (cylinder_scalar_basis b s (Sum.inr j)).1 = (0 : TangentSpace (𝓡 2) x)
        rw [cylinder_scalar_basis_inr]
        rfl
      · apply (metricRm04At h x).map_coord_zero 1
        change (cylinder_scalar_basis b s (Sum.inr i)).1 = (0 : TangentSpace (𝓡 2) x)
        rw [cylinder_scalar_basis_inr]
        rfl
      · apply (metricRm04At h x).map_coord_zero 0
        change (cylinder_scalar_basis b s (Sum.inr j)).1 = (0 : TangentSpace (𝓡 2) x)
        rw [cylinder_scalar_basis_inr]
        rfl
    · intro q
      rw [hRm]
      simp only [e, bP, cylinder_scalar_basis_inl]
  rw [htrace]
  dsimp only [h]
  rw [metricScalarAt_scaleMetric, roundSphereTwo_metricScalarAt]
  norm_num

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
