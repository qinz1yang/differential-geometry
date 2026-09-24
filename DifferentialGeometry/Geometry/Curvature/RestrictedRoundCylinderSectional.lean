import DifferentialGeometry.Geometry.Curvature.RoundSphere
import DifferentialGeometry.Geometry.Curvature.RoundCylinder
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Curvature.RiemannPerturbation
import DifferentialGeometry.Geometry.Curvature.Algebraic.SectionalLowerBound

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness

private theorem metricRm04_horizontal_pos_of_small_metric_derivatives
    {V H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g G : SmoothRiemannianMetric I M) (x : M) {ε : ℝ} (hε : ε < 1 / 1000)
    (hsmall : ∀ m : ℕ, m ≤ 2 → metricDerivNorm m g G G x ≤ ε)
    (u v : TangentSpace I x) (hu : G.inner x u u = 2) (hv : G.inner x v v = 2)
    (hr : riemannOp (LeviCivita G) x u v v = u) :
    0 < metricRm04StandardAt g x u v v u := by
  have hRm : metricRm04StandardAt G x u v v u = 2 := by
    rw [metricRm04StandardAt_eq_inner_riemannOp, hr]
    exact hu
  have herr := abs_metricRm04_sub_le_of_small_metric_derivatives g G x
    (show ε ≤ 1 / 2 by linarith) hsmall u v v u
  rw [hRm, hu, hv, hr, hu] at herr
  have hs : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have he : ε * (360 * Real.sqrt 2 * Real.sqrt 2 * Real.sqrt 2 + Real.sqrt 2) *
      Real.sqrt 2 = 1442 * ε := by
    calc
      _ = ε * (360 * (Real.sqrt 2 * Real.sqrt 2) ^ 2 +
        Real.sqrt 2 * Real.sqrt 2) := by ring
      _ = _ := by rw [hs]; ring
  rw [he] at herr
  have hh := (abs_le.mp herr).1
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]


private theorem riemannOp_roundCylinder_horizontal
    (x : Metric.sphere (0 : E) 1 × ℝ)
    (u v : TangentSpace (𝓡 n) x.1)
    (hv : (roundMetric (E := E) (n := n)).inner x.1 v v = 1)
    (huv : (roundMetric (E := E) (n := n)).inner x.1 u v = 0) :
    riemannOp (LeviCivita (roundCylinderMetric (E := E) (n := n))) x
      (u, 0) (v, 0) (v, 0) = (u, 0) := by
  change EuclideanSpace ℝ (Fin n) at u v
  unfold roundCylinderMetric cylinderMetric
  erw [riemannOp_productMetric]
  erw [riemannOp_scaleMetric, round_riemann_one, riemannOp_line_eq_zero]
  rw [hv, huv]
  change ((1 : ℝ) • u - (0 : ℝ) • v, (0 : ℝ)) = (u, 0)
  simp only [one_smul, zero_smul, sub_zero]

theorem metricRm04_restricted_roundCylinder_horizontal_pos_of_small_metric_derivatives
    (U : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (g : SmoothRiemannianMetric ((𝓡 n).prod 𝓘(ℝ)) U) (x : U)
    {ε : ℝ} (hε : ε < 1 / 1000)
    (hsmall : ∀ m : ℕ, m ≤ 2 → metricDerivNorm m g
      ((roundCylinderMetric (E := E) (n := n)).restrictOpen U)
      ((roundCylinderMetric (E := E) (n := n)).restrictOpen U) x ≤ ε)
    (u v : TangentSpace (𝓡 n) x.val.1)
    (hu : (roundMetric (E := E) (n := n)).inner x.val.1 u u = 1)
    (hv : (roundMetric (E := E) (n := n)).inner x.val.1 v v = 1)
    (huv : (roundMetric (E := E) (n := n)).inner x.val.1 u v = 0) :
    0 < metricRm04StandardAt g x (u, 0) (v, 0) (v, 0) (u, 0) := by
  let _ : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  change EuclideanSpace ℝ (Fin n) at u v
  let G := (roundCylinderMetric (E := E) (n := n)).restrictOpen U
  have hnormu : G.inner x (u, 0) (u, 0) = 2 := by
    change (roundCylinderMetric (E := E) (n := n)).inner x.val (u, 0) (u, 0) = 2
    unfold roundCylinderMetric
    erw [cylinderMetric_inner]
    change 2 * (roundMetric (E := E) (n := n)).inner x.val.1 u u + 0 * 0 = 2
    rw [hu]
    norm_num
  have hnormv : G.inner x (v, 0) (v, 0) = 2 := by
    change (roundCylinderMetric (E := E) (n := n)).inner x.val (v, 0) (v, 0) = 2
    unfold roundCylinderMetric
    erw [cylinderMetric_inner]
    change 2 * (roundMetric (E := E) (n := n)).inner x.val.1 v v + 0 * 0 = 2
    rw [hv]
    norm_num
  have hr : riemannOp (LeviCivita G) x (u, 0) (v, 0) (v, 0) = (u, 0) := by
    have hh := riemannOp_restrictOpen (roundCylinderMetric (E := E) (n := n)) U x
      (u, 0) (v, 0) (v, 0)
    rw [mfderiv_subtype_val] at hh
    exact hh.trans (riemannOp_roundCylinder_horizontal x.val u v hv huv)
  exact metricRm04_horizontal_pos_of_small_metric_derivatives g G x hε hsmall
    (u, 0) (v, 0) hnormu hnormv hr

private theorem metricRm04_lower_bound_of_round_curvature_pair
    {V H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g G : SmoothRiemannianMetric I M) (x : M) {ε : ℝ} (hε : ε ≤ 1 / 1000)
    (hsmall : ∀ m : ℕ, m ≤ 2 → metricDerivNorm m g G G x ≤ ε)
    (u v : TangentSpace I x)
    (hr : riemannOp (LeviCivita G) x u v v = (G.inner x v v / 2) • u) :
    (1 / 16 : ℝ) * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) ≤
      metricRm04StandardAt g x u v v u := by
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  let A := G.inner x u u
  let B := G.inner x v v
  have hA : 0 ≤ A := metric_inner_self_nonneg G x u
  have hB : 0 ≤ B := metric_inner_self_nonneg G x v
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hnormA : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA
  have hnormB : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB
  have hdiag (w : TangentSpace I x) : g.inner x w w ≤ (5 / 4 : ℝ) * G.inner x w w := by
    have hm := (metricDifference_abs_le g G G x w w).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hsmall 0 (by norm_num)) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
    rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg G x w)] at hm
    nlinarith [metric_inner_self_nonneg G x w,
      mul_nonneg (show 0 ≤ 1 / 4 - ε by linarith) (metric_inner_self_nonneg G x w),
      (abs_le.mp hm).2]
  have hgram : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≤ 2 * (A * B) := by
    have hp := mul_le_mul (hdiag u) (hdiag v) (metric_inner_self_nonneg g x v)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 4) hA)
    change g.inner x u u * g.inner x v v ≤ (5 / 4 : ℝ) * A * ((5 / 4 : ℝ) * B) at hp
    nlinarith [sq_nonneg (g.inner x u v)]
  have hRm : metricRm04StandardAt G x u v v u = A * B / 2 := by
    rw [metricRm04StandardAt_eq_inner_riemannOp, hr, map_smul, smul_eq_mul]
    dsimp only [A, B]
    ring
  have herr := abs_metricRm04_sub_le_of_small_metric_derivatives g G x
    (show ε ≤ 1 / 2 by linarith) hsmall u v v u
  rw [hRm, hr, Geometry.Riemannian.sqrt_inner_smul,
    abs_of_nonneg (div_nonneg hB (by norm_num))] at herr
  change |metricRm04StandardAt g x u v v u - A * B / 2| ≤
    ε * (360 * Real.sqrt A * Real.sqrt B * Real.sqrt B + B / 2 * Real.sqrt A) * Real.sqrt A at herr
  have he : ε * (360 * Real.sqrt A * Real.sqrt B * Real.sqrt B + B / 2 * Real.sqrt A) *
      Real.sqrt A = (721 / 2 : ℝ) * ε * (A * B) := by
    calc
      _ = ε * (360 * (Real.sqrt A * Real.sqrt A) * (Real.sqrt B * Real.sqrt B) +
        B / 2 * (Real.sqrt A * Real.sqrt A)) := by ring
      _ = _ := by rw [hnormA, hnormB]; ring
  rw [he] at herr
  have hepsmul := mul_le_mul_of_nonneg_right hε hAB
  have hlo := (abs_le.mp herr).1
  nlinarith

private theorem riemannOp_roundCylinder_horizontal_orthogonal
    (x : Metric.sphere (0 : E) 1 × ℝ) (u v : TangentSpace (𝓡 n) x.1)
    (huv : (Geometry.roundMetric (E := E) (n := n)).inner x.1 u v = 0) :
    riemannOp (LeviCivita (roundCylinderMetric (E := E) (n := n))) x
      (u, 0) (v, 0) (v, 0) =
      ((roundCylinderMetric (E := E) (n := n)).inner x (v, 0) (v, 0) / 2) • (u, 0) := by
  let _ : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  change EuclideanSpace ℝ (Fin n) at u v
  have hinner : (roundCylinderMetric (E := E) (n := n)).inner x (v, 0) (v, 0) =
      2 * (Geometry.roundMetric (E := E) (n := n)).inner x.1 v v := by
    unfold roundCylinderMetric
    erw [cylinderMetric_inner]
    change 2 * (Geometry.roundMetric (E := E) (n := n)).inner x.1 v v + (0 : ℝ) * 0 = _
    ring
  rw [hinner]
  unfold roundCylinderMetric cylinderMetric
  erw [riemannOp_productMetric, riemannOp_scaleMetric, round_riemann_one,
    riemannOp_line_eq_zero]
  rw [huv]
  change ((Geometry.roundMetric (E := E) (n := n)).inner x.1 v v • u - (0 : ℝ) • v, (0 : ℝ)) =
    (2 * (Geometry.roundMetric (E := E) (n := n)).inner x.1 v v / 2) • (u, 0)
  simp only [zero_smul, sub_zero]
  apply Prod.ext
  · change _ • u = (2 * _ / 2) • u
    congr 1
    ring
  · change (0 : ℝ) = (2 * _ / 2) * 0
    ring

private theorem riemannOp_restricted_roundCylinder_horizontal_orthogonal
    (U : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ)) (x : U)
    (u v : TangentSpace (𝓡 n) x.val.1)
    (huv : (Geometry.roundMetric (E := E) (n := n)).inner x.val.1 u v = 0) :
    let G := (roundCylinderMetric (E := E) (n := n)).restrictOpen U
    riemannOp (LeviCivita G) x (u, 0) (v, 0) (v, 0) =
      (G.inner x (v, 0) (v, 0) / 2) • (u, 0) := by
  let _ : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  have hrestrict := riemannOp_restrictOpen (roundCylinderMetric (E := E) (n := n)) U x
    (u, 0) (v, 0) (v, 0)
  rw [mfderiv_subtype_val] at hrestrict
  exact hrestrict.trans (riemannOp_roundCylinder_horizontal_orthogonal x.val u v huv)

theorem metricRm04_restricted_roundCylinder_horizontal_lower_bound_of_small_metric_derivatives
    (U : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (g : SmoothRiemannianMetric ((𝓡 n).prod 𝓘(ℝ)) U) (x : U)
    {ε : ℝ} (hε : ε ≤ 1 / 1000)
    (hsmall : ∀ m : ℕ, m ≤ 2 → metricDerivNorm m g
      ((roundCylinderMetric (E := E) (n := n)).restrictOpen U)
      ((roundCylinderMetric (E := E) (n := n)).restrictOpen U) x ≤ ε)
    (u v : TangentSpace (𝓡 n) x.val.1) :
    (1 / 16 : ℝ) * (g.inner x (u, 0) (u, 0) * g.inner x (v, 0) (v, 0) -
      (g.inner x (u, 0) (v, 0)) ^ 2) ≤
      metricRm04StandardAt g x (u, 0) (v, 0) (v, 0) (u, 0) := by
  let _ : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  let A := fun u v w z : EuclideanSpace ℝ (Fin n) =>
    metricRm04StandardAt g x (u, 0) (v, 0) (w, 0) (z, 0)
  let lift : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace ((𝓡 n).prod 𝓘(ℝ)) x :=
    ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) ℝ
  have hAlg : IsAlgCurvForm A := by
    have hbase : IsAlgCurvForm (fun u v w z : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) x =>
        metricRm04StandardAt g x u v w z) :=
      mem_algebraicCurvatureTensorSubmodule.mp (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro u₁ u₂ v w z
      change metricRm04StandardAt g x (lift (u₁ + u₂)) (lift v) (lift w) (lift z) = _
      rw [map_add]
      exact hbase.add_left _ _ _ _ _
    · intro a u v w z
      change metricRm04StandardAt g x (lift (a • u)) (lift v) (lift w) (lift z) = _
      rw [map_smul]
      exact hbase.smul_left _ _ _ _ _
    · exact fun u v w z => hbase.anti_first _ _ _ _
    · exact fun u v w z => hbase.anti_last _ _ _ _
    · exact fun u v w z => hbase.bianchi _ _ _ _
  let G' : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ :=
    { toFun := fun u => ((Geometry.roundMetric (E := E) (n := n)).inner x.val.1 u).toLinearMap
      map_add' := by
        intro a b
        ext z
        exact congrArg (fun L => L z) (((Geometry.roundMetric (E := E) (n := n)).inner x.val.1).map_add a b)
      map_smul' := by
        intro a b
        ext z
        exact congrArg (fun L => L z) (((Geometry.roundMetric (E := E) (n := n)).inner x.val.1).map_smul a b) }
  let g' : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ :=
    { toFun := fun u => ((g.inner x (lift u)).comp lift).toLinearMap
      map_add' := by
        intro a b
        ext z
        change g.inner x (lift (a + b)) (lift z) = _
        rw [map_add, map_add]
        rfl
      map_smul' := by
        intro a b
        ext z
        change g.inner x (lift (a • b)) (lift z) = _
        rw [map_smul, map_smul]
        rfl }
  apply hAlg.sectional_lower_bound_of_orthogonal G' g'
    (fun u hu => (Geometry.roundMetric (E := E) (n := n)).pos x.val.1 u hu)
    (fun u v => g.symm x (u, 0) (v, 0))
  intro a b hab
  exact metricRm04_lower_bound_of_round_curvature_pair g
    ((roundCylinderMetric (E := E) (n := n)).restrictOpen U) x hε hsmall (a, 0) (b, 0)
    (riemannOp_restricted_roundCylinder_horizontal_orthogonal U x a b hab)

end DifferentialGeometry.Geometry.Curvature
