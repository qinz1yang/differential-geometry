import DifferentialGeometry.Geometry.Curvature.RoundCylinder
import DifferentialGeometry.Geometry.Curvature.RicciSharpPerturbation
import DifferentialGeometry.Geometry.Curvature.RicciJetEstimate
import DifferentialGeometry.Geometry.Curvature.RicciSharpUniformPerturbation
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Geometry.Curvature

theorem ricciSharp_roundCylinder_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (x : Metric.sphere (0 : E) 1 × ℝ) (v : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) x) :
    let g := roundCylinderMetric (E := E) (n := n)
    Real.sqrt (g.inner x (ricciSharp g x v) (ricciSharp g x v)) ≤
      |((n : ℝ) - 1) / 2| * Real.sqrt (g.inner x v v) := by
  let g := roundCylinderMetric (E := E) (n := n)
  let h := scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := n))
  let c := ((n : ℝ) - 1) / 2
  let u : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) x := (v.1, 0)
  have he : ricciSharp g x v = c • u := by
    refine (ricciSharp_roundCylinder x v).trans ?_
    apply Prod.ext
    · rfl
    · change (0 : ℝ) = c * 0
      ring
  have hn : Real.sqrt (g.inner x u u) ≤ Real.sqrt (g.inner x v v) := by
    apply Real.sqrt_le_sqrt
    calc
      _ = h.inner x.1 v.1 v.1 + (0 : ℝ) * 0 := cylinderMetric_inner h x u u
      _ ≤ h.inner x.1 v.1 v.1 + v.2 * v.2 := by nlinarith [sq_nonneg v.2]
      _ = _ := (cylinderMetric_inner h x v v).symm
  change Real.sqrt (g.inner x (ricciSharp g x v) (ricciSharp g x v)) ≤
    |c| * Real.sqrt (g.inner x v v)
  calc
    _ = Real.sqrt (g.inner x (c • u) (c • u)) := congrArg
      (fun z : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) x ↦ Real.sqrt (g.inner x z z)) he
    _ = |c| * Real.sqrt (g.inner x u u) := Riemannian.sqrt_inner_smul g x c u
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (abs_nonneg c)

theorem exists_ricciSharp_roundCylinder_difference_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    (x : Metric.sphere (0 : E) 1 × ℝ) :
    let gRef := roundCylinderMetric (E := E) (n := 2)
    ∃ C : ℝ, 0 < C ∧ ∀ (g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ))
      (Metric.sphere (0 : E) 1 × ℝ)) (ε : ℝ), ε ≤ 1 / 2 →
      (∀ k : ℕ, k ≤ 2 → metricDerivNorm k g gRef gRef x ≤ ε) →
      ∀ v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x,
        let d := ricciSharp g x v - ricciSharp gRef x v
        Real.sqrt (gRef.inner x d d) ≤ C * ε * Real.sqrt (gRef.inner x v v) := by
  let gRef := roundCylinderMetric (E := E) (n := 2)
  let : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = 2 + 1 from Fact.out]
    norm_num)
  let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) := ⟨by simp⟩
  obtain ⟨K, hK, hRic⟩ :=
    exists_ricci_tensor_difference_bound_of_small_metric_derivatives gRef x
  refine ⟨2 * K + 1, by positivity, ?_⟩
  intro g ε hε hsmall v
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hε1 : ε < 1 := by linarith
  have hnorm : Real.sqrt (gRef.inner x (ricciSharp gRef x v) (ricciSharp gRef x v)) ≤
      (1 / 2 : ℝ) * Real.sqrt (gRef.inner x v v) := by
    exact (ricciSharp_roundCylinder_norm_le (E := E) (n := 2) x v).trans_eq
      (congrArg (fun c : ℝ ↦ c * Real.sqrt (gRef.inner x v v))
        (by norm_num : |((2 : ℝ) - 1) / 2| = (1 / 2 : ℝ)))
  have h := ricciSharp_difference_bound_of_tensor_difference g gRef x ε (K * ε) hε1
    (hsmall 0 (by norm_num)) (hRic g ε hε hsmall) v
  dsimp only at h ⊢
  apply h.trans
  have hb := mul_le_mul_of_nonneg_left hnorm hε0
  apply (div_le_iff₀ (show 0 < 1 - ε by linarith)).mpr
  have hv := Real.sqrt_nonneg (gRef.inner x v v)
  have hbound : (2 * K + 1) * ε * Real.sqrt (gRef.inner x v v) * ε ≤
      (2 * K + 1) * ε * Real.sqrt (gRef.inner x v v) * (1 / 2) :=
    mul_le_mul_of_nonneg_left hε (by positivity)
  nlinarith

theorem ricciSharp_roundCylinder_difference_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    (g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ))
    (x : Metric.sphere (0 : E) 1 × ℝ) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k g (roundCylinderMetric (E := E) (n := 2))
        (roundCylinderMetric (E := E) (n := 2)) x ≤ ε)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
    let gRef := roundCylinderMetric (E := E) (n := 2)
    let d := ricciSharp g x v - ricciSharp gRef x v
    Real.sqrt (gRef.inner x d d) ≤ 1441 * ε * Real.sqrt (gRef.inner x v v) := by
  let gRef := roundCylinderMetric (E := E) (n := 2)
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hnorm : Real.sqrt (gRef.inner x (ricciSharp gRef x v) (ricciSharp gRef x v)) ≤
      (1 / 2 : ℝ) * Real.sqrt (gRef.inner x v v) := by
    exact (ricciSharp_roundCylinder_norm_le (E := E) (n := 2) x v).trans_eq
      (congrArg (fun c : ℝ ↦ c * Real.sqrt (gRef.inner x v v))
        (by norm_num : |((2 : ℝ) - 1) / 2| = (1 / 2 : ℝ)))
  have h := ricciSharp_difference_bound_of_small_metric_derivatives
    (I := (𝓡 2).prod 𝓘(ℝ)) g gRef x ε hε hsmall v
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  dsimp only at h ⊢
  rw [hdim] at h
  norm_num only [Nat.cast_ofNat] at h
  apply h.trans
  apply (div_le_iff₀ (show 0 < 1 - ε by linarith)).mpr
  change 720 * ε * Real.sqrt (gRef.inner x v v) +
    ε * Real.sqrt (gRef.inner x (ricciSharp gRef x v) (ricciSharp gRef x v)) ≤
      1441 * ε * Real.sqrt (gRef.inner x v v) * (1 - ε)
  have hb := mul_le_mul_of_nonneg_left hnorm hε0
  have hc := mul_le_mul_of_nonneg_left hε
    (show 0 ≤ 1441 * ε * Real.sqrt (gRef.inner x v v) by positivity)
  nlinarith

end DifferentialGeometry.Geometry.Curvature
