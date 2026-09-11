import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticScalarRatio

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance ascrDecayIsManifoldOne : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem exists_scalar_distance_tail_bound_of_ascr_ne_top
    (g : SmoothRiemannianMetric I M) (p : M)
    (hfinite : asymptoticScalarCurvatureRatio g p ≠ ⊤) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ x : M,
      rho ≤ (riemannianEDistOf g p x).toReal →
        metricScalarAt (I := I) g x * ((riemannianEDistOf g p x).toReal) ^ 2 ≤
          (asymptoticScalarCurvatureRatio g p).toReal + 1 := by
  let A : ℝ := (asymptoticScalarCurvatureRatio g p).toReal
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hlt : asymptoticScalarCurvatureRatio g p < ENNReal.ofReal (A + 1) := by
    rw [← ENNReal.ofReal_toReal hfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hA).mpr (by linarith)
  obtain ⟨rho, hrho⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hrhopos, htail⟩ := iInf_lt_iff.mp hrho
  refine ⟨rho, hrhopos, ?_⟩
  intro x hx
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ A + 1)).mp
  have hpoint : ENNReal.ofReal (metricScalarAt (I := I) g x *
      ((riemannianEDistOf g p x).toReal) ^ 2) ≤ scalarCurvatureDistanceTail g p rho := by
    unfold scalarCurvatureDistanceTail
    exact le_iSup₂ (f := fun (y : M)
      (_ : rho ≤ (riemannianEDistOf g p y).toReal) =>
        ENNReal.ofReal (metricScalarAt (I := I) g y *
          ((riemannianEDistOf g p y).toReal) ^ 2)) x hx
  exact hpoint.trans htail.le

theorem scalar_le_of_scalar_distance_tail_bound
    (g : SmoothRiemannianMetric I M) (p : M)
    {rho B eps : ℝ} (hrho : 0 < rho) (hB : 0 ≤ B) (heps : 0 < eps)
    (hbound : ∀ x : M, rho ≤ (riemannianEDistOf g p x).toReal →
      metricScalarAt (I := I) g x * ((riemannianEDistOf g p x).toReal) ^ 2 ≤ B)
    (x : M)
    (hx : rho + Real.sqrt (B / eps) + 1 ≤ (riemannianEDistOf g p x).toReal) :
    metricScalarAt (I := I) g x ≤ eps := by
  let d : ℝ := (riemannianEDistOf g p x).toReal
  have hsqrt : 0 ≤ Real.sqrt (B / eps) := Real.sqrt_nonneg _
  have hd : 0 < d := by dsimp only [d]; linarith
  have hrhod : rho ≤ d := by dsimp only [d]; linarith
  have hsqrtd : Real.sqrt (B / eps) ≤ d := by dsimp only [d]; linarith
  have hsquare : B / eps ≤ d ^ 2 := by
    rw [← Real.sq_sqrt (div_nonneg hB heps.le)]
    exact (sq_le_sq₀ hsqrt hd.le).mpr hsqrtd
  have hBupper : B ≤ eps * d ^ 2 := by
    have h := (div_le_iff₀ heps).mp hsquare
    simpa only [mul_comm] using h
  have hscalar := hbound x hrhod
  change metricScalarAt (I := I) g x * d ^ 2 ≤ B at hscalar
  have hsqpos : 0 < d ^ 2 := sq_pos_of_pos hd
  exact (mul_le_mul_iff_left₀ hsqpos).mp (hscalar.trans hBupper)

theorem scalar_decay_of_ascr_ne_top
    (g : SmoothRiemannianMetric I M) (p : M)
    (hfinite : asymptoticScalarCurvatureRatio g p ≠ ⊤) :
    ∀ eps : ℝ, 0 < eps → ∃ D : ℝ, 0 < D ∧
      ∀ x : M, D ≤ (riemannianEDistOf g p x).toReal →
        metricScalarAt (I := I) g x ≤ eps := by
  obtain ⟨rho, hrho, hbound⟩ := exists_scalar_distance_tail_bound_of_ascr_ne_top g p hfinite
  intro eps heps
  let B : ℝ := (asymptoticScalarCurvatureRatio g p).toReal + 1
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨rho + Real.sqrt (B / eps) + 1, by positivity, ?_⟩
  intro x hx
  exact scalar_le_of_scalar_distance_tail_bound g p hrho hB heps hbound x hx

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
