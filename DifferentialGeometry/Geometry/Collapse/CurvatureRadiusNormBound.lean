import DifferentialGeometry.Geometry.Collapse.CurvatureScaleVolumeComparison

set_option autoImplicit false

noncomputable section

open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- At one original center, bounds on every strict volume-tested radius imply
one bound on the whole open curvature-radius ball. The volume threshold depends
only on the original volume ratio; after a tested-bound coefficient is chosen,
the resulting coefficient precedes every manifold, metric, center and radius. -/
theorem exists_uniform_whole_radius_curvature_bound_of_tested_bounds
    (w : ℝ) (hw : 0 < w) :
    ∃ κ : ℝ, 0 < κ ∧ κ < euclideanThreeUnitBallVolume ∧
      ∀ A : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle (𝓡 3) M)]
        (g : SmoothRiemannianMetric (𝓡 3) M) (_ : RiemannianMetricComplete g)
        (p : M) (R : ℝ),
        0 < R → curvatureRadius g p = ENNReal.ofReal R →
        ENNReal.ofReal (w * R ^ 3) ≤ ballVolume g p R →
        (∀ r : ℝ, 0 < r → r < R →
          ENNReal.ofReal (κ * r ^ 3) ≤ ballVolume g p r →
          ∀ x ∈ riemannianBallOf g p r,
            curvatureDerivativeNorm g 0 x ≤ A * (r ^ 2)⁻¹) →
        ∀ x ∈ riemannianBallOf g p R,
          curvatureDerivativeNorm g 0 x ≤ C * (R ^ 2)⁻¹ := by
  have hω : 0 < euclideanThreeUnitBallVolume := by
    unfold euclideanThreeUnitBallVolume
    positivity
  let κ := min (w * Real.exp (-4) / 8) (euclideanThreeUnitBallVolume / 2)
  have hκ : 0 < κ := lt_min (by positivity) (half_pos hω)
  have hκupper : κ < euclideanThreeUnitBallVolume :=
    (min_le_right _ _).trans_lt (half_lt_self hω)
  refine ⟨κ, hκ, hκupper, ?_⟩
  intro A
  let C := 4 * max A 0
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ g hg p R hR hradius hvolume htested x hx
  change riemannianEDistOf g p x < ENNReal.ofReal R at hx
  have hfinite : riemannianEDistOf g p x ≠ ⊤ := ne_top_of_lt hx
  have hdist : (riemannianEDistOf g p x).toReal < R := by
    apply (ENNReal.ofReal_lt_ofReal_iff hR).mp
    simpa only [ENNReal.ofReal_toReal hfinite] using hx
  obtain ⟨r, hmaxr, hrR⟩ := exists_between (max_lt (half_lt_self hR) hdist)
  have hhalf : R / 2 < r := (le_max_left _ _).trans_lt hmaxr
  have hr : 0 < r := (half_pos hR).trans hhalf
  have hxr : x ∈ riemannianBallOf g p r := by
    change riemannianEDistOf g p x < ENNReal.ofReal r
    rw [← ENNReal.ofReal_toReal hfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr ((le_max_right _ _).trans_lt hmaxr)
  have hratio := ballVolume_ratio_at_curvature_scale g (by simp) hg p
    hr hrR.le hradius.symm.le
  have hcoefficient :
      (Real.exp (-4) * (r / (2 * R)) ^ 3) * (w * R ^ 3) =
        (w * Real.exp (-4) / 8) * r ^ 3 := by
    field_simp [hR.ne']
    ring
  have htestVolume : ENNReal.ofReal (κ * r ^ 3) ≤ ballVolume g p r := by
    calc
      ENNReal.ofReal (κ * r ^ 3) ≤
          ENNReal.ofReal ((w * Real.exp (-4) / 8) * r ^ 3) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _)
          (pow_nonneg hr.le 3))
      _ = ENNReal.ofReal (Real.exp (-4) * (r / (2 * R)) ^ 3) *
          ENNReal.ofReal (w * R ^ 3) := by
        rw [← ENNReal.ofReal_mul (by positivity), hcoefficient]
      _ ≤ ENNReal.ofReal (Real.exp (-4) * (r / (2 * R)) ^ 3) *
          ballVolume g p R := mul_le_mul' le_rfl hvolume
      _ ≤ ballVolume g p r := hratio
  have hnorm := htested r hr hrR htestVolume x hxr
  have hinverse : (r ^ 2)⁻¹ ≤ ((R / 2) ^ 2)⁻¹ :=
    inv_anti₀ (sq_pos_of_pos (half_pos hR))
      (pow_le_pow_left₀ (half_pos hR).le hhalf.le 2)
  calc
    curvatureDerivativeNorm g 0 x ≤ A * (r ^ 2)⁻¹ := hnorm
    _ ≤ max A 0 * (r ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr (sq_nonneg r))
    _ ≤ max A 0 * ((R / 2) ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hinverse (le_max_right _ _)
    _ = C * (R ^ 2)⁻¹ := by
      dsimp only [C]
      field_simp [hR.ne']
      ring

/-- The actual derivative-control predicate supplies the center-specific tests
of the preceding theorem. Only order zero of its finite budget is used. -/
theorem exists_uniform_whole_radius_curvature_bound
    (A : ℝ → ℝ) (w : ℝ) (hw : 0 < w) :
    ∃ κ C : ℝ, 0 < κ ∧ κ < euclideanThreeUnitBallVolume ∧ 0 ≤ C ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle (𝓡 3) M)]
        (g : SmoothRiemannianMetric (𝓡 3) M) (_ : RiemannianMetricComplete g)
        (p : M) (R w₀ : ℝ) (K : ℕ),
        0 < R → curvatureRadius g p = ENNReal.ofReal R →
        ENNReal.ofReal (w * R ^ 3) ≤ ballVolume g p R →
        curvatureDerivativesControlled g K A w₀ → w₀ ≤ κ →
        ∀ x ∈ riemannianBallOf g p R,
          curvatureDerivativeNorm g 0 x ≤ C * (R ^ 2)⁻¹ := by
  obtain ⟨κ, hκ, hκupper, htested⟩ :=
    exists_uniform_whole_radius_curvature_bound_of_tested_bounds w hw
  obtain ⟨C, hC, hbound⟩ := htested (A κ)
  refine ⟨κ, C, hκ, hκupper, hC, ?_⟩
  intro M _ _ _ _ _ _ g hg p R w₀ K hR hradius hvolume hcontrol hw₀
  apply hbound M g hg p R hR hradius hvolume
  intro r hr hrR htestVolume x hx
  have htestRadius : ENNReal.ofReal r < curvatureRadius g p := by
    rw [hradius]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr hrR
  simpa only [Nat.zero_add] using hcontrol p κ r hw₀ hκupper hr
    htestRadius htestVolume 0 (Nat.zero_le K) x hx

end DifferentialGeometry.Geometry.Collapse
