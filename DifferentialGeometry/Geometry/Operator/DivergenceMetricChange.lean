import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.CovariantTrace

noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem divergence_riemannianVolumeDensity_smul
    (q h : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence (leviCivitaConnectionOfMetric q)
      (fun y => riemannianVolumeDensity q h y • X y) x =
      riemannianVolumeDensity q h x * divergence (leviCivitaConnectionOfMetric h) X x := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Z := smoothSmul (riemannianVolumeDensity q h) (riemannianVolumeDensity_contMDiff q h) X
  have hint (z : M) (hz : z ∈ I.interior M) :
      divergence (leviCivitaConnectionOfMetric q) Z z =
        riemannianVolumeDensity q h z * divergence (leviCivitaConnectionOfMetric h) X z := by
    rw [← divergence_g_eq_leviCivita_divergence_of_isInteriorPoint q Z hz,
      ← divergence_g_eq_leviCivita_divergence_of_isInteriorPoint h X hz,
      divergence_g_def, divergence_g_def, localDivergence_def, localDivergence_def]
    have hnum : (∑ i : Fin (Module.finrank ℝ E), partialDeriv i
        (fun y => chartCoeffOnE (I := I) z Z i y * chartDensityOnE q z y)
        (extChartAt I z z)) =
        ∑ i : Fin (Module.finrank ℝ E), partialDeriv i
          (fun y => chartCoeffOnE (I := I) z X i y * chartDensityOnE h z y)
          (extChartAt I z z) := by
      apply Finset.sum_congr rfl
      intro i hi
      have heq : (fun y => chartCoeffOnE (I := I) z Z i y * chartDensityOnE q z y)
          =ᶠ[𝓝 (extChartAt I z z)]
          (fun y => chartCoeffOnE (I := I) z X i y * chartDensityOnE h z y) := by
        have hzi := WithBoundary.extChartAt_mem_interior_target_of_isInteriorPoint
          (I := I) z (mem_chart_source H z) hz
        filter_upwards [isOpen_interior.mem_nhds hzi] with y hy
        have hyt := interior_subset hy
        have hys : (extChartAt I z).symm y ∈ (chartAt H z).source := by
          simpa only [extChartAt_source_eq_chartAt_source] using (extChartAt I z).map_target hyt
        rw [chartCoeffOnE_smoothSmul z (riemannianVolumeDensity q h)
          (riemannianVolumeDensity_contMDiff q h) X i hyt]
        change (riemannianVolumeDensity q h ((extChartAt I z).symm y) * _) *
          chartDensity q z ((extChartAt I z).symm y) =
          _ * chartDensity h z ((extChartAt I z).symm y)
        rw [riemannianVolumeDensity_apply_of_mem_chart_source q h z hys]
        calc
          _ = chartCoeffOnE (I := I) z X i y *
              ((chartDensity h z ((extChartAt I z).symm y) /
                chartDensity q z ((extChartAt I z).symm y)) *
                chartDensity q z ((extChartAt I z).symm y)) := by ring
          _ = _ := by rw [div_mul_cancel₀ _ (ne_of_gt (chartDensity_pos q z hys))]
      exact congrArg (fun A : E →L[ℝ] ℝ => A ((chartModelBasis E) i)) heq.fderiv_eq
    rw [hnum, riemannianVolumeDensity_apply_of_mem_chart_source q h z (mem_chart_source H z)]
    field_simp [ne_of_gt (chartDensity_pos q z (mem_chart_source H z)),
      ne_of_gt (chartDensity_pos h z (mem_chart_source H z))]
  have hleft := (leviCivita_divergence_contMDiff q Z).continuous.continuousAt (x := x)
  have hright := ((riemannianVolumeDensity_contMDiff q h).continuous.mul
    (leviCivita_divergence_contMDiff h X).continuous).continuousAt (x := x)
  by_contra hne
  have hev := (hleft.sub hright).eventually_ne (sub_ne_zero.mpr hne)
  obtain ⟨y, hy, hyint⟩ := mem_closure_iff_nhds.mp (I.dense_interior (M := M) x) _ hev
  exact hy (sub_eq_zero.mpr (hint y hyint))

theorem divergence_metric_change
    (q h : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence (leviCivitaConnectionOfMetric h) X x =
      divergence (leviCivitaConnectionOfMetric q) X x +
        (riemannianVolumeDensity q h x)⁻¹ *
          mvfderiv (I := I) (riemannianVolumeDensity q h) x (X x) := by
  have heq := divergence_riemannianVolumeDensity_smul q h X x
  change divergence (leviCivitaConnectionOfMetric q)
    (riemannianVolumeDensity q h • (X : ∀ y, TangentSpace I y)) x = _ at heq
  rw [divergence_smul (leviCivitaConnectionOfMetric q) inferInstance
    ((riemannianVolumeDensity_contMDiff q h).mdifferentiable (by simp)).mdifferentiableAt
    (X.contMDiff.mdifferentiable (by simp)).mdifferentiableAt] at heq
  have hne := ne_of_gt (riemannianVolumeDensity_pos q h x)
  apply (mul_left_cancel₀ hne)
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  exact heq.symm

theorem laplacian_eq_divergence_add_volumeDensity_drift
    (q h : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) :
    laplacian (leviCivitaConnectionOfMetric h) h f x =
      divergence (leviCivitaConnectionOfMetric q) (gradientFun h f) x +
        mvfderiv (I := I) f x
          (gradientFun h (fun y => Real.log (riemannianVolumeDensity q h y)) x) := by
  have heq := divergence_metric_change q h
    ⟨gradientFun h f, gradientFun_smooth h hf⟩ x
  change laplacian (leviCivitaConnectionOfMetric h) h f x =
    divergence (leviCivitaConnectionOfMetric q) (gradientFun h f) x +
      (riemannianVolumeDensity q h x)⁻¹ *
        mvfderiv (I := I) (riemannianVolumeDensity q h) x (gradientFun h f x) at heq
  rw [heq, gradientFun_log h
    ((riemannianVolumeDensity_contMDiff q h).mdifferentiable (by simp)).mdifferentiableAt
    (riemannianVolumeDensity_pos q h x), map_smul, smul_eq_mul]
  congr 2
  rw [← inner_gradientFun h (riemannianVolumeDensity q h),
    ← inner_gradientFun h f, h.symm]

theorem riemannianVolumeDensity_mul_laplacian_div
    (q h : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) :
    riemannianVolumeDensity q h x *
        laplacian (leviCivitaConnectionOfMetric h) h
          (fun y => f y / riemannianVolumeDensity q h y) x =
      divergence (leviCivitaConnectionOfMetric q) (gradientFun h f) x -
        mvfderiv (I := I) f x
          (gradientFun h (fun y => Real.log (riemannianVolumeDensity q h y)) x) -
        f x * divergence (leviCivitaConnectionOfMetric q)
          (gradientFun h (fun y => Real.log (riemannianVolumeDensity q h y))) x := by
  let ρ := riemannianVolumeDensity q h
  have hρ := riemannianVolumeDensity_contMDiff q h
  have hn (y : M) : ρ y ≠ 0 := ne_of_gt (riemannianVolumeDensity_pos q h y)
  let ψ := fun y => f y / ρ y
  have hψ : ContMDiff I 𝓘(ℝ) ∞ ψ := hf.div₀ hρ hn
  have hlog : ContMDiff I 𝓘(ℝ) ∞ (fun y => Real.log (ρ y)) := by
    intro y
    exact (Real.contDiffAt_log.mpr (hn y)).contMDiffAt.comp y (hρ y)
  let Y := gradientFun h (fun y => Real.log (ρ y))
  have hY := gradientFun_smooth h hlog
  have hgrad (y : M) : ρ y • gradientFun h ψ y =
      gradientFun h f y - f y • Y y := by
    have heq : (fun z => ρ z * ψ z) = f := by
      funext z
      exact mul_div_cancel₀ _ (hn z)
    have hm := gradientFun_mul h (hρ.mdifferentiable (by simp) y)
      (hψ.mdifferentiable (by simp) y)
    rw [heq] at hm
    apply eq_sub_iff_add_eq.mpr
    calc
      _ = ρ y • gradientFun h ψ y + ψ y • gradientFun h ρ y := by
        dsimp only [Y]
        rw [gradientFun_log h (hρ.mdifferentiable (by simp) y)
          (riemannianVolumeDensity_pos q h y), smul_smul]
        rfl
      _ = gradientFun h f y := hm.symm
  have heq := divergence_riemannianVolumeDensity_smul q h
    ⟨gradientFun h ψ, gradientFun_smooth h hψ⟩ x
  change divergence (leviCivitaConnectionOfMetric q)
      (fun y => ρ y • gradientFun h ψ y) x = _ at heq
  rw [funext hgrad] at heq
  change divergence (leviCivitaConnectionOfMetric q)
    (gradientFun h f - f • Y) x = _ at heq
  have hfY : MDiffAt (T% (f • Y)) x :=
    (hf.smul_section hY).mdifferentiable (by simp) x
  rw [divergence_sub _ ((gradientFun_smooth h hf).mdifferentiable (by simp) x) hfY,
    divergence_smul _ inferInstance (hf.mdifferentiable (by simp) x)
      (hY.mdifferentiable (by simp) x)] at heq
  calc
    _ = divergence (leviCivitaConnectionOfMetric q) (gradientFun h f) x -
        (f x * divergence (leviCivitaConnectionOfMetric q) Y x +
          mvfderiv (I := I) f x (Y x)) := heq.symm
    _ = _ := by ring

end DifferentialGeometry.Geometry.Operator
