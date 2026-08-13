import DifferentialGeometry.Analysis.Heat.Semigroup.StrongSolution

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem strongSolutionAt_smooth_representatives_satisfy_heat_equation
    (g : SmoothRiemannianMetric I M)
    {u f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    {t : ℝ}
    (hstrong : IsStrongSolutionAt (I := I) (M := M) g u f t)
    (u_smooth du_smooth f_smooth : SmoothScalar g)
    (hu : smoothToLp (I := I) (M := M) g u_smooth = u t)
    (hdu : HasDerivAt u (smoothToLp (I := I) (M := M) g du_smooth) t)
    (hf : smoothToLp (I := I) (M := M) g f_smooth = f t) :
    du_smooth = u_smooth.laplacian + f_smooth := by
  obtain ⟨u_h, hu_h, hstrong_deriv⟩ := hstrong
  let u_smooth_h : laplacianDomain (I := I) (M := M) g :=
    ⟨smoothToH1Compl (I := I) (M := M) g u_smooth,
      smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) u_smooth⟩
  have hu_h_eq : u_h = u_smooth_h := by
    apply Subtype.ext
    apply H1ComplToLp_injective_on_laplacianDomain (I := I) (M := M) g
    rw [hu_h, ← hu, H1ComplToLp_smoothToH1Compl]
  have hderiv_eq :
      smoothToLp (I := I) (M := M) g du_smooth =
        laplacianOp (I := I) (M := M) g u_h + f t :=
    hdu.unique hstrong_deriv
  apply smoothToLp_injective (I := I) (M := M) g
  rw [map_add, hderiv_eq, hu_h_eq, hf]
  exact congrArg (fun v => v + f t)
    (laplacianOp_smoothToH1Compl_eq_smoothToLp_laplacian
      (I := I) (M := M) u_smooth)

theorem mildSolution_smooth_representatives_satisfy_heat_equation
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ContDiff ℝ 1 f) {t : ℝ} (ht : 0 < t)
    (u_smooth du_smooth f_smooth : SmoothScalar g)
    (hu : smoothToLp (I := I) (M := M) g u_smooth =
      mildSolution (I := I) (M := M) g u_0 f t)
    (hdu : smoothToLp (I := I) (M := M) g du_smooth =
      -(heatPower (I := I) (M := M) g 1 t u_0) +
        mildSolution (I := I) (M := M) g (f 0) (deriv f) t)
    (hf_t : smoothToLp (I := I) (M := M) g f_smooth = f t) :
    du_smooth = u_smooth.laplacian + f_smooth := by
  apply strongSolutionAt_smooth_representatives_satisfy_heat_equation
    (I := I) (M := M) g
    (mildSolution_isStrongSolutionAt_of_hasDerivAt_forcing
      (I := I) (M := M) g u_0
      (f' := deriv f)
      (fun s => (hf.differentiable (by norm_num) s).hasDerivAt)
      hf.continuous_deriv_one ht)
    u_smooth du_smooth f_smooth hu
  · rw [hdu]
    exact mildSolution_hasDerivAt_of_contDiff_forcing
      (I := I) (M := M) g u_0 hf ht
  · exact hf_t

end HeatEquation
end Analysis
end DifferentialGeometry

end
