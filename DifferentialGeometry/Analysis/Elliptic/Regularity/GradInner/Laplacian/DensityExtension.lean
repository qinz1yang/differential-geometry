import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.Smooth

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLaplacianDensityExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDomain
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmooth

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem gradInnerCLM_eq_H1ComplToLp_resolvent_of_smooth_approximation
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_convergence_H1Compl : Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      atTop (𝓝 u_h))
    (h_convergence_candidate : Tendsto
      (fun n => gradInnerLaplacianRhs (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (gradInnerLaplacianRhs
        (I := I) (M := M) g φ hu_h)))
    (h_smooth_identity : ∀ n,
      gradInnerLaplacianRhs (I := I) (M := M) g φ
          (smoothToH1Compl_mem_laplacianDomainPow_two
            (I := I) (M := M) g (h_smooth_seq n)) =
        smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ
            (h_smooth_seq n)).oneSubLapClassical) :
    gradInnerCLM (I := I) (M := M) g φ u_h =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs
            (I := I) (M := M) g φ hu_h)) := by
  classical
  have h_LHS_convergence : Tendsto
      (fun n => gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (gradInnerCLM (I := I) (M := M) g φ u_h)) := by
    exact ((gradInnerCLM (I := I) (M := M) g φ).continuous.tendsto _).comp
      h_convergence_H1Compl
  have h_RHS_convergence : Tendsto
      (fun n => H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g (h_smooth_seq n)))))
      atTop (𝓝 (H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs
            (I := I) (M := M) g φ hu_h)))) := by
    have h_resolvent_cont :
        Continuous (resolvent (I := I) (M := M) g) :=
      (resolvent (I := I) (M := M) g).continuous
    have h_H1ComplToLp_cont :
        Continuous (H1ComplToLp (I := I) (M := M) g) :=
      (H1ComplToLp (I := I) (M := M) g).continuous
    have h_composition_cont :
        Continuous (fun f => H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g f)) :=
      h_H1ComplToLp_cont.comp h_resolvent_cont
    exact (h_composition_cont.tendsto _).comp h_convergence_candidate
  have h_smooth_eq : ∀ n,
      gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n)) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g (h_smooth_seq n)))) := fun n =>
    gradInnerCLM_smoothToH1Compl_eq_resolvent_of_rhs_identification
      (I := I) (M := M) g φ (h_smooth_seq n) (h_smooth_identity n)
  have h_seq_eq : (fun n => gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))) =
      (fun n => H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianRhs (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g (h_smooth_seq n))))) := by
    funext n
    exact h_smooth_eq n
  rw [h_seq_eq] at h_LHS_convergence
  exact tendsto_nhds_unique h_LHS_convergence h_RHS_convergence

theorem gradInnerCLM_mem_image_laplacianDomain_of_smooth_approximation
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_convergence_H1Compl : Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      atTop (𝓝 u_h))
    (h_convergence_candidate : Tendsto
      (fun n => gradInnerLaplacianRhs (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (gradInnerLaplacianRhs
        (I := I) (M := M) g φ hu_h)))
    (h_smooth_identity : ∀ n,
      gradInnerLaplacianRhs (I := I) (M := M) g φ
          (smoothToH1Compl_mem_laplacianDomainPow_two
            (I := I) (M := M) g (h_smooth_seq n)) =
        smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ
            (h_smooth_seq n)).oneSubLapClassical) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  classical
  refine ⟨resolvent (I := I) (M := M) g
    (gradInnerLaplacianRhs (I := I) (M := M) g φ hu_h),
    ?_, ?_⟩
  · exact (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
      ⟨gradInnerLaplacianRhs (I := I) (M := M) g φ hu_h, rfl⟩
  · exact (gradInnerCLM_eq_H1ComplToLp_resolvent_of_smooth_approximation
      (I := I) (M := M) g φ hu_h h_smooth_seq h_convergence_H1Compl
      h_convergence_candidate h_smooth_identity).symm

theorem smoothMulH1Compl_mem_pow_two_of_smooth_approximation
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_convergence_H1Compl : Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      atTop (𝓝 u_h))
    (h_convergence_candidate : Tendsto
      (fun n => gradInnerLaplacianRhs (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (gradInnerLaplacianRhs
        (I := I) (M := M) g φ hu_h)))
    (h_smooth_identity : ∀ n,
      gradInnerLaplacianRhs (I := I) (M := M) g φ
          (smoothToH1Compl_mem_laplacianDomainPow_two
            (I := I) (M := M) g (h_smooth_seq n)) =
        smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ
            (h_smooth_seq n)).oneSubLapClassical) :
    smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2 := by
  classical
  rw [smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image
    (I := I) (M := M) g φ hu_h]
  exact gradInnerCLM_mem_image_laplacianDomain_of_smooth_approximation
    (I := I) (M := M) g φ hu_h h_smooth_seq h_convergence_H1Compl
    h_convergence_candidate h_smooth_identity

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_smoothSeq_convergence
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_convergence_H1Compl : Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      atTop (𝓝 u_h)) :
    Tendsto
      (fun n => gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (gradInnerCLM (I := I) (M := M) g φ u_h)) :=
  ((gradInnerCLM (I := I) (M := M) g φ).continuous.tendsto _).comp h_convergence_H1Compl

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciPairingCLM_smoothSeq_convergence
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_convergence_H1Compl : Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      atTop (𝓝 u_h)) :
    Tendsto
      (fun n => ricciPairingCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (ricciPairingCLM (I := I) (M := M) g φ u_h)) :=
  ((ricciPairingCLM (I := I) (M := M) g φ).continuous.tendsto _).comp h_convergence_H1Compl

end GradInnerLaplacianDensityExtension
end Laplacian
end Analysis
end DifferentialGeometry

end
