import DifferentialGeometry.Geometry.Metric.RicciSoliton.ChartRegularity
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Defs
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.LinearAlgebra.Basis.Bilinear


noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open Curvature Connection Operator
open DifferentialGeometry.Tensor.Coordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

theorem gradientRicciSoliton_of_chart_second_derivative
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (sigma : ℝ)
    (hcoord : ∀ x : M, ∀ i j : Fin (Module.finrank ℝ E),
      fderiv ℝ (fderiv ℝ (scalarOnE (I := I) x f)) (extChartAt I x x)
          (chartModelBasis E i) (chartModelBasis E j) =
        (sigma / 2) * g.inner x
            (centeredChartTangentBasis (I := I) x i)
            (centeredChartTangentBasis (I := I) x j) -
          ricciTensor (I := I) g x
            (centeredChartTangentBasis (I := I) x i)
            (centeredChartTangentBasis (I := I) x j) +
          ∑ k : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x i j k (extChartAt I x x) *
              fderiv ℝ (scalarOnE (I := I) x f) (extChartAt I x x)
                (chartModelBasis E k)) :
    gradientRicciSoliton (I := I) g f sigma := by
  intro x v w
  have hu : ContDiffAt ℝ ∞ (scalarOnE (I := I) x f) (extChartAt I x x) :=
    (scalarOnE_contDiffOn (I := I) x f.contMDiff).contDiffAt
      (extChartAt_target_mem_nhds (I := I) x)
  have hdu : DifferentiableAt ℝ (fderiv ℝ (scalarOnE (I := I) x f))
      (extChartAt I x x) :=
    (hu.fderiv_right (m := ∞) le_rfl).differentiableAt (by simp)
  have hsecond (i j : Fin (Module.finrank ℝ E)) :
      chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x) =
        fderiv ℝ (fderiv ℝ (scalarOnE (I := I) x f)) (extChartAt I x x)
          (chartModelBasis E i) (chartModelBasis E j) := by
    unfold chartIteratedPartialDeriv partialDeriv
    rw [fderiv_clm_apply hdu (differentiableAt_const _)]
    simp [ContinuousLinearMap.flip_apply]
  let B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    centeredChartTangentBasis (I := I) x
  have hbilin :
      (ricciTensor (I := I) g x).toBilinForm + hessFun (I := I) g f x =
        (sigma / 2) • (g.inner x).toBilinForm := by
    apply LinearMap.ext_basis B B
    intro i j
    change ricciTensor (I := I) g x
          (centeredChartTangentBasis (I := I) x i)
          (centeredChartTangentBasis (I := I) x j) +
        hessFun (I := I) g f x
          (centeredChartTangentBasis (I := I) x i)
          (centeredChartTangentBasis (I := I) x j) =
      (sigma / 2) * g.inner x
        (centeredChartTangentBasis (I := I) x i)
        (centeredChartTangentBasis (I := I) x j)
    rw [hessFun_basis_apply, chartHessianTensor_def, hsecond, hcoord]
    unfold partialDeriv
    ring
  have hvw := congrArg
    (fun q : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ => q v w) hbilin
  exact hvw

theorem exists_gradientRicciSoliton_of_local_chart_second_derivative
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (sigma : ℝ)
    (hlocal : ∀ x : M, ∃ V : Set E,
      IsOpen V ∧ extChartAt I x x ∈ V ∧
      ContDiffOn ℝ ∞ (scalarOnE (I := I) x f) V)
    (hcoord : ∀ x : M, ∀ i j : Fin (Module.finrank ℝ E),
      fderiv ℝ (fderiv ℝ (scalarOnE (I := I) x f)) (extChartAt I x x)
          (chartModelBasis E i) (chartModelBasis E j) =
        (sigma / 2) * g.inner x
            (centeredChartTangentBasis (I := I) x i)
            (centeredChartTangentBasis (I := I) x j) -
          ricciTensor (I := I) g x
            (centeredChartTangentBasis (I := I) x i)
            (centeredChartTangentBasis (I := I) x j) +
          ∑ k : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x i j k (extChartAt I x x) *
              fderiv ℝ (scalarOnE (I := I) x f) (extChartAt I x x)
                (chartModelBasis E k)) :
    ∃ hf : ContMDiff I 𝓘(ℝ) ∞ f,
      gradientRicciSoliton (I := I) g ⟨f, hf⟩ sigma := by
  have hf : ContMDiff I 𝓘(ℝ) ∞ f := by
    intro x
    obtain ⟨V, hV, hxV, hfV⟩ := hlocal x
    apply contMDiffAt_iff_source.mpr
    exact (hfV.contDiffAt (hV.mem_nhds hxV)).contMDiffAt.contMDiffWithinAt
  exact ⟨hf, gradientRicciSoliton_of_chart_second_derivative g ⟨f, hf⟩ sigma hcoord⟩

theorem exists_gradientRicciSoliton_of_local_chart_equation
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (sigma : ℝ)
    (hlocal : ∀ α : M, ∃ U : Set E,
      IsOpen U ∧ extChartAt I α α ∈ U ∧ U ⊆ (extChartAt I α).target ∧
      DifferentiableOn ℝ (scalarOnE (I := I) α f) U ∧
      DifferentiableOn ℝ (fderiv ℝ (scalarOnE (I := I) α f)) U ∧
      ∀ y ∈ U, ∀ i j : Fin (Module.finrank ℝ E),
        fderiv ℝ (fderiv ℝ (scalarOnE (I := I) α f)) y
            (chartModelBasis E i) (chartModelBasis E j) =
          (sigma / 2) * chartGramOnE g α i j y - chartRicciTensor g α i j y +
            ∑ k : Fin (Module.finrank ℝ E),
              chartChristoffel g α i j k y *
                fderiv ℝ (scalarOnE (I := I) α f) y (chartModelBasis E k)) :
    ∃ hf : ContMDiff I 𝓘(ℝ) ∞ f,
      gradientRicciSoliton (I := I) g ⟨f, hf⟩ sigma := by
  have hlocalSmooth : ∀ α : M, ∃ U : Set E,
      IsOpen U ∧ extChartAt I α α ∈ U ∧
      ContDiffOn ℝ ∞ (scalarOnE (I := I) α f) U := by
    intro α
    obtain ⟨U, hU, hcenter, hUt, hu, hdu, heq⟩ := hlocal α
    exact ⟨U, hU, hcenter,
      contDiffOn_of_chart_ricci_soliton_equation g α sigma hU hUt hu hdu heq⟩
  apply exists_gradientRicciSoliton_of_local_chart_second_derivative
    g f sigma hlocalSmooth
  intro x i j
  obtain ⟨U, _, hcenter, _, _, _, heq⟩ := hlocal x
  have hgood : x ∈ chartLeviCivitaGoodSet (I := I) x := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source]
    exact mem_extChartAt_source x
  have hric :
      ricciTensor (I := I) g x
          (centeredChartTangentBasis (I := I) x i)
          (centeredChartTangentBasis (I := I) x j) =
        chartRicciTensor g x i j (extChartAt I x x) := by
    simpa only [chartBasisVecFiber_self] using
      (ricciTensor_chartBasisVec_alpha_eq g x i j hgood)
  have hgram : chartGramOnE g x i j (extChartAt I x x) =
      g.inner x (centeredChartTangentBasis (I := I) x i)
        (centeredChartTangentBasis (I := I) x j) := by
    rw [chartGramOnE_def, extChartAt_to_inv, chartGramMatrix_apply,
      chartBasisVecFiber_self, chartBasisVecFiber_self]
  have h := heq (extChartAt I x x) hcenter i j
  rw [hgram, ← hric] at h
  exact h

end DifferentialGeometry.Geometry
