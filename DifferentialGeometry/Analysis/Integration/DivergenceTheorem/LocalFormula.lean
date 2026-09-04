import DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Analysis.Integration.L2.CompactSupport
import DifferentialGeometry.Analysis.Calculus.PartialDerivative.Defs
import DifferentialGeometry.Geometry.Coordinates.VectorField
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
export DifferentialGeometry.Integral.Measure
  (chartDensityOnE chartDensityOnE_contDiffOn)
export DifferentialGeometry.Tensor.Coordinates
  (chartCoeff chartCoeff_contMDiffOn chartCoeff_def chartCoeff_recompose
    chartCoeffOnE chartCoeffOnE_contDiffOn)

def localDivergence (g : SmoothRiemannianMetric I M)
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    M → ℝ := fun x =>
  (∑ i : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
        (fun y => chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y)
        (extChartAt I α x))
    / chartDensity (I := I) g α x

@[simp] lemma localDivergence_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    localDivergence (I := I) g α X x =
      (∑ i : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
            (fun y => chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
        / chartDensity (I := I) g α x := rfl

lemma chartCoeffOnE_mul_chartDensityOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E =>
        chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y)
      (extChartAt I α).target :=
  (chartCoeffOnE_contDiffOn (I := I) α X i).mul
    (chartDensityOnE_contDiffOn (I := I) g α)

private lemma partialDeriv_contDiffOn_interior
    (i : Fin (Module.finrank ℝ E)) {u : E → ℝ} {s : Set E}
    (hu : ContDiffOn ℝ ∞ u s) :
    ContDiffOn ℝ ∞ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i u) (interior s) := by
  have hu_int : ContDiffOn ℝ ∞ u (interior s) := hu.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ u) (interior s) :=
    hu_int.fderiv_of_isOpen isOpen_interior
      (by rw [ENat.coe_top_add_one])
  have hconst : ContDiffOn ℝ ∞ (fun _ : E => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
      (interior s) := contDiffOn_const
  exact hfderiv.clm_apply hconst

lemma partialDeriv_chartCoeffOnE_mul_chartDensityOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) :=
  partialDeriv_contDiffOn_interior i
    (chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i)

private def localDivergenceDomain (α : M) : Set M :=
  (extChartAt I α).source ∩
    (extChartAt I α) ⁻¹' interior (extChartAt I α).target

omit [Module.Finite ℝ E] in
private lemma localDivergenceDomain_subset_baseSet (α : M) :
    localDivergenceDomain (I := I) α ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx
  rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
  rw [← extChartAt_source_eq_chartAt_source (I := I)]
  exact hx.1

private lemma localDivergence_summand_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) α X i y *
              chartDensityOnE (I := I) g α y)
          (extChartAt I α x))
      (localDivergenceDomain (I := I) α) := by
  have hpartial : ContDiffOn ℝ ∞
      (fun y : E =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) :=
    partialDeriv_chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i
  have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun y : E =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) := hpartial.contMDiffOn
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  have hchart' : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (localDivergenceDomain (I := I) α) := by
    refine hchart.mono ?_
    intro x hx
    have h1 : x ∈ (extChartAt I α).source := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
    exact h1
  have hsubset : localDivergenceDomain (I := I) α ⊆
      (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target :=
    fun _ hx => hx.2
  exact hpartialM.comp hchart' hsubset

private lemma chartDensity_contMDiffOn_localDivergenceDomain
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g α)
      (localDivergenceDomain (I := I) α) :=
  (chartDensity_contMDiffOn (I := I) g α).mono
    (localDivergenceDomain_subset_baseSet (I := I) α)

private lemma chartDensity_ne_zero_on_localDivergenceDomain
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ x ∈ localDivergenceDomain (I := I) α, chartDensity (I := I) g α x ≠ 0 :=
  fun _ hx => ne_of_gt
    (chartDensity_pos (I := I) g α
      (localDivergenceDomain_subset_baseSet (I := I) α hx))

theorem localDivergence_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn I 𝓘(ℝ) ∞ (localDivergence (I := I) g α X)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  have hnum : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        ∑ i : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
            (fun y : E =>
              chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
      (localDivergenceDomain (I := I) α) :=
    contMDiffOn_finsetSum
      (fun i _ => localDivergence_summand_contMDiffOn (I := I) g α X i)
  have hden :
      ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g α)
        (localDivergenceDomain (I := I) α) :=
    chartDensity_contMDiffOn_localDivergenceDomain (I := I) g α
  exact hnum.div₀ hden
    (chartDensity_ne_zero_on_localDivergenceDomain (I := I) g α)

def divergenceG (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun x => localDivergence (I := I) g x X x

@[simp] lemma divergence_g_def
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergenceG (I := I) g X x = localDivergence (I := I) g x X x := rfl

theorem divergence_g_chart_product
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergenceG (I := I) g X x =
      (∑ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (chartCoeffOnE (I := I) x X i) (extChartAt I x x)) +
        (∑ i : Fin (Module.finrank ℝ E),
          chartCoeffOnE (I := I) x X i (extChartAt I x x) *
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
              (chartDensityOnE (I := I) g x) (extChartAt I x x)) /
          chartDensity (I := I) g x x := by
  classical
  set y₀ : E := extChartAt I x x with hy₀_def
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hy₀_target : y₀ ∈ (extChartAt I x).target := by
    simp [hy₀_def]
  have htarget_nhd : (extChartAt I x).target ∈ 𝓝 y₀ :=
    (isOpen_extChartAt_target (I := I) x).mem_nhds hy₀_target
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hρ_pos : 0 < chartDensity (I := I) g x x :=
    chartDensity_pos (I := I) g x hbase
  have hρ_ne : chartDensity (I := I) g x x ≠ 0 := ne_of_gt hρ_pos
  have hsymm : (extChartAt I x).symm y₀ = x := by
    simp [hy₀_def]
  have hρOnE :
      chartDensityOnE (I := I) g x y₀ = chartDensity (I := I) g x x := by
    change chartDensity (I := I) g x ((extChartAt I x).symm y₀) =
      chartDensity (I := I) g x x
    rw [hsymm]
  have hcoeff_diff :
      ∀ i : Fin (Module.finrank ℝ E),
        DifferentiableAt ℝ (chartCoeffOnE (I := I) x X i) y₀ := by
    intro i
    have hsmooth : ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) x X i)
        (extChartAt I x).target :=
      chartCoeffOnE_contDiffOn (I := I) x X i
    exact ((hsmooth y₀ hy₀_target).contDiffAt htarget_nhd).differentiableAt
      (by simp)
  have hρ_diff :
      DifferentiableAt ℝ (chartDensityOnE (I := I) g x) y₀ := by
    have hsmooth : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g x)
        (extChartAt I x).target :=
      chartDensityOnE_contDiffOn (I := I) g x
    exact ((hsmooth y₀ hy₀_target).contDiffAt htarget_nhd).differentiableAt
      (by simp)
  have hprod :
      ∀ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) x X i y *
              chartDensityOnE (I := I) g x y) y₀ =
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀ *
            chartDensityOnE (I := I) g x y₀ +
          chartCoeffOnE (I := I) x X i y₀ *
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartDensityOnE (I := I) g x) y₀ := by
    intro i
    unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
    have hmul : fderiv ℝ
        (fun y : E =>
          chartCoeffOnE (I := I) x X i y *
            chartDensityOnE (I := I) g x y) y₀ =
        chartCoeffOnE (I := I) x X i y₀ •
          fderiv ℝ (chartDensityOnE (I := I) g x) y₀ +
        chartDensityOnE (I := I) g x y₀ •
          fderiv ℝ (chartCoeffOnE (I := I) x X i) y₀ :=
      fderiv_fun_mul (hcoeff_diff i) hρ_diff
    rw [hmul]
    rw [add_apply,
      smul_apply, smul_apply]
    simp only [smul_eq_mul]
    ring
  rw [divergence_g_def, localDivergence_def]
  change
    (∑ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) x X i y *
              chartDensityOnE (I := I) g x y) y₀) /
      chartDensity (I := I) g x x = _
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) x X i y *
              chartDensityOnE (I := I) g x y) y₀) =
        ∑ i : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀ *
            chartDensityOnE (I := I) g x y₀ +
          chartCoeffOnE (I := I) x X i y₀ *
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartDensityOnE (I := I) g x) y₀) by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact hprod i]
  rw [Finset.sum_add_distrib]
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀ *
          chartDensityOnE (I := I) g x y₀) =
        (∑ i : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀) *
          chartDensityOnE (I := I) g x y₀ by
      rw [Finset.sum_mul]]
  rw [hρOnE]
  rw [add_div]
  rw [mul_div_assoc, div_self hρ_ne, mul_one]

end DivergenceTheorem
end Integral
end DifferentialGeometry
