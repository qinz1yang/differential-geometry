import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.DerivedDataConstructor
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.VariationalIdentity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.ThirdMixedPartial
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.FChartEffDef
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.ResidualMemW1p
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.SmoothCoefWeakPartialIBP
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.VariationalIdentityTestFunctionCalculus
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.VariationalIdentityBaseDataLocalRegularity
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.VariationalIdentityIntegrationByParts
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.VariationalIdentityVanishingOffSupport
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TwiceDifferentiatedVariationalIdentity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedVariationalIdentity
open DifferentialGeometry.Analysis.Laplacian.ChosenThirdMixedPartialChartPushed
open DifferentialGeometry.Analysis.Laplacian.FChartEffTwiceDef
open DifferentialGeometry.Analysis.Laplacian.FChartResidualMemW1p
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma integrable_mul_triple_of_tsupport {Ω K : Set EuclN}
    (hΩ_open : IsOpen Ω) (hK_in : K ⊆ Ω) (hK_compact : IsCompact K)
    (hK_closed : IsClosed K) (hK_meas : MeasurableSet K)
    {a : EuclN → ℝ} (ha_cont_on : ContinuousOn a Ω)
    {u : EuclN → ℝ} (hu_int : IntegrableOn u K (volume : Measure EuclN))
    {h₁ : EuclN → ℝ} (hh₁_cont : Continuous h₁) (hh₁_supp : tsupport h₁ ⊆ K) :
    Integrable (fun y => a y * u y * h₁ y)
      ((volume : Measure EuclN).restrict Ω) := by
  let h_prod : EuclN → ℝ := fun y => a y * h₁ y
  have hh_prod_supp : tsupport h_prod ⊆ K := by
    refine closure_minimal (fun y hy => ?_) hK_closed
    by_contra hy_notin
    have hh1y : h₁ y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy_notin (hh₁_supp h))
    exact hy (by change a y * _ = 0; rw [hh1y, mul_zero])
  have hh_prod_cont : Continuous h_prod := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ K
    · exact (ha_cont_on.continuousAt
        (hΩ_open.mem_nhds (hK_in hy))).mul hh₁_cont.continuousAt
    · have h_compl_open : IsOpen (Kᶜ) := hK_closed.isOpen_compl
      have h_eq_zero : ∀ᶠ z in 𝓝 y, h_prod z = 0 := by
        filter_upwards [h_compl_open.mem_nhds hy] with z hz
        have hh1z : h₁ z = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hz (hh₁_supp h))
        change a z * h₁ z = 0; rw [hh1z, mul_zero]
      rw [continuousAt_congr h_eq_zero]; exact continuousAt_const
  have hh_prod_contOn_K : ContinuousOn h_prod K := hh_prod_cont.continuousOn
  have hu_h_int_K : IntegrableOn (fun y => u y * h_prod y) K
      (volume : Measure EuclN) :=
    hu_int.mul_continuousOn hh_prod_contOn_K hK_compact
  have h_vanish : ∀ y, y ∉ K → u y * h_prod y = 0 := by
    intro y hy
    have : h_prod y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hy_supp => hy (hh_prod_supp hy_supp))
    simp [this]
  have h_eq_ind :
      (fun y => u y * h_prod y) = K.indicator (fun y => u y * h_prod y) := by
    funext y
    by_cases hy : y ∈ K
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy, h_vanish y hy]
  have ind_int : Integrable (K.indicator (fun y => u y * h_prod y))
      (volume : Measure EuclN) :=
    (integrable_indicator_iff hK_meas).mpr hu_h_int_K
  have full_int : Integrable (fun y => u y * h_prod y) (volume : Measure EuclN) := by
    rw [h_eq_ind]; exact ind_int
  have h_reassoc : (fun y => u y * h_prod y) =
      (fun y => a y * u y * h₁ y) := by
    funext y; change u y * (a y * h₁ y) = _; ring
  rw [h_reassoc] at full_int
  exact full_int.restrict

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma fderiv_apply_continuousOn_of_contDiffOn {Ω : Set EuclN}
    (hΩ : IsOpen Ω) {a : EuclN → ℝ} (ha : ContDiffOn ℝ ∞ a Ω) (v : EuclN) :
    ContinuousOn (fun y => (fderiv ℝ a y) v) Ω := by
  have h_fderiv : ContDiffOn ℝ ∞ (fun y => fderiv ℝ a y) Ω :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 ha).2
  have h_eval : ContDiff ℝ ∞ (fun (L : EuclN →L[ℝ] ℝ) => L v) :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff
  exact (h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)).continuousOn

private lemma integral_add_thirteen {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : α → ℝ}
    (h1 : Integrable f1 μ)
    (h2 : Integrable f2 μ)
    (h3 : Integrable f3 μ)
    (h4 : Integrable f4 μ)
    (h5 : Integrable f5 μ)
    (h6 : Integrable f6 μ)
    (h7 : Integrable f7 μ)
    (h8 : Integrable f8 μ)
    (h9 : Integrable f9 μ)
    (h10 : Integrable f10 μ)
    (h11 : Integrable f11 μ)
    (h12 : Integrable f12 μ)
    (h13 : Integrable f13 μ) :
    (∫ y, f1 y + f2 y + f3 y + f4 y + f5 y + f6 y + f7 y + f8 y + f9 y + f10 y + f11 y + f12 y + f13
      y ∂μ) =
      (∫ y, f1 y ∂μ) +
      (∫ y, f2 y ∂μ) +
      (∫ y, f3 y ∂μ) +
      (∫ y, f4 y ∂μ) +
      (∫ y, f5 y ∂μ) +
      (∫ y, f6 y ∂μ) +
      (∫ y, f7 y ∂μ) +
      (∫ y, f8 y ∂μ) +
      (∫ y, f9 y ∂μ) +
      (∫ y, f10 y ∂μ) +
      (∫ y, f11 y ∂μ) +
      (∫ y, f12 y ∂μ) +
      (∫ y, f13 y ∂μ) := by
  have hs2 : Integrable (fun y => f1 y + f2 y) μ := h1.add h2
  have hs3 : Integrable (fun y => f1 y + f2 y + f3 y) μ := hs2.add h3
  have hs4 : Integrable (fun y => f1 y + f2 y + f3 y + f4 y) μ := hs3.add h4
  have hs5 : Integrable (fun y => f1 y + f2 y + f3 y + f4 y + f5 y) μ := hs4.add h5
  have hs6 : Integrable (fun y => f1 y + f2 y + f3 y + f4 y + f5 y + f6 y) μ := hs5.add h6
  have hs7 : Integrable (fun y => f1 y + f2 y + f3 y + f4 y + f5 y + f6 y + f7 y) μ := hs6.add h7
  have hs8 : Integrable (fun y => f1 y + f2 y + f3 y + f4 y + f5 y + f6 y + f7 y + f8 y) μ :=
    hs7.add h8
  have hs9 : Integrable (fun y => f1 y + f2 y + f3 y + f4 y + f5 y + f6 y + f7 y + f8 y + f9 y) μ :=
    hs8.add h9
  have hs10 : Integrable (fun y => f1 y + f2 y + f3 y + f4 y + f5 y + f6 y + f7 y + f8 y + f9 y +
    f10 y) μ := hs9.add h10
  have hs11 : Integrable (fun y => f1 y + f2 y + f3 y + f4 y + f5 y + f6 y + f7 y + f8 y + f9 y +
    f10 y + f11 y) μ := hs10.add h11
  have hs12 : Integrable (fun y => f1 y + f2 y + f3 y + f4 y + f5 y + f6 y + f7 y + f8 y + f9 y +
    f10 y + f11 y + f12 y) μ := hs11.add h12
  rw [MeasureTheory.integral_add hs12 h13,
    MeasureTheory.integral_add hs11 h12,
    MeasureTheory.integral_add hs10 h11,
    MeasureTheory.integral_add hs9 h10,
    MeasureTheory.integral_add hs8 h9,
    MeasureTheory.integral_add hs7 h8,
    MeasureTheory.integral_add hs6 h7,
    MeasureTheory.integral_add hs5 h6,
    MeasureTheory.integral_add hs4 h5,
    MeasureTheory.integral_add hs3 h4,
    MeasureTheory.integral_add hs2 h3,
    MeasureTheory.integral_add h1 h2]

-- Residual diffuse `whnf`/`isDefEq` cost of this ~1600-line chart identity. Factoring its
-- integral-additivity (`integral_add_thirteen`), triple-integrability
-- (`integrable_mul_triple_of_tsupport`), fderiv-apply (`fderiv_apply_continuousOn_of_contDiffOn`)
-- and sum-distribution steps into the lemmas above cut the needed budget from 4000000 to ~230000
-- (default 200000); the remainder is spread across the 295-line numerator-decomposition block.
private lemma numerator_secondOrder_decomp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ}
    (Ω K : Set EuclN)
    (integrable_triple_psi : ∀ {a : EuclN → ℝ}, ContinuousOn a Ω →
        ∀ {u : EuclN → ℝ}, IntegrableOn u K (volume : Measure EuclN) →
        Integrable (fun y => a y * u y * ψ y)
          ((volume : Measure EuclN).restrict Ω))
    (hΩ_open : IsOpen Ω)
    (h_base_wp_int : ∀ i : Fin (Module.finrank ℝ E),
      IntegrableOn ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)).weak_partial i) K
        (volume : Measure EuclN))
    (h_base_uc_int : IntegrableOn (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)).u_chart K
        (volume : Measure EuclN))
    (h_base_fc_int : IntegrableOn (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)).f_chart K
        (volume : Measure EuclN))
    (h_chosenFChartDeriv_int : ∀ l : Fin (Module.finrank ℝ E),
      IntegrableOn (chosenFChartDeriv (I := I) (M := M) g α hu_h l)
        K (volume : Measure EuclN))
    (h_fChartDeriv2_int :
      IntegrableOn (fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂)
        K (volume : Measure EuclN))
    (h_c_cont_on : ContinuousOn (densityOnEuclid (I := I) g α) Ω)
    (h_d2c_cont_on : ContinuousOn
      (densitySecondDerivOnEuclid (I := I) g α l₁ l₂) Ω)
    (h_dc_l₁_cont_on : ContinuousOn (densityDerivOnEuclid (I := I) g α l₁) Ω)
    (h_dc_l₂_cont_on : ContinuousOn (densityDerivOnEuclid (I := I) g α l₂) Ω)
    (h_int_C1_pair : ∀ i j,
      Integrable (fun y => (fderiv ℝ (weightedInvGramSecondDerivOnEuclid
            (I := I) g α i j l₁ l₂) y) (EuclideanSpace.single j 1) *
          (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)).weak_partial i y
        * ψ y)
        ((volume : Measure EuclN).restrict Ω))
    (h_int_C2_pair : ∀ i j,
      Integrable (fun y => weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y)
        ((volume : Measure EuclN).restrict Ω))
    (h_int_C3_pair : ∀ i j,
      Integrable (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid
            (I := I) g α i j l₁) y) (EuclideanSpace.single j 1) *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y * ψ y)
        ((volume : Measure EuclN).restrict Ω))
    (h_int_C4_pair : ∀ i j,
      Integrable (fun y => weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
          chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₂ j y * ψ y)
        ((volume : Measure EuclN).restrict Ω))
    (h_int_X1_named : ∀ i j,
      Integrable (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid
            (I := I) g α i j l₂) y) (EuclideanSpace.single j 1) *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y * ψ y)
        ((volume : Measure EuclN).restrict Ω))
    (h_int_X2_named : ∀ i j,
      Integrable (fun y => weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
          chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ j y * ψ y)
        ((volume : Measure EuclN).restrict Ω)) :
    (∫ y in Ω,
      effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
      ∂(volume : Measure EuclN)) =
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                (EuclideanSpace.single j 1) *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
              ψ y
              ∂(volume : Measure EuclN)) +
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
              chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ j y *
              ψ y
              ∂(volume : Measure EuclN)) +
      (-
         ∫ y in Ω,
            (fderiv ℝ (densityOnEuclid (I := I) g α) y) (EuclideanSpace.single l₂ 1) *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1
                hu_h)).weak_partial l₁ y * ψ y ∂(volume : Measure EuclN)) +
     ∫ y in Ω,
     (fderiv ℝ (densityOnEuclid (I := I) g α) y) (EuclideanSpace.single l₂ 1) *
     chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y
     ∂(volume : Measure EuclN) +
     ∫ y in Ω, densityOnEuclid (I := I) g α y *
     fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y * ψ y
     ∂(volume : Measure EuclN) +
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Ω,
              (fderiv ℝ (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y)
                (EuclideanSpace.single j 1) *
              (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1
                hu_h)).weak_partial i y * ψ y
              ∂(volume : Measure EuclN)) +
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Ω, weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y
              ∂(volume : Measure EuclN)) +
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                (EuclideanSpace.single j 1) *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y * ψ y
              ∂(volume : Measure EuclN)) +
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
              chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₂ j y * ψ y
              ∂(volume : Measure EuclN)) +
      (-
         ∫ y in Ω,
            (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y) (EuclideanSpace.single l₂ 1) *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)).u_chart y
                * ψ y ∂(volume : Measure EuclN)) +
      (-
         ∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1
                hu_h)).weak_partial l₂ y * ψ y ∂(volume : Measure EuclN)) +
     ∫ y in Ω,
     (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y) (EuclideanSpace.single l₂ 1) *
     (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
       (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
         ∂(volume : Measure EuclN) +
     ∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
     chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ y * ψ y
     ∂(volume : Measure EuclN) := by
  let D_base : ChartBilinearH1ComplData (I := I) (M := M) g α :=
    chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
  let I_num : ℝ := ∫ y in Ω,
    effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
    ∂(volume : Measure EuclN)
  let X1 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω,
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
        (EuclideanSpace.single j 1) *
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
      ψ y
      ∂(volume : Measure EuclN)
  let X2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ j y *
      ψ y
      ∂(volume : Measure EuclN)
  let N_A3 : ℝ := ∫ y in Ω,
    (fderiv ℝ (densityOnEuclid (I := I) g α) y) (EuclideanSpace.single l₂ 1) *
    D_base.weak_partial l₁ y * ψ y ∂(volume : Measure EuclN)
  let N_B1 : ℝ := ∫ y in Ω,
    (fderiv ℝ (densityOnEuclid (I := I) g α) y) (EuclideanSpace.single l₂ 1) *
    chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y
    ∂(volume : Measure EuclN)
  let N_B2 : ℝ := ∫ y in Ω, densityOnEuclid (I := I) g α y *
    fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y * ψ y
    ∂(volume : Measure EuclN)
  let C1 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω,
      (fderiv ℝ (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y)
        (EuclideanSpace.single j 1) *
      D_base.weak_partial i y * ψ y
      ∂(volume : Measure EuclN)
  let C2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω, weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y
      ∂(volume : Measure EuclN)
  let C3 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω,
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
        (EuclideanSpace.single j 1) *
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y * ψ y
      ∂(volume : Measure EuclN)
  let C4 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₂ j y * ψ y
      ∂(volume : Measure EuclN)
  let N_D1 : ℝ := ∫ y in Ω,
    (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y) (EuclideanSpace.single l₂ 1) *
    D_base.u_chart y * ψ y ∂(volume : Measure EuclN)
  let N_D2 : ℝ := ∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
    D_base.weak_partial l₂ y * ψ y ∂(volume : Measure EuclN)
  let N_E1 : ℝ := ∫ y in Ω,
    (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y) (EuclideanSpace.single l₂ 1) *
    D_base.f_chart y * ψ y ∂(volume : Measure EuclN)
  let N_E2 : ℝ := ∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
    chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ y * ψ y
    ∂(volume : Measure EuclN)
  classical
  change (∫ y in Ω,
      effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
      ∂(volume : Measure EuclN)) = _
  have h_integrand_eq : ∀ y : EuclN,
      effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
              (EuclideanSpace.single j 1) *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
            ψ y) +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
            chosenThirdMixedPartialChartPushedU
              (I := I) (M := M) g α u_h i l₁ j y *
            ψ y) +
      (- (densityDerivOnEuclid (I := I) g α l₂ y *
            D_base.weak_partial l₁ y * ψ y)) +
      densityDerivOnEuclid (I := I) g α l₂ y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y +
      densityOnEuclid (I := I) g α y *
        fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y * ψ y +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y)
              (EuclideanSpace.single j 1) *
            D_base.weak_partial i y * ψ y) +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y *
            ψ y) +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
              (EuclideanSpace.single j 1) *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
            ψ y) +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
            chosenThirdMixedPartialChartPushedU
              (I := I) (M := M) g α u_h i l₂ j y *
            ψ y) +
      (- (densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y *
            D_base.u_chart y * ψ y)) +
      (- (densityDerivOnEuclid (I := I) g α l₁ y *
            D_base.weak_partial l₂ y * ψ y)) +
      densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y * D_base.f_chart y * ψ y +
      densityDerivOnEuclid (I := I) g α l₁ y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ y * ψ y := by
    intro y
    unfold effectiveSourceChartSecondOrderNumerator
    simp only [add_mul, sub_mul, Finset.sum_mul]
    ring
  rw [setIntegral_congr_fun hΩ_open.measurableSet (fun y _ => h_integrand_eq y)]
  let int_A1 : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
          (EuclideanSpace.single j 1) *
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
        ψ y
  let int_A2 : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
        chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ j y *
        ψ y
  let int_A3 : EuclN → ℝ := fun y =>
    - (densityDerivOnEuclid (I := I) g α l₂ y *
        D_base.weak_partial l₁ y * ψ y)
  let int_B1 : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α l₂ y *
      chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y
  let int_B2 : EuclN → ℝ := fun y =>
    densityOnEuclid (I := I) g α y *
      fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y * ψ y
  let int_C1 : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y)
          (EuclideanSpace.single j 1) *
        D_base.weak_partial i y * ψ y
  let int_C2 : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y *
        ψ y
  let int_C3 : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
          (EuclideanSpace.single j 1) *
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
        ψ y
  let int_C4 : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
        chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₂ j y *
        ψ y
  let int_D1 : EuclN → ℝ := fun y =>
    - (densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y *
        D_base.u_chart y * ψ y)
  let int_D2 : EuclN → ℝ := fun y =>
    - (densityDerivOnEuclid (I := I) g α l₁ y *
        D_base.weak_partial l₂ y * ψ y)
  let int_E1 : EuclN → ℝ := fun y =>
    densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y *
      D_base.f_chart y * ψ y
  let int_E2 : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α l₁ y *
      chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ y * ψ y
  have hint_A1 : Integrable int_A1 ((volume : Measure EuclN).restrict Ω) :=
    integrable_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => h_int_X1_named i j))
  have hint_A2 : Integrable int_A2 ((volume : Measure EuclN).restrict Ω) :=
    integrable_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => h_int_X2_named i j))
  have hint_A3 : Integrable int_A3 ((volume : Measure EuclN).restrict Ω) :=
    (integrable_triple_psi h_dc_l₂_cont_on (h_base_wp_int l₁)).neg
  have hint_B1 : Integrable int_B1 ((volume : Measure EuclN).restrict Ω) :=
    integrable_triple_psi h_dc_l₂_cont_on (h_chosenFChartDeriv_int l₁)
  have hint_B2 : Integrable int_B2 ((volume : Measure EuclN).restrict Ω) :=
    integrable_triple_psi h_c_cont_on h_fChartDeriv2_int
  have hint_C1 : Integrable int_C1 ((volume : Measure EuclN).restrict Ω) :=
    integrable_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => h_int_C1_pair i j))
  have hint_C2 : Integrable int_C2 ((volume : Measure EuclN).restrict Ω) :=
    integrable_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => h_int_C2_pair i j))
  have hint_C3 : Integrable int_C3 ((volume : Measure EuclN).restrict Ω) :=
    integrable_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => h_int_C3_pair i j))
  have hint_C4 : Integrable int_C4 ((volume : Measure EuclN).restrict Ω) :=
    integrable_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => h_int_C4_pair i j))
  have hint_D1 : Integrable int_D1 ((volume : Measure EuclN).restrict Ω) :=
    (integrable_triple_psi h_d2c_cont_on h_base_uc_int).neg
  have hint_D2 : Integrable int_D2 ((volume : Measure EuclN).restrict Ω) :=
    (integrable_triple_psi h_dc_l₁_cont_on (h_base_wp_int l₂)).neg
  have hint_E1 : Integrable int_E1 ((volume : Measure EuclN).restrict Ω) :=
    integrable_triple_psi h_d2c_cont_on h_base_fc_int
  have hint_E2 : Integrable int_E2 ((volume : Measure EuclN).restrict Ω) :=
    integrable_triple_psi h_dc_l₁_cont_on (h_chosenFChartDeriv_int l₂)
  have h_int_split := integral_add_thirteen hint_A1 hint_A2 hint_A3 hint_B1
    hint_B2 hint_C1 hint_C2 hint_C3 hint_C4 hint_D1 hint_D2 hint_E1 hint_E2
  have eq_intA1 : (∫ y in Ω, int_A1 y ∂(volume : Measure EuclN)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), X1 i j := by
    change (∫ y in Ω,
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                (EuclideanSpace.single j 1) *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
              ψ y
        ∂(volume : Measure EuclN)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), X1 i j
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_X1_named i j)))]
    refine Finset.sum_congr rfl ?_; intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_X1_named i j)]
  have eq_intA2 : (∫ y in Ω, int_A2 y ∂(volume : Measure EuclN)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), X2 i j := by
    change (∫ y in Ω,
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ j y *
              ψ y
        ∂(volume : Measure EuclN)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), X2 i j
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_X2_named i j)))]
    refine Finset.sum_congr rfl ?_; intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_X2_named i j)]
  have eq_intA3 : (∫ y in Ω, int_A3 y ∂(volume : Measure EuclN)) = - N_A3 := by
    change (∫ y in Ω,
        - (densityDerivOnEuclid (I := I) g α l₂ y *
          D_base.weak_partial l₁ y * ψ y)
        ∂(volume : Measure EuclN)) = - N_A3
    rw [MeasureTheory.integral_neg]
    rfl
  have eq_intB1 : (∫ y in Ω, int_B1 y ∂(volume : Measure EuclN)) = N_B1 := rfl
  have eq_intB2 : (∫ y in Ω, int_B2 y ∂(volume : Measure EuclN)) = N_B2 := rfl
  have eq_intC1 : (∫ y in Ω, int_C1 y ∂(volume : Measure EuclN)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C1 i j := by
    change (∫ y in Ω,
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramSecondDerivOnEuclid
              (I := I) g α i j l₁ l₂) y)
              (EuclideanSpace.single j 1) *
              D_base.weak_partial i y * ψ y
        ∂(volume : Measure EuclN)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C1 i j
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_C1_pair i j)))]
    refine Finset.sum_congr rfl ?_; intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_C1_pair i j)]
  have eq_intC2 : (∫ y in Ω, int_C2 y ∂(volume : Measure EuclN)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C2 i j := by
    change (∫ y in Ω,
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y *
              ψ y
        ∂(volume : Measure EuclN)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C2 i j
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_C2_pair i j)))]
    refine Finset.sum_congr rfl ?_; intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_C2_pair i j)]
  have eq_intC3 : (∫ y in Ω, int_C3 y ∂(volume : Measure EuclN)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C3 i j := by
    change (∫ y in Ω,
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                (EuclideanSpace.single j 1) *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
              ψ y
        ∂(volume : Measure EuclN)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C3 i j
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_C3_pair i j)))]
    refine Finset.sum_congr rfl ?_; intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_C3_pair i j)]
  have eq_intC4 : (∫ y in Ω, int_C4 y ∂(volume : Measure EuclN)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C4 i j := by
    change (∫ y in Ω,
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₂ j y * ψ y
        ∂(volume : Measure EuclN)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C4 i j
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_C4_pair i j)))]
    refine Finset.sum_congr rfl ?_; intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_C4_pair i j)]
  have eq_intD1 : (∫ y in Ω, int_D1 y ∂(volume : Measure EuclN)) = - N_D1 := by
    change (∫ y in Ω,
        - (densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y *
          D_base.u_chart y * ψ y)
        ∂(volume : Measure EuclN)) = - N_D1
    rw [MeasureTheory.integral_neg]
    rfl
  have eq_intD2 : (∫ y in Ω, int_D2 y ∂(volume : Measure EuclN)) = - N_D2 := by
    change (∫ y in Ω,
        - (densityDerivOnEuclid (I := I) g α l₁ y *
          D_base.weak_partial l₂ y * ψ y)
        ∂(volume : Measure EuclN)) = - N_D2
    rw [MeasureTheory.integral_neg]
  have eq_intE1 : (∫ y in Ω, int_E1 y ∂(volume : Measure EuclN)) = N_E1 := rfl
  have eq_intE2 : (∫ y in Ω, int_E2 y ∂(volume : Measure EuclN)) = N_E2 := rfl
  rw [h_int_split, eq_intA1, eq_intA2, eq_intA3, eq_intB1, eq_intB2,
    eq_intC1, eq_intC2, eq_intC3, eq_intC4, eq_intD1, eq_intD2, eq_intE1, eq_intE2]


theorem twice_differentiated_variational_identity_holds
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_chosenFChartDeriv_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
        (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ l₂ y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN))
    + (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
        ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
      ∂(volume : Measure EuclN) := by
  classical
  let Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  let D_base := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M)
    g α (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h)
  have h_base_f_chart_memW1p :=
    base_f_chart_memW1p_from_residual_memW1p (I := I) (M := M) g α hu_h
      (fChartResidual_memW1p_truly_unconditional (I := I) (M := M) g α hu_h)
  let ψl₂ : EuclN → ℝ := fun y => (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)

  have hψl₂_smooth : ContDiff ℝ (⊤ : ℕ∞) ψl₂ :=
    contDiff_fderiv_apply_single (ψ := ψ) hψ_smooth l₂
  have hψl₂_cs : HasCompactSupport ψl₂ :=
    hasCompactSupport_fderiv_apply_single (ψ := ψ) hψ_cs l₂
  have hψl₂_supp : tsupport ψl₂ ⊆ Ω :=
    (tsupport_fderiv_apply_single_subset ψ l₂).trans hψ_supp
  have h_once := differentiated_variational_identity_holds
    (I := I) (M := M) g α hu_h l₁ hψl₂_smooth hψl₂_cs hψl₂_supp
  have h_schwarz_A1 : ∀ y : EuclN, ∀ i j : Fin (Module.finrank ℝ E),
      (fderiv ℝ ψl₂ y) (EuclideanSpace.single j 1) =
      (fderiv ℝ (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single j 1)) y)
        (EuclideanSpace.single l₂ 1) := by
    intro y _ j
    change (fderiv ℝ (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l₂ 1)) y)
        (EuclideanSpace.single j 1) = _
    exact fderiv_apply_single_swap (ψ := ψ) hψ_smooth y j l₂
  let ψj : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun j y => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
  have hψj_smooth : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψj j) := fun j =>
    contDiff_fderiv_apply_single (ψ := ψ) hψ_smooth j
  have hψj_cs : ∀ j, HasCompactSupport (ψj j) := fun j =>
    hasCompactSupport_fderiv_apply_single (ψ := ψ) hψ_cs j
  have hψj_supp : ∀ j, tsupport (ψj j) ⊆ Ω := fun j =>
    (tsupport_fderiv_apply_single_subset ψ j).trans hψ_supp
  have h_aij_contDiffOn : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ (⊤ : ℕ∞) (weightedInvGramOnEuclid (I := I) g α i j) Ω :=
    fun i j => weightedInvGramOnEuclid_contDiffOn (I := I) g α i j
  have h_pair_A1 : ∀ i j : Fin (Module.finrank ℝ E),
      (∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
                (EuclideanSpace.single l₂ 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                ψj j y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y *
                ψj j y
              ∂(volume : Measure EuclN))) := fun i j =>
    per_pair_ibp_chosenSecond (I := I) (M := M) g α hu_h i l₁ l₂
      (h_aij_contDiffOn i j) (hψj_smooth j) (hψj_cs j) (hψj_supp j)
  have h_daij_contDiffOn : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ (⊤ : ℕ∞)
        (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) Ω :=
    fun i j => weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l₂
  have h_pair_A1_inner : ∀ i j : Fin (Module.finrank ℝ E),
      (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                (EuclideanSpace.single j 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                ψ y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ j y *
                ψ y
              ∂(volume : Measure EuclN))) := fun i j =>
    per_pair_ibp_chosenSecond (I := I) (M := M) g α hu_h i l₁ j
      (h_daij_contDiffOn i j) hψ_smooth hψ_cs hψ_supp
  have h_density_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (densityOnEuclid (I := I) g α) Ω :=
    densityOnEuclid_contDiffOn (I := I) g α
  have h_A2 :
      (∫ y in Ω, densityOnEuclid (I := I) g α y *
          D_base.weak_partial l₁ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (densityOnEuclid (I := I) g α) y)
                (EuclideanSpace.single l₂ 1) *
                D_base.weak_partial l₁ y * ψ y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, densityOnEuclid (I := I) g α y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
              ∂(volume : Measure EuclN))) :=
    per_pair_ibp_base_weak_partial (I := I) (M := M) g α hu_h l₁ l₂
      h_density_contDiffOn hψ_smooth hψ_cs hψ_supp
  have h_B :
      (∫ y in Ω, densityOnEuclid (I := I) g α y *
          chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (densityOnEuclid (I := I) g α) y)
                (EuclideanSpace.single l₂ 1) *
                chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, densityOnEuclid (I := I) g α y *
                fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y * ψ y
              ∂(volume : Measure EuclN))) :=
    per_pair_ibp_chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ l₂
      h_chosenFChartDeriv_memW1p h_density_contDiffOn
      hψ_smooth hψ_cs hψ_supp
  have h_daij_l₁_contDiffOn : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ (⊤ : ℕ∞)
        (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) Ω :=
    fun i j => weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l₁
  have h_pair_C : ∀ i j : Fin (Module.finrank ℝ E),
      (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
          D_base.weak_partial i y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                (EuclideanSpace.single l₂ 1) *
                D_base.weak_partial i y * ψ y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₂ y * ψ y
              ∂(volume : Measure EuclN))) := fun i j =>
    per_pair_ibp_base_weak_partial (I := I) (M := M) g α hu_h i l₂
      (h_daij_l₁_contDiffOn i j) hψ_smooth hψ_cs hψ_supp
  have h_dc_l₁_contDiffOn :
      ContDiffOn ℝ (⊤ : ℕ∞) (densityDerivOnEuclid (I := I) g α l₁) Ω :=
    densityDerivOnEuclid_contDiffOn (I := I) g α l₁
  have h_D :
      (∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
          D_base.u_chart y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y)
                (EuclideanSpace.single l₂ 1) *
                D_base.u_chart y * ψ y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
                D_base.weak_partial l₂ y * ψ y
              ∂(volume : Measure EuclN))) :=
    per_pair_ibp_base_u_chart (I := I) (M := M) g α hu_h l₂
      h_dc_l₁_contDiffOn hψ_smooth hψ_cs hψ_supp
  have h_E :
      (∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
          D_base.f_chart y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y)
                (EuclideanSpace.single l₂ 1) *
                D_base.f_chart y * ψ y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
                chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ y * ψ y
              ∂(volume : Measure EuclN))) :=
    per_pair_ibp_base_f_chart (I := I) (M := M) g α hu_h l₂
      h_dc_l₁_contDiffOn hψ_smooth hψ_cs hψ_supp
  have hA1_Schwarz : (∫ y in Ω,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
            (fderiv ℝ ψl₂ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) =
      (∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
              (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1))
        ∂(volume : Measure EuclN)) := by
    refine setIntegral_congr_fun hΩ_open.measurableSet (fun y _ => ?_)
    refine Finset.sum_congr rfl ?_; intro i _
    refine Finset.sum_congr rfl ?_; intro j _
    rw [h_schwarz_A1 y i j]
  have hC_Schwarz : (∫ y in Ω,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
            D_base.weak_partial i y *
            (fderiv ℝ ψl₂ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) =
      (∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
              D_base.weak_partial i y *
              (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1))
        ∂(volume : Measure EuclN)) := by
    refine setIntegral_congr_fun hΩ_open.measurableSet (fun y _ => ?_)
    refine Finset.sum_congr rfl ?_; intro i _
    refine Finset.sum_congr rfl ?_; intro j _
    rw [h_schwarz_A1 y i j]
  let K : Set EuclN := tsupport ψ
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  have hK_meas : MeasurableSet K := (isClosed_tsupport ψ).measurableSet
  have hvolK_finite : (volume : Measure EuclN) K < (⊤ : ℝ≥0∞) :=
    hK_compact.measure_lt_top
  have hvolK_finite' :
      (volume.restrict K : Measure EuclN) Set.univ < (⊤ : ℝ≥0∞) := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hvolK_finite
  haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict K) := ⟨hvolK_finite'⟩
  have hψj_fderiv_cont : ∀ j k : Fin (Module.finrank ℝ E),
      Continuous (fun y : EuclN => (fderiv ℝ (ψj j) y) (EuclideanSpace.single k 1)) :=
    fun j k => ((hψj_smooth j).continuous_fderiv (by simp)).clm_apply
      continuous_const
  have hψ_fderiv_cont : ∀ j : Fin (Module.finrank ℝ E),
      Continuous (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
    fun j => (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have h_fderiv_zero_outside_K_ψ : ∀ z ∉ K, fderiv ℝ ψ z = 0 :=
    fun z hz => fderiv_zero_outside_tsupport ψ z hz
  have h_fderiv_zero_outside_K_ψj : ∀ j, ∀ z ∉ K, fderiv ℝ (ψj j) z = 0 :=
    fun j z hz => fderiv_partial_zero_outside_tsupport (ψ := ψ) z hz j
  have h_aij_cont_on : ∀ i j, ContinuousOn (weightedInvGramOnEuclid
      (I := I) g α i j) Ω :=
    fun i j => (h_aij_contDiffOn i j).continuousOn
  have h_daij_cont_on : ∀ i j, ContinuousOn (weightedInvGramDerivOnEuclid
      (I := I) g α i j l₂) Ω :=
    fun i j => (h_daij_contDiffOn i j).continuousOn
  have h_daij_l₁_cont_on : ∀ i j, ContinuousOn (weightedInvGramDerivOnEuclid
      (I := I) g α i j l₁) Ω :=
    fun i j => (h_daij_l₁_contDiffOn i j).continuousOn
  have h_aij_fderiv_l₂_cont_on : ∀ i j, ContinuousOn (fun y =>
      (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
        (EuclideanSpace.single l₂ 1)) Ω := fun i j => by
    change ContinuousOn (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) Ω
    exact h_daij_cont_on i j
  have h_daij_l₂_fderiv_j_cont_on : ∀ i j, ContinuousOn (fun y =>
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
        (EuclideanSpace.single j 1)) Ω := fun i j =>
    weightedInvGramSecondDerivOnEuclid_continuousOn (I := I) g α i j l₂ j
  have h_daij_l₁_fderiv_l₂_cont_on : ∀ i j, ContinuousOn (fun y =>
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
        (EuclideanSpace.single l₂ 1)) Ω := fun i j =>
    weightedInvGramSecondDerivOnEuclid_continuousOn (I := I) g α i j l₁ l₂
  have integrable_triple :
      ∀ {a : EuclN → ℝ} (ha_cont_on : ContinuousOn a Ω)
        {u : EuclN → ℝ} (hu_int : IntegrableOn u K (volume : Measure EuclN))
        {h₁ : EuclN → ℝ} (hh₁_cont : Continuous h₁)
        (hh₁_supp : tsupport h₁ ⊆ K),
        Integrable (fun y => a y * u y * h₁ y)
          ((volume : Measure EuclN).restrict Ω) := by
    intro a ha_cont_on u hu_int h₁ hh₁_cont hh₁_supp
    exact integrable_mul_triple_of_tsupport hΩ_open hK_in hK_compact
      (isClosed_tsupport ψ) hK_meas ha_cont_on hu_int hh₁_cont hh₁_supp
  have h_chosenSecond_int : ∀ i l : Fin (Module.finrank ℝ E),
      IntegrableOn (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l)
        K (volume : Measure EuclN) :=
    fun i l => (chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l hK_compact hK_in).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_chosenThird_int : ∀ i l j : Fin (Module.finrank ℝ E),
      IntegrableOn (chosenThirdMixedPartialChartPushedU
        (I := I) (M := M) g α u_h i l j) K (volume : Measure EuclN) :=
    fun i l j => (chosenThirdMixedPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l j hK_compact hK_in).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_base_wp_int : ∀ i : Fin (Module.finrank ℝ E),
      IntegrableOn (D_base.weak_partial i) K (volume : Measure EuclN) :=
    fun i => (D_base.weak_partial_locally_memLp i K hK_compact hK_in).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_int_A1_pair : ∀ i j,
      Integrable (fun y => weightedInvGramOnEuclid (I := I) g α i j y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1))
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    let h₁ : EuclN → ℝ := fun y =>
      (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1)
    have hh₁_cont : Continuous h₁ := hψj_fderiv_cont j l₂
    have hh₁_supp : tsupport h₁ ⊆ K := by
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
      by_contra hy_notin
      have : (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1) = 0 := by
        rw [h_fderiv_zero_outside_K_ψj j y hy_notin]; simp
      exact hy this
    exact integrable_triple (h_aij_cont_on i j) (h_chosenSecond_int i l₁)
      hh₁_cont hh₁_supp
  have h_int_A1_inner_pair : ∀ i j,
      Integrable (fun y => weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    let h₁ : EuclN → ℝ := fun y =>
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
    have hh₁_cont : Continuous h₁ := hψ_fderiv_cont j
    have hh₁_supp : tsupport h₁ ⊆ K := by
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
      by_contra hy_notin
      have : (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0 := by
        rw [h_fderiv_zero_outside_K_ψ y hy_notin]; simp
      exact hy this
    exact integrable_triple (h_daij_cont_on i j) (h_chosenSecond_int i l₁)
      hh₁_cont hh₁_supp
  have h_int_C_pair : ∀ i j,
      Integrable (fun y => weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
          D_base.weak_partial i y *
          (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1))
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    let h₁ : EuclN → ℝ := fun y =>
      (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1)
    have hh₁_cont : Continuous h₁ := hψj_fderiv_cont j l₂
    have hh₁_supp : tsupport h₁ ⊆ K := by
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
      by_contra hy_notin
      have : (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1) = 0 := by
        rw [h_fderiv_zero_outside_K_ψj j y hy_notin]; simp
      exact hy this
    exact integrable_triple (h_daij_l₁_cont_on i j) (h_base_wp_int i)
      hh₁_cont hh₁_supp
  have sum_swap_LHS_A1 :
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
              (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1))
        ∂(volume : Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
            (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1)
            ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_A1_pair i j)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_A1_pair i j)]
  have sum_swap_C :
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
              D_base.weak_partial i y *
              (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1))
        ∂(volume : Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
            D_base.weak_partial i y *
            (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1)
            ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_C_pair i j)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_C_pair i j)]
  rw [hA1_Schwarz, hC_Schwarz, sum_swap_LHS_A1, sum_swap_C] at h_once
  have h_LHS_A1_after_IBP :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
            (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1)
            ∂(volume : Measure EuclN)
        =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((∫ y in Ω,
                (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
                  (EuclideanSpace.single l₂ 1) *
                  chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                  ψj j y
                ∂(volume : Measure EuclN))
            + (∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
                  chosenThirdMixedPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₁ l₂ y *
                  ψj j y
                ∂(volume : Measure EuclN)))) := by
    refine Finset.sum_congr rfl ?_; intro i _
    refine Finset.sum_congr rfl ?_; intro j _
    exact h_pair_A1 i j
  have h_C_after_IBP :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
            D_base.weak_partial i y *
            (fderiv ℝ (ψj j) y) (EuclideanSpace.single l₂ 1)
            ∂(volume : Measure EuclN)
        =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((∫ y in Ω,
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                  (EuclideanSpace.single l₂ 1) *
                  D_base.weak_partial i y * ψj j y
                ∂(volume : Measure EuclN))
            + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                  chosenSecondPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₂ y * ψj j y
                ∂(volume : Measure EuclN)))) := by
    refine Finset.sum_congr rfl ?_; intro i _
    refine Finset.sum_congr rfl ?_; intro j _
    exact per_pair_ibp_base_weak_partial (I := I) (M := M) g α hu_h i l₂
      (h_daij_l₁_contDiffOn i j) (hψj_smooth j) (hψj_cs j) (hψj_supp j)
  rw [h_LHS_A1_after_IBP, h_C_after_IBP, h_A2, h_B, h_D, h_E] at h_once
  have h_fderiv_aij_eq : ∀ y : EuclN, ∀ i j : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
        (EuclideanSpace.single l₂ 1) =
      weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y :=
    fun _ _ _ => rfl
  have h_fderiv_daij_l₁_eq : ∀ y : EuclN, ∀ i j : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
        (EuclideanSpace.single l₂ 1) =
      weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y :=
    fun _ _ _ => rfl
  have h_fderiv_c_eq : ∀ y : EuclN,
      (fderiv ℝ (densityOnEuclid (I := I) g α) y)
        (EuclideanSpace.single l₂ 1) =
      densityDerivOnEuclid (I := I) g α l₂ y :=
    fun _ => rfl
  have h_fderiv_dc_l₁_eq : ∀ y : EuclN,
      (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y)
        (EuclideanSpace.single l₂ 1) =
      densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y :=
    fun _ => rfl
  have h_ψj_eq : ∀ j : Fin (Module.finrank ℝ E), ∀ y : EuclN,
      ψj j y = (fderiv ℝ ψ y) (EuclideanSpace.single j 1) := fun _ _ => rfl
  let h_pair_A1_inner_ext : ∀ i j : Fin (Module.finrank ℝ E),
      (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN))
        = -((∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                (EuclideanSpace.single j 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                ψ y
              ∂(volume : Measure EuclN))
          + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ j y *
                ψ y
              ∂(volume : Measure EuclN))) := h_pair_A1_inner
  have h_int_X1_ij : ∀ i j,
      Integrable (fun y => (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
            (EuclideanSpace.single l₂ 1) *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          ψj j y)
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    have hh₁_cont : Continuous (ψj j) := (hψj_smooth j).continuous
    have hh₁_supp : tsupport (ψj j) ⊆ K :=
      tsupport_fderiv_apply_single_subset ψ j
    exact integrable_triple (h_aij_fderiv_l₂_cont_on i j) (h_chosenSecond_int i l₁)
      hh₁_cont hh₁_supp
  have h_int_Y1_ij : ∀ i j,
      Integrable (fun y => weightedInvGramOnEuclid (I := I) g α i j y *
          chosenThirdMixedPartialChartPushedU
            (I := I) (M := M) g α u_h i l₁ l₂ y *
          ψj j y)
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    have hh₁_cont : Continuous (ψj j) := (hψj_smooth j).continuous
    have hh₁_supp : tsupport (ψj j) ⊆ K :=
      tsupport_fderiv_apply_single_subset ψ j
    exact integrable_triple (h_aij_cont_on i j) (h_chosenThird_int i l₁ l₂)
      hh₁_cont hh₁_supp
  have h_int_X2_ij : ∀ i j,
      Integrable (fun y =>
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
            (EuclideanSpace.single l₂ 1) *
          D_base.weak_partial i y * ψj j y)
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    have hh₁_cont : Continuous (ψj j) := (hψj_smooth j).continuous
    have hh₁_supp : tsupport (ψj j) ⊆ K :=
      tsupport_fderiv_apply_single_subset ψ j
    exact integrable_triple (h_daij_l₁_fderiv_l₂_cont_on i j) (h_base_wp_int i)
      hh₁_cont hh₁_supp
  have h_int_Y2_ij : ∀ i j,
      Integrable (fun y => weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
          ψj j y)
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    have hh₁_cont : Continuous (ψj j) := (hψj_smooth j).continuous
    have hh₁_supp : tsupport (ψj j) ⊆ K :=
      tsupport_fderiv_apply_single_subset ψ j
    exact integrable_triple (h_daij_l₁_cont_on i j) (h_chosenSecond_int i l₂)
      hh₁_cont hh₁_supp
  have h_sum_distrib_LHS_A1 :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((∫ y in Ω,
                (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
                  (EuclideanSpace.single l₂ 1) *
                  chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                  ψj j y
                ∂(volume : Measure EuclN))
            + (∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
                  chosenThirdMixedPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₁ l₂ y *
                  ψj j y
                ∂(volume : Measure EuclN))))
      = - ((∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω,
                (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
                  (EuclideanSpace.single l₂ 1) *
                  chosenSecondPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₁ y *
                  ψj j y
                ∂(volume : Measure EuclN))
          + (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y *
                ψj j y
              ∂(volume : Measure EuclN))) := by
    simp_rw [neg_add]
    have h_inner : ∀ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-(∫ y in Ω,
              (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
                (EuclideanSpace.single l₂ 1) *
              chosenSecondPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ y * ψj j y
              ∂(volume : Measure EuclN))
            + -(∫ y in Ω,
                weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y * ψj j y
              ∂(volume : Measure EuclN))) =
        (∑ j : Fin (Module.finrank ℝ E),
          -(∫ y in Ω,
              (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
                (EuclideanSpace.single l₂ 1) *
              chosenSecondPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ y * ψj j y
              ∂(volume : Measure EuclN))) +
        (∑ j : Fin (Module.finrank ℝ E),
          -(∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ l₂ y * ψj j y
              ∂(volume : Measure EuclN))) := fun _ => Finset.sum_add_distrib
    rw [Finset.sum_congr rfl (fun i _ => h_inner i)]
    rw [Finset.sum_add_distrib]
    simp_rw [Finset.sum_neg_distrib (s :=
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
  have h_sum_distrib_C :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((∫ y in Ω,
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                  (EuclideanSpace.single l₂ 1) *
                  D_base.weak_partial i y * ψj j y
                ∂(volume : Measure EuclN))
            + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                  chosenSecondPartialChartPushedU
                    (I := I) (M := M) g α u_h i l₂ y * ψj j y
                ∂(volume : Measure EuclN))))
      = - ((∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω,
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                  (EuclideanSpace.single l₂ 1) *
                  D_base.weak_partial i y * ψj j y
                ∂(volume : Measure EuclN))
          + (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₂ y * ψj j y
              ∂(volume : Measure EuclN))) := by
    simp_rw [neg_add]
    have h_inner : ∀ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-(∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                (EuclideanSpace.single l₂ 1) *
              D_base.weak_partial i y * ψj j y
              ∂(volume : Measure EuclN))
            + -(∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₂ y * ψj j y
              ∂(volume : Measure EuclN))) =
        (∑ j : Fin (Module.finrank ℝ E),
          -(∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
                (EuclideanSpace.single l₂ 1) *
              D_base.weak_partial i y * ψj j y
              ∂(volume : Measure EuclN))) +
        (∑ j : Fin (Module.finrank ℝ E),
          -(∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
              chosenSecondPartialChartPushedU
                (I := I) (M := M) g α u_h i l₂ y * ψj j y
              ∂(volume : Measure EuclN))) := fun _ => Finset.sum_add_distrib
    rw [Finset.sum_congr rfl (fun i _ => h_inner i)]
    rw [Finset.sum_add_distrib]
    simp_rw [Finset.sum_neg_distrib (s :=
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
  rw [h_sum_distrib_LHS_A1, h_sum_distrib_C] at h_once
  let α1_sub1 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω,
      (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
        (EuclideanSpace.single l₂ 1) *
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
      ψj j y
      ∂(volume : Measure EuclN)
  let α1_sub2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ l₂ y *
      ψj j y
      ∂(volume : Measure EuclN)
  let γ_sub1 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω,
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
        (EuclideanSpace.single l₂ 1) *
      D_base.weak_partial i y * ψj j y
      ∂(volume : Measure EuclN)
  let γ_sub2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
      ψj j y
      ∂(volume : Measure EuclN)
  have hα1_sub1_inner_IBP_form : ∀ i j : Fin (Module.finrank ℝ E),
      α1_sub1 i j = -((∫ y in Ω,
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
              (EuclideanSpace.single j 1) *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
              ψ y
            ∂(volume : Measure EuclN))
          + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ j y *
              ψ y
            ∂(volume : Measure EuclN))) := by
    intro i j
    have : α1_sub1 i j =
        ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN) := by
      change (∫ y in Ω,
          (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
            (EuclideanSpace.single l₂ 1) *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
          ψj j y
          ∂(volume : Measure EuclN)) = _
      refine setIntegral_congr_fun hΩ_open.measurableSet (fun y _ => ?_)
      have := h_fderiv_aij_eq y i j
      rw [show ψj j y = (fderiv ℝ ψ y) (EuclideanSpace.single j 1) from rfl]
      rw [this]
    rw [this]
    exact h_pair_A1_inner i j
  have h_sum_α1_sub1_IBP :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), α1_sub1 i j =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((∫ y in Ω,
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                  (EuclideanSpace.single j 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                ψ y
                ∂(volume : Measure EuclN))
            + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ j y *
                ψ y
                ∂(volume : Measure EuclN)))) := by
    refine Finset.sum_congr rfl ?_; intro i _
    refine Finset.sum_congr rfl ?_; intro j _
    exact hα1_sub1_inner_IBP_form i j
  have h_sum_α1_sub1_split :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((∫ y in Ω,
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                  (EuclideanSpace.single j 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                ψ y
                ∂(volume : Measure EuclN))
            + (∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ j y *
                ψ y
                ∂(volume : Measure EuclN))))
      = - ((∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω,
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                  (EuclideanSpace.single j 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                ψ y
                ∂(volume : Measure EuclN))
          + (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ j y *
                ψ y
                ∂(volume : Measure EuclN))) := by
    simp_rw [neg_add]
    have h_inner : ∀ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-(∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                (EuclideanSpace.single j 1) *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
              ψ y
              ∂(volume : Measure EuclN))
            + -(∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ j y *
                ψ y
              ∂(volume : Measure EuclN))) =
        (∑ j : Fin (Module.finrank ℝ E),
          -(∫ y in Ω,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                (EuclideanSpace.single j 1) *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
              ψ y
              ∂(volume : Measure EuclN))) +
        (∑ j : Fin (Module.finrank ℝ E),
          -(∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ j y *
              ψ y
              ∂(volume : Measure EuclN))) := fun _ => Finset.sum_add_distrib
    rw [Finset.sum_congr rfl (fun i _ => h_inner i)]
    rw [Finset.sum_add_distrib]
    simp_rw [Finset.sum_neg_distrib (s :=
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
  have hSum_α1_sub1_final :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), α1_sub1 i j =
      - ((∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω,
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
                  (EuclideanSpace.single j 1) *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
                ψ y
                ∂(volume : Measure EuclN))
          + (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ j y *
                ψ y
                ∂(volume : Measure EuclN))) := by
    rw [h_sum_α1_sub1_IBP, h_sum_α1_sub1_split]
  have hSwap_LHS1 :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
            chosenThirdMixedPartialChartPushedU
              (I := I) (M := M) g α u_h i l₁ l₂ y *
            ψj j y
            ∂(volume : Measure EuclN) =
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ l₂ y *
              ψj j y)
        ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_Y1_ij i j)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_Y1_ij i j)]
  have hψj_consolidate_LHS1 :
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ l₂ y *
              ψj j y)
        ∂(volume : Measure EuclN) =
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ l₂ y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN) := rfl
  have h_LHS1_eq :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), α1_sub2 i j) =
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ l₂ y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN) := by
    rw [show (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        α1_sub2 i j) = (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
              chosenThirdMixedPartialChartPushedU
                (I := I) (M := M) g α u_h i l₁ l₂ y *
              ψj j y
              ∂(volume : Measure EuclN)) from rfl]
    rw [hSwap_LHS1]
  let I_lhs1_target : ℝ :=
    ∫ y in Ω,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenThirdMixedPartialChartPushedU
              (I := I) (M := M) g α u_h i l₁ l₂ y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)
  let I_lhs2_target : ℝ :=
    ∫ y in Ω, densityOnEuclid (I := I) g α y *
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
      ∂(volume : Measure EuclN)
  let I_rhs_target : ℝ :=
    ∫ y in Ω, densityOnEuclid (I := I) g α y *
      effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
      ∂(volume : Measure EuclN)
  let X1 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω,
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
        (EuclideanSpace.single j 1) *
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
      ψ y
      ∂(volume : Measure EuclN)
  let X2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ j y *
      ψ y
      ∂(volume : Measure EuclN)
  let C1 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω,
      (fderiv ℝ (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y)
        (EuclideanSpace.single j 1) *
      D_base.weak_partial i y * ψ y
      ∂(volume : Measure EuclN)
  let C2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω, weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y
      ∂(volume : Measure EuclN)
  let C3 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω,
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
        (EuclideanSpace.single j 1) *
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y * ψ y
      ∂(volume : Measure EuclN)
  let C4 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₂ j y * ψ y
      ∂(volume : Measure EuclN)
  have h_d2aij_contDiffOn : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ (⊤ : ℕ∞)
        (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) Ω :=
    fun i j => weightedInvGramSecondDerivOnEuclid_contDiffOn (I := I) g α i j l₁ l₂
  have h_γ_sub1_IBP : ∀ i j : Fin (Module.finrank ℝ E),
      γ_sub1 i j = -(C1 i j + C2 i j) := by
    intro i j
    have h_rewrite : γ_sub1 i j =
        ∫ y in Ω, weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
          D_base.weak_partial i y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN) := by
      change (∫ y in Ω,
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
            (EuclideanSpace.single l₂ 1) *
          D_base.weak_partial i y * ψj j y
          ∂(volume : Measure EuclN)) = _
      rfl
    rw [h_rewrite]
    exact per_pair_ibp_base_weak_partial (I := I) (M := M) g α hu_h i j
      (h_d2aij_contDiffOn i j) hψ_smooth hψ_cs hψ_supp
  have h_γ_sub2_IBP : ∀ i j : Fin (Module.finrank ℝ E),
      γ_sub2 i j = -(C3 i j + C4 i j) := by
    intro i j
    have h_rewrite : γ_sub2 i j =
        ∫ y in Ω, weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN) := by
      change (∫ y in Ω,
          weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
          ψj j y
          ∂(volume : Measure EuclN)) = _
      rfl
    rw [h_rewrite]
    exact per_pair_ibp_chosenSecond (I := I) (M := M) g α hu_h i l₂ j
      (h_daij_l₁_contDiffOn i j) hψ_smooth hψ_cs hψ_supp
  have h_sumγ_sub1 :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), γ_sub1 i j =
      - (∑ i, ∑ j, C1 i j) - (∑ i, ∑ j, C2 i j) := by
    calc ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), γ_sub1 i j
        = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), -(C1 i j + C2 i j) := by
          refine Finset.sum_congr rfl ?_; intro i _
          refine Finset.sum_congr rfl ?_; intro j _
          exact h_γ_sub1_IBP i j
      _ = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), (-C1 i j + -C2 i j) := by
          refine Finset.sum_congr rfl ?_; intro i _
          refine Finset.sum_congr rfl ?_; intro j _
          ring
      _ = ∑ i : Fin (Module.finrank ℝ E),
          ((∑ j, -C1 i j) + (∑ j, -C2 i j)) := by
          refine Finset.sum_congr rfl ?_; intro i _
          exact Finset.sum_add_distrib
      _ = (∑ i, ∑ j, -C1 i j) + (∑ i, ∑ j, -C2 i j) := Finset.sum_add_distrib
      _ = - (∑ i, ∑ j, C1 i j) - (∑ i, ∑ j, C2 i j) := by
          simp_rw [Finset.sum_neg_distrib (s :=
            (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
          ring
  have h_sumγ_sub2 :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), γ_sub2 i j =
      - (∑ i, ∑ j, C3 i j) - (∑ i, ∑ j, C4 i j) := by
    calc ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), γ_sub2 i j
        = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), -(C3 i j + C4 i j) := by
          refine Finset.sum_congr rfl ?_; intro i _
          refine Finset.sum_congr rfl ?_; intro j _
          exact h_γ_sub2_IBP i j
      _ = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), (-C3 i j + -C4 i j) := by
          refine Finset.sum_congr rfl ?_; intro i _
          refine Finset.sum_congr rfl ?_; intro j _
          ring
      _ = ∑ i : Fin (Module.finrank ℝ E),
          ((∑ j, -C3 i j) + (∑ j, -C4 i j)) := by
          refine Finset.sum_congr rfl ?_; intro i _
          exact Finset.sum_add_distrib
      _ = (∑ i, ∑ j, -C3 i j) + (∑ i, ∑ j, -C4 i j) := Finset.sum_add_distrib
      _ = - (∑ i, ∑ j, C3 i j) - (∑ i, ∑ j, C4 i j) := by
          simp_rw [Finset.sum_neg_distrib (s :=
            (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
          ring
  have h_α1_sub2_eq : α1_sub2 = fun i j =>
    ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ l₂ y *
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
      ∂(volume : Measure EuclN) := by
    funext i j; rfl
  have h_lhs1_swap_to_sum :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
            chosenThirdMixedPartialChartPushedU
              (I := I) (M := M) g α u_h i l₁ l₂ y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
            ∂(volume : Measure EuclN)) =
      I_lhs1_target := by
    change (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        ∫ y in Ω, weightedInvGramOnEuclid (I := I) g α i j y *
          chosenThirdMixedPartialChartPushedU
            (I := I) (M := M) g α u_h i l₁ l₂ y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN)) =
        ∫ y in Ω,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_Y1_ij i j)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_Y1_ij i j)]
  have h_α1_sub2_to_lhs1 :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), α1_sub2 i j) = I_lhs1_target := by
    rw [h_α1_sub2_eq]; exact h_lhs1_swap_to_sum
  let N_A3 : ℝ := ∫ y in Ω,
    (fderiv ℝ (densityOnEuclid (I := I) g α) y) (EuclideanSpace.single l₂ 1) *
    D_base.weak_partial l₁ y * ψ y ∂(volume : Measure EuclN)
  let N_B1 : ℝ := ∫ y in Ω,
    (fderiv ℝ (densityOnEuclid (I := I) g α) y) (EuclideanSpace.single l₂ 1) *
    chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y
    ∂(volume : Measure EuclN)
  let N_B2 : ℝ := ∫ y in Ω, densityOnEuclid (I := I) g α y *
    fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y * ψ y
    ∂(volume : Measure EuclN)
  let N_D1 : ℝ := ∫ y in Ω,
    (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y) (EuclideanSpace.single l₂ 1) *
    D_base.u_chart y * ψ y ∂(volume : Measure EuclN)
  let N_D2 : ℝ := ∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
    D_base.weak_partial l₂ y * ψ y ∂(volume : Measure EuclN)
  let N_E1 : ℝ := ∫ y in Ω,
    (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y) (EuclideanSpace.single l₂ 1) *
    D_base.f_chart y * ψ y ∂(volume : Measure EuclN)
  let N_E2 : ℝ := ∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y *
    chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ y * ψ y
    ∂(volume : Measure EuclN)
  have h_A2_named :
      (∫ y in Ω, densityOnEuclid (I := I) g α y * D_base.weak_partial l₁ y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN))
      = -(N_A3 + I_lhs2_target) := h_A2
  have h_B_named :
      (∫ y in Ω, densityOnEuclid (I := I) g α y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN))
      = -(N_B1 + N_B2) := h_B
  have h_D_named :
      (∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y * D_base.u_chart y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN))
      = -(N_D1 + N_D2) := h_D
  have h_E_named :
      (∫ y in Ω, densityDerivOnEuclid (I := I) g α l₁ y * D_base.f_chart y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN))
      = -(N_E1 + N_E2) := h_E
  let I_num : ℝ := ∫ y in Ω,
    effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
    ∂(volume : Measure EuclN)
  have h_psi_cont : Continuous ψ := hψ_smooth.continuous
  have h_psi_supp : tsupport ψ ⊆ K := le_refl _
  have h_base_uc_int : IntegrableOn D_base.u_chart K (volume : Measure EuclN) :=
    (base_u_chart_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
      hK_compact hK_meas hK_in).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_base_fc_int : IntegrableOn D_base.f_chart K (volume : Measure EuclN) :=
    (base_f_chart_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
      hK_compact hK_meas hK_in).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_chosenFChartDeriv_int : ∀ l : Fin (Module.finrank ℝ E),
      IntegrableOn (chosenFChartDeriv (I := I) (M := M) g α hu_h l)
        K (volume : Measure EuclN) := fun l => by
    have h_global :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_base_f_chart_memW1p l
    have h_K_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1; exact Set.inter_eq_self_of_subset_left hK_in
    have h_memLp_K : MemLp (chosenFChartDeriv (I := I) (M := M) g α hu_h l) 2
        ((volume : Measure EuclN).restrict K) := by
      change MemLp (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l D_base.f_chart Ω) 2 _
      rw [← h_K_eq]; exact h_global.restrict K
    exact h_memLp_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_fChartDeriv2_int :
      IntegrableOn (fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂)
        K (volume : Measure EuclN) := by
    have h_global :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_chosenFChartDeriv_memW1p l₂
    have h_K_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1; exact Set.inter_eq_self_of_subset_left hK_in
    have h_memLp_K : MemLp (fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂) 2
        ((volume : Measure EuclN).restrict K) := by
      change MemLp (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l₂
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁) Ω) 2 _
      rw [← h_K_eq]; exact h_global.restrict K
    exact h_memLp_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_c_cont_on : ContinuousOn (densityOnEuclid (I := I) g α) Ω :=
    h_density_contDiffOn.continuousOn
  have h_dc_l₁_cont_on : ContinuousOn (densityDerivOnEuclid (I := I) g α l₁) Ω :=
    h_dc_l₁_contDiffOn.continuousOn
  have h_dc_l₂_cont_on : ContinuousOn (densityDerivOnEuclid (I := I) g α l₂) Ω :=
    (densityDerivOnEuclid_contDiffOn (I := I) g α l₂).continuousOn
  have h_d2c_cont_on : ContinuousOn
      (densitySecondDerivOnEuclid (I := I) g α l₁ l₂) Ω :=
    densitySecondDerivOnEuclid_continuousOn (I := I) g α l₁ l₂
  have h_d2aij_cont_on : ∀ i j, ContinuousOn
      (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) Ω :=
    fun i j => weightedInvGramSecondDerivOnEuclid_continuousOn (I := I) g α i j l₁ l₂
  have integrable_triple_psi :
      ∀ {a : EuclN → ℝ}, ContinuousOn a Ω →
        ∀ {u : EuclN → ℝ}, IntegrableOn u K (volume : Measure EuclN) →
        Integrable (fun y => a y * u y * ψ y)
          ((volume : Measure EuclN).restrict Ω) := by
    intro a ha u hu_int
    exact integrable_triple ha hu_int h_psi_cont h_psi_supp
  have integrable_double_psi :
      ∀ {a : EuclN → ℝ}, ContinuousOn a Ω →
        ∀ {u : EuclN → ℝ}, IntegrableOn u K (volume : Measure EuclN) →
        Integrable (fun y => a y * u y * ψ y)
          ((volume : Measure EuclN).restrict Ω) :=
    @integrable_triple_psi
  have h_int_C1_pair : ∀ i j,
      Integrable (fun y => (fderiv ℝ (weightedInvGramSecondDerivOnEuclid
            (I := I) g α i j l₁ l₂) y) (EuclideanSpace.single j 1) *
          D_base.weak_partial i y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    have h_ai_cont_on := fderiv_apply_continuousOn_of_contDiffOn hΩ_open
      (h_d2aij_contDiffOn i j) (EuclideanSpace.single j (1 : ℝ))
    exact integrable_triple_psi h_ai_cont_on (h_base_wp_int i)
  have h_int_C2_pair : ∀ i j,
      Integrable (fun y => weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple_psi (h_d2aij_cont_on i j) (h_chosenSecond_int i j)
  have h_int_C3_pair : ∀ i j,
      Integrable (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid
            (I := I) g α i j l₁) y) (EuclideanSpace.single j 1) *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    have h_ai_cont_on : ContinuousOn (fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
          (EuclideanSpace.single j 1)) Ω :=
      weightedInvGramSecondDerivOnEuclid_continuousOn (I := I) g α i j l₁ j
    exact integrable_triple_psi h_ai_cont_on (h_chosenSecond_int i l₂)
  have h_int_C4_pair : ∀ i j,
      Integrable (fun y => weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
          chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₂ j y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple_psi (h_daij_l₁_cont_on i j) (h_chosenThird_int i l₂ j)
  have h_int_X1_named : ∀ i j,
      Integrable (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid
            (I := I) g α i j l₂) y) (EuclideanSpace.single j 1) *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j => by
    have h_ai_cont_on : ContinuousOn (fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
          (EuclideanSpace.single j 1)) Ω :=
      weightedInvGramSecondDerivOnEuclid_continuousOn (I := I) g α i j l₂ j
    exact integrable_triple_psi h_ai_cont_on (h_chosenSecond_int i l₁)
  have h_int_X2_named : ∀ i j,
      Integrable (fun y => weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
          chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ j y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple_psi (h_daij_cont_on i j) (h_chosenThird_int i l₁ j)
  have h_I_num_decomp : I_num =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), X1 i j) +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), X2 i j) +
      (- N_A3) + N_B1 + N_B2 +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C1 i j) +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C2 i j) +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C3 i j) +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), C4 i j) +
      (- N_D1) + (- N_D2) + N_E1 + N_E2 :=
    numerator_secondOrder_decomp g α hu_h l₁ l₂ Ω K
      integrable_triple_psi hΩ_open h_base_wp_int h_base_uc_int h_base_fc_int
      h_chosenFChartDeriv_int h_fChartDeriv2_int h_c_cont_on h_d2c_cont_on
      h_dc_l₁_cont_on h_dc_l₂_cont_on h_int_C1_pair h_int_C2_pair h_int_C3_pair
      h_int_C4_pair h_int_X1_named h_int_X2_named
  have h_I_num_eq_rhs :=
    integral_fChartEffTwiceNumerator_eq_integral_density_fChartEffTwice
      (I := I) (M := M) g α hu_h l₁ l₂ h_chosenFChartDeriv_memW1p ψ
  rw [show I_num = ∫ y in chartTargetEuclid (I := I) (M := M) α,
        effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
        ∂(volume : Measure EuclN) from rfl] at h_I_num_decomp
  change I_lhs1_target + I_lhs2_target = I_rhs_target
  rw [hSum_α1_sub1_final, h_sumγ_sub1, h_sumγ_sub2, h_α1_sub2_to_lhs1] at h_once
  change I_lhs1_target + I_lhs2_target =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
        ∂(volume : Measure EuclN)
  rw [← h_I_num_eq_rhs]
  rw [h_I_num_decomp]
  linarith

end TwiceDifferentiatedVariationalIdentity
end Laplacian
end Analysis
end DifferentialGeometry

end
