import DifferentialGeometry.Analysis.Parabolic.Energy.DirichletQuotient
import DifferentialGeometry.Analysis.Parabolic.Energy.Continuity
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Energy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.HeatEnergy
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
open Set MeasureTheory Filter
open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval}
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem heat_potential_eq_zero_of_terminal_eq_zero_on_surface
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 2) {V u : ℝ → M → ℝ}
    (hu : IsHeatPotOn D (flowG S) V u)
    {a b : ℝ} (hab : a < b) (hcar : Icc a b ⊆ D.carrier)
    (hreg : Ioo a b ⊆ D.regular)
    (hV : ContinuousOn (fun p : ℝ × M => V p.1 p.2) (Icc a b ×ˢ univ))
    (hVsmooth : ∀ t ∈ Ioo a b, ContMDiff I 𝓘(ℝ, ℝ) ∞ (V t))
    (hterminal : ∀ x, u b x = 0) : ∀ t ∈ Icc a b, ∀ x, u t x = 0 := by
  let μ := fun t => riemannianVolumeMeasure I M (S.family.metric t)
  let energy := fun t => ∫ x, (u t x) ^ 2 ∂μ t
  let dirichlet := fun t => ∫ x, normGradSqFun (S.family.metric t) (u t) x ∂μ t
  have hEcont : ContinuousOn energy (Icc a b) :=
    (hu.continuousOn_integral_sq hS.smoothMetric).mono hcar
  have hDcont : ContinuousOn dirichlet (Ioo a b) :=
    (hu.continuousOn_integral_normGradSqFun hS.smoothMetric).mono hreg
  obtain ⟨Av,hAv⟩ := (isCompact_Icc.prod isCompact_univ).bddAbove_image hV.norm
  let A := max Av 0
  have hA : 0 ≤ A := le_max_right _ _
  have hAbound (t : ℝ) (ht : t ∈ Icc a b) (x : M) : |V t x| ≤ A := by
    exact (hAv ⟨(t,x),⟨ht,mem_univ x⟩,rfl⟩).trans (le_max_left _ _)
  have hscalarCont : ContinuousOn (fun p : ℝ × M => S.scalar p.1 p.2) (Icc a b ×ˢ univ) :=
    hS.scalarCont.mono (prod_mono hcar Subset.rfl)
  obtain ⟨Kr,hKr⟩ := (isCompact_Icc.prod isCompact_univ).bddAbove_image hscalarCont
  let K := max Kr 0
  have hK : 0 ≤ K := le_max_right _ _
  have hKbound (t : ℝ) (ht : t ∈ Icc a b) (x : M) : S.scalar t x ≤ K :=
    (hKr ⟨(t,x),⟨ht,mem_univ x⟩,rfl⟩).trans (le_max_left _ _)
  have hEnonneg (t : ℝ) : 0 ≤ energy t := integral_nonneg fun _ => sq_nonneg _
  have hDnonneg (t : ℝ) : 0 ≤ dirichlet t := integral_nonneg fun x =>
    DifferentialGeometry.metric_inner_self_nonneg (S.family.metric t) x _
  have hEd (t : ℝ) (ht : t ∈ Ioo a b) :=
    S.hasDerivAt_integral_sq_of_heat_potential hS hu (hreg ht) (hVsmooth t ht).continuous
  have hDd (t : ℝ) (ht : t ∈ Ioo a b) :=
    hasDerivAt_integral_normGradSqFun_of_isHeatPotOn_of_finrank_eq_two S hS hdim hu
      (hreg ht) (hVsmooth t ht)
  have hbounds (t : ℝ) (ht : t ∈ Ioo a b) (hpos : 0 < energy t) :
      (deriv dirichlet t * energy t - dirichlet t * deriv energy t) / (energy t)^2 ≤
        K * (dirichlet t / energy t) + A^2/2 ∧
      -(2 * (dirichlet t / energy t) + (2*A+K)) * energy t ≤ deriv energy t := by
    let g := S.family.metric t
    let : IsFiniteMeasure (μ t) := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
    have huSmooth := hu.sliceSmooth t (D.regular_subset (hreg ht))
    let lap := laplacian (LeviCivita g) g (u t)
    have hLap : ContMDiff I 𝓘(ℝ, ℝ) ∞ lap := contMDiff_laplacian_leviCivita g huSmooth
    let U : C(M, ℝ) := ⟨u t,huSmooth.continuous⟩
    let Z : C(M, ℝ) := ⟨fun x => -lap x,hLap.continuous.neg⟩
    let W : C(M, ℝ) := ⟨V t,(hVsmooth t ht).continuous⟩
    let R : C(M, ℝ) := ⟨S.scalar t,(metricScalar_smooth g).continuous⟩
    have hgreen : dirichlet t = ∫ x, Z x * U x ∂μ t :=
      integral_normGradSqFun_eq_integral_neg_laplacian_mul g huSmooth (HasCompactSupport.of_compactSpace _)
    have hD' : HasDerivAt dirichlet (-2 * (∫ x, (Z x)^2 ∂μ t) +
        2 * (∫ x, Z x * (W x * U x) ∂μ t)) t := by
      convert hDd t ht using 1
      dsimp only [Z,W,U,ContinuousMap.coe_mk]
      simp only [neg_sq,neg_mul,integral_neg]
      have heq : (∫ x, lap x * (V t x * u t x) ∂μ t) =
          ∫ x, V t x * u t x * lap x ∂μ t :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      rw [heq]
      ring
    exact integral_frequency_differential_bounds (μ t) U Z W R rfl hpos hgreen (hDnonneg t)
      (hEd t ht) hD' hA (hAbound t (Ioo_subset_Icc_self ht)) (hKbound t (Ioo_subset_Icc_self ht))
  have hEzero : ∀ t ∈ Icc a b, energy t = 0 := by
    apply eq_zero_of_terminal_zero_of_dirichlet_quotient_bounds hab hK (div_nonneg (sq_nonneg A) (by norm_num))
      hEcont hDcont (fun t _ => hEnonneg t) (fun t _ => hDnonneg t)
      (fun t ht => (hEd t ht).differentiableAt.hasDerivAt)
      (fun t ht => (hDd t ht).differentiableAt.hasDerivAt)
      (fun t ht hp => (hbounds t ht hp).1) (fun t ht hp => (hbounds t ht hp).2)
    simp only [energy,hterminal,zero_pow (by decide : 2 ≠ 0),integral_zero]
  intro t ht x
  let : IsFiniteMeasure (μ t) := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (S.family.metric t)
  let : (μ t).IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure (S.family.metric t)
  have huc := (hu.sliceSmooth t (hcar ht)).continuous
  have hint : Integrable (fun x => (u t x)^2) (μ t) :=
    (huc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (u t x)) hint).mp (hEzero t ht)
  have hall := congrFun (MeasureTheory.Measure.eq_of_ae_eq hae (huc.pow 2) continuous_const) x
  exact sq_eq_zero_iff.mp hall

end DifferentialGeometry.PDE.RicciFlow
