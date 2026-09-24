import DifferentialGeometry.Analysis.Calculus.SecondDerivative.Prod
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeClassical
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.VolumeDensity
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.Equation
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Entropy
open Bundle Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold ContDiff _root_.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem hasDerivAt_of_conjugate_heat_weak_equation
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) {J : Set ℝ} (hJ : IsOpen J) (hreg : ∀ s ∈ J, T - s ∈ D.regular)
    {u : ℝ → M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ (fun p : ℝ × M => u p.1 p.2) (J ×ˢ univ))
    (hweak : ∀ a : M, ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ (extChartAt I a).target →
      (∫ p, chartDensityOnE (S.base.metric (T - p.1)) a p.2 *
          u p.1 ((extChartAt I a).symm p.2) * fderiv ℝ φ p (1, 0) ∂volume.prod (modelHaar (E := E))) =
        ∑ i, ∑ j, ∫ p, (chartInvGramOnE (S.base.metric (T - p.1)) a i j p.2 *
          chartDensityOnE (S.base.metric (T - p.1)) a p.2) *
          lineDeriv ℝ (fun q : ℝ × E => u q.1 ((extChartAt I a).symm q.2)) p (0, chartModelBasis E j) *
          fderiv ℝ φ p (0, chartModelBasis E i) ∂volume.prod (modelHaar (E := E)))
    {t : ℝ} (ht : t ∈ J) (x : M) :
    HasDerivAt (fun r => u r x)
      (laplacianAt (reverseFamily (flowG S) T) t (u t) x - S.scalar (T - t) x * u t x) t := by
  let a := x
  let Ω := J ×ˢ (extChartAt I a).target
  let U := fun p : ℝ × E => u p.1 ((extChartAt I a).symm p.2)
  let ρ := fun p : ℝ × E => chartDensityOnE (S.base.metric (T - p.1)) a p.2
  let A := fun i j : Fin (Module.finrank ℝ E) => fun p : ℝ × E =>
    chartInvGramOnE (S.base.metric (T - p.1)) a i j p.2 * ρ p
  let b := fun i : Fin (Module.finrank ℝ E) => ((0 : ℝ), chartModelBasis E i)
  let ν := (volume : Measure ℝ).prod (modelHaar (E := E))
  have hΩ : IsOpen Ω := hJ.prod (isOpen_extChartAt_target (I := I) a)
  have hU : ContDiffOn ℝ ∞ U Ω := scalarOnE_contDiffOn_prod a hu
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × E => (T - p.1, p.2)) :=
    (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
  have hρ : ContDiffOn ℝ ∞ ρ Ω :=
    (chartDensityOnE_family_contDiffOn hS.smoothMetric Subset.rfl a).comp hmap.contDiffOn
      (fun p hp => ⟨hreg p.1 hp.1, hp.2⟩)
  have hA (i j : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞ (A i j) Ω := by
    apply ContDiffOn.mul _ hρ
    apply (MetricFamilySmoothOn.chartInvGramOnE_contDiffOn hS.smoothMetric Subset.rfl a i j).comp hmap.contDiffOn
    intro p hp
    exact ⟨hreg p.1 hp.1, (isOpen_extChartAt_target (I := I) a).interior_eq.symm ▸ hp.2⟩
  have hDU (j) : ContDiffOn ℝ 1 (fun p => fderiv ℝ U p (b j)) Ω :=
    ((hU.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).fderiv_of_isOpen hΩ (by norm_num)).clm_apply contDiffOn_const
  have hdiv := Analysis.Sobolev.fderiv_eq_sum_fderiv_add_of_weak_divergence (μ := ν) hΩ
    (Finset.univ : Finset (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)))
    (1, 0) (fun ij => b ij.1)
    ((hρ.of_le (by simp)).mul (hU.of_le (by simp)))
    (fun ij _ => ((hA ij.1 ij.2).of_le (by simp)).mul (hDU ij.2))
    (continuousOn_const (c := (0 : ℝ))) (by
      intro φ hφ hφc hφs
      have hdφ (p : ℝ × E) (hp : p ∉ Ω) : fderiv ℝ φ p = 0 :=
        fderiv_of_notMem_tsupport ℝ (fun hs => hp (hφs hs))
      have hres (B : ℝ × E → ℝ) (v : ℝ × E) :
          (∫ p in Ω, B p * fderiv ℝ φ p v ∂ν) = ∫ p, B p * fderiv ℝ φ p v ∂ν := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro p hp
        rw [hdφ p hp, zero_apply, mul_zero]
      simp only [Fintype.sum_prod_type, zero_mul, integral_zero, sub_zero, hres]
      refine (hweak a φ hφ hφc hφs).trans ?_
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards with p
      by_cases hp : p ∈ Ω
      · rw [((hU.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).lineDeriv_eq_fderiv]
      · rw [hdφ p hp, zero_apply, mul_zero, mul_zero])
  have hP : ∀ p ∈ Ω, fderiv ℝ (fun q => ρ q * U q) p (1, 0) =
      ∑ i, ∑ j, fderiv ℝ (fun q => A i j q * fderiv ℝ U q (b j)) p (b i) := by
    simpa only [Fintype.sum_prod_type, add_zero] using hdiv
  let z := extChartAt I a x
  have hz : z ∈ (extChartAt I a).target := mem_extChartAt_target (I := I) x
  have hzInv : (extChartAt I a).symm z = x := extChartAt_to_inv x
  have htz : (t, z) ∈ Ω := ⟨ht, hz⟩
  have hUdiff := (hU.contDiffAt (hΩ.mem_nhds htz)).differentiableAt (by simp)
  have huTime : HasDerivAt (fun r => u r x) (fderiv ℝ U (t, z) (1, 0)) t := by
    have h := hUdiff.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))
    simpa only [Function.comp_def, id_eq, U, hzInv] using h
  have hρTime : HasDerivAt (fun r => ρ (r, z))
      (S.scalar (T - t) x * ρ (t, z)) t := by
    have h := (hasDerivAt_chartDensity_of_isSolutionOn S hS (hreg t ht) a
      (extChartAt_symm_mem_trivializationAt_baseSet a hz)).comp t
      ((hasDerivAt_id t).const_sub T)
    simpa only [Function.comp_def, ρ, chartDensityOnE, hzInv, neg_mul, mul_neg_one, neg_neg] using h
  have hρpos : 0 < ρ (t, z) := chartDensity_pos (S.base.metric (T - t)) a
    (extChartAt_symm_mem_trivializationAt_baseSet a hz)
  let B := fun i : Fin (Module.finrank ℝ E) => fun p : ℝ × E =>
    ∑ j, A i j p * fderiv ℝ U p (b j)
  have hB (i) : ContDiffOn ℝ 1 (B i) Ω :=
    ContDiffOn.sum (fun j _ => ((hA i j).of_le (by simp)).mul (hDU j))
  have hsmooth : ContMDiff I 𝓘(ℝ) ∞ (u t) := by
    have h := hu.comp (contMDiffOn_const.prodMk contMDiffOn_id)
      (s := (univ : Set M)) (fun y _ => ⟨ht, mem_univ y⟩)
    exact contMDiffOn_univ.mp h
  have hBslice (i) : (fun y => B i (t, y)) =ᶠ[𝓝 z]
      chartVossWeylIntegrand (S.base.metric (T - t)) a (u t) i := by
    filter_upwards [(isOpen_extChartAt_target (I := I) a).mem_nhds hz] with y hy
    have hp : (t, y) ∈ Ω := ⟨ht, hy⟩
    have hd := Analysis.fderiv_const_prod ((hU.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp))
    dsimp only [B, A, chartVossWeylIntegrand, gradChartCoeffOnE, partialDeriv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    have hdir : fderiv ℝ (scalarOnE (I := I) a (u t)) y (chartModelBasis E j) =
        fderiv ℝ U (t, y) (b j) := by
      change fderiv ℝ (fun y => u t ((extChartAt I a).symm y)) y (chartModelBasis E j) = _
      simpa only [U, b, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using
        congrArg (fun L : E →L[ℝ] ℝ => L (chartModelBasis E j)) hd
    rw [hdir]
    ring
  have hflux (i) : fderiv ℝ (B i) (t, z) (b i) =
      partialDeriv i (chartVossWeylIntegrand (S.base.metric (T - t)) a (u t) i) z := by
    have hd := Analysis.fderiv_const_prod (((hB i).contDiffAt (hΩ.mem_nhds htz)).differentiableAt (by norm_num))
    have he := congrArg (fun L : E →L[ℝ] ℝ => L (chartModelBasis E i)) hd
    rw [(hBslice i).fderiv_eq] at he
    simpa only [b, partialDeriv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using he.symm
  have hsum : (∑ i, ∑ j, fderiv ℝ (fun q => A i j q * fderiv ℝ U q (b j)) (t, z) (b i)) =
      ∑ i, fderiv ℝ (B i) (t, z) (b i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show B i = (fun q => ∑ j, A i j q * fderiv ℝ U q (b j)) from rfl,
      fderiv_fun_sum (fun j _ =>
        ((((hA i j).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).mul (hDU j)).contDiffAt
          (hΩ.mem_nhds htz)).differentiableAt (by norm_num)), sum_apply]
  have hlap := voss_weyl_laplacian_formula_pointwise (S.base.metric (T - t)) a hsmooth
    (mem_chart_source H x)
  have hprod := ((hρ.mul hU).contDiffAt (hΩ.mem_nhds htz)).differentiableAt (by simp)
  have hprodTime := hprod.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))
  have hprodTime' := hρTime.mul huTime
  have hsame : (fun r => ρ (r, z) * U (r, z)) = (fun r => ρ (r, z) * u r x) := by
    simp only [U, hzInv]
  simp only [Function.comp_def, id_eq] at hprodTime
  rw [hsame] at hprodTime
  have heq := hprodTime.unique hprodTime'
  rw [hP (t, z) htz, hsum] at heq
  simp_rw [hflux] at heq
  have hlap' : laplacianAt (reverseFamily (flowG S) T) t (u t) x =
      (∑ i, partialDeriv i (chartVossWeylIntegrand (S.base.metric (T - t)) a (u t) i) z) /
        ρ (t, z) := by
    rw [show laplacianAt (reverseFamily (flowG S) T) t (u t) x =
      ΔG (I := I) (S.base.metric (T - t)) ⟨u t, hsmooth⟩ x from
        laplacian_levi_eq (S.base.metric (T - t)) hsmooth x, hlap]
    simp only [chartVossWeylLaplacian, ρ, chartDensityOnE, hzInv, z]
  apply huTime.congr_deriv
  rw [hlap']
  apply (eq_sub_iff_add_eq).mpr
  apply (eq_div_iff hρpos.ne').mpr
  nlinarith [heq]

end DifferentialGeometry.PDE.RicciFlow.Entropy
