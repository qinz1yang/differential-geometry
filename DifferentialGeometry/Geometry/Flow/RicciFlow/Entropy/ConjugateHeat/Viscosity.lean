import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.Distribution
import DifferentialGeometry.Analysis.Viscosity.Parabolic
import DifferentialGeometry.Analysis.Integration.Lp.Lipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff Topology Matrix.Norms.Elementwise
namespace DifferentialGeometry.PDE.RicciFlow.Entropy
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem conjugate_heat_distribution_le_in_chart_of_upper_tests
    [MeasurableSpace (ℝ × E)] [BorelSpace (ℝ × E)]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) {J : Set ℝ} (hJ : IsOpen J) (hreg : ∀ t ∈ J, T - t ∈ D.regular)
    (a : M) {u : ℝ × E → ℝ}
    (hu : LocallyLipschitzOn (J ×ˢ interior (extChartAt I a).target) u)
    (htests : ∀ z ∈ J ×ˢ interior (extChartAt I a).target,
      ∀ phi : ℝ × E → ℝ, ContDiffAt ℝ 2 phi z →
      IsLocalMax (fun w => u w - phi w) z →
      fderiv ℝ phi z (1, 0) -
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (S.base.metric (T - z.1)) a i j z.2 *
            (fderiv ℝ (fderiv ℝ phi) z (0, chartModelBasis E i) (0, chartModelBasis E j) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (S.base.metric (T - z.1)) a i j k z.2 *
                  fderiv ℝ phi z (0, chartModelBasis E k))) +
        S.scalar (T - z.1) ((extChartAt I a).symm z.2) * u z ≤ 0)
    (μ : Measure (ℝ × E)) [μ.IsAddHaarMeasure]
    {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ J ×ˢ interior (extChartAt I a).target) (hφ0 : ∀ x, 0 ≤ φ x) :
    let A := fun w : ℝ × E => fun i j : Fin (Module.finrank ℝ E) =>
      chartInvGramOnE (S.base.metric (T - w.1)) a i j w.2
    let beta := fun w : ℝ × E => fun k : Fin (Module.finrank ℝ E) =>
      ∑ i, ∑ j, A w i j * chartChristoffel (S.base.metric (T - w.1)) a i j k w.2;
    -(∑ i, ∑ j, ∫ w, u w * fderiv ℝ (fderiv ℝ (fun z => A z i j * φ z))
        w (0, chartModelBasis E j) (0, chartModelBasis E i) ∂μ) -
      (∫ w, u w * fderiv ℝ φ w (1, 0) ∂μ) -
      (∑ k, ∫ w, u w * fderiv ℝ (fun z => beta z k * φ z) w (0, chartModelBasis E k) ∂μ) +
      (∫ w, (S.scalar (T - w.1) ((extChartAt I a).symm w.2) * u w) * φ w ∂μ) ≤ 0 := by
  classical
  let A : ℝ × E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun w i j => chartInvGramOnE (I := I) (S.base.metric (T - w.1)) a i j w.2
  let Gamma := fun w : ℝ × E => fun i j k : Fin (Module.finrank ℝ E) =>
    chartChristoffel (I := I) (S.base.metric (T - w.1)) a i j k w.2
  let beta := fun w : ℝ × E => fun k : Fin (Module.finrank ℝ E) =>
    ∑ i, ∑ j, A w i j * Gamma w i j k
  let e := chartModelBasis E
  let b := fun w : ℝ × E => e.equivFunL.symm (beta w)
  let c := fun w : ℝ × E => S.scalar (T - w.1) ((extChartAt I a).symm w.2)
  let Ω := J ×ˢ interior (extChartAt I a).target
  have hΩ : IsOpen Ω := hJ.prod isOpen_interior
  have hmap : ContDiff ℝ ∞ (fun w : ℝ × E => (T - w.1, w.2)) :=
    (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
  have hmaps : MapsTo (fun w : ℝ × E => (T - w.1, w.2)) Ω
      (D.regular ×ˢ interior (extChartAt I a).target) := by
    intro w hw
    exact ⟨hreg w.1 hw.1, hw.2⟩
  have hAc (i j : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞ (fun w => A w i j) Ω := by
    have h := MetricFamilySmoothOn.chartInvGramOnE_contDiffOn (I := I) (M := M)
      (D := D) (g_fam := S.base.metric) hS.smoothMetric
      (J := D.regular) Subset.rfl a i j
    have hh := h.comp hmap.contDiffOn hmaps
    exact hh
  have hGc (i j k : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞ (fun w => Gamma w i j k) Ω := by
    have h := MetricFamilySmoothOn.chartChristoffelOnE_contDiffOn (I := I) (M := M)
      (D := D) (g_fam := S.base.metric) hS.smoothMetric
      (J := D.regular) Subset.rfl D.regular_isOpen.uniqueDiffOn a i j k
    have hh := h.comp hmap.contDiffOn hmaps
    exact hh
  have hcc : ContDiffOn ℝ ∞ c Ω := by
    have h := (chartScalFun_smooth S hS a).comp hmap.contDiffOn hmaps
    exact h
  have hbetac (k : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞ (fun w => beta w k) Ω :=
    ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (hAc i j).mul (hGc i j k)
  have hb : ContDiffOn ℝ ∞ b Ω :=
    e.equivFunL.symm.contDiff.comp_contDiffOn (contDiffOn_pi.mpr hbetac)
  have hbrepr (w : ℝ × E) (k : Fin (Module.finrank ℝ E)) : e.repr (b w) k = beta w k := by
    change e.equivFun (e.equivFun.symm (beta w)) k = _
    rw [e.equivFun.apply_symm_apply]
  have hbexpand (w : ℝ × E) : ((0 : ℝ), b w) = ∑ k, beta w k • (0, e k) := by
    change (0, e.equivFun.symm (beta w)) = _
    rw [Module.Basis.equivFun_symm_apply]
    ext <;> simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_mk, smul_zero, Finset.sum_const_zero]
  have hop (w : ℝ × E) (D : (ℝ × E) →L[ℝ] ℝ) :
      D (1, b w) = D (1, 0) + ∑ i, ∑ j, A w i j * ∑ k, Gamma w i j k * D (0, e k) := by
    have hsplit : D (1, b w) = D (1, 0) + D (0, b w) := by
      rw [← map_add]
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    rw [hsplit, hbexpand, map_sum]
    simp only [map_smul, smul_eq_mul, beta, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h := Analysis.Viscosity.parabolic_distribution_le_of_upper_tests_of_locallyLipschitzOn
    (μ := μ) e hΩ hu ((contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr (hAc i)).of_le (WithTop.coe_le_coe.mpr le_top))
    (fun w hw => chartInvGramOnE_posDef (S.base.metric (T - w.1)) a (interior_subset hw.2))
    (hb.of_le (by norm_num)) ((hcc.of_le (by norm_num)).locallyLipschitzOn_of_isOpen hΩ)
    (r := fun _ => 0) (LipschitzWith.const (0 : ℝ)).locallyLipschitz.locallyLipschitzOn
    (fun w hw ψ hψ hm => ?_) hφ hφc hφs hφ0
  · simp only [hbrepr, sub_zero] at h
    exact h
  · have hupper := htests w hw ψ (hψ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt hm
    change fderiv ℝ ψ w (1, 0) -
      (∑ i, ∑ j, A w i j * (fderiv ℝ (fderiv ℝ ψ) w (0, e i) (0, e j) -
        ∑ k, Gamma w i j k * fderiv ℝ ψ w (0, e k))) + c w * u w ≤ 0 at hupper
    rw [hop]
    simp_rw [mul_sub, Finset.sum_sub_distrib] at hupper
    linarith only [hupper]

private theorem conjugate_heat_weak_le_in_chart_of_upper_tests_of_contDiff
    [MeasurableSpace (ℝ × E)] [BorelSpace (ℝ × E)]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) {J : Set ℝ} (hJ : IsOpen J) (hreg : ∀ t ∈ J, T - t ∈ D.regular)
    (a : M) {u : ℝ × E → ℝ}
    (hu : LocallyLipschitzOn (J ×ˢ interior (extChartAt I a).target) u)
    (htests : ∀ z ∈ J ×ˢ interior (extChartAt I a).target,
      ∀ phi : ℝ × E → ℝ, ContDiffAt ℝ 2 phi z →
      IsLocalMax (fun w => u w - phi w) z →
      fderiv ℝ phi z (1, 0) -
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (S.base.metric (T - z.1)) a i j z.2 *
            (fderiv ℝ (fderiv ℝ phi) z (0, chartModelBasis E i) (0, chartModelBasis E j) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (S.base.metric (T - z.1)) a i j k z.2 *
                  fderiv ℝ phi z (0, chartModelBasis E k))) +
        S.scalar (T - z.1) ((extChartAt I a).symm z.2) * u z ≤ 0)
    (μ : Measure (ℝ × E)) [μ.IsAddHaarMeasure]
    {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ J ×ˢ interior (extChartAt I a).target) (hφ0 : ∀ x, 0 ≤ φ x) :
    let ρ := fun w : ℝ × E => chartDensityOnE (S.base.metric (T - w.1)) a w.2
    let A := fun w : ℝ × E => fun i j : Fin (Module.finrank ℝ E) =>
      chartInvGramOnE (S.base.metric (T - w.1)) a i j w.2;
    (∑ i, ∑ j, ∫ w, (A w i j * ρ w) * lineDeriv ℝ u w (0, chartModelBasis E j) *
      fderiv ℝ φ w (0, chartModelBasis E i) ∂μ) ≤
        ∫ w, ρ w * u w * fderiv ℝ φ w (1, 0) ∂μ := by
  intro ρ A
  let Ω := J ×ˢ interior (extChartAt I a).target
  have hΩ : IsOpen Ω := hJ.prod isOpen_interior
  have hρ : ContDiffOn ℝ ∞ ρ Ω := by
    have h := chartDensityOnE_family_contDiffOn hS.smoothMetric Subset.rfl a
    have hm : ContDiff ℝ ∞ (fun w : ℝ × E => (T - w.1, w.2)) :=
      (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
    have hh := h.comp (s := Ω) hm.contDiffOn
      (fun w hw => ⟨hreg w.1 hw.1, interior_subset hw.2⟩)
    exact hh
  have hψ : ContDiff ℝ 2 (fun w => ρ w * φ w) :=
    (((hρ.of_le (WithTop.coe_le_coe.mpr le_top)).mul hφ.contDiffOn).contDiff_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs))
  have hψ0 (w : ℝ × E) : 0 ≤ ρ w * φ w :=
    mul_nonneg (Real.sqrt_nonneg _) (hφ0 w)
  have hdist := conjugate_heat_distribution_le_in_chart_of_upper_tests S hS T hJ hreg a
    hu htests μ hψ hφc.mul_left (tsupport_mul_subset_right.trans hφs) hψ0
  have hid := integral_conjugate_heat_adjoint_eq_divergence_in_chart S hS
    T hJ hreg a (μ := μ) hu hφ hφc hφs
  dsimp only [ρ] at hdist hid
  rw [hid] at hdist
  exact sub_nonpos.mp hdist

theorem conjugate_heat_weak_le_in_chart_of_upper_tests
    [MeasurableSpace (ℝ × E)] [BorelSpace (ℝ × E)]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) {J : Set ℝ} (hJ : IsOpen J) (hreg : ∀ t ∈ J, T - t ∈ D.regular)
    (a : M) {u : ℝ × E → ℝ}
    (hu : LocallyLipschitzOn (J ×ˢ interior (extChartAt I a).target) u)
    (htests : ∀ z ∈ J ×ˢ interior (extChartAt I a).target,
      ∀ phi : ℝ × E → ℝ, ContDiffAt ℝ 2 phi z →
      IsLocalMax (fun w => u w - phi w) z →
      fderiv ℝ phi z (1, 0) -
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (S.base.metric (T - z.1)) a i j z.2 *
            (fderiv ℝ (fderiv ℝ phi) z (0, chartModelBasis E i) (0, chartModelBasis E j) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (S.base.metric (T - z.1)) a i j k z.2 *
                  fderiv ℝ phi z (0, chartModelBasis E k))) +
        S.scalar (T - z.1) ((extChartAt I a).symm z.2) * u z ≤ 0)
    (μ : Measure (ℝ × E)) [μ.IsAddHaarMeasure]
    {φ : ℝ × E → ℝ} (hφ : LocallyLipschitzOn (J ×ˢ interior (extChartAt I a).target) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ J ×ˢ interior (extChartAt I a).target) (hφ0 : ∀ x, 0 ≤ φ x) :
    let ρ := fun w : ℝ × E => chartDensityOnE (S.base.metric (T - w.1)) a w.2
    let A := fun w : ℝ × E => fun i j : Fin (Module.finrank ℝ E) =>
      chartInvGramOnE (S.base.metric (T - w.1)) a i j w.2;
    (∑ i, ∑ j, ∫ w, (A w i j * ρ w) * lineDeriv ℝ u w (0, chartModelBasis E j) *
      fderiv ℝ φ w (0, chartModelBasis E i) ∂μ) ≤
        ∫ w, ρ w * u w * fderiv ℝ φ w (1, 0) ∂μ := by
  intro ρ A
  let Ω := J ×ˢ interior (extChartAt I a).target
  have hΩ : IsOpen Ω := hJ.prod isOpen_interior
  have hρ : ContDiffOn ℝ ∞ ρ Ω := by
    have h := chartDensityOnE_family_contDiffOn hS.smoothMetric Subset.rfl a
    have hm : ContDiff ℝ ∞ (fun w : ℝ × E => (T - w.1, w.2)) :=
      (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
    have hh := h.comp (s := Ω) hm.contDiffOn
      (fun w hw => ⟨hreg w.1 hw.1, interior_subset hw.2⟩)
    exact hh
  have hmap : ContDiff ℝ ∞ (fun w : ℝ × E => (T - w.1, w.2)) :=
    (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
  have hmaps : MapsTo (fun w : ℝ × E => (T - w.1, w.2)) Ω
      (D.regular ×ˢ interior (extChartAt I a).target) := by
    intro w hw
    exact ⟨hreg w.1 hw.1, hw.2⟩
  have hAc (i j : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞ (fun w => A w i j) Ω := by
    have h := MetricFamilySmoothOn.chartInvGramOnE_contDiffOn (I := I) (M := M)
      (D := D) (g_fam := S.base.metric) hS.smoothMetric
      (J := D.regular) Subset.rfl a i j
    have hh := h.comp hmap.contDiffOn hmaps
    exact hh
  have hdu (j : Fin (Module.finrank ℝ E)) :
      LocallyIntegrableOn (fun w => lineDeriv ℝ u w (0, chartModelBasis E j)) Ω μ := by
    apply (locallyIntegrableOn_iff hΩ.isLocallyClosed).mpr
    intro K hKΩ hK
    exact memLp_one_iff_integrable.mp
      (hu.memLp_lineDeriv_of_isCompact hΩ hK hKΩ hK.measure_ne_top (0, chartModelBasis E j) 1)
  let b : Option (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → (ℝ × E) → ℝ
    | none => fun w => ρ w * u w
    | some ij => fun w => -((A w ij.1 ij.2 * ρ w) * lineDeriv ℝ u w (0, chartModelBasis E ij.2))
  let v : Option (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → ℝ × E
    | none => (1, 0)
    | some ij => (0, chartModelBasis E ij.1)
  have hb (i) : LocallyIntegrableOn (b i) Ω μ := by
    cases i with
    | none => exact (hρ.continuousOn.mul hu.continuousOn).locallyIntegrableOn hΩ.measurableSet
    | some ij => exact ((hdu ij.2).continuousOn_mul
        ((hAc ij.1 ij.2).continuousOn.mul hρ.continuousOn) hΩ.isLocallyClosed).neg
  have hsum (ψ : ℝ × E → ℝ) :
      (∑ i, ∫ w, b i w * fderiv ℝ ψ w (v i) ∂μ) =
        (∫ w, ρ w * u w * fderiv ℝ ψ w (1, 0) ∂μ) -
          ∑ i, ∑ j, ∫ w, (A w i j * ρ w) * lineDeriv ℝ u w (0, chartModelBasis E j) *
            fderiv ℝ ψ w (0, chartModelBasis E i) ∂μ := by
    simp only [Fintype.sum_option, Fintype.sum_prod_type, b, v, neg_mul,
      integral_neg, Finset.sum_neg_distrib]
    ring
  have h := Analysis.sum_integral_mul_fderiv_nonneg_of_contDiff_test hΩ hb v
    (fun ψ hψ hψc hψs hψ0 => by
      rw [hsum]
      exact sub_nonneg.mpr (conjugate_heat_weak_le_in_chart_of_upper_tests_of_contDiff
        S hS T hJ hreg a hu htests μ
        (hψ.of_le (WithTop.coe_le_coe.mpr le_top)) hψc hψs hψ0)) hφ hφc hφs hφ0
  rw [hsum] at h
  exact sub_nonneg.mp h

end DifferentialGeometry.PDE.RicciFlow.Entropy
