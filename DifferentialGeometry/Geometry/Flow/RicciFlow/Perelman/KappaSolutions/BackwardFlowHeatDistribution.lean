import DifferentialGeometry.Analysis.Parabolic.WeakEquationManifold
import DifferentialGeometry.Analysis.Viscosity.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.Distribution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowHeatTest
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.Lipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set _root_.MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Entropy
open scoped Manifold ContDiff _root_.Topology NNReal Matrix.Norms.Elementwise

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem backward_flow_limit_perelmanDensity_distribution_le_in_chart
    [MeasurableSpace (ℝ × E)] [BorelSpace (ℝ × E)]
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source n ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (((backwardFlowSequence F tau htau q).term (subseq n)).S.base.metric t).inner
            (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x w))
    (hmetric : ∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi.map n w.1) (tau (subseq n) * w.2)) ell atTop Q)
    (hLip : ∀ B : ℝ, 0 ≤ B → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ s t : Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf (L.S.base.metric 0) x y).toReal + |(s : ℝ) - t|))
    (a : L.M) (μ : Measure (ℝ × E)) [μ.IsAddHaarMeasure]
    {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo 1 T ×ˢ (extChartAt I a).target) (hφ0 : ∀ x, 0 ≤ φ x) :
    let u := fun w : ℝ × E => perelmanDensity (Module.finrank ℝ E) w.1
      (fun x => ell (x, projIcc 1 T hT.le w.1)) ((extChartAt I a).symm w.2)
    let A := fun w : ℝ × E => fun i j : Fin (Module.finrank ℝ E) =>
      chartInvGramOnE (I := I) (L.S.base.metric (1 - w.1)) a i j w.2
    let beta := fun w : ℝ × E => fun k : Fin (Module.finrank ℝ E) =>
      ∑ i, ∑ j, A w i j * chartChristoffel (I := I) (L.S.base.metric (1 - w.1)) a i j k w.2;
    -(∑ i, ∑ j, ∫ w, u w * fderiv ℝ (fderiv ℝ (fun z => A z i j * φ z))
        w (0, chartModelBasis E j) (0, chartModelBasis E i) ∂μ) -
      (∫ w, u w * fderiv ℝ φ w (1, 0) ∂μ) -
      (∑ k, ∫ w, u w * fderiv ℝ (fun z => beta z k * φ z) w (0, chartModelBasis E k) ∂μ) +
      (∫ w, (metricScalarAt (L.S.base.metric (1 - w.1)) ((extChartAt I a).symm w.2) * u w) * φ w ∂μ) ≤ 0 := by
  classical
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace H L.M
  let u := fun w : ℝ × E => perelmanDensity (Module.finrank ℝ E) w.1
    (fun x => ell (x, projIcc 1 T hT.le w.1)) ((extChartAt I a).symm w.2)
  let A : ℝ × E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun w i j => chartInvGramOnE (I := I) (L.S.base.metric (1 - w.1)) a i j w.2
  let Gamma := fun w : ℝ × E => fun i j k : Fin (Module.finrank ℝ E) =>
    chartChristoffel (I := I) (L.S.base.metric (1 - w.1)) a i j k w.2
  let beta := fun w : ℝ × E => fun k : Fin (Module.finrank ℝ E) =>
    ∑ i, ∑ j, A w i j * Gamma w i j k
  let e := chartModelBasis E
  let b := fun w : ℝ × E => e.equivFunL.symm (beta w)
  let c := fun w : ℝ × E => metricScalarAt (L.S.base.metric (1 - w.1)) ((extChartAt I a).symm w.2)
  let Ω := Ioo (1 : ℝ) T ×ˢ (extChartAt I a).target
  have hΩ : IsOpen Ω := isOpen_Ioo.prod (isOpen_extChartAt_target (I := I) a)
  have hu : LocallyLipschitzOn Ω u :=
    (locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds
      (L.S.base.metric 0) L.basepoint hT.le ell hLip a (Module.finrank ℝ E)).mono
      (fun _ hw => ⟨zero_lt_one.trans hw.1.1, hw.2⟩)
  have hmap : ContDiff ℝ ∞ (fun w : ℝ × E => (1 - w.1, w.2)) :=
    (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
  have hmaps : MapsTo (fun w : ℝ × E => (1 - w.1, w.2)) Ω
      (Iio 0 ×ˢ interior (extChartAt I a).target) := by
    intro w hw
    exact ⟨sub_neg.mpr hw.1.1, by simpa only [(isOpen_extChartAt_target (I := I) a).interior_eq] using hw.2⟩
  have hAc (i j : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞ (fun w => A w i j) Ω := by
    have h := MetricFamilySmoothOn.chartInvGramOnE_contDiffOn (I := I) (M := L.M)
      (D := ancientTimeInterval) (g_fam := L.S.base.metric) L.isSolution.smoothMetric
      (J := Iio 0) Subset.rfl a i j
    have hh := h.comp hmap.contDiffOn hmaps
    exact hh
  have hGc (i j k : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞ (fun w => Gamma w i j k) Ω := by
    have h := MetricFamilySmoothOn.chartChristoffelOnE_contDiffOn (I := I) (M := L.M)
      (D := ancientTimeInterval) (g_fam := L.S.base.metric) L.isSolution.smoothMetric
      (J := Iio 0) Subset.rfl (uniqueDiffOn_Iio 0) a i j k
    have hh := h.comp hmap.contDiffOn hmaps
    exact hh
  have hcc : ContDiffOn ℝ ∞ c Ω := by
    have h := (chartScalFun_smooth L.S L.isSolution a).comp hmap.contDiffOn hmaps
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
    (fun w hw => chartInvGramOnE_posDef (L.S.base.metric (1 - w.1)) a hw.2)
    (hb.of_le (by norm_num)) ((hcc.of_le (by norm_num)).locallyLipschitzOn_of_isOpen hΩ)
    (r := fun _ => 0) (LipschitzWith.const (0 : ℝ)).locallyLipschitz.locallyLipschitzOn
    (fun w hw ψ hψ hm => ?_) hφ hφc hφs hφ0
  · simp only [hbrepr, sub_zero] at h
    exact h
  · have hupper := backward_flow_limit_perelmanDensity_upper_test_in_chart
      F hF p tau htau q L Phi R G hG hmetric hT ell hell a hw ψ
        (hψ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt hm
    change fderiv ℝ ψ w (1, 0) -
      (∑ i, ∑ j, A w i j * (fderiv ℝ (fderiv ℝ ψ) w (0, e i) (0, e j) -
        ∑ k, Gamma w i j k * fderiv ℝ ψ w (0, e k))) + c w * u w ≤ 0 at hupper
    rw [hop]
    simp_rw [mul_sub, Finset.sum_sub_distrib] at hupper
    linarith only [hupper]

private theorem backward_flow_limit_perelmanDensity_weak_le_in_chart_of_contDiff
    [MeasurableSpace (ℝ × E)] [BorelSpace (ℝ × E)]
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source n ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (((backwardFlowSequence F tau htau q).term (subseq n)).S.base.metric t).inner
            (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x w))
    (hmetric : ∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi.map n w.1) (tau (subseq n) * w.2)) ell atTop Q)
    (hLip : ∀ B : ℝ, 0 ≤ B → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ s t : Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf (L.S.base.metric 0) x y).toReal + |(s : ℝ) - t|))
    (a : L.M) (μ : Measure (ℝ × E)) [μ.IsAddHaarMeasure]
    {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo 1 T ×ˢ (extChartAt I a).target) (hφ0 : ∀ x, 0 ≤ φ x) :
    let u := fun w : ℝ × E => perelmanDensity (Module.finrank ℝ E) w.1
      (fun x => ell (x, projIcc 1 T hT.le w.1)) ((extChartAt I a).symm w.2)
    let ρ := fun w : ℝ × E => chartDensityOnE (L.S.base.metric (1 - w.1)) a w.2
    let A := fun w : ℝ × E => fun i j : Fin (Module.finrank ℝ E) =>
      chartInvGramOnE (L.S.base.metric (1 - w.1)) a i j w.2;
    (∑ i, ∑ j, ∫ w, (A w i j * ρ w) * lineDeriv ℝ u w (0, chartModelBasis E j) *
      fderiv ℝ φ w (0, chartModelBasis E i) ∂μ) ≤
        ∫ w, ρ w * u w * fderiv ℝ φ w (1, 0) ∂μ := by
  intro u ρ A
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace H L.M
  let Ω := Ioo (1 : ℝ) T ×ˢ (extChartAt I a).target
  have hΩ : IsOpen Ω := isOpen_Ioo.prod (isOpen_extChartAt_target (I := I) a)
  have hu : LocallyLipschitzOn Ω u :=
    (locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds
      (L.S.base.metric 0) L.basepoint hT.le ell hLip a (Module.finrank ℝ E)).mono
      (fun _ hw => ⟨zero_lt_one.trans hw.1.1, hw.2⟩)
  have hρ : ContDiffOn ℝ ∞ ρ Ω := by
    have h := chartDensityOnE_family_contDiffOn L.isSolution.smoothMetric Subset.rfl a
    have hm : ContDiff ℝ ∞ (fun w : ℝ × E => (1 - w.1, w.2)) :=
      (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
    have hh := h.comp (s := Ω) hm.contDiffOn
      (fun w hw => ⟨sub_neg.mpr hw.1.1, hw.2⟩)
    exact hh
  have hψ : ContDiff ℝ 2 (fun w => ρ w * φ w) :=
    (((hρ.of_le (WithTop.coe_le_coe.mpr le_top)).mul hφ.contDiffOn).contDiff_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs))
  have hψ0 (w : ℝ × E) : 0 ≤ ρ w * φ w :=
    mul_nonneg (Real.sqrt_nonneg _) (hφ0 w)
  have hdist := backward_flow_limit_perelmanDensity_distribution_le_in_chart
    F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip a μ hψ hφc.mul_left
    (tsupport_mul_subset_right.trans hφs) hψ0
  have hi : LocallyLipschitzOn (Ioo (1 : ℝ) T ×ˢ interior (extChartAt I a).target) u :=
    hu.mono (prod_mono Subset.rfl interior_subset)
  have his : tsupport φ ⊆ Ioo (1 : ℝ) T ×ˢ interior (extChartAt I a).target := by
    simpa only [(isOpen_extChartAt_target (I := I) a).interior_eq] using hφs
  have hid := integral_conjugate_heat_adjoint_eq_divergence_in_chart L.S L.isSolution
    1 isOpen_Ioo (fun s hs => sub_neg.mpr hs.1) a (μ := μ) hi hφ hφc his
  dsimp only [u, ρ, SolutionOn.scalar, SolutionFamily.scalar] at hdist hid
  rw [hid] at hdist
  exact sub_nonpos.mp hdist

theorem backward_flow_limit_perelmanDensity_weak_le_in_chart
    [MeasurableSpace (ℝ × E)] [BorelSpace (ℝ × E)]
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source n ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (((backwardFlowSequence F tau htau q).term (subseq n)).S.base.metric t).inner
            (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x w))
    (hmetric : ∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi.map n w.1) (tau (subseq n) * w.2)) ell atTop Q)
    (hLip : ∀ B : ℝ, 0 ≤ B → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ s t : Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf (L.S.base.metric 0) x y).toReal + |(s : ℝ) - t|))
    (a : L.M) (μ : Measure (ℝ × E)) [μ.IsAddHaarMeasure]
    {φ : ℝ × E → ℝ} (hφ : LocallyLipschitzOn (Ioo 1 T ×ˢ (extChartAt I a).target) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo 1 T ×ˢ (extChartAt I a).target) (hφ0 : ∀ x, 0 ≤ φ x) :
    let u := fun w : ℝ × E => perelmanDensity (Module.finrank ℝ E) w.1
      (fun x => ell (x, projIcc 1 T hT.le w.1)) ((extChartAt I a).symm w.2)
    let ρ := fun w : ℝ × E => chartDensityOnE (L.S.base.metric (1 - w.1)) a w.2
    let A := fun w : ℝ × E => fun i j : Fin (Module.finrank ℝ E) =>
      chartInvGramOnE (L.S.base.metric (1 - w.1)) a i j w.2;
    (∑ i, ∑ j, ∫ w, (A w i j * ρ w) * lineDeriv ℝ u w (0, chartModelBasis E j) *
      fderiv ℝ φ w (0, chartModelBasis E i) ∂μ) ≤
        ∫ w, ρ w * u w * fderiv ℝ φ w (1, 0) ∂μ := by
  intro u ρ A
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace H L.M
  let Ω := Ioo (1 : ℝ) T ×ˢ (extChartAt I a).target
  have hΩ : IsOpen Ω := isOpen_Ioo.prod (isOpen_extChartAt_target (I := I) a)
  have hu : LocallyLipschitzOn Ω u :=
    (locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds
      (L.S.base.metric 0) L.basepoint hT.le ell hLip a (Module.finrank ℝ E)).mono
      (fun _ hw => ⟨zero_lt_one.trans hw.1.1, hw.2⟩)
  have hρ : ContDiffOn ℝ ∞ ρ Ω := by
    have h := chartDensityOnE_family_contDiffOn L.isSolution.smoothMetric Subset.rfl a
    have hm : ContDiff ℝ ∞ (fun w : ℝ × E => (1 - w.1, w.2)) :=
      (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
    have hh := h.comp (s := Ω) hm.contDiffOn
      (fun w hw => ⟨sub_neg.mpr hw.1.1, hw.2⟩)
    exact hh
  have hmap : ContDiff ℝ ∞ (fun w : ℝ × E => (1 - w.1, w.2)) :=
    (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
  have hmaps : MapsTo (fun w : ℝ × E => (1 - w.1, w.2)) Ω
      (Iio 0 ×ˢ interior (extChartAt I a).target) := by
    intro w hw
    exact ⟨sub_neg.mpr hw.1.1, by simpa only [(isOpen_extChartAt_target (I := I) a).interior_eq] using hw.2⟩
  have hAc (i j : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞ (fun w => A w i j) Ω := by
    have h := MetricFamilySmoothOn.chartInvGramOnE_contDiffOn (I := I) (M := L.M)
      (D := ancientTimeInterval) (g_fam := L.S.base.metric) L.isSolution.smoothMetric
      (J := Iio 0) Subset.rfl a i j
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
      exact sub_nonneg.mpr (backward_flow_limit_perelmanDensity_weak_le_in_chart_of_contDiff
        F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip a μ
        (hψ.of_le (WithTop.coe_le_coe.mpr le_top)) hψc hψs hψ0)) hφ hφc hφs hφ0
  rw [hsum] at h
  exact sub_nonneg.mp h

theorem backward_flow_limit_perelmanDensity_tensor_weak_le
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source n ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (((backwardFlowSequence F tau htau q).term (subseq n)).S.base.metric t).inner
            (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x w))
    (hmetric : ∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi.map n w.1) (tau (subseq n) * w.2)) ell atTop Q)
    (hLip : ∀ B : ℝ, 0 ≤ B → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ s t : Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf (L.S.base.metric 0) x y).toReal + |(s : ℝ) - t|))
    (χ : C(L.M, ℝ)) (hχc : HasCompactSupport (χ : L.M → ℝ)) (hχ0 : ∀ x, 0 ≤ χ x)
    {C : ℝ≥0} (hχ : ∀ x y, edist (χ x) (χ y) ≤ C * riemannianEDistOf (L.S.base.metric 0) x y)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo 1 T) (hψ0 : ∀ t, 0 ≤ ψ t) :
    let u := fun t => perelmanDensity (Module.finrank ℝ E) t
      (fun x => ell (x, projIcc 1 T hT.le t))
    let g := fun t => L.S.base.metric (1 - t)
    Integrable (fun t => ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x)
      ∂riemannianVolumeMeasure (I := I) (M := L.M) (g t)) volume ∧
    Integrable (fun t => deriv ψ t * ∫ x, u t x * χ x
      ∂riemannianVolumeMeasure (I := I) (M := L.M) (g t)) volume ∧
    (∫ t, ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x)
      ∂riemannianVolumeMeasure (I := I) (M := L.M) (g t)) ≤
      ∫ t, deriv ψ t * ∫ x, u t x * χ x
        ∂riemannianVolumeMeasure (I := I) (M := L.M) (g t) := by
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace H L.M
  let _ : MeasurableSpace E := borel E
  let _ : BorelSpace E := ⟨rfl⟩
  let u : ℝ → C(L.M, ℝ) := fun t =>
    ⟨perelmanDensity (Module.finrank ℝ E) t (fun x => ell (x, projIcc 1 T hT.le t)),
      continuous_const.mul (Real.continuous_exp.comp
        (ell.continuous.comp (continuous_id.prodMk continuous_const)).neg)⟩
  apply Analysis.Parabolic.integral_tensor_test_le_of_chart_weak_le isOpen_Ioo
    (fun t => L.S.base.metric (1 - t)) u
    (fun α => (locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds
      (L.S.base.metric 0) L.basepoint hT.le ell hLip α (Module.finrank ℝ E)).mono
      (fun _ hw => ⟨zero_lt_one.trans hw.1.1, hw.2⟩))
    (fun α i j => ?_)
    (fun α φ hφ hφc hφs hφ0 => backward_flow_limit_perelmanDensity_weak_le_in_chart
      F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip α
      (volume.prod (modelHaar (E := E))) hφ hφc hφs hφ0)
    (L.S.base.metric 0) χ hχc hχ0 hχ hψ hψc hψs hψ0
  have hmap : ContinuousOn (fun z : ℝ × L.M => (1 - z.1, z.2))
      (Ioo 1 T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
  have hmaps : MapsTo (fun z : ℝ × L.M => (1 - z.1, z.2))
      (Ioo 1 T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)
      (ancientTimeInterval.carrier ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    fun z hz => ⟨show 1 - z.1 ≤ 0 from sub_nonpos.mpr hz.1.1.le, hz.2⟩
  have hc : ContinuousOn
      ((fun z : ℝ × L.M => chartGramMatrix (L.S.base.metric z.1) α z.2 i j) ∘
        (fun z : ℝ × L.M => (1 - z.1, z.2)))
      (Ioo 1 T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    (L.isSolution.smoothMetric.chartGramMatrix_continuousOn_carrier α i j).comp hmap hmaps
  exact hc


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
