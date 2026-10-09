import DifferentialGeometry.Analysis.Viscosity.Comparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowHeatTest

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Entropy
open scoped _root_.Manifold ContDiff BigOperators _root_.Topology
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

theorem perelmanDensity_comparison_of_rescaled_reducedLength_limit_in_chart
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    (Phi : ℕ → PartialDiffeomorph I I L.M F.M ∞)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ (Phi n).source ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (c n)⁻¹ * (F.S.base.metric (c n * (t - 1))).inner (Phi n x)
            (mfderiv I I (Phi n) x v) (mfderiv I I (Phi n) x w))
    (hmetric : ∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi n w.1) (c n * w.2)) ell atTop Q)
    (a : L.M) {alpha beta : ℝ} (hwindow : Icc alpha beta ⊆ Ioo 1 T)
    {K : Set E} (hK : IsCompact K) (hchart : K ⊆ (extChartAt I a).target)
    (v : ℝ × E → ℝ) (hv : ContinuousOn v (Icc alpha beta ×ˢ K))
    (hv2 : ∀ z ∈ Ioo alpha beta ×ˢ interior K, ContDiffAt ℝ 2 v z)
    (hsuper : ∀ z ∈ Ioo alpha beta ×ˢ interior K,
      0 ≤ fderiv ℝ v z (1, 0) -
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a i j z.2 *
            (fderiv ℝ (fderiv ℝ v) z (0, chartModelBasis E i) (0, chartModelBasis E j) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) (L.S.base.metric (1 - z.1)) a i j k z.2 *
                  fderiv ℝ v z (0, chartModelBasis E k))) +
        metricScalarAt (L.S.base.metric (1 - z.1)) ((extChartAt I a).symm z.2) * v z) :
    let u := fun w : ℝ × E => perelmanDensity (Module.finrank ℝ E) w.1
      (fun x => ell (x, projIcc 1 T hT.le w.1)) ((extChartAt I a).symm w.2)
    (∀ x ∈ K, u (alpha, x) ≤ v (alpha, x)) →
    (∀ t ∈ Icc alpha beta, ∀ x ∈ K \ interior K, u (t, x) ≤ v (t, x)) →
    ∀ z ∈ Icc alpha beta ×ˢ K, u z ≤ v z := by
  let n := Module.finrank ℝ E
  let u := fun w : ℝ × E => perelmanDensity n w.1
    (fun x => ell (x, projIcc 1 T hT.le w.1)) ((extChartAt I a).symm w.2)
  let A := fun (z : ℝ × E) i j => chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a i j z.2
  let B := fun (z : ℝ × E) i j k => chartChristoffel (I := I) (L.S.base.metric (1 - z.1)) a i j k z.2
  let d := fun z : ℝ × E =>
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (A z i j * B z i j k) • chartModelBasis E k
  let rho := fun z : ℝ × E => metricScalarAt (L.S.base.metric (1 - z.1)) ((extChartAt I a).symm z.2)
  have hxcont : ContinuousOn (fun z : ℝ × E => (extChartAt I a).symm z.2) (Icc alpha beta ×ˢ K) :=
    (continuousOn_extChartAt_symm a).comp continuous_snd.continuousOn (fun _ hz => hchart hz.2)
  have hellcont : ContinuousOn
      (fun z : ℝ × E => ell ((extChartAt I a).symm z.2, projIcc 1 T hT.le z.1))
      (Icc alpha beta ×ˢ K) :=
    ell.continuous.comp_continuousOn (hxcont.prodMk (continuous_projIcc.comp continuous_fst).continuousOn)
  have huc : ContinuousOn u (Icc alpha beta ×ˢ K) := by
    have hpref : ContinuousOn (fun z : ℝ × E => perelmanDensityPrefactor n z.1)
        (Icc alpha beta ×ˢ K) := by
      apply (continuous_const.mul continuous_fst).continuousOn.rpow_const
      intro z hz
      exact Or.inl (mul_pos (mul_pos (by norm_num) Real.pi_pos)
        (zero_lt_one.trans (hwindow hz.1).1)).ne'
    exact hpref.mul (Real.continuous_exp.comp_continuousOn hellcont.neg)
  have hrho : ContinuousOn rho (Icc alpha beta ×ˢ K) := by
    have hh : ContinuousOn (fun w : ℝ × L.M => metricScalarAt (L.S.base.metric w.1) w.2)
        (Iic 0 ×ˢ univ) := L.isSolution.scalarCont
    apply hh.comp ((continuous_const.sub continuous_fst).continuousOn.prodMk hxcont)
    intro z hz
    exact ⟨sub_nonpos.mpr (hwindow hz.1).1.le, mem_univ _⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hrho
  have hbound : ∀ z ∈ Ioo alpha beta ×ˢ interior K, -C ≤ rho z := by
    intro z hz
    have hh := hC z ⟨⟨hz.1.1.le, hz.1.2.le⟩, interior_subset hz.2⟩
    exact (abs_le.mp hh).1
  have hop (z : ℝ × E) (P : (ℝ × E) →L[ℝ] ℝ)
      (Q : (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) :
      P (1, d z) - (∑ i : Fin n, ∑ j : Fin n, A z i j * Q (0, chartModelBasis E i) (0, chartModelBasis E j)) =
        P (1, 0) - ∑ i : Fin n, ∑ j : Fin n, A z i j *
          (Q (0, chartModelBasis E i) (0, chartModelBasis E j) -
            ∑ k : Fin n, B z i j k * P (0, chartModelBasis E k)) := by
    have heq : ((1 : ℝ), d z) = (1, (0 : E)) + (0, d z) := by ext <;> simp
    rw [heq, map_add]
    change P (1, 0) + P ((ContinuousLinearMap.inr ℝ ℝ E) (d z)) - _ = _
    simp only [d, map_sum, map_smul, smul_eq_mul, ContinuousLinearMap.inr_apply,
      Finset.mul_sum, mul_assoc, mul_sub, Finset.sum_sub_distrib]
    ring
  dsimp only
  intro hinit hside
  apply DifferentialGeometry.Analysis.Viscosity.linear_parabolic_comparison_with_smooth_supersolution
    hK (huc.sub hv) hv2 A (fun _ => chartModelBasis E) d rho (fun _ => 0) C hbound _ _ hinit hside
  · intro z hz phi hphi hmax
    rw [hop]
    exact perelmanDensity_upper_test_of_rescaled_reducedLength_limit_in_chart
      F hF p c hc L Phi R G hG hmetric hT ell hell a
      ⟨hwindow ⟨hz.1.1.le, hz.1.2.le⟩, hchart (interior_subset hz.2)⟩ phi hphi hmax
  · intro z hz
    rw [hop]
    exact hsuper z hz

theorem backward_flow_limit_perelmanDensity_comparison_in_chart
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
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
    (a : L.M) {alpha beta : ℝ} (hwindow : Icc alpha beta ⊆ Ioo 1 T)
    {K : Set E} (hK : IsCompact K) (hchart : K ⊆ (extChartAt I a).target)
    (v : ℝ × E → ℝ) (hv : ContinuousOn v (Icc alpha beta ×ˢ K))
    (hv2 : ∀ z ∈ Ioo alpha beta ×ˢ interior K, ContDiffAt ℝ 2 v z)
    (hsuper : ∀ z ∈ Ioo alpha beta ×ˢ interior K,
      0 ≤ fderiv ℝ v z (1, 0) -
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (L.S.base.metric (1 - z.1)) a i j z.2 *
            (fderiv ℝ (fderiv ℝ v) z (0, chartModelBasis E i) (0, chartModelBasis E j) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) (L.S.base.metric (1 - z.1)) a i j k z.2 *
                  fderiv ℝ v z (0, chartModelBasis E k))) +
        metricScalarAt (L.S.base.metric (1 - z.1)) ((extChartAt I a).symm z.2) * v z) :
    let u := fun w : ℝ × E => perelmanDensity (Module.finrank ℝ E) w.1
      (fun x => ell (x, projIcc 1 T hT.le w.1)) ((extChartAt I a).symm w.2)
    (∀ x ∈ K, u (alpha, x) ≤ v (alpha, x)) →
    (∀ t ∈ Icc alpha beta, ∀ x ∈ K \ interior K, u (t, x) ≤ v (t, x)) →
    ∀ z ∈ Icc alpha beta ×ˢ K, u z ≤ v z := by
  apply perelmanDensity_comparison_of_rescaled_reducedLength_limit_in_chart
    F hF p (fun n => tau (subseq n)) (fun n => htau (subseq n)) L Phi.partialDiffeomorph
    R G _ hmetric hT ell hell a hwindow hK hchart v hv hv2 hsuper
  intro K hK
  filter_upwards [hG K hK] with n hn
  obtain ⟨U, hU, hKU, hsource, hinner⟩ := hn
  refine ⟨U, hU, hKU, hsource, ?_⟩
  intro t x hx v w
  let e : PartialDiffeomorph I I L.M F.M ∞ := Phi.partialDiffeomorph n
  have hh := hinner t x hx v w
  rw [backwardFlowSequence_metric] at hh
  change (G n t).inner x v w =
    (scaleMetric (tau (subseq n))⁻¹ (inv_pos.mpr (htau (subseq n)))
      (F.S.base.metric (tau (subseq n) * (t - 1)))).inner (e x)
        (mfderiv I I e x v) (mfderiv I I e x w) at hh
  rw [scaleMetric_inner] at hh
  exact hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
