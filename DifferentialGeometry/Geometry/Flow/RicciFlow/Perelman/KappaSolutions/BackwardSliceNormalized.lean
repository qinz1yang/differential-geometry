import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowNormalized
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MetricJetScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedCurvatureOperator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalPoleCenters
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange

noncomputable section
open Set Filter
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology
universe u uH
variable {n : ℕ} {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H} [I.Boundaryless]
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_backward_slice_normalized_shrinker_of_reducedLength_bound
    (F : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = 3)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (hescape : Tendsto tau atTop atTop) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A) :
    ∃ (P : PointedRiemannianManifold.{u, 0, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Psi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P phi)
        (C : MetricConvergenceData Psi),
        (∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Psi i) ∧
        (∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric) ∧
        MetricComplete P ∧ ConnectedSpace P.M ∧
        (∀ x : P.M, 0 < metricScalarAt P.metric x) ∧
        (∀ x : P.M, metricAlgebraicCurvatureTensorAt P.metric x ∈
          algebraicCurvatureOperatorNonnegativeCone) ∧
        ∃ f : C^∞⟮I, P.M; ℝ⟯,
          Geometry.normalizedGradientRicciSoliton P.metric f ∧
          normalizedShrinkerMass P.metric f = asymptoticReducedVolume F.S 0 p ∧
          ∀ K : Set P.M, IsCompact K → TendstoUniformlyOn
            (fun i x => redLength F.S 0 p (Psi.map i x) (tau (phi i))) f atTop K := by
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := ⟨by omega⟩
  let sigma := fun i => tau i / 2
  have hsigma (i : ℕ) : 0 < sigma i := half_pos (htau i)
  have hsbase (i : ℕ) : redLength F.S 0 p (q i) (sigma i) ≤
      2 * (1 + Real.sqrt 3) ^ 2 * A := by
    have h := redLength_le_of_backward_time_le F hF p (q i)
      (s := tau i / 2) (hsigma i) (by linarith [htau i]) (hbase i)
    have heq : tau i / (tau i / 2) = 2 := by field_simp [(htau i).ne']
    simpa only [sigma, heq, mul_comm ((1 + Real.sqrt 3) ^ 2) 2] using h
  have hses : Tendsto sigma atTop atTop := hescape.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  obtain ⟨L, phi, hphi, Phi, hconn, hcomp, hconv, R, G, hG, hmetric,
    ell, _hnonneg, _hellbase, hLip, hell⟩ :=
    exists_backward_flow_reducedLength_limit_with_uniform_metric_convergence
      F hF p sigma hsigma q hsbase (T := 3) (by norm_num)
  let _ : ConnectedSpace L.M := hconn
  have hconv' (t : ℝ) (ht : t ∈ Icc (1 - 3) (0 : ℝ)) :=
    (hconv t ht.2).imp (fun C hC => hC.1)
  have hcomp' (t : ℝ) (ht : t ∈ Icc (1 - 3) (0 : ℝ)) := hcomp t ht.2
  have hsescape := hses.comp hphi.tendsto_atTop
  obtain ⟨hf, hsol, hmass⟩ := backward_flow_reducedLength_limit_normalized_shrinker_and_mass
    F hF p sigma hsigma q L Phi R G hG hmetric (by norm_num : (1 : ℝ) < 3)
    ell hell hLip hdim hsescape hconv' hcomp' (t := 2) (by norm_num)
  have hpos := backward_flow_reducedLength_limit_scalar_pos
    F hF p sigma hsigma q L Phi R G hG hmetric (by norm_num : (1 : ℝ) < 3)
    ell hell hLip hdim hsescape hconv' hcomp' (t := 2) (by norm_num)
  let P : PointedRiemannianManifold.{u, 0, uH} (I := I) :=
    { L.atTime (-1) with metric := scaleMetric (2 : ℝ)⁻¹ (by norm_num) (L.S.base.metric (-1)) }
  let Psi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P phi := {
    partialDiffeomorph := Phi.partialDiffeomorph
    source_exhausts := Phi.source_exhausts
    base_mem := Phi.base_mem
    basepoint_map := Phi.basepoint_map }
  have hmetric' : MetricCInfConvergenceOnCompacts (fun i => G i (-1))
      (L.S.base.metric (-1)) R := by
    intro K hK r epsilon hepsilon
    obtain ⟨N, hN⟩ := hmetric (-1) (-1) (fun _ ht => ht.2.trans (by norm_num)) K hK r epsilon hepsilon
    exact ⟨N, fun i hi => hN i hi (-1) ⟨le_rfl, le_rfl⟩⟩
  let GS := fun i => scaleMetric (2 : ℝ)⁻¹ (by norm_num) (G i (-1))
  have hscaled : MetricCInfConvergenceOnCompacts GS P.metric P.metric :=
    (metricCInfConvOnCompacts_scale_all (2 : ℝ)⁻¹ (by norm_num)
      (fun i => G i (-1)) (L.S.base.metric (-1)) R hmetric').change_reference P.metric
  have hscaledG : ∀ K : Set P.M, IsCompact K → ∀ᶠ i in atTop,
      ∃ U : Set P.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Psi.source i ∧
        ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (GS i).inner x v w = ((backwardSliceSequence F tau htau q).obj (phi i)).metric.inner
            (Psi.map i x) (mfderiv I I (Psi.map i) x v) (mfderiv I I (Psi.map i) x w) := by
    intro K hK
    filter_upwards [hG K hK] with i hi
    obtain ⟨U, hU, hKU, hUsrc, hGi⟩ := hi
    refine ⟨U, hU, hKU, hUsrc, ?_⟩
    intro x hx v w
    change (2 : ℝ)⁻¹ * (G i (-1)).inner x v w = _
    rw [hGi (-1) x hx v w, backwardFlowSequence_metric]
    have htime : sigma (phi i) * ((-1 : ℝ) - 1) = -tau (phi i) := by dsimp [sigma]; ring
    rw [htime]
    change (2 : ℝ)⁻¹ * ((sigma (phi i))⁻¹ *
      (F.S.base.metric (-tau (phi i))).inner (Phi.map i x)
        (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w)) =
      (tau (phi i))⁻¹ * (F.S.base.metric (-tau (phi i))).inner (Phi.map i x)
        (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w)
    dsimp only [sigma]
    field_simp
  obtain ⟨C, hcanonical, href⟩ :=
    exists_canonicalMetricConvergenceData_of_metric_extension Psi GS hscaled hscaledG
  have hcone : ∀ x : P.M, metricAlgebraicCurvatureTensorAt P.metric x ∈
      algebraicCurvatureOperatorNonnegativeCone := by
    apply curvatureOperator_nonnegative_of_canonical_metricCGConvergence C hcanonical
    intro K _hK
    filter_upwards [] with i
    intro y _hy _hysrc
    change metricAlgebraicCurvatureTensorAt
      (scaleMetric (tau (phi i))⁻¹ (inv_pos.mpr (htau _))
        (F.S.base.metric (-tau (phi i)))) (Psi.map i y) ∈ _
    rw [metricAlgebraicCurvatureTensorAt_scaleMetric]
    apply algebraicCurvatureOperatorNonnegativeCone.smul_mem ?_ (inv_pos.mpr (htau _)).le
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff _ _).mpr
    intro m c v w
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator (-tau (phi i)) (neg_nonpos.mpr (htau _).le)
        (Psi.map i y) m c v w
  have hcomplete : MetricComplete P := by
    have hc : RiemannianMetricComplete (L.S.base.metric (-1)) := ⟨hcomp (-1) (by norm_num)⟩
    exact (hc.of_lower (by norm_num : (0 : ℝ) < 2⁻¹) (fun _ _ => le_rfl)).complete
  refine ⟨P, phi, hphi, Psi, C, hcanonical, href, hcomplete, hconn, ?_, hcone,
    ⟨fun x => ell (x, projIcc 1 3 (by norm_num) 2), hf⟩, ?_, ?_, ?_⟩
  · intro x
    change L.M at x
    change 0 < metricScalarAt (scaleMetric (2 : ℝ)⁻¹ (by norm_num) (L.S.base.metric (-1))) x
    rw [metricScalarAt_scaleMetric, inv_inv]
    exact mul_pos (by norm_num) (by simpa only [show (1 : ℝ) - 2 = -1 by norm_num] using hpos x)
  · change Geometry.normalizedGradientRicciSoliton
      (scaleMetric (2 : ℝ)⁻¹ (by norm_num) (L.S.base.metric (-1)))
      ⟨fun x => ell (x, projIcc 1 3 (by norm_num) 2), hf⟩
    convert hsol using 1
    norm_num
  · change normalizedShrinkerMass
      (scaleMetric (2 : ℝ)⁻¹ (by norm_num) (L.S.base.metric (-1)))
      (fun x => ell (x, projIcc 1 3 (by norm_num) 2)) = _
    convert hmass using 1
    norm_num
  · intro K hK
    let theta : Icc (1 : ℝ) 3 := ⟨2, by norm_num, by norm_num⟩
    have hc : Continuous (fun x : P.M => (x, theta)) := continuous_id.prodMk continuous_const
    have h := (hell ((fun x : P.M => (x, theta)) '' K) (hK.image hc)).comp (fun x : P.M => (x, theta))
    have h' := h.mono (show K ⊆ (fun x : P.M => (x, theta)) ⁻¹'
      ((fun x : P.M => (x, theta)) '' K) from fun x hx => mem_image_of_mem _ hx)
    have hscale (i : ℕ) : sigma (phi i) * (theta : ℝ) = tau (phi i) := by dsimp [sigma, theta]; ring
    change TendstoUniformlyOn
      (fun i x => redLength F.S 0 p (Phi.map i x) (tau (phi i)))
      (fun x => ell (x, projIcc 1 3 (by norm_num) 2)) atTop K
    rw [projIcc_of_mem (by norm_num : (1 : ℝ) ≤ 3) (show (2 : ℝ) ∈ Icc 1 3 by norm_num)]
    dsimp only [P, PointedFlowData.atTime] at h' ⊢
    simpa only [Function.comp_def, hscale, theta] using h'


theorem exists_samePole_normalized_asymptotic_shrinker_of_finrank_eq_three
    (F : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = 3) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, 0, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      (∀ i, lCost F.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) / 2) ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k) ∧
        MetricComplete (I := I) L ∧
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace H L.M := L.charted
         let _ : IsManifold I ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         let _ : SigmaCompactSpace L.M := L.sigmaCompact
         ConnectedSpace L.M ∧
         (∃ x : L.M, metricScalarAt L.metric x ≠ 0) ∧
         (∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
           0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j)) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯,
           Geometry.gradientRicciSoliton L.metric f 1 ∧
           IsHamiltonNormalizedPotential L.metric f ∧
           Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau (phi i)))
             atTop (𝓝 (normalizedShrinkerMass L.metric f))) := by
  classical
  choose q hq using fun i => exists_redLength_le_half_finrank_of_ancient F hF p (htau i)
  obtain ⟨L, phi, hphi, Phi, C, hcanonical, _href, hcomplete, hconnected,
    hpos, hcone, f, hsol, hmass, _hpotential⟩ :=
    exists_backward_slice_normalized_shrinker_of_reducedLength_bound
      F hF hdim p tau htau hescape q hq
  refine ⟨q, L, phi, hphi, hq, Phi, C, hcanonical, hcomplete, hconnected,
    ⟨L.basepoint, (hpos L.basepoint).ne'⟩, ?_, f, hsol.2.1, ?_, ?_⟩
  · intro x m c v w
    exact (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      L.metric x).mp (hcone x) m c v w
  · exact Geometry.normalizedGradientRicciSoliton_potential_equation hsol
  · rw [hmass]
    exact (ancient_reducedVolume_tendsto_atTop F hF p).comp (hescape.comp hphi.tendsto_atTop)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
