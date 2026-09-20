import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointCompactLimit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.ModelChange
import DifferentialGeometry.Topology.Manifold.ModelChangeRoundtrip
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPullback
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Operations
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import DifferentialGeometry.Geometry.Curvature.ModelChange
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointTerminalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointMetricNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticReducedVolumeStrictBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.GaussianShrinkerMass
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

section Inner

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem exists_backward_slice_asymptotic_shrinker_inner
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I)
          (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) ∧
        (∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric) ∧
        MetricComplete (I := I) L ∧
        (ConnectedSpace L.M ∧
         (∃ x : L.M, metricScalarAt (I := I) L.metric x ≠ 0) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯, gradientRicciSoliton (I := I) L.metric f 1) := by
  classical
  let p : F.M := F.basepoint
  obtain ⟨b, hb, hbmem, q, N, hsigma, heta, _, htauTop, _, hbound, hancient, _⟩ :=
    exists_poleRescaledFlowSeq_tail_of_ancient F hF p tau hescape
  let tauN : ℕ → ℝ := fun i => tau (i + N)
  let qN : ℕ → F.M := fun i => q (i + N)
  let U := poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem tauN qN hsigma
  have hbase : ∀ i, redLength (U.term i).S 0 p (qN i) 1 ≤
      (Module.finrank ℝ E : ℝ) / 2 := by
    intro i
    have hscale := redLength_parabolic F.S b (tauN i + b)⁻¹ b (tauN i + b)
      (inv_pos.mpr (hsigma i)) hbmem (hsigma i).le p (qN i)
    have heq : redLength (U.term i).S 0 p (qN i) 1 =
        redLength F.S b p (qN i) (tauN i + b) := by
      change redLength (parabolicSolution F.S b (tauN i + b)⁻¹
        (inv_pos.mpr (hsigma i)) hbmem) 0 p (qN i) 1 = _
      simpa only [parabolicBackward, sub_self, mul_zero,
        inv_mul_cancel₀ (show tauN i + b ≠ 0 from (hsigma i).ne')] using hscale
    rw [heq]
    exact hbound i
  obtain ⟨P, phi, hphi, Phi, R, _, hR, bf, hsrc, htgt, co, hconn, hcomplete⟩ :=
    exists_complete_halfLineMetricConvergenceData_of_poleEndpoint_redLength_bound
      F hF p b hbmem tauN qN hsigma hancient hbase
  let _ : ConnectedSpace P.M := hconn
  have hcomplete0 := hcomplete 0 le_rfl
  have hboundary : BoundarylessManifold I P.M := inferInstance
  obtain ⟨_, ellC, _, _, hf, hsol, hham, _, hmass⟩ :=
    HalfLineMetricConvergenceData.exists_poleEndpoint_terminal_normalized_soliton_of_ancient
      F hF.carrier_eq hF.regular_eq b hbmem tauN qN hsigma Phi R hR bf hsrc htgt co
        hcomplete0 hboundary (fun _ => kappa) hancient hb hF p hbase htauTop hphi
  let f : C^∞⟮I, P.M; ℝ⟯ :=
    ⟨fun x => ellC (x, (⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩ : Ici (1 : ℝ))), hf⟩
  have hnormalized : normalizedGradientRicciSoliton (co.gInf 0) f := by
    refine ⟨⟨hcomplete0⟩, hsol, ?_⟩
    intro x
    simpa only [hamiltonNormalized, normGradSqFun_def, one_mul] using hham x
  have hmasslt : normalizedShrinkerMass (co.gInf 0) f < 1 := by
    rw [hmass]
    exact asymptoticReducedVolume_lt_one_of_ancient F hF p hb
  have hscalar := normalizedGradientRicciSoliton_scalar_pos_of_mass_lt_one hnormalized hmasslt
  obtain ⟨Psi, _, C, hC, href⟩ :=
    exists_backwardSlice_canonical_metric_convergence_of_poleEndpoint
      F hF.carrier_eq hF.regular_eq b hbmem tauN (fun i => htau (i + N)) qN hsigma
        Phi R bf hsrc htgt co hphi htauTop
  let Q : PointedRiemannianManifold.{u, uE, uH} (I := I) := { P with metric := co.gInf 0 }
  let rho : ℕ → ℕ := fun k => phi (co.φ k) + N
  let PsiOriginal : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) Q rho :=
    { partialDiffeomorph := Psi.partialDiffeomorph
      source_exhausts := Psi.source_exhausts
      base_mem := Psi.base_mem
      basepoint_map := Psi.basepoint_map }
  obtain ⟨COriginal, hCOriginal, hrefOriginal⟩ :=
    exists_metricConvergenceData_canonicalSourceData (I := I) PsiOriginal (by
      intro K hK p epsilon hepsilon
      obtain ⟨k0, hk0⟩ := C.converges K hK p epsilon hepsilon
      refine ⟨k0, fun k hk => ?_⟩
      have hbound := (hk0 k hk).2
      rw [hC k] at hbound
      exact hbound)
  refine ⟨q, Q, rho, heta.comp (hphi.comp co.strictMono), PsiOriginal, COriginal,
    ?_, ?_, hcomplete0, hconn, ⟨P.basepoint, (hscalar P.basepoint).ne'⟩, f, hsol⟩
  · intro k
    exact hCOriginal k
  · intro k
    exact hrefOriginal k

end Inner

section Normed

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [hE : NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_backward_slice_asymptotic_shrinker
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) ∧
        (∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric) ∧
        MetricComplete (I := I) L ∧
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace H L.M := L.charted
         let _ : IsManifold I ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         ConnectedSpace L.M ∧
         (∃ x : L.M, metricScalarAt (I := I) L.metric x ≠ 0) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯, gradientRicciSoliton (I := I) L.metric f 1) := by
  classical
  let _ := hE
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let J := I.transContinuousLinearEquiv e
  let a : F.M ≃ₘ⟮I, J⟯ F.M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I F.M e
  let G := F.pullback a.symm
  have hG : IsAncientKappaSolution kappa G := F.pullback_isAncientKappaSolution a.symm hF
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :=
    ⟨by simpa using (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hdim))⟩
  obtain ⟨q, P, phi, hphi, Psi, C, hC, _, hcomplete, hconn, hnonflat, f, hsol⟩ :=
    exists_backward_slice_asymptotic_shrinker_inner G hG tau htau hescape
  let _ : IsManifold I ∞ P.M := e.isManifold_transContinuousLinearEquiv_iff.mp P.smooth
  let aP : P.M ≃ₘ⟮I, J⟯ P.M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I P.M e
  let Q : PointedRiemannianManifold.{u, uE, uH} (I := I) :=
    { M := P.M
      topology := P.topology
      charted := P.charted
      smooth := inferInstance
      sigmaCompact := P.sigmaCompact
      t2 := P.t2
      t2TangentBundle := inferInstance
      basepoint := P.basepoint
      metric := Diffeomorph.pullbackMetricCross P.metric aP }
  let qF : ℕ → F.M := q
  let X := backwardSliceSequence F tau htau qF
  let PsiI : PointedRiemannianConvergenceMaps (I := I) X Q phi :=
    { partialDiffeomorph k :=
        { toPartialEquiv := (Psi.partialDiffeomorph k).toPartialEquiv
          open_source := (Psi.partialDiffeomorph k).open_source
          open_target := (Psi.partialDiffeomorph k).open_target
          contMDiffOn_toFun :=
            e.contMDiffOn_transContinuousLinearEquiv_left.mp
              (e.contMDiffOn_transContinuousLinearEquiv_right.mp
                (Psi.partialDiffeomorph k).contMDiffOn_toFun)
          contMDiffOn_invFun :=
            e.contMDiffOn_transContinuousLinearEquiv_left.mp
              (e.contMDiffOn_transContinuousLinearEquiv_right.mp
                (Psi.partialDiffeomorph k).contMDiffOn_invFun) }
      source_exhausts := Psi.source_exhausts
      base_mem := Psi.base_mem
      basepoint_map := Psi.basepoint_map }
  have hmetric : Q.metric.transContinuousLinearEquiv e = P.metric := by
    change Diffeomorph.pullbackMetricCross
      (Diffeomorph.pullbackMetricCross P.metric aP) aP.symm = P.metric
    rw [Diffeomorph.pullbackMetricCross_trans]
    have heq : aP.symm.trans aP = Diffeomorph.refl J P.M ∞ := by ext x; rfl
    rw [heq, Diffeomorph.pullbackMetricCross_refl]
  have hsource (i : ℕ) :
      (X.obj i).metric.transContinuousLinearEquiv e =
        ((backwardSliceSequence G tau htau q).obj i).metric := by
    change Diffeomorph.pullbackMetricCross
      (scaleMetric (tau i)⁻¹ (inv_pos.mpr (htau i)) (F.S.base.metric (-tau i))) a.symm = _
    exact Diffeomorph.pullbackMetricCross_scaleMetric _ _ _ _
  have hderiv (k : ℕ) (K : Set P.M) (n : ℕ) :
      (CanonicalMetricCompactness.canonicalSourceData PsiI k).derivNormSupOn K n =
        (CanonicalMetricCompactness.canonicalSourceData Psi k).derivNormSupOn K n := by
    rw [← canonicalSourceData_derivNormSupOn_transContinuousLinearEquiv PsiI e k K n]
    let U : TopologicalSpace.Opens P.M := metricSourceOpenSubset Psi k
    let V : TopologicalSpace.Opens F.M := metricTargetOpenSubset Psi k
    let dI : U ≃ₘ⟮J, J⟯ V :=
      metricSourceTargetDiffeomorph (PsiI.transContinuousLinearEquiv e) k
    let dJ : U ≃ₘ⟮J, J⟯ V := metricSourceTargetDiffeomorph Psi k
    have hd : dI = dJ := by
      ext x
      rfl
    change metricDerivNormSupOn (I := J) (Subtype.val ⁻¹' K : Set U) n
        (Diffeomorph.pullbackMetric
          (((X.obj (phi k)).metric.transContinuousLinearEquiv e).restrictOpen V) dI)
        ((Q.metric.transContinuousLinearEquiv e).restrictOpen U)
        ((Q.metric.transContinuousLinearEquiv e).restrictOpen U) =
      metricDerivNormSupOn (I := J) (Subtype.val ⁻¹' K : Set U) n
        (Diffeomorph.pullbackMetric
          (((backwardSliceSequence G tau htau q).obj (phi k)).metric.restrictOpen V) dJ)
        (P.metric.restrictOpen U) (P.metric.restrictOpen U)
    rw [hsource (phi k), hmetric, hd]
    rfl
  obtain ⟨CI, hCI, hrefI⟩ := exists_metricConvergenceData_canonicalSourceData PsiI (by
    intro K hK n epsilon hepsilon
    obtain ⟨k0, hk0⟩ := C.converges K hK n epsilon hepsilon
    refine ⟨k0, fun k hk => ?_⟩
    rw [hderiv]
    have hh := (hk0 k hk).2
    rwa [hC k] at hh)
  have hQcomplete : MetricComplete Q :=
    (RiemannianMetricComplete.pullbackCross P.metric aP ⟨hcomplete⟩).complete
  let fI : C^∞⟮I, Q.M; ℝ⟯ := f.comp aP.toContMDiffMap
  have hsolI : gradientRicciSoliton Q.metric fI 1 := gradientRicciSoliton_pullbackCross hsol aP
  have hscalar (x : P.M) : metricScalarAt Q.metric x = metricScalarAt P.metric x := by
    have hh := metricScalarAt_transContinuousLinearEquiv Q.metric e x
    rw [hmetric] at hh
    exact hh.symm
  refine ⟨qF, Q, phi, hphi, PsiI, CI, hCI, hrefI, hQcomplete, hconn, ?_, fI, hsolI⟩
  obtain ⟨x, hx⟩ := hnonflat
  exact ⟨x, by rw [hscalar]; exact hx⟩

end Normed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
