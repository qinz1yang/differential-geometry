import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalReducedVolumeMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointCompactLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointTerminalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalCenterPoleRescalings
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointMassLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointMetricNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticReducedVolumeStrictBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.GaussianShrinkerMass
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedCurvatureOperator
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.ModelChange
import DifferentialGeometry.Topology.Manifold.ModelChangeRoundtrip
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerNormalizationModelChange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPullback
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Operations
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import DifferentialGeometry.Geometry.Curvature.ModelChange
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.ModelChange

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

attribute [local instance] normalizedSourceTopology normalizedSourceCharted
  normalizedSourceSmooth normalizedSourceT2 normalizedSourceSigma



omit [I.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
theorem ancient_reducedVolume_antitone_of_redVolume_antitone
    (hgap : ∀ (D : RealTimeInterval)
      (S : SolutionOn (I := I) (M := F.M) D)
      (T : ℝ) (x : F.M) {tau1 tau2 : ℝ},
      IsSolutionOn (I := I) S →
      0 < tau1 → tau1 ≤ tau2 → T ∈ D.carrier →
      Set.Ico (T - tau2) T ⊆ D.regular →
      redVolume S T x tau2 ≤ redVolume S T x tau1)
    (p : F.M) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Ioi 0) := by
  intro tau1 h1 tau2 h2 h12
  exact hgap ancientTimeInterval F.S 0 p F.isSolution h1 h12 (by simp)
    (fun t ht => ht.2)

section IcoSlab

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [I.Boundaryless] in
def redVolumeIcoSlabAntitone {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop :=
  ∀ (T : ℝ) (x : M) {tau1 tau2 : ℝ},
    IsSolutionOn (I := I) S →
    0 < tau1 → tau1 ≤ tau2 → T ∈ D.carrier →
    Set.Ico (T - tau2) T ⊆ D.regular →
    redVolume S T x tau2 ≤ redVolume S T x tau1

end IcoSlab

omit [I.Boundaryless] in
theorem ancient_reducedVolume_antitone_of_icoSlabAntitone
    (h : ∀ (D : RealTimeInterval) (S : SolutionOn (I := I) (M := F.M) D),
      redVolumeIcoSlabAntitone (I := I) (D := D) S)
    (p : F.M) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Ioi 0) :=
  ancient_reducedVolume_antitone_of_redVolume_antitone F
    (fun D S T x => h D S T x) p

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

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
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem exists_samePole_normalized_asymptotic_shrinker_inner
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : 2 ≤ Module.finrank ℝ E) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      (∀ i, lCost F.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
        (Module.finrank ℝ E : ℝ) / 2) ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I)
          (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k) ∧
        MetricComplete (I := I) L ∧
        (ConnectedSpace L.M ∧
         (∃ x : L.M, metricScalarAt L.metric x ≠ 0) ∧
         (∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
           0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j)) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯,
           gradientRicciSoliton L.metric f 1 ∧
           IsHamiltonNormalizedPotential L.metric f ∧
           Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau (phi i)))
             atTop (𝓝 (normalizedShrinkerMass L.metric f))) := by
  classical
  obtain ⟨q, hq, b, hb, hbmem, N, hsigma, Cbase, _, heta, _, htauTop,
      _, hbound, _, hancient, _⟩ :=
    exists_poleRescaledFlowSeq_tail_with_terminal_redLength_bound F hF p tau htau hescape
  let tauN : ℕ → ℝ := fun i => tau (i + N)
  let qN : ℕ → F.M := fun i => q (i + N)
  let U := poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem tauN qN hsigma
  let Y := poleEndpointRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem tauN qN hsigma
  have hbase : ∀ i, redLength (U.term i).S 0 p (qN i) 1 ≤ Cbase := by
    intro i
    rw [poleRescaledFlowSeq_redLength_one F hF.carrier_eq hF.regular_eq
      b hbmem tauN qN hsigma]
    exact hbound i
  obtain ⟨P, phi, hphi, Phi, R, _, hR, bf, hsrc, htgt, co, hconn, hcomplete⟩ :=
    exists_complete_halfLineMetricConvergenceData_of_poleEndpoint_redLength_bound
      F hF p b hbmem tauN qN hsigma hancient hbase
  let _ : ConnectedSpace P.M := hconn
  have hcomplete0 := hcomplete 0 le_rfl
  have hboundary : BoundarylessManifold I P.M := inferInstance
  obtain ⟨psi, ellC, _, _, hf, hsol, hham, hpotential, hmass⟩ :=
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
  have hrho : StrictMono rho := heta.comp (hphi.comp co.strictMono)
  have hmass0 : normalizedShrinkerMass (co.gInf 0) f =
      asymptoticReducedVolume F.S 0 p :=
    hmass.trans (asymptoticReducedVolume_eq_terminal_of_negative F hdim hF hb p)
  have hmassconv : Tendsto (fun k => intrinsicReducedVolume F.S 0 p (tau (rho k)))
      atTop (𝓝 (normalizedShrinkerMass (co.gInf 0) f)) := by
    rw [hmass0]
    simpa only [mul_one] using intrinsicReducedVolume_tendsto_mul_atTop_of_antitone
      F.S 0 p (ancient_reducedVolume_antitone F hF p)
      (fun k => htau (rho k)) (hescape.comp hrho.tendsto_atTop) (a := 1) zero_lt_one
  obtain ⟨Czero, hCzero, _⟩ := co.exists_canonicalMetricConvergenceData Phi (t := 0) le_rfl
  have hcone := curvatureOperator_nonnegative_of_canonical_metricCGConvergence Czero hCzero
    (fun K _ => Eventually.of_forall fun k y _ _ => by
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (I := I) ((Y.term (phi (co.φ k))).S.base.metric 0) _).mpr
      intro n c v w
      change 0 ≤ ∑ i, ∑ j, c i * c j *
        (Y.term (phi (co.φ k))).S.base.rm04 0 _ (vec4 (v i) (w i) (w j) (v j))
      exact poleEndpointRescaledFlowSeq_nonnegativeCurvatureOperator
        F hF.carrier_eq hF.regular_eq b hbmem tauN qN hsigma
        hF.nonnegativeCurvatureOperator (phi (co.φ k)) le_rfl _ n c v w)
  refine ⟨q, Q, rho, hrho, hq, PsiOriginal, COriginal, hCOriginal,
    hcomplete0, hconn, ⟨P.basepoint, (hscalar P.basepoint).ne'⟩, ?_, f, hsol,
    hpotential, hmassconv⟩
  intro x n c v w
  exact (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
    (I := I) (co.gInf 0) x).mp (hcone x) n c v w

end Inner

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

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

section Normed

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

attribute [local instance] normalizedSourceTopology normalizedSourceCharted
  normalizedSourceSmooth normalizedSourceT2 normalizedSourceSigma

theorem exists_samePole_normalized_asymptotic_shrinker
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : 2 ≤ Module.finrank ℝ E) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      (∀ i, lCost F.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
        (Module.finrank ℝ E : ℝ) / 2) ∧
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
           gradientRicciSoliton L.metric f 1 ∧
           IsHamiltonNormalizedPotential L.metric f ∧
           Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau (phi i)))
             atTop (𝓝 (normalizedShrinkerMass L.metric f))) := by
  classical
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let J := I.transContinuousLinearEquiv e
  let a : F.M ≃ₘ⟮I, J⟯ F.M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I F.M e
  let G := F.pullback a.symm
  have hG : IsAncientKappaSolution kappa G := F.pullback_isAncientKappaSolution a.symm hF
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :=
    ⟨by simpa using (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hdim))⟩
  obtain ⟨q, P, phi, hphi, hq, Psi, C, hC, hcomplete,
      hconn, hnonflat, hcone, f, hsol, hpotential, hmassconv⟩ :=
    exists_samePole_normalized_asymptotic_shrinker_inner G hG
      (by simpa only [finrank_euclideanSpace, Fintype.card_fin] using hdim) p tau htau hescape
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
  have hqF (i : ℕ) : lCost F.S 0 p (qF i) (tau i) / (2 * Real.sqrt (tau i)) ≤
      (Module.finrank ℝ E : ℝ) / 2 := by
    have hh := hq i
    have hcost : lCost G.S 0 p (q i) (tau i) = lCost F.S 0 p (qF i) (tau i) :=
      lCost_pullback_cross F.S a.symm 0 p (q i) (tau i)
    rw [hcost] at hh
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using hh
  have hpotentialI : IsHamiltonNormalizedPotential Q.metric fI := by
    apply (isHamiltonNormalizedPotential_transContinuousLinearEquiv_iff Q.metric e fI).mp
    rw [hmetric]
    exact hpotential
  have hmassI : normalizedShrinkerMass Q.metric fI = normalizedShrinkerMass P.metric f := by
    rw [← normalizedShrinkerMass_transContinuousLinearEquiv Q.metric e fI, hmetric]
    rfl
  have hvolume (t : ℝ) : intrinsicReducedVolume G.S 0 p t =
      intrinsicReducedVolume F.S 0 p t := by
    change redVolume (F.S.pullback a.symm) 0 p t = redVolume F.S 0 p t
    exact redVolume_transContinuousLinearEquiv F.S e 0 p t
  have hmassconvI : Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau (phi i)))
      atTop (𝓝 (normalizedShrinkerMass Q.metric fI)) := by
    rw [hmassI]
    simpa only [hvolume] using hmassconv
  have hconeI (x : Q.M) (n : ℕ) (c : Fin n → ℝ)
      (v w : Fin n → TangentSpace I x) :
      0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt Q.metric x
        (v i) (w i) (w j) (v j) := by
    have hh := hcone (aP x) n c
      (fun i => mfderiv I J aP x (v i)) (fun i => mfderiv I J aP x (w i))
    simpa only [Q, metricRm04Standard_pullbackCross] using hh
  refine ⟨qF, Q, phi, hphi, hqF, PsiI, CI, hCI, hQcomplete,
    hconn, ?_, hconeI, fI, hsolI, hpotentialI, hmassconvI⟩
  obtain ⟨x, hx⟩ := hnonflat
  exact ⟨x, by rw [hscalar]; exact hx⟩

end Normed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
