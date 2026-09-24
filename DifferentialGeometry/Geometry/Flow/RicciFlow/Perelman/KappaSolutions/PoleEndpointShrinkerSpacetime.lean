import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointParabolicComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointCompactLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointTerminalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointMetricNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticReducedVolumeStrictBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.GaussianShrinkerMass

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_poleEndpoint_shrinker_limit
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop) :
    ∃ (b : ℝ) (_ : b < 0) (hbmem : b ∈ ancientTimeInterval.carrier)
      (q : ℕ → F.M) (N : ℕ) (hsigma : ∀ i, 0 < tau (i + N) + b)
      (P : PointedRiemannianManifold.{u, 0, 0} I3) (phi : ℕ → ℕ)
      (Phi : PointedCGHMaps
        (poleEndpointRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem
          (fun i => tau (i + N)) (fun i => q (i + N)) hsigma) P phi)
      (R : SmoothRiemannianMetric I3 P.M) (bf : BumpFamily Phi)
      (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
      (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt),
      StrictMono phi ∧ R = P.metric ∧ RiemannianMetricComplete R ∧ ConnectedSpace P.M ∧
      (∀ s : ℝ, s ≤ 0 →
        MetricComplete ({ P with metric := co.gInf s } : PointedRiemannianManifold I3)) ∧
      IsSolutionOn ({ base := { metric := co.gInf } } :
        SolutionOn (I := I3) (M := P.M) ancientTimeInterval) ∧
      (∃ f : C^∞⟮I3, P.M; ℝ⟯, gradientRicciSoliton (co.gInf 0) f 1 ∧
        IsHamiltonNormalizedPotential (co.gInf 0) f ∧
        normalizedShrinkerMass (co.gInf 0) f = asymptoticReducedVolume F.S b p ∧
        normalizedShrinkerMass (co.gInf 0) f < 1) ∧
      (∀ y : P.M, 0 < metricScalarAt (co.gInf 0) y) ∧
      (∀ a c : ℝ, a ≤ c → c ≤ 0 → ∀ K : Set P.M, IsCompact K →
        ∀ order : ℕ, ∀ eps : ℝ, 0 < eps → ∀ᶠ i in atTop,
          Nonempty (MetricComparisonOn co.gInf
            (fun s => scaleMetric (tau (phi (co.φ i) + N) + b)⁻¹
              (inv_pos.mpr (hsigma (phi (co.φ i))))
              (F.S.base.metric (-tau (phi (co.φ i) + N) +
                (tau (phi (co.φ i) + N) + b) * s)))
            (Phi.map (co.φ i)) K (Icc a c) order eps)) ∧
      (∀ K : Set P.M, IsCompact K → ∀ order : ℕ, ∀ eps : ℝ, 0 < eps → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn (fun theta => co.gInf (1 - theta))
          (backwardScaledMetric F.S (tau (phi (co.φ i) + N)) (htau (phi (co.φ i) + N)))
          (Phi.map (co.φ i)) K (Icc (1 : ℝ) 3) order eps)) ∧
      ∃ Psi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q)
          ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I3)
          (fun i => phi (co.φ i) + N),
        (∀ i, Psi.partialDiffeomorph i = Phi.partialDiffeomorph (co.φ i)) ∧
        ∃ C : MetricConvergenceData Psi,
          (∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Psi i) ∧
          (∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric) := by
  classical
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨b, hb, hbmem, q, N, hsigma, _heta, _htop, htauTop, _hsigmaTop,
      hbound, hancient, _hmetric⟩ := exists_poleRescaledFlowSeq_tail_of_ancient F hF p tau hescape
  let tauN : ℕ → ℝ := fun i => tau (i + N)
  let qN : ℕ → F.M := fun i => q (i + N)
  let U := poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem tauN qN hsigma
  have hbase : ∀ i, redLength (U.term i).S 0 p (qN i) 1 ≤
      (Module.finrank ℝ ThreeSpace : ℝ) / 2 := by
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
  obtain ⟨P, phi, hphi, Phi, R, hRP, hR, bf, hsrc, htgt, co, hconn, hcomplete⟩ :=
    exists_complete_halfLineMetricConvergenceData_of_poleEndpoint_redLength_bound
      F hF p b hbmem tauN qN hsigma hancient hbase
  let _ : ConnectedSpace P.M := hconn
  have hcomplete0 := hcomplete 0 le_rfl
  obtain ⟨_psi, ellC, _hpsi, _hell, hf, hsol, hham, hpotential, hmass⟩ :=
    HalfLineMetricConvergenceData.exists_poleEndpoint_terminal_normalized_soliton_of_ancient
      F hF.carrier_eq hF.regular_eq b hbmem tauN qN hsigma Phi R hR bf hsrc htgt co
        hcomplete0 inferInstance (fun _ => kappa) hancient hb hF p hbase htauTop hphi
  let f : C^∞⟮I3, P.M; ℝ⟯ :=
    ⟨fun y => ellC (y, (⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩ : Ici (1 : ℝ))), hf⟩
  have hnormalized : normalizedGradientRicciSoliton (co.gInf 0) f := by
    refine ⟨⟨hcomplete0⟩, hsol, ?_⟩
    intro y
    simpa only [hamiltonNormalized, normGradSqFun_def, one_mul] using hham y
  have hmasslt : normalizedShrinkerMass (co.gInf 0) f < 1 := by
    rw [hmass]
    exact asymptoticReducedVolume_lt_one_of_ancient F hF p hb
  have hscalar := normalizedGradientRicciSoliton_scalar_pos_of_mass_lt_one hnormalized hmasslt
  obtain ⟨Psi, hPsi, C, hC, _href⟩ :=
    exists_backwardSlice_canonical_metric_convergence_of_poleEndpoint
      F hF.carrier_eq hF.regular_eq b hbmem tauN (fun i => htau (i + N)) qN hsigma
        Phi R bf hsrc htgt co hphi htauTop
  let Q : PointedRiemannianManifold.{u, 0, 0} I3 := { P with metric := co.gInf 0 }
  let PsiOriginal : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) Q
      (fun i => phi (co.φ i) + N) :=
    { partialDiffeomorph := Psi.partialDiffeomorph
      source_exhausts := Psi.source_exhausts
      base_mem := Psi.base_mem
      basepoint_map := Psi.basepoint_map }
  obtain ⟨COriginal, hCOriginal, hrefOriginal⟩ :=
    exists_metricConvergenceData_canonicalSourceData PsiOriginal (by
      intro K hK order eps heps
      obtain ⟨i0, hi0⟩ := C.converges K hK order eps heps
      refine ⟨i0, fun i hi => ?_⟩
      have hh := (hi0 i hi).2
      rw [hC i] at hh
      exact hh)
  have hback : ∀ K : Set P.M, IsCompact K → ∀ order : ℕ, ∀ eps : ℝ, 0 < eps → ∀ᶠ i in atTop,
      Nonempty (MetricComparisonOn (fun theta => co.gInf (1 - theta))
        (backwardScaledMetric F.S (tau (phi (co.φ i) + N)) (htau (phi (co.φ i) + N)))
        (Phi.map (co.φ i)) K (Icc (1 : ℝ) 3) order eps) := by
    intro K hK order eps heps
    exact co.eventually_backwardScaledMetric_comparison F b hbmem tauN (fun i => htau (i + N))
      htauTop qN hsigma hphi Phi K hK order eps heps
  refine ⟨b, hb, hbmem, q, N, hsigma, P, phi, Phi, R, bf, hsrc, htgt, co,
    hphi, hRP, hR, hconn, hcomplete, co.isSolutionOn Phi rfl Subset.rfl,
    ⟨f, hsol, hpotential, hmass, hmasslt⟩, hscalar, ?_,
    hback, PsiOriginal, hPsi, COriginal, hCOriginal, hrefOriginal⟩
  intro a c hac hc K hK order eps heps
  have hh := co.eventually_metric_comparison Phi rfl Subset.rfl hac hc K hK order eps heps
  filter_upwards [hh] with i hi
  have heq : (fun s => ((poleEndpointRescaledFlowSeq F hF.carrier_eq hF.regular_eq
      b hbmem tauN qN hsigma).term (phi (co.φ i))).S.base.metric s) =
      (fun s => scaleMetric (tau (phi (co.φ i) + N) + b)⁻¹
        (inv_pos.mpr (hsigma (phi (co.φ i))))
        (F.S.base.metric (-tau (phi (co.φ i) + N) +
          (tau (phi (co.φ i) + N) + b) * s))) := by
    funext s
    exact poleEndpointRescaledFlowSeq_metric F hF.carrier_eq hF.regular_eq
      b hbmem tauN qN hsigma (phi (co.φ i)) s
  rw [heq] at hi
  exact hi

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
