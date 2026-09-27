import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointAncientTerminalNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthCompactness


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

namespace HalfLineMetricConvergenceData

theorem exists_poleEndpoint_terminal_normalized_soliton_of_ancient
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps
      (poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma) P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i)
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i))
    (hb : b < 0) {kappa0 : ℝ} (hAncient : IsAncientKappaSolution kappa0 F)
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S 0 p (q i) 1 ≤ A)
    (hescape : Tendsto tau atTop atTop) (hphi : StrictMono phi) :
    ∃ (psi : ℕ → ℕ) (ellC : C(P.M × Ici (1 : ℝ), ℝ)), StrictMono psi ∧
      TendstoLocallyUniformly
        (fun k (z : P.M × Ici (1 : ℝ)) =>
          redLength ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term
            (phi (co.φ (psi k)))).S 0 p
            (Phi.map (co.φ (psi k)) z.1) z.2) ellC atTop ∧
      ∃ hf₁ : ContMDiff I 𝓘(ℝ) ∞ (fun x => ellC (x, ⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩)),
      let f₁ : C^∞⟮I, P.M; ℝ⟯ :=
        ⟨fun x => ellC (x, ⟨1, (le_rfl : (1 : ℝ) ≤ 1)⟩), hf₁⟩
      gradientRicciSoliton (co.gInf 0) f₁ 1 ∧
        hamiltonNormalized (co.gInf 0) f₁ 1 ∧
        IsHamiltonNormalizedPotential (co.gInf 0) f₁ ∧
        normalizedShrinkerMass (co.gInf 0) f₁ = asymptoticReducedVolume F.S b p := by
  obtain ⟨psi, ellC, hpsi, hconv⟩ :=
    exists_subseq_tendstoLocallyUniformly_poleEndpoint_redLength
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p
      (Eventually.of_forall fun k => hbase (phi (co.φ k)))
  refine ⟨psi, ellC, hpsi, hconv, ?_⟩
  exact poleEndpoint_redLength_limit_exists_terminal_normalized_soliton_of_ancient
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co
    hcomplete hboundary kappa hF hb hAncient p hbase hescape hphi psi hpsi ellC hconv

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
