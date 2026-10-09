import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointHamiltonJacobi
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineRicciSoliton
import DifferentialGeometry.Analysis.Parabolic.ScalarHeat.PotentialCongruence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.ExponentialDensity
import DifferentialGeometry.Topology.Manifold.ContMDiffLogarithm
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private theorem contMDiffOn_of_normalized_exponential
    {k : WithTop ℕ∞} (n : ℝ) (ell : M × ℝ → ℝ)
    {J : Set ℝ} (hJ : J ⊆ Set.Ioi 0)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) k
      (fun z : ℝ × M => Real.exp (-ell (z.2, z.1) -
        n / 2 * Real.log z.1 - n / 2 * Real.log (4 * Real.pi)))
      (J ×ˢ Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) k
      (fun z : ℝ × M => ell (z.2, z.1)) (J ×ˢ Set.univ) := by
  let u := fun z : ℝ × M => Real.exp (-ell (z.2, z.1) -
    n / 2 * Real.log z.1 - n / 2 * Real.log (4 * Real.pi))
  have hlogu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) k
      (fun z : ℝ × M => Real.log (u z)) (J ×ˢ Set.univ) :=
    hu.log (fun z _ => (Real.exp_pos _).ne')
  have hlogt : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) k
      (fun z : ℝ × M => Real.log z.1) (J ×ˢ Set.univ) :=
    contMDiffOn_fst.log (fun z hz => (hJ hz.1).ne')
  have hrestore : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) k
      (fun z : ℝ × M => -Real.log (u z) -
        n / 2 * Real.log z.1 - n / 2 * Real.log (4 * Real.pi))
      (J ×ˢ Set.univ) :=
    (hlogu.neg.sub (contMDiffOn_const.mul hlogt)).sub contMDiffOn_const
  apply hrestore.congr
  intro z _
  dsimp only [u]
  rw [Real.log_exp]
  ring

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter _root_.MeasureTheory Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Entropy
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Topology

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
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private local instance : MeasurableSpace P.M := borel P.M
private local instance : BorelSpace P.M := ⟨rfl⟩

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

namespace HalfLineMetricConvergenceData

open DifferentialGeometry.Analysis.Parabolic

theorem poleEndpoint_redLength_limit_gradientRicciSoliton_and_hamiltonNormalized
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (hb : b < 0) {kappa0 : ℝ}
    (hAncient : IsAncientKappaSolution kappa0 F)
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    (hescape : Tendsto tau atTop atTop) (hphi : StrictMono phi)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) (ellC : C(P.M × Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × Ici (1 : ℝ)) =>
        redLength ((U).term (phi (co.φ (psi k)))).S 0 p
          (Phi.map (co.φ (psi k)) z.1) z.2) ellC atTop)
    (ell : P.M × ℝ → ℝ)
    (hagree : ∀ (y : P.M) (t : ℝ) (ht : 1 ≤ t), ell (y, t) = ellC (y, ⟨t, ht⟩))
    {t : ℝ} (ht : 1 < t) :
    ∃ hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => ell (x, t)),
      gradientRicciSoliton (I := I) (co.gInf (1 - t))
        ⟨fun x => ell (x, t), hf⟩ (1 / t) ∧
      hamiltonNormalized (I := I) (co.gInf (1 - t))
        ⟨fun x => ell (x, t), hf⟩ (1 / t) := by
  let Dsol : RealTimeInterval := RealTimeInterval.openInfinite 1 t ht
  let u : ℝ → P.M → ℝ := fun r x => Real.exp (-ell (x, r) -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log r -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
  let G : MetricConnectionFamily (I := I) (M := P.M) ℝ :=
    { metric := fun r => co.gInf (1 - r)
      connection := fun r => leviCivitaConnectionOfMetric (I := I) (co.gInf (1 - r))
      metricCompatible := fun r =>
        leviCivitaConnectionOfMetric_isMetricCompatible (I := I) (co.gInf (1 - r)) }
  have hu : IsHeatPotOn Dsol G (fun r x => -metricScalarAt (co.gInf (1 - r)) x) u :=
    isHeatPotOn_poleEndpoint_redDensity_limit_of_ancient
      F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co
      hcomplete hboundary kappa hF hb hAncient p hbase hescape hphi
      psi hpsi ellC hconv ell hagree Dsol Subset.rfl
  have hdensity : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × P.M => Real.exp (-ell (z.2, z.1) -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi)))
      (Ioi (1 : ℝ) ×ˢ univ) := hu.jointSmooth
  have hell : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × P.M => ell (z.2, z.1)) (Ioi (1 : ℝ) ×ˢ univ) :=
    DifferentialGeometry.Analysis.contMDiffOn_of_normalized_exponential
      (Module.finrank ℝ E : ℝ) ell
      (fun r hr => show 0 < r from zero_lt_one.trans (show 1 < r from hr)) hdensity
  have hbaseSelected : ∀ᶠ k in atTop,
      redLength ((U).term (phi (co.φ k))).S 0 p (q (phi (co.φ k))) 1 ≤ A :=
    Eventually.of_forall fun k => hbase (phi (co.φ k))
  have hconvPointwise : ∀ y : P.M, ∀ r ∈ Ioi (1 : ℝ),
      Tendsto (fun k => redLength ((U).term (phi (co.φ (psi k)))).S 0 p
        (Phi.map (co.φ (psi k)) y) r) atTop (𝓝 (ell (y, r))) := by
    intro y r hr
    have hrOne : 1 ≤ r := (show 1 < r from hr).le
    have hpt := hconv.tendstoLocallyUniformlyOn.tendsto_at
      (mem_univ (y, (⟨r, hrOne⟩ : Ici (1 : ℝ))))
    rw [hagree y r hrOne]
    exact hpt
  have hHJ := poleEndpoint_redLength_limit_hamilton_jacobi
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co
    hcomplete hboundary kappa hF p hbaseSelected psi hpsi.tendsto_atTop
    ell hconvPointwise hell
  have hconjugate : IsHeatPotOn Dsol G
      (fun r x => -metricScalarAt (co.gInf (1 - r)) x)
      (fun r => perelmanDensity (Module.finrank ℝ E) r (fun x => ell (x, r))) := by
    apply hu.congr
    intro r hr x
    have hrpos : 0 < r := zero_lt_one.trans (show 1 < r from hr)
    exact (congrFun (perelmanDensity_eq_exp_log (Module.finrank ℝ E)
      hrpos (fun y => ell (y, r))) x).symm
  have hYreg : Iio 0 ⊆ (Y).D.regular := fun _ hr => hr
  exact co.gradientRicciSoliton_and_hamiltonNormalized_time_sub_of_hamilton_jacobi
    hYreg 1 Dsol (fun r x => ell (x, r)) (show t ∈ Dsol.regular from ht)
    (zero_lt_one.trans ht) ht hconjugate (fun r hr _ x => hHJ r hr x)

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
