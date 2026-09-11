import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundBackwardSpaceForm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerMassClassification


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance universalVolumeTopology : TopologicalSpace F.M := F.topology
local instance universalVolumeCharted : ChartedSpace H F.M := F.charted
local instance universalVolumeSmooth : IsManifold I ∞ F.M := F.smooth
local instance universalVolumeC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance universalVolumeT2 : T2Space F.M := F.t2
local instance universalVolumeSigma : SigmaCompactSpace F.M := F.sigmaCompact


theorem ancientKappaThree_reducedVolume_lower
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnotround : ¬ IsShrinkingSphericalSpaceFormFlow F) (p : F.M)
    {tau0 : ℝ} (htau0 : 0 < tau0) :
    ENNReal.ofReal (Real.exp (-1)) ≤ intrinsicReducedVolume F.S 0 p tau0 := by
  let tau : ℕ → ℝ := fun i => (i : ℝ) + 1
  have htau : ∀ i, 0 < tau i := fun i => by dsimp only [tau]; positivity
  have hescape : Tendsto tau atTop atTop := by
    apply tendsto_atTop_mono (fun i => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    dsimp only [tau]
    linarith
  have hdim2 : 2 ≤ Module.finrank ℝ E := by omega
  obtain ⟨q, L, phi, hphi, _hcenters, Phi, C, hcanonical, hcomplete, hgeometry⟩ :=
    exists_samePole_normalized_asymptotic_shrinker F hF hdim2 p tau htau hescape
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  let _ : IsManifold I ∞ L.M := L.smooth
  let _ : IsManifold I 1 L.M := IsManifold.of_le (n := ∞) (by decide)
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  obtain ⟨hconnected, hnonflat, hnco, f, hsoliton, hnormal, hmass⟩ := hgeometry
  have hmassLower : ENNReal.ofReal (Real.exp (-1)) ≤ normalizedShrinkerMass L.metric f := by
    rcases normalized_nonflat_three_shrinker_round_or_mass L hdim hcomplete hconnected
      hnonflat hnco f hsoliton hnormal with hround | hdouble | hsingle
    · obtain ⟨hcompact, hscalar, hEin⟩ := hround
      obtain ⟨hT, D, e, hmetric⟩ :=
        ancient_sphericalSpaceFormFlow_of_round_backward_convergence F hdim hF.connected
          tau htau hescape q hphi Phi C hcanonical hcompact (by norm_num : 0 < (3 : ℝ) / 2)
          hscalar hEin
      exact False.elim (hnotround ⟨3 / (2 * F.S.scalar 0 F.basepoint), hT, D, e, hmetric⟩)
    · rw [hdouble]
      apply ENNReal.ofReal_le_ofReal
      have hpos := Real.exp_pos (-1 : ℝ)
      linarith
    · exact hsingle.ge
  apply hmassLower.trans
  apply le_of_tendsto hmass
  have htimes : Tendsto (fun i => tau (phi i)) atTop atTop :=
    hescape.comp hphi.tendsto_atTop
  filter_upwards [htimes.eventually_ge_atTop tau0] with i hi
  exact ancient_reducedVolume_antitone F hF p htau0 (htau (phi i)) hi

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
