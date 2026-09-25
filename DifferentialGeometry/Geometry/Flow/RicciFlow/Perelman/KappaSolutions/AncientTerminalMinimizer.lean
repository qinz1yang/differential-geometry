import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMinimizerInterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.SmoothExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Naturality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Naturality
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import DifferentialGeometry.Topology.Manifold.ModelWithCorners

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood Set
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientTerminalMinimizerTopology : TopologicalSpace F.M := F.topology
local instance ancientTerminalMinimizerCharted : ChartedSpace H F.M := F.charted
local instance ancientTerminalMinimizerSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientTerminalMinimizerT2 : T2Space F.M := F.t2
local instance ancientTerminalMinimizerSigma : SigmaCompactSpace F.M := F.sigmaCompact

private theorem exists_lRegularized_minimizer_of_ancient_of_innerProductSpace
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x y : F.M) {tau : ℝ} (htau : 0 < tau) :
    ∃ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
      alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
      IsLRegularizedGeodesicOn F.S 0 alpha (Ioc 0 (Real.sqrt tau)) ∧
      lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
        lCost F.S 0 x (alpha (Real.sqrt tau)) tau := by
  obtain ⟨alpha, halpha, hgeo, ha0, hab, hact, _⟩ :=
    exists_lRegularizedMin_contMDiff_one_regularizedGeodesicOn_of_ancient F hF x y htau
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hregb : 0 - (Real.sqrt tau) ^ 2 ∈ ancientTimeInterval.regular := by
    rw [ancientTimeInterval_regular, mem_Iio, zero_sub]
    exact neg_neg_of_pos (sq_pos_of_pos hb)
  obtain ⟨beta, hbeta, heq, hgeob⟩ :=
    exists_lRegularizedGeodesic_extension_Ioc_of_contMDiff_one
      F.S F.isSolution 0 hb halpha hregb hgeo
  have hb0 : beta 0 = x := (heq ⟨le_rfl, hb.le⟩).trans ha0
  have hbb : beta (Real.sqrt tau) = y := (heq ⟨hb.le, le_rfl⟩).trans hab
  refine ⟨beta, hbeta, hb0, hbb, hgeob, ?_⟩
  rw [hbb, ← hact]
  apply lRegularizedAction_congr F.S 0
  intro s hs
  rw [uIoo_of_le hb.le] at hs
  exact heq ⟨hs.1.le, hs.2.le⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood Set
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientTerminalTopology : TopologicalSpace F.M := F.topology
local instance ancientTerminalCharted : ChartedSpace H F.M := F.charted
local instance ancientTerminalSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientTerminalT2 : T2Space F.M := F.t2
local instance ancientTerminalSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_lRegularized_minimizer_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x y : F.M) {tau : ℝ} (htau : 0 < tau) :
    ∃ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
      alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
      IsLRegularizedGeodesicOn F.S 0 alpha (Ioc 0 (Real.sqrt tau)) ∧
      lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
        lCost F.S 0 x (alpha (Real.sqrt tau)) tau := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let J := I.transContinuousLinearEquiv e
  let Phi : F.M ≃ₘ⟮I, J⟯ F.M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I F.M e
  let G := F.pullback Phi.symm
  have hG : IsAncientKappaSolution kappa G := F.pullback_isAncientKappaSolution Phi.symm hF
  obtain ⟨alpha, halpha, hstart, hend, hgeo, haction⟩ :=
    exists_lRegularized_minimizer_of_ancient_of_innerProductSpace G hG x y htau
  refine ⟨alpha, ?_, hstart, hend, ?_, ?_⟩
  · exact (Phi.symm.contMDiff.of_le (by simp)).comp halpha
  · exact hgeo.comp_diffeomorph F.S Phi.symm
  · change lRegularizedAction (F.S.pullback Phi.symm) 0 alpha 0 (Real.sqrt tau) =
      lCost (F.S.pullback Phi.symm) 0 x (alpha (Real.sqrt tau)) tau at haction
    exact (lRegularizedAction_pullback F.S Phi.symm 0 alpha 0 (Real.sqrt tau)).symm.trans
      (haction.trans (lCost_pullback F.S Phi.symm 0 x (alpha (Real.sqrt tau)) tau))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
