/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.BasedCircle
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedBranchOrientability
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneCollar
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneSource
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneTubeCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoOrientable
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneMarkedChart
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneTransport
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneTube

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

open Classical in
theorem exists_isMarkedBranchCollar [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c)
    {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J)
    (hpre : hD.branchPreimage c = J) :
    ∃ (Q C : Set (EuclideanSpace ℝ (Fin 2)))
      (τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2))
      (sheet : EuclideanSpace ℝ (Fin 2) → OpenPartialHomeomorph M (ℝ × ℝ × ℝ)),
      hD.IsMarkedBranchCollar c J Q C τ ρ sheet := by
  classical
  obtain ⟨Q, hQ, hfrontQ, -⟩ := isPLBall_of_isPLSphere_one hJ
  obtain ⟨τ, hτ⟩ := hD.exists_isBranchDeckInvolution_of_branchPreimage_eq c hpre
  obtain ⟨C, ρ, hρ⟩ := hD.exists_isTwoSidedBranchCollar_of_branchPreimage_eq hc hJ hpre hQ hfrontQ
  obtain ⟨a₀, ha₀⟩ := hτ.2.1
  obtain ⟨e₀, -⟩ := hD.exists_isMarkedCrossingChartAt hc hτ hρ ha₀
  refine ⟨Q, C, τ, ρ,
    fun a => if h : a ∈ J then (hD.exists_isMarkedCrossingChartAt hc hτ hρ h).choose else e₀,
    hτ, hρ, fun a ha => ?_⟩
  change hD.IsMarkedCrossingChartAt c J τ ρ a
    (if h : a ∈ J then (hD.exists_isMarkedCrossingChartAt hc hτ hρ h).choose else e₀)
  rw [dite_eq_left ha]
  exact (hD.exists_isMarkedCrossingChartAt hc hτ hρ ha).choose_spec

end NormalSingularCellData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

open Classical in
theorem NormalSingularCellData.not_branchPreimage_eq_of_isOrientable
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hL : IsCombinatorialManifold 3 L)
    (hor : IsOrientable 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {D : SingularTwoCell L.space} {BdM B : Set L.space}
      (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch},
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ {J : Set (EuclideanSpace ℝ (Fin 2))}, IsPLSphere 1 J →
        hD.branchPreimage c = J → False := by
  classical
  let _ := combinatorialChartedSpace L hL
  intro D BdM B hD c hc J hJ hpre
  obtain ⟨Q, C, τ, ρ, sheet, hmc⟩ := hD.exists_isMarkedBranchCollar hc hJ hpre
  obtain ⟨Pc, hPc, N, hN, φ, u, r, htube⟩ :=
    exists_isSourceTrackedBranchTube L hL D BdM B hD c hc J Q C τ ρ sheet hJ hmc
  have : Finite Pc.faces := hPc
  have : Finite N.faces := hN
  have : ConnectedSpace (hD.branchPreimage c) :=
    hD.connectedSpace_branchPreimage_of_isPLSphere_one c hJ hpre
  obtain ⟨R, Lc, hRfin, hRL, hNeq⟩ := htube.derived
  have : Finite R.faces := hRfin.to_subtype
  have hNor : IsOrientable 3 N := by
    subst hNeq
    exact (isOrientable_derivedNeighborhood_of_isSubdivision hL hor hRL Lc).1
  obtain ⟨g, v, hgc, hgb, hv01, hv12, hv23, hv30, hr⟩ := htube.cyclic
  obtain ⟨p, hpcov, hpcard, T, hl02, hl13⟩ :=
    exists_sourceRayTransport_of_isSourceTrackedBranchTube hD Subtype.val_injective hmc.2.1 htube
  have hconf : IsSheetExchange u g (v 0) (v 1) (v 2) (v 3) :=
    T.isSheetExchange hpcov hpcard htube.mapsTo hl02 hl13 hr hv01 hv12 hv23 hv30
  have hsq : u (u (g ((v 0 : ℝ) : loopCircle))) = g ((v 0 : ℝ) : loopCircle) := by
    rw [← hr 0]
    exact T.square_fixes_rays hpcov hpcard htube.mapsTo 0
  exact IsCylindricalDiagram.not_closedBranchCase1 Pc N htube.isPLBall htube.isManifold hNor
    htube.isCylindrical htube.isEndMap htube.seam hgc hgb hconf hsq

open Classical in
theorem NormalSystem.not_branchPreimage_eq_of_isOrientableManifold {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (S : NormalSystem F)
    (hor : S.IsOrientableManifold) :
    letI : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 S.manifoldComplex)
      (isCombinatorialManifold_double_succ_succ S.manifoldComplex S.isManifold)
    ∀ {D : SingularTwoCell (double 3 S.manifoldComplex).space}
      {BdM B : Set (double 3 S.manifoldComplex).space}
      (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch},
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ {J : Set (EuclideanSpace ℝ (Fin 2))}, IsPLSphere 1 J →
        hD.branchPreimage c = J → False := by
  classical
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 S.manifoldComplex)
    (isCombinatorialManifold_double_succ_succ S.manifoldComplex S.isManifold)
  intro D BdM B hD c hc J hJ hpre
  exact NormalSingularCellData.not_branchPreimage_eq_of_isOrientable
    (double 3 S.manifoldComplex)
    (isCombinatorialManifold_double_succ_succ S.manifoldComplex S.isManifold)
    (S.isOrientable_double_manifoldComplex hor) hD hc hJ hpre

end DifferentialGeometry.Topology.PiecewiseLinear
