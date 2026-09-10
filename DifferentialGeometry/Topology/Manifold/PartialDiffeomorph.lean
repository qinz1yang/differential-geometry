/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false
open Manifold Set Topology
open scoped Manifold ContDiff
noncomputable section

namespace Poincare.Topology.PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def extendedChart [I.Boundaryless] [IsManifold I ∞ M] (x : M) :
    _root_.PartialDiffeomorph I (modelWithCornersSelf ℝ E) M E ∞ where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by simpa only [extChartAt_source] using
    (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

def subtypeVal (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    _root_.PartialDiffeomorph I I U M ∞ where
  __ := U.openPartialHomeomorphSubtypeCoe hU
  contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
  contMDiffOn_invFun := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U _ _ x).mp
    exact contMDiffWithinAt_id.congr
      (fun y hy ↦ (U.openPartialHomeomorphSubtypeCoe hU).right_inv hy)
      ((U.openPartialHomeomorphSubtypeCoe hU).right_inv hx)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

def restrict (φ : _root_.PartialDiffeomorph I J M N ∞) (U : Set M) (hU : IsOpen U) :
    _root_.PartialDiffeomorph I J M N ∞ where
  __ := φ.toOpenPartialHomeomorph.restrOpen U hU
  contMDiffOn_toFun := φ.contMDiffOn_toFun.mono inter_subset_left
  contMDiffOn_invFun := φ.contMDiffOn_invFun.mono inter_subset_left

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners ℝ F' G'}
    {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']

def prod (φ : _root_.PartialDiffeomorph I J M N ∞)
    (ψ : _root_.PartialDiffeomorph I' J' M' N' ∞) :
    _root_.PartialDiffeomorph (I.prod I') (J.prod J') (M × M') (N × N') ∞ where
  __ := φ.toOpenPartialHomeomorph.prod ψ.toOpenPartialHomeomorph
  contMDiffOn_toFun := φ.contMDiffOn_toFun.prodMap ψ.contMDiffOn_toFun
  contMDiffOn_invFun := φ.contMDiffOn_invFun.prodMap ψ.contMDiffOn_invFun

end Poincare.Topology.PartialDiffeomorph
