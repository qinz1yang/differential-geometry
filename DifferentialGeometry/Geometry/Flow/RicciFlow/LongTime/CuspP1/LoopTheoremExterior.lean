/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopTheoremMain

set_option autoImplicit false

/-!
# LT-P4: the `hloop` input for the exterior region

No explicit inputs.
-/

noncomputable section
open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped ContDiff Manifold
open GC.Endpoint

namespace GC.LongTime.CuspP1
open GC.Topology
universe u

theorem exists_essential_embedded_null_of_not_injective_LTP4
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {K : ℕ} {cores : PersistentHyperbolicCores F K}
    (E : PersistentCuspExterior cores) (i : Fin cores.count)
    (q : Fin (E.truncation i).count) (t : ℝ) (ht : E.start ≤ t)
    (φ : C(Torus, ↥(E.region t)))
    (hφ : ∀ z, (φ z : (postStage F.observation t).Carrier) =
      cores.map i t (E.after_cores.trans ht) ((E.truncation i).cuspMap q (z, halfZero)))
    (y : Torus) (hn : ¬ Function.Injective (FundamentalGroup.map φ y)) :
    ∃ γ : freeLoop Torus, Topology.IsEmbedding γ ∧ ¬ γ.Nullhomotopic ∧
      loopDegreeClass γ 1 ∈ (FundamentalGroup.map φ (γ 0)).ker := by
  haveI : Nonempty (TorusIdx_LTP1 E.truncation) := ⟨⟨i, q⟩⟩
  obtain ⟨σ, hσ, hzero, hside, hWc, hfront⟩ := exists_bicollar_of_exterior_LTP1 E t ht
  exact exists_essential_embedded_null_of_bicollared_boundary_LTP4
    (M := (postStage F.observation t).Carrier) (postStage F.observation t).orientation σ hσ
    (E.region t) hWc hside hfront
    ⟨i, q⟩ φ (fun z => by rw [hφ, hzero]) y hn

theorem hloop_LTP4
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {K : ℕ} {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) :
    ∀ (E : PersistentCuspExterior L.cores), E = persistentExterior_CPE2 L j hj →
      ∀ (i : Fin L.cores.count) (q : Fin (E.truncation i).count) (y : Torus)
        (φ : C(Torus, ↥(E.region E.start))),
        (∀ z, (φ z : (postStage F.observation E.start).Carrier) =
          portLoopMap_CPH E i q E.start le_rfl z) →
        ¬ Function.Injective (FundamentalGroup.map φ y) →
        ∃ γ : freeLoop Torus, Topology.IsEmbedding γ ∧ ¬ γ.Nullhomotopic ∧
          loopDegreeClass γ 1 ∈ (FundamentalGroup.map φ (γ 0)).ker := by
  intro E _ i q y φ hφ hn
  exact exists_essential_embedded_null_of_not_injective_LTP4 E i q E.start le_rfl φ
    (fun z => by rw [hφ, portLoopMap_apply_CPH]) y hn

end GC.LongTime.CuspP1
