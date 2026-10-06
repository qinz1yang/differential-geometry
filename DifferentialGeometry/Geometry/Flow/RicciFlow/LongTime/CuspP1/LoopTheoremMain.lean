/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopTheoremCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopTheoremCut
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopSurface
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopCollarStage
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.Producer1AssemblyBasic
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PortAdapterPersistent
import DifferentialGeometry.Topology.ThreeManifold.TriangulationOrientable

set_option autoImplicit false

/-!
# LT-P4 wrapper: the Loop Theorem for the exterior region

Chain: LT-P2/R2 triangulation, LT-P3 cut, Moise 5.2 (core).
-/

noncomputable section
open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped ContDiff Manifold

namespace GC.LongTime.CuspP1
open GC.Topology
universe u

/-- Abstract theorem (design doc section 0); no explicit inputs. -/
theorem exists_essential_embedded_null_of_bicollared_boundary_LTP4
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] (o : TangentOrientationSection M)
    {ι : Type} [Finite ι] [Nonempty ι] [TopologicalSpace ι] [DiscreteTopology ι]
    (σ : OpenPartialHomeomorph ((ι × Torus) × ℝ) M)
    (hσ : σ.source = {p | -1 < p.2 ∧ p.2 < 1})
    (W : Set M) (hWc : IsClosed W)
    (hside : ∀ p ∈ σ.source, σ p ∈ W ↔ 0 ≤ p.2)
    (hfront : W \ range (fun x : ι × Torus => σ (x, 0)) ⊆ interior W)
    (j : ι) (φ : C(Torus, ↥W)) (hφ : ∀ z, (φ z : M) = σ ((j, z), 0))
    (y : Torus) (hn : ¬ Function.Injective (FundamentalGroup.map φ y)) :
    ∃ γ : freeLoop Torus, Topology.IsEmbedding γ ∧ ¬ γ.Nullhomotopic ∧
      loopDegreeClass γ 1 ∈ (FundamentalGroup.map φ (γ 0)).ker := by
  have hsrc : ∀ (j : ι) (z : Torus), ((j, z), (0 : ℝ)) ∈ σ.source := fun j z => by
    rw [hσ]; exact ⟨by norm_num, by norm_num⟩
  have hO : IsTriangulationOrientable M := by
    intro N K _ hK ⟨h⟩
    exact isOrientable_of_homeomorph_tangentOrientation o hK h
  obtain ⟨N₀, K₀, hf₀, h₀, hK₀, hKo₀, L, hLf, hL, hLY⟩ := hasPLPresentation_surface_of_openPartialHomeomorph_family_LTR2 σ hσ
      (fun x : ι × Torus => σ (x, 0)) (fun _ => rfl) hO
  obtain ⟨K, hf, h, hK, hKo, hc⟩ :=
    cut_data_of_triangulation_LTP4 σ hσ W hWc hside hfront K₀ h₀ hK₀ hKo₀ L hL hLY
  obtain ⟨c, hc'⟩ := hc j
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : σ ((j, a), 0) = σ ((j, b), 0) := by
      rw [← hφ, ← hφ, hab]
    have := σ.injOn (hsrc j a) (hsrc j b) h1
    simpa using this
  refine exists_essential_embedded_null_of_cut_LTP4 hφinj K h hK hKo c ?_ hn
  intro k
  rw [hc' k]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, Subtype.ext (by rw [hφ]; exact hz)⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, (hφ z).symm.trans (congrArg Subtype.val hz)⟩

end GC.LongTime.CuspP1
