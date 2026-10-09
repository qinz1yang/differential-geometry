/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.FixtureSolidTorusLoop

set_option autoImplicit false

/-!
# Fixture FX2 (cut form): `exists_essential_embedded_null_of_cut_LTP4` on the solid torus

The PL cut data (triangulation `K` of `W`, `h : |K| ≃ₜ W`, combinatorial 3-manifold with boundary,
orientability, boundary component `c` identified with the Clifford torus) is *produced* by the
delivered LT-R2 / LT-P3 theorems from the concrete bicollar `σ_FX2`, orientation `o_FX2`; it is not
assumed.
-/

noncomputable section
open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped ContDiff Manifold

namespace GC.LongTime.CuspP1
open GC.Endpoint GC.Topology

theorem loopTheoremCut_output_FX2 :
    ∃ γ : freeLoop Torus, Topology.IsEmbedding γ ∧ ¬ γ.Nullhomotopic ∧
      loopDegreeClass γ 1 ∈ (FundamentalGroup.map φ_FX2 (γ 0)).ker := by
  have hsrc : ∀ (j : Unit) (z : Torus), ((j, z), (0 : ℝ)) ∈ σ_FX2.source := fun j z => by
    rw [σ_FX2_source]; exact ⟨by norm_num, by norm_num⟩
  have hO : IsTriangulationOrientable M_FX2 := by
    intro N K _ hK ⟨h⟩
    exact isOrientable_of_homeomorph_tangentOrientation o_FX2 hK h
  obtain ⟨N₀, K₀, hf₀, h₀, hK₀, hKo₀, L, hLf, hL, hLY⟩ :=
    hasPLPresentation_surface_of_openPartialHomeomorph_family_LTR2 σ_FX2 σ_FX2_source
      (fun x : Unit × Torus => σ_FX2 (x, 0)) (fun _ => rfl) hO
  obtain ⟨K, hf, h, hK, hKo, hc⟩ :=
    cut_data_of_triangulation_LTP4 σ_FX2 σ_FX2_source W_FX2 isClosed_W_FX2 hside_FX2 hfront_FX2
      K₀ h₀ hK₀ hKo₀ L hL hLY
  obtain ⟨c, hc'⟩ := hc ()
  have hφinj : Function.Injective φ_FX2 := by
    intro a b hab
    have h1 : σ_FX2 (((), a), 0) = σ_FX2 (((), b), 0) := congrArg Subtype.val hab
    have := σ_FX2.injOn (hsrc () a) (hsrc () b) h1
    simpa using this
  refine exists_essential_embedded_null_of_cut_LTP4 hφinj K h hK hKo c ?_
    not_injective_boundary_FX2
  intro k
  rw [hc' k]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, Subtype.ext hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, congrArg Subtype.val hz⟩

end GC.LongTime.CuspP1
