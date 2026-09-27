/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallVocabulary
import Mathlib.Topology.Homeomorph.Lemmas

open Set Topology

theorem Homeomorph.image_connectedComponentIn_family {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (Ψ : X ≃ₜ Y) (S : Set X) :
    (fun A : Set X => Ψ '' A) '' ((fun x => connectedComponentIn S x) '' S) =
      (fun y => connectedComponentIn (Ψ '' S) y) '' (Ψ '' S) := by
  rw [image_image, image_image]
  apply image_congr
  intro x hx
  exact Ψ.image_connectedComponentIn hx

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}

open Classical in
theorem section34TraceComponents_update_image
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3)
    (Ψ : M₂ ≃ₜ M₂) (hSf : Ψ '' frontier (⋃ w, tgtV w) = frontier (⋃ w, tgtV w)) :
    section34TraceComponents tgtV (Function.update fblBd s (Ψ '' fblBd s)) s =
      (fun A : Set M₂ => Ψ '' A) '' section34TraceComponents tgtV fblBd s := by
  have htrace : Ψ '' fblBd s ∩ frontier (⋃ w, tgtV w) =
      Ψ '' (fblBd s ∩ frontier (⋃ w, tgtV w)) := by
    rw [image_inter Ψ.injective, hSf]
  simp only [section34TraceComponents, Function.update_self, htrace]
  exact (Ψ.image_connectedComponentIn_family _).symm

open Classical in
theorem section34TraceCount_update_image
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3)
    (Ψ : M₂ ≃ₜ M₂) (hSf : Ψ '' frontier (⋃ w, tgtV w) = frontier (⋃ w, tgtV w)) :
    section34TraceCount tgtV (Function.update fblBd s (Ψ '' fblBd s)) s =
      section34TraceCount tgtV fblBd s := by
  rw [section34TraceCount, section34TraceComponents_update_image tgtV fblBd s Ψ hSf]
  exact ncard_image_of_injective _ Ψ.injective.image_injective

end DifferentialGeometry.Topology.PiecewiseLinear
