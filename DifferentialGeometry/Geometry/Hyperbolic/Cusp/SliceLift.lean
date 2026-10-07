/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.PositiveMetric

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

local notation "V₃" => Fin 3 → ℝ
local notation "V₂" => Fin 2 → ℝ
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

def positiveSlice (r : ℝ) (hr : 0 < r) : C(V₂, positiveDepth) where
  toFun z := ⟨![r, z 0, z 1], hr⟩
  continuous_toFun :=
    (show Continuous (fun z : V₂ => (![r, z 0, z 1] : V₃)) by fun_prop).subtype_mk _

def modelSlice (r₀ r : ℝ) : C(V₂, Hyperboloid E₃) where
  toFun z := Horospherical.shiftedModel r₀ ![r, z 0, z 1]
  continuous_toFun :=
    (Horospherical.contMDiff_shiftedModel r₀).continuous.comp (by fun_prop)

theorem modelSlice_injective (r₀ r : ℝ) : Function.Injective (modelSlice r₀ r) :=
  Horospherical.shiftedModel_slice_injective r₀ r

theorem positiveModel_positiveSlice (r₀ r : ℝ) (hr : 0 < r) (z : V₂) :
    positiveModel r₀ (positiveSlice r hr z) = modelSlice r₀ r z := rfl

variable {H : FiniteVolumeHyperbolicModel}

theorem positiveMap_positiveSlice (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    (q : V₂ → Torus) (r : ℝ) (hr : 0 < r) (z : V₂) :
    positiveMap Tr i q (positiveSlice r hr z) =
      Tr.cuspMap i (q z, halfSpaceOneLift r) := by
  have hz : horizontal (![r, z 0, z 1] : V₃) = z := by
    funext j
    fin_cases j <;> rfl
  change Tr.cuspMap i (q (horizontal ![r, z 0, z 1]), halfSpaceOneLift r) = _
  rw [hz]

theorem modelSlice_cover_square (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    (q : V₂ → Torus) (r₀ r : ℝ) (hr : 0 < r) (P : Hyperboloid E₃ → H.Carrier)
    (hcomm : positiveMap Tr i q = P ∘ positiveModel r₀) (z : V₂) :
    P (modelSlice r₀ r z) = Tr.cuspMap i (q z, halfSpaceOneLift r) := by
  have h := congrFun hcomm (positiveSlice r hr z)
  change positiveMap Tr i q (positiveSlice r hr z) = P (modelSlice r₀ r z) at h
  exact h.symm.trans (positiveMap_positiveSlice Tr i q r hr z)

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
