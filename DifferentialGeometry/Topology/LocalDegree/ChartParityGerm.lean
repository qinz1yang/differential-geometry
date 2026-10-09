/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.ChartParity

open Filter
open scoped Topology Manifold

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ} {M : Type*} [TopologicalSpace M]

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))

theorem chartOrientationParity_right_congr
    (a b c : OpenPartialHomeomorph M E) (x : M)
    (ha : x ∈ a.source) (hb : x ∈ b.source) (hc : x ∈ c.source)
    (hbc : b =ᶠ[𝓝 x] c) :
    chartOrientationParity a b x ha hb = chartOrientationParity a c x ha hc := by
  have ht : Tendsto a.symm (𝓝 (a x)) (𝓝 x) := by
    simpa only [a.left_inv ha] using
      (a.continuousOn_symm.continuousAt (a.open_target.mem_nhds (a.map_source ha))).tendsto
  have heq : (a.symm ≫ₕ b) =ᶠ[𝓝 (a x)] (a.symm ≫ₕ c) := hbc.comp_tendsto ht
  unfold chartOrientationParity
  exact embeddingOrientationParity_congr (a.symm ≫ₕ b).open_source (a.symm ≫ₕ c).open_source
    (a.symm ≫ₕ b).continuousOn (a.symm ≫ₕ b).injOn
    (a.symm ≫ₕ c).continuousOn (a.symm ≫ₕ c).injOn _ _ heq

theorem chartOrientationParity_congr
    (a b a' b' : OpenPartialHomeomorph M E) (x : M)
    (ha : x ∈ a.source) (hb : x ∈ b.source)
    (ha' : x ∈ a'.source) (hb' : x ∈ b'.source)
    (haa' : a =ᶠ[𝓝 x] a') (hbb' : b =ᶠ[𝓝 x] b') :
    chartOrientationParity a b x ha hb = chartOrientationParity a' b' x ha' hb' := by
  calc
    chartOrientationParity a b x ha hb = chartOrientationParity b a x hb ha :=
      chartOrientationParity_symm a b x ha hb
    _ = chartOrientationParity b a' x hb ha' :=
      chartOrientationParity_right_congr b a a' x hb ha ha' haa'
    _ = chartOrientationParity a' b x ha' hb := chartOrientationParity_symm b a' x hb ha'
    _ = chartOrientationParity a' b' x ha' hb' :=
      chartOrientationParity_right_congr a' b b' x ha' hb hb' hbb'

end DifferentialGeometry.LocalDegree
