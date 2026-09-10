/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarRescale

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

noncomputable section

universe u v w x

namespace DifferentialGeometry.Topology.SmoothTwoSidedCollar

variable
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type x} [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {S : Type*} [TopologicalSpace S] [ChartedSpace H S]
    {M : Type*} [TopologicalSpace M] [ChartedSpace G M]
    {e : S → M} (h : SmoothTwoSidedCollar I J e)

noncomputable def toTwoSidedCollar : ThreeManifold.TwoSidedCollar e :=
  ThreeManifold.TwoSidedCollar.ofOpenInterval h.radius_pos h.toFun
    h.isOpenEmbedding_toFun h.toFun_zero

@[simp]
theorem toTwoSidedCollar_toFun (p : S × ℝ) :
    h.toTwoSidedCollar.toFun p =
      h.toFun (p.1, ThreeManifold.TwoSidedCollar.realHomeomorphIoo
        h.radius h.radius_pos p.2) :=
  rfl

end DifferentialGeometry.Topology.SmoothTwoSidedCollar
