/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChart
import Mathlib.LinearAlgebra.Projection

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem eventually_mem_space_iff_sub_mem_submodule
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {n : ℕ}
    (hK : IsCombinatorialManifold (n + 1) K) (P : Submodule ℝ E)
    (hdim : Module.finrank ℝ P = n + 1) {x : E} (hx : x ∈ K.space)
    (hsub : ∀ᶠ y in 𝓝 x, y ∈ K.space → y - x ∈ P) :
    ∀ᶠ y in 𝓝 x, y ∈ K.space ↔ y - x ∈ P := by
  classical
  let _ := combinatorialChartedSpace K hK
  obtain ⟨Q, hPQ⟩ := Submodule.exists_isCompl P
  let π : E →L[ℝ] P := (P.projectionOnto Q hPQ).toContinuousLinearMap
  let e : P ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (by
      simpa only [finrank_euclideanSpace, Fintype.card_fin] using hdim)
  let f : E → EuclideanSpace ℝ (Fin (n + 1)) := fun y => e (π (y - x))
  have hf : Continuous f := e.continuous.comp (π.continuous.comp (continuous_id.sub
      continuous_const))
  have hinj : ∀ {y z : E}, y - x ∈ P → z - x ∈ P → f y = f z → y = z := by
    intro y z hy hz hyz
    have hp := e.injective hyz
    change P.projectionOnto Q hPQ (y - x) = P.projectionOnto Q hPQ (z - x) at hp
    rw [P.projectionOnto_apply_of_mem_left hPQ hy, P.projectionOnto_apply_of_mem_left hPQ hz] at hp
    have heq := congrArg (fun p : P => (p : E) + x) hp
    simpa only [sub_add_cancel] using heq
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hsub
  let V : Set K.space := Subtype.val ⁻¹' U
  have hV : IsOpen V := hU.preimage continuous_subtype_val
  have hcont : Continuous (fun y : K.space => f y) := hf.comp continuous_subtype_val
  have hfinj : InjOn (fun y : K.space => f y) V := by
    intro y hy z hz hyz
    exact Subtype.ext (hinj (hUsub hy y.property) (hUsub hz z.property) hyz)
  have hopen : IsOpen ((fun y : K.space => f y) '' V) :=
    DifferentialGeometry.Topology.isOpen_image_of_continuousOn_injOn
      (E := EuclideanSpace ℝ (Fin (n + 1))) hV hcont.continuousOn hfinj
  have hpoint : f x ∈ (fun y : K.space => f y) '' V := ⟨⟨x, hx⟩, hxU, rfl⟩
  have hlocal := hf.continuousAt.eventually (hopen.mem_nhds hpoint)
  filter_upwards [hsub, hlocal] with y hy hyimage
  refine ⟨hy, fun hyP => ?_⟩
  obtain ⟨z, hz, hzy⟩ := hyimage
  have hzy' : (z : E) = y := hinj (hUsub hz z.property) hyP hzy
  exact hzy' ▸ z.property

end DifferentialGeometry.Topology.PiecewiseLinear
