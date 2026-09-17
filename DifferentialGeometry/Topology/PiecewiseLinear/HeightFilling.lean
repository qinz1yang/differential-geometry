import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceFilling
import DifferentialGeometry.Topology.PiecewiseLinear.HeightRotation
import DifferentialGeometry.Topology.PiecewiseLinear.FiberFilling

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_continuousLinearMap_injOn_heightIndex_eq
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsPLSphere 2 L.space) (hdim : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ L.vertices)
    {A : Set E} (hA : A.Finite) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : E →L[ℝ] ℝ, dist f ℓ < ε ∧ f ≠ 0 ∧ InjOn f A ∧
      heightIndex L.space f = heightIndex L.space ℓ := by
  have hclose : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, dist f ℓ < ε :=
    Metric.ball_mem_nhds ℓ hε
  have hne : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f ≠ 0 :=
    isOpen_compl_singleton.mem_nhds hℓ
  obtain ⟨δ, hδ, hδgood⟩ := Metric.mem_nhds_iff.mp
    (hclose.and (hne.and (eventually_heightIndex_eq L hL hdim ℓ hℓ hinj)))
  obtain ⟨f, hf, hfinj⟩ := exists_continuousLinearMap_injOn hA ℓ hδ
  obtain ⟨hfclose, hfne, hfindex⟩ := hδgood hf
  exact ⟨f, hfclose, hfne, hfinj, hfindex⟩

open Classical in
theorem exists_filling_injOn_vertices_of_heightIndex_eq_zero
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsPLSphere 2 L.space) (hdim : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ L.vertices)
    (hzero : heightIndex L.space ℓ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (f : E →L[ℝ] ℝ),
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      (boundaryComplex 3 R).space = L.space ∧ frontier R.space = L.space ∧
      closure (interior R.space) = R.space ∧ IsConnected (interior R.space) ∧
      IsConnected R.spaceᶜ ∧ dist f ℓ < ε ∧ f ≠ 0 ∧ InjOn f R.vertices ∧
      heightIndex L.space f = 0 ∧
      ∀ r : ℝ, (∃ x ∈ L.space, f x < r) → (∃ y ∈ L.space, r < f y) →
        ∃ g : (Fin 3 → ℝ) → E,
          IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) (R.space ∩ {x | f x = r}) ∧
          g '' stdSimplexBoundary 2 = L.space ∩ {x | f x = r} := by
  obtain ⟨R, hRfin, hRman, hRboundary, hRfront, hRcl, hRconn, hRext⟩ :=
    hL.isCombinatorialManifold.exists_isCombinatorialManifoldWithBoundary_boundaryComplex
      L hdim hL.isConnected
  have hvertices : R.vertices.Finite :=
    hRfin.preimage Finset.singleton_injective.injOn
  obtain ⟨f, hfclose, hfne, hfinj, hfindex⟩ :=
    exists_continuousLinearMap_injOn_heightIndex_eq L hL hdim ℓ hℓ hinj hvertices hε
  refine ⟨R, f, hRfin, hRman, hRboundary, hRfront, hRcl, hRconn, hRext,
    hfclose, hfne, hfinj, hfindex.trans hzero, ?_⟩
  let _ : Finite R.faces := hRfin.to_subtype
  let B := boundaryComplex 3 R
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 R).to_subtype
  have hB : IsPLSphere 2 B.space := hRboundary.symm ▸ hL
  have hfB : InjOn f B.vertices := hfinj.mono (fun _ hv => boundaryComplex_faces_subset 3 R hv)
  intro r hbelow habove
  have hfrontB : frontier R.space = B.space := hRfront.trans hRboundary.symm
  have hzeroB : heightIndex B.space f = 0 := by rw [hRboundary, hfindex, hzero]
  obtain ⟨g, hg, hgB⟩ := exists_isPLHomeomorphOn_filling_fiber_of_heightIndex_eq_zero
    B R hB hdim hfrontB hRcl hRconn.isPreconnected f hfne hfB hzeroB r
      (by rwa [hRboundary]) (by rwa [hRboundary])
  exact ⟨g, hg, hRboundary ▸ hgB⟩

end DifferentialGeometry.Topology.PiecewiseLinear
