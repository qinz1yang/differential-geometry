import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PortSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.GluingInjectionTheorem
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.StageTransportBasic

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

/-- Seam injectivity of a `TorusPresentation` is invariant under reparametrising the torus. -/
theorem injective_seam_reparam_CPE2 {M : ConnectedClosedOrientedManifold.{u} 3}
    (G : TorusPresentation (NoCuts.carrier M)) (k : Fin G.pairing.count) (e : Torus ≃ₜ Torus)
    (f : C(Torus, M.Carrier)) (hf : ∀ x, f x = G.seamTorus k (e x))
    (hk : ∀ t, Function.Injective (FundamentalGroup.map (G.seamTorus k) t)) (y : Torus) :
    Function.Injective (FundamentalGroup.map f y) := by
  have hfe : f = (G.seamTorus k).comp (e : C(Torus, Torus)) := ContinuousMap.ext hf
  subst hfe
  rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
  exact (hk _).comp (fundamentalGroup_map_homeomorph_injective e y)

/-- Adapter for `hglue` of `exists_compressible_exterior_port_CPE`.

Data supplied from outside (explicit, no new named Prop):
* `G`: a `TorusPresentation` of the closed component `C` of the `j`-th slice whose seam tori are
  the decomposition seam tori up to reparametrisation (`hseam`);
* `hports_of`: the piece boundary tori of `G` (cores and exterior pieces) are `π₁`-injective as soon as
  the core ports (`boundaryMap`) and exterior ports (`extPortMap_CPE`) are.  Discharger: the cut
  construction identifying `G`'s pieces with the truncated cores and the exterior region
  (CP1-C2 / `seam_image`).
The injectivity theorem used is the tree's K09c `injective_seamTorus_of_ports`, whose engine CP1-C
reproved for pieces (`injective_pieceInterior_incl_CPC`). -/
theorem hglue_of_presentation_CPE2
    (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (G : TorusPresentation (NoCuts.carrier ((slices j).stage.toClosedOrientedManifold.component C)))
    (hseam : ∀ s : Fin (L.decomposition j C).boundary.count, ∃ (k : Fin G.pairing.count)
      (e : Torus ≃ₜ Torus), ∀ x, (L.decomposition j C).reconstructionAtlas.torusInPrime
        (L.decomposition j C).reconstruction s x = G.seamTorus k (e x))
    (hports_of :
      (∀ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
        Function.Injective (FundamentalGroup.map
          (extPortMap_CPE L j hj (L.port j hj ⟨C, s'⟩).1 (L.port j hj ⟨C, s'⟩).2) y)) →
      (∀ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
        Function.Injective (FundamentalGroup.map
          ((L.truncation j (L.port j hj ⟨C, s'⟩).1).boundary.boundaryMap
            (L.port j hj ⟨C, s'⟩).2) y)) →
      ∀ i, (G.pieceBoundaryTori i).incompressible) :
    (∀ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
        Function.Injective (FundamentalGroup.map
          (extPortMap_CPE L j hj (L.port j hj ⟨C, s'⟩).1 (L.port j hj ⟨C, s'⟩).2) y)) →
      (∀ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
        Function.Injective (FundamentalGroup.map
          ((L.truncation j (L.port j hj ⟨C, s'⟩).1).boundary.boundaryMap
            (L.port j hj ⟨C, s'⟩).2) y)) →
      ∀ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
        Function.Injective (FundamentalGroup.map
          ((L.decomposition j C).reconstructionAtlas.torusInPrime
            (L.decomposition j C).reconstruction s') y) := by
  intro hE hC s y
  obtain ⟨k, e, hk⟩ := hseam s
  exact injective_seam_reparam_CPE2 G k e _ hk
    (G.injective_seamTorus_of_ports G.externalCount_eq_zero (hports_of hE hC) k) y

end GC.LongTime.CuspP1
