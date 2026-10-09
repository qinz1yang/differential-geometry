import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PortSelection

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

/-- Reduction of peripheral injection into the truncated core to injectivity into the ambient
finite-volume hyperbolic manifold: if `π₁(T) → π₁(H)` along `inclusion ∘ boundaryMap q` is
injective, then so is `π₁(T) → π₁(core)` along `boundaryMap q`. -/
theorem peripheral_injective_of_ambient_CPF {H : FiniteVolumeHyperbolicModel.{u}}
    (T : HyperbolicTruncation H) (q : Fin T.count) (y : Torus)
    (h : Function.Injective (FundamentalGroup.map
      (T.inclusion.comp (T.boundary.boundaryMap q)) y)) :
    Function.Injective (FundamentalGroup.map (T.boundary.boundaryMap q) y) := by
  intro a b hab
  apply h
  rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp, Function.comp_apply, Function.comp_apply, hab]

/-- Same, in the exact shape of `hperi` in `exists_compressible_exterior_port_CPE`.  The ambient
hypothesis `hamb` is the remaining (missing-from-tree) input: injectivity of the cusp torus
into `π₁(H)` (needs Cartan–Hadamard / universal cover `≅ ℍ³`, horoball). -/
theorem hperi_of_ambient_CPF {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {slices : ℕ → RegularSlice F.observation}
    (L : LateCutFamily F K slices) (j : ℕ)
    (hamb : ∀ (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) (y : Torus),
      Function.Injective (FundamentalGroup.map
        ((L.truncation j i).inclusion.comp ((L.truncation j i).boundary.boundaryMap q)) y)) :
    ∀ (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) (y : Torus),
      Function.Injective (FundamentalGroup.map ((L.truncation j i).boundary.boundaryMap q) y) :=
  fun i q y => peripheral_injective_of_ambient_CPF _ q y (hamb i q y)

end GC.LongTime.CuspP1
