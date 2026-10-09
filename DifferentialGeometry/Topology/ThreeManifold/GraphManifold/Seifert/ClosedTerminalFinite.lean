import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFiniteHost
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFiniteBase
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFiniteSlopeData
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFiniteCentral

/-!
# Finiteness of the actual closed triangle block fundamental group

The original product host generates the fundamental group after the three actual fillings.
Its native pants boundaries give the simultaneous relation and the section generators, while
its original fibre is central and each actual meridian imposes the specified slope relation.
The spherical triangle quotient, Euler abelianization and Schur argument prove finiteness of
this actual group. A final basepoint change gives the frozen closed-carrier endpoint.
-/

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Topology ContinuousMap unitInterval
universe u
namespace GC.Seifert
namespace SeifertBlock
variable {W : CompactCarrier.{u}} {d : SeifertData} (B : SeifertBlock W d)

set_option backward.isDefEq.respectTransparency false in
theorem exists_finite_fundamentalGroup_of_closed_three_cones (hclosed : d.ports = 0)
    (hcones : d.cones.length = 3) (hchi : 0 < d.orbChi) :
    ∃ p : B.presentation.components.piece (B.piece none),
      Finite (FundamentalGroup W.Carrier (B.productToCarrier p)) := by
  let hk := d.closedThreeCones_kind hclosed hcones
  obtain ⟨b, β, hgen, hboundary⟩ :=
    B.product.base.exists_closedTriangleBoundaryGeneratorsOfKind hk
  let a := fun j => GC.Topology.markedMap
    (B.product.base.boundaryCircle (Fin.cast hk.symm j)) 1 (β j)
      (FundamentalGroup.fromPath ⟦circleLoop⟧)
  let p₀ := B.product.closedTriangleBaseSlice b
  let G := FundamentalGroup W.Carrier (B.productToCarrier p₀)
  let h : FundamentalGroup B.product.base.surface.Carrier b →* G :=
    FundamentalGroup.map (B.productToCarrier.comp B.product.closedTriangleBaseSlice) b
  let x : Fin 3 → G := fun j => h (a j)
  let z : G := B.fibreClass p₀
  let e := B.closedTriangleNativeConeEquiv hclosed hcones
  let p : Fin 3 → ℕ := fun j => d.cones[e j].1
  let q : Fin 3 → ℤ := fun j => d.cones[e j].2
  have hx : Subgroup.closure (Set.range x ∪ {z}) = ⊤ :=
    B.closure_baseSlice_fibreClass_of_closed_three_cones hclosed hcones b a hgen
  have hb : x 0 * x 2 * x 1 = 1 := by
    simpa only [map_mul, map_one] using congrArg h hboundary
  have hf : ∀ j, x j ^ p j * z ^ q j = 1 := by
    intro j
    let m := closedConeFillingEquiv (d := d) hclosed hcones (e j)
    have hr : ∀ γ : Path b (B.product.base.boundaryCircle (B.port (.inr m)) 1),
        h (GC.Topology.markedMap (B.product.base.boundaryCircle (B.port (.inr m))) 1 γ
          (FundamentalGroup.fromPath ⟦circleLoop⟧)) ^ (d.fillingSlope m).1 *
            z ^ (d.fillingSlope m).2 = 1 := fun γ => B.filledBaseSlice_fibre_relation b m γ
    dsimp only [m, e] at hr
    rw [B.closedTriangleNativeConeEquiv_port hclosed hcones j,
      closedConeFillingEquiv_slope (d := d) hclosed hcones] at hr
    simpa only [zpow_natCast] using hr (β j)
  have hz : ∀ g : G, g * z = z * g :=
    B.fibreClass_central_of_closed_three_cones hclosed hcones p₀
  obtain ⟨hp, hchar, hnum⟩ :=
    d.closedTriangle_arithmetic_of_equiv hclosed hcones hchi e
  exact ⟨p₀, finite_closedTriangleCentralExtension G x z p q hp hx hb hf hz hchar hnum⟩

end SeifertBlock

set_option backward.isDefEq.respectTransparency false in
theorem closedTriangle_finite_fundamentalGroup
    (Q : ConnectedClosedOrientedManifold.{u} 3) (d : SeifertData)
    (B : SeifertBlock (NoCuts.carrier Q) d) (hclosed : d.ports = 0)
    (hcones : d.cones.length = 3) (hchi : 0 < d.orbChi) :
    Finite (FundamentalGroup Q.Carrier (chosenPoint Q)) := by
  obtain ⟨p, hp⟩ := B.exists_finite_fundamentalGroup_of_closed_three_cones hclosed hcones hchi
  have : Finite (FundamentalGroup Q.Carrier (B.productToCarrier p)) := hp
  let γ := PathConnectedSpace.somePath (chosenPoint Q) (B.productToCarrier p)
  exact Finite.of_surjective (fundamentalGroupChangeBasepoint γ)
    (fundamentalGroupChangeBasepoint γ).surjective

end GC.Seifert
