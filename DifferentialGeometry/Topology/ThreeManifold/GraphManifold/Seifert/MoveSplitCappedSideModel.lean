import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSide

/-!
# The capped solid tori of the split sphere (ledger item)

Lane N2c, tier 2 (side model). `exists_sideData`: for a linear split seam and any spherical
capping `K` of `Q` along the split tube, the two capped sides of the split sphere carry the solid
tori of `SideData` for every small collar height `δ₂`. This is the one local statement of the lane
left with `sorry` under the amendment of 2026-10-03 (night); everything else of tiers 2–4 is
proved from it.

Paper proof. Let `R = V ∪ H` and `t` a side. The sphere `S = D_a ∪ γ × S¹ ∪ D_b` cuts `R` into
`R_t = P_t × S¹ ∪ D² × α_t`, where `P_t` is the annulus of the pants between `γ` and the circle
`c_t = port t` and `α_t` the arc of the core circle of `V`; after capping, `V_t = R_t ∪ cap_t`.
The fibre circles of `H` extend to a circle action on `V_t`: on `V` they are the meridian circles
(the seam `j` sends the meridian of `V` to the fibre), and in the ball chart of
`exists_sideBall` they are the circles about the vertical axis, since on the untwisted shell the
tube reads the meridian disc `6 (x₁ + i x₂)` on the polar caps and the fibre `unitOf (x₁ + i x₂)`
on the band. The fixed set is the circle `C` formed by the core arc of `V` and the vertical
diameter of the ball; the orbit space is an annulus `A_t` between `C` and `c_t`, glued from the
annulus `P_t` of the pants, the sector `[0, 3] × α_t` of `V` and the vertical half disc of the
ball. A diffeomorphism `S¹ × [0, 1] ≅ A_t` which is normal to `C` near `C` (in the axis chart of
the ball and the radial chart of `V`) and equal to the radial collar of `c_t` of width `δ₂ / 4`
near `c_t` lifts to `solid t : D² × S¹ → V_t`, `(ρ e^{iφ}, ψ) ↦` the point at angle `φ` over the
orbit point with coordinates `(ψ, ρ)`: smooth at `ρ = 0` by normality, a local diffeomorphism and
injective because the lift is equivariant and the base map is a diffeomorphism, with collar the
host collar through the swap of the two circles (`holonomy`). Its image is `V_t`, so it covers the
cap and the core points of `R_t`, meets the core only in points of `V ∪ H`, and meets the other
solid torus only on its boundary torus (the two boundary tori coincide exactly when the two other
ports of `H` form one seam).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

namespace GC.Seifert.ElementaryPresentation

universe u

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)

end GC.Seifert.ElementaryPresentation
