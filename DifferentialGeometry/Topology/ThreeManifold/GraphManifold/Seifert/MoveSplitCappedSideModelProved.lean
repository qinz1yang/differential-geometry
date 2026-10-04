import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelGermSmooth
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedCollarAdapter

/-!
# The capped solid tori of the split sphere (ledger item N4, proved)

Lane N2f, side model, step 8. For a side `t` choose the ball chart and the cap filling `SideCap`
(`nonempty_sideCap`). The two solid tori `germSolid` with the ports `sidePort`, the holonomy
`sideHol`, the collar germ `η = 1/3` and the collar width `δ* = 1` form a `SideDataGerm`
(`sideDataGerm`); the radius-three disc compression of the collar adapter turns it into
`SideData` for every collar height `0 < δ₂ ≤ δ₀`. This proves the statement of the ledger item
`exists_sideData` of `MoveSplitCappedSideModel` (`exists_sideData_proved`), with the same binders.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

namespace GC.Seifert.ElementaryPresentation

open SplitTube

universe u

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {E : ElementaryPresentation (NoCuts.carrier Q)}
  {j : Fin E.toTorus.pairing.count} {b : Bool} {h : E.IsSplitSeam j b} {hlin : E.IsLinearSeam j}
  {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N (E.splitSeamTube j b h hlin)}

def sideDataGerm (S : ∀ t, E.SideCap h hlin K t) : E.SideDataGerm h K () where
  η _ := 1 / 3
  η_pos _ := by norm_num
  δ_star := 1
  δ_star_pos := one_pos
  port t := sidePort (E.hostSide h) t
  port_ne t := sidePort_ne _ t
  port_false_ne_true := sidePort_false_ne_true _
  holonomy _ := E.sideHol h hlin
  solid := germSolid S
  smooth := contMDiff_germSolid S
  mfderiv_bijective := bijective_mfderiv_germSolid S
  injective := germSolid_injective S
  collar t p s hs hs3 := germSolid_collar S t p s hs hs3
  cap_mem t w := germSolid_cap_mem S t w
  core_mem _ hy hc := germSolid_core_mem S hy hc
  image t q := germSolid_image S t q
  boundary_of_eq q q' he := germSolid_boundary_of_eq S q q' he

variable (E) (h)

theorem exists_sideData_proved (hlin : E.IsLinearSeam j)
    {T : SphericalTubeSystem Q.toClosedOrientedManifold} (hT : T = E.splitSeamTube j b h hlin)
    {N : ClosedOrientedManifold.{u} 3} (K : SphericalCapping Q.toClosedOrientedManifold N T)
    (a : T.Index) :
    ∃ δ₀ > (0 : ℝ), ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₀ → Nonempty (E.SideData h K a δ₂) := by
  subst hT
  exact exists_sideData_of_collarGerm
    (sideDataGerm fun t => Classical.choice (E.nonempty_sideCap h hlin K t))

end GC.Seifert.ElementaryPresentation
