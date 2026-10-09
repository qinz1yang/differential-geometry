import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSideDataGerm
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSideDataAdapter

/-!
# The side data of a mixed split (ledger item N4 in mixed form, proved)

Lane N2f, tier 2. For a linear split seam of a mixed stage `σ`, a split datum `SD` and a spherical
capping `K` along the split tube `σ.splitSeamTube SD hlin`, choose for each side the ball chart and
the cap filling (`nonempty_sideCap`). The two solid tori `germSolid` with the ports `sidePort`, the
holonomy `sideHol`, the collar germ `η = 1/3` and the collar width `δ* = 1` form a mixed
`SideDataGerm` (`sideDataGerm`); the radius-three disc compression turns it into `SideData` for
every collar height `0 < δ₂ ≤ δ₀`. This proves `ExistsMixedSideData`
(`existsMixedSideData_proved`), and through `exists_sideData_of_existsMixedSideData` again the
elementary statement.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

universe u

namespace GC.Seifert.RelativeNormalization

namespace MixedStage

open SplitTube

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q}
  {j : Fin σ.toTorus.pairing.count} {b : Bool} {h : σ.IsSplitSeam j b} {SD : σ.SplitData h}
  {hlin : σ.IsLinearSeam j} {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N (σ.splitSeamTube SD hlin)}

def sideDataGerm (S : ∀ t, σ.SideCap h SD hlin K t) : σ.SideDataGerm SD K () where
  η _ := 1 / 3
  η_pos _ := by norm_num
  δ_star := 1
  δ_star_pos := one_pos
  port t := sidePort (σ.hostSide h) t
  port_ne t := sidePort_ne _ t
  port_false_ne_true := sidePort_false_ne_true _
  holonomy _ := σ.sideHol h SD hlin
  solid := germSolid S
  smooth := contMDiff_germSolid S
  mfderiv_bijective := bijective_mfderiv_germSolid S
  injective := germSolid_injective S
  collar t p s hs hs3 := germSolid_collar S t p s hs hs3
  cap_mem t w := germSolid_cap_mem S t w
  core_mem _ hy hc := germSolid_core_mem S hy hc
  image t q := germSolid_image S t q
  boundary_of_eq q q' he := germSolid_boundary_of_eq S q q' he

end MixedStage

theorem existsMixedSideData_proved : ExistsMixedSideData.{u} := by
  intro Q σ j b h SD hlin T hT N K a
  subst hT
  exact MixedStage.exists_sideData_of_collarGerm
    (MixedStage.sideDataGerm fun t => Classical.choice (σ.nonempty_sideCap h SD hlin K t))

end GC.Seifert.RelativeNormalization
