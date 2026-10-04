import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSurgery
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedCapBall

/-!
# The split move through the capped sides of the split sphere

Lane N2c. This module collects the tiers of the split move `MoveSplit` built on the sphere
surgery of `Seifert/MoveSplitSphere.lean`.

Tier 0 (`Seifert/MoveSplitCappedStandard.lean`): near a split seam the solid torus is a product
over the round disc `discPlanarBase 1` and the host a product over the round pants
`pantsPlanarBase`, with the piece collars equal to the standard radial collars on a sub-collar
(`ElementaryPresentation.exists_standardSplit`).

Tier 1 (`Seifert/MoveSplitCappedSphere.lean`): for a linear split seam, the split sphere
`D_a ∪ γ × S¹ ∪ D_b` (`ElementaryPresentation.splitSeamSphere`, a smooth embedding of the round
sphere) and its one-tube system `splitSeamTube` with that middle sphere. The tube is swept by
the meridian profiles of `Seifert/MoveSplitCappedProfile.lean` through the hemisphere and band
charts of `Seifert/MoveSplitCappedCharts.lean` and the model maps of
`Seifert/MoveSplitCappedModel.lean`, assembled in `Seifert/MoveSplitCappedTube.lean` from any
`SplitTube.SplitCharts` (the meridian discs, the fibre cylinder and the seam chart).

Tier 2, first step (`Seifert/MoveSplitCappedSurgery.lean`): the cut-cap transition along the
explicit split tube with the connected-sum dichotomy (`exists_splitSeamSurgery`), and the tube
avoids every piece other than the solid torus and the host (`tubeMap_ne_cutMap`).
Tier 2, caps (`Seifert/MoveSplitCappedCapBall.lean`): for any spherical capping, the cap and the
adjacent tube shell form one smooth ball chart reading the tube radially and untwisted on an
outer shell (`SplitTube.exists_capBall`, via the collar matching and Smale's theorem).
-/

set_option autoImplicit false
