# Segment germs and one-step cradle comparison

Ten public theorems in three leaves give exact metric formulas for the
existing Mathlib IccExtend of a supplied isometry segment, the adjacent
angle bound for its actual opposite parts, and one-step model-side comparison.
No new segment or angle representation is introduced.

The six metric formulas preserve all interval points and prove the radial,
within-arm and opposite-arm distances for t -> IccExtend sigma(h+t) and
 t -> IccExtend sigma(h-t). Both ends and zero parameters are included.
The canonical germ-angle theorem takes any third specified minimizing germ
at an interior point sigma(h) of the supplied segment, together with one
open comparison neighborhood there. It derives the adjacent angle sum <=pi.
The full arms need not stay in this neighborhood.

The comparison consumer now DERIVES the adjacent inequality from these
actual segment germs and local four-point comparison. It assumes the two
short-triangle comparison inequalities explicitly, then proves nonincrease
of the actual model-side function. A metric consumer uses the same x,u,v,
chosen segment sigma and new center sigma(h). It derives the short-triangle
side window and the exact remaining arm length from metric triangle
inequalities and the supplied isometry, so they are not extra scalar
assumptions. The endpoint stopping inequality is also proved directly from
metric betweenness, including zero arms and arbitrary angle in [0,pi].

The short-triangle comparison hypotheses have not yet been produced from
the all-small-hinges assumption in ALG02. The consumers allow an arbitrary
old germ and require only the stated radial/minimizing properties for the
third new germ; intended endpoint joins supply these properties. Full
geometric state construction, sorting, finite stopping/infinite iteration
and final globalization remain open. These leaves do not establish ALG02.

Sources actually used: blueprint207A ALG01/02 bodies7264-7415, especially
opposite germs7294-7337 and geometric step7353-7400; pinned AKP vol1
ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245 defs-CBB.tex307-386 and951-1090.
These unchanged passages were read in the preceding milestone and their
source checks are reused. Mathlib Order/Interval/Set/ProjIcc.lean42-60,
159-248 and Topology/Order/ProjIcc.lean1-68 were freshly read: IccExtend
is the actual interval projection extension, with exact values on the
interval. Source hashes and pin are in the accompanying source record.
Existing errata/source-version comparisons are unchanged and reused.

Blueprint207, previous mathematical leaves and PC migration interfaces are
unchanged. Endpoint-free recognition, intrinsic adaptation and uniform
curvature-to-covering production also remain open.
