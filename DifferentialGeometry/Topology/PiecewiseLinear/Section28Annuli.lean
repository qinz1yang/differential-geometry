/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsAnnulusParametrizationOfProductCircleCut
import DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates

/-!
# A producer skeleton for annuli between essential polygons on a solid torus

The endpoint is the existing `Moise286`, with the ambient closure of each actual connected
component and the original two polygon labels. Moise, printed p. 204 (PDF p. 214), first uses
Theorem 28.3 to put the finite polygon family in standard position. He then recognizes bands
crossing the cylindrical diagram, excludes a Mobius band using orientability, and treats the
latitudinal case separately.

This skeleton proposes a stronger common product-coordinate formulation of the first step.
It is not the literal statement of Theorem 28.3. Producing the boundary PL torus chart and
simultaneously straightening all essential polygons to distinct fibers is the main geometric
obligation. The chart concerns the boundary only; an extension over the solid torus is not
asserted. A proof must establish the parallelization without using `Moise286`, and must justify
the use of the frozen no-PL-disk hypothesis, rather than assume a surface classification.

Leaves, both owned by the PL surface lane:
* `exists_product_coordinates_for_disjoint_essential_polygons`: simultaneous boundary
  coordinates and distinct labeled fibers for the whole finite family; reviewed OK, frozen, proof
  OPEN.
* `exists_annulus_parametrization_of_product_circle_cut`: recognize a component of the product
  model cut along finitely many fibers, with the precise two endpoint images; reviewed OK, frozen,
  proof OPEN.

The second leaf has no solid-torus or essential-polygon hypotheses. Its remaining work is to
find the two neighboring marked points on the second PL circle, identify the product component,
and transport its ambient closure. `n > 1` and injectivity of the marking prevent one circle
from being used for both ends. The indices are not presumed to be in cyclic order. Both PL
circles and all marked points are tied to the single coordinate map supplied by the first leaf.

Existing inputs inspected: `CircleArcs.lean` supplies
`exists_arc_decomposition_of_isPLSphere_one`, with PL arcs between two specified points.
`IsPLHomeomorphOn.prodMap` and `IsPLHomeomorphOn.image_closure` supply product and closure
transport.
`AnnulusCylinder` already recognizes an interval cylindrical diagram as an annulus, with
orientability excluding the twisted case. No replacement for that classification is introduced.
`AnnulusComplement`, `AnnulusComponents`, `SurfaceAnnulusComplement` and `SurfaceCircleComplement`
provide collars, surface complements and component control, but not simultaneous polygon
coordinates or the finite-cut endpoint parameterization. `TorusMeridian` provides an embedded
example, not a producer for every combinatorial solid torus.

The first review and lead due diligence are recorded in
`consult/BB-section28-annuli-first-review-digest.md`. Both statements and the assembly are
unchanged. The first leaf still owes boundary PL recognition, the no-disk-to-essential bridge,
and compatible relative straightening of the whole family. The proof of 28.9 may be used
independently of 28.6; the converse use of 28.7 would be circular.

Joint fixture: UNTESTED. A proposed nondegenerate instance is the square solid torus
`1 <= max (abs x) (abs y) <= 3`, `abs z <= 1`, with the two rectangular meridians in `y = 0`
on the positive and negative x sides. The shared PL product chart, combinatorial-solid-torus
witness and no-disk witnesses have not been formalized. In particular, this description is not
a joint satisfiability certificate. The reviewed paper fixture uses eight triangulated trapezoidal
blocks and two circle labels;
its radial seams preserve those labels, but continuous radial multiplication is not a PL map.
The `n = 2` case and arbitrary label order are retained.

The assembly is proved from the two leaves. Its transitive axiom closure still contains
`sorryAx`; the named input remains open until both reviewed producers are proved in real modules.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-22 with a zero-diagnostic
check and an axiom audit; statement byte-identical with the frozen leaf):
`exists_annulus_parametrization_of_product_circle_cut`, with the new helper
`IsPLSphere.exists_arc_between_adjacent_marks`.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-22 with zero-diagnostic checks
and an axiom audit; statement byte-identical with the frozen leaf):
`exists_product_coordinates_for_disjoint_essential_polygons` (module
`EssentialPolygonProductCoordinates`, over `PrismLateralCircleSides` — a non-bounding PL circle
in the open lateral annulus of the prism splits it into two annulus charts — and
`LateralAnnulusLevels`, the annulus chain: finitely many disjoint such circles become levels of
one boundary-preserving PL self-map).  Route: 28.9 and `hess` make `G 0` nonseparating, its
annulus complement carries the other circles as levels, the annulus chart plus bicollar is a
cylindrical diagram whose end map preserves orientation (`MobiusEmbedding`), the pseudo-isotopy is
squeezed into the top slab to remove the twist, and `exists_isPLHomeomorphOn_of_eq_endMap` gives
the product chart.  With this leaf proved the file has no `sorry` and was promoted from `Skeleton/`
to a real module on 2026-09-22: `moise286 : Moise286` is unconditional.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem moise286 : Moise286 := by
  classical
  intro S hS n G hn hG hGS hdisj hess x hx
  obtain ⟨J, Q, f, q, hJ, hQ, hf, hq, hinj, hfamily⟩ :=
    exists_product_coordinates_for_disjoint_essential_polygons hS G hn hG hGS hdisj hess
  have hG_eq : G = fun i => f '' (J ×ˢ {q i}) := funext hfamily
  rw [hG_eq] at hx ⊢
  obtain ⟨i, j, hij, ρ, hρ, hzero, hone⟩ :=
    exists_annulus_parametrization_of_product_circle_cut hJ hQ hf hn q hq hinj hx
  exact ⟨i, j, hij, J, ρ, hJ, hρ, hzero, hone⟩

end DifferentialGeometry.Topology.PiecewiseLinear
