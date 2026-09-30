# Full AC53: oriented orthogonal lines and their exact coordinates

Seventeen public theorems and one explicit definition in six leaves construct
an onto pointed Euclidean product from any finite ordered family of actual
orthogonal lines. The inputs are a proper metric space with global zero-curvature
four-point comparison, actual geodesic segments, and isometric maps gamma_j:R->X
through p with pairwise canonical positive-ray germ angle pi/2. No extra finite
dimension hypothesis is needed. Properness already supplies completeness.

The returned factor has the original ambient universe, actual inherited metric,
properness, completeness, nonnegative comparison and actual geodesic segments.
The onto product isometry satisfies, for ALL real signed parameters,

    e(p)=(0,z), e(gamma_j(t))=(t e_j,z),
    lineCoordinate(gamma_j)(x)=(e(x)).first(j),
    d(x,gamma_j(T))-T -> -(e(x)).first(j).

Thus its prescribed Euclidean coordinates are exactly the negative Busemann
functions of the original positive rays. Ordering and signs are fixed in the
statement; no rotation, permutation or orientation change is left unspecified.
The rank-zero construction is the canonical trivial Euclidean product with X.

Six shared crossing-line theorems use the accepted exact quadratic distance to
a complete line. Swapping the two actual lines proves reciprocal coordinates,
then lineCoordinate(gamma)(beta(t))=t*lineCoordinate(gamma)(beta(1)) for every
signed t. The exact two-line distance formula identifies each positive-arm
comparison angle, and its actual joint germ limit, with arccos of that slope.
A right angle therefore forces the whole second line into the actual zero slice.
These lemmas require no properness, geodesics or dimension assumption.

The explicit orthogonalLineInFactor is exactly t mapped to the original beta(t)
with its proved zero-coordinate membership. It preserves distances, basepoint
and every mutual germ angle. The canonical splitting evaluates as (0,x) on this
slice. Induction splits the LAST axis; explicit finSuccProdIsometry coordinate
and singleton formulas reassemble Euclidean coordinates in the prescribed order.
The remaining original lines recurse in that same zero factor with unchanged
parameters and geometry. The exact coordinate identity is then derived directly
from the defining distances at0 and1, rather than another asymptotic assumption.
The already proved line Busemann limit supplies the final sign and existence.

Source bodies checked: blueprint207A AC53 full4786-4833 and ALS02/03; KL
Asterisque365 Sublemma4.5(1), printed28-29/PDF23-24, surrounding definitions4.1/4.2
and Lemma4.4 through printed30/PDF25; BBI10.5.1-6 and proof printed366-369/PDF381-384.
The applicable retained KL May15,2015 sheet and BBI July6,2024 errata PDF13 were
freshly read by the independent reviewer. Their existing splitting corrections
are retained. There is no fresh remote-clearance claim. The new crossing-line
proof is an elementary consequence of accepted ALS02, a shorter alternative to
KL's product-geodesic Cauchy-Schwarz argument; it is not claimed to reproduce that
argument. Exact accepted dependency and Mathlib locators are in the receipt.

Independent proof review checked signed times, the actual germ filter, canonical
zero factors, all coordinate reassembly maps, positive singleton normalization,
rank0, inherited factor geometry and universe. Root reviewed the proof bodies,
implemented exact coordinate/Busemann closure, and runs combined acceptance.
AC53 is complete. Producing orthogonality from original cross-pair long-strainer
conditions (AC62-66) and downstream compatibility remain unfinished. Blueprint207,
earlier mathematical leaves and migration interfaces are unchanged.
