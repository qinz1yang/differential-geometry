# Actual intrinsic extended distance from path variation

Fifteen public theorems and three definitions in two leaves construct the
actual induced intrinsic extended distance. intrinsicEDist(x,y) is the
infimum of Mathlib eVariationOn over ALL continuous unit-interval Path(x,y)
in the original topology. It is not an unconstrained distance input and
assumes neither geodesicity nor any comparison conclusion. Applying this
construction to a subtype takes paths in that actual region.

Exact path-variation identities prove reversal invariance and concatenation
additivity, with infinity allowed. The path extension to the real line has
the same variation on[0,1]. The induced distance dominates the original
edistance, vanishes on the diagonal, is symmetric and satisfies the triangle
inequality. In an original EMetricSpace it separates points. Its distance
is finite exactly when there is a finite-variation path, and absent paths
give infinity. Constant paths are present and explicitly have zero length.

intrinsicEMetricSpace constructs the extended metric and its generated
topology/uniformity. intrinsicMetricSpace gives the finite metric ONLY under
the explicit all-pairs finiteness hypothesis; exact edistance and distance
formulas are proved. These are explicit constructions, not global instances
that silently replace the original metric. No equality of the original and
induced topologies is claimed. If the original finite metric has the existing
actual-curve length property, the induced edistance equals the original one.

Source reading: BBI AMS2001 sections2.1.1-2.1.2 printed26-29/PDF41-44,
Definition2.3.1 and Proposition2.3.4 printed34-35/PDF49-50, section2.3.3 and
Proposition2.3.12 printed35-38/PDF50-53, Proposition2.4.1 printed38/PDF53.
These complete targeted pages were extracted and read. Retained July6,2024
author errata PDF1-3 were freshly read. They add admissibility/zero length
of constants to the length-structure definition, repair the lower
semicontinuity proof on printed35, and require finite-distance qualifications
in sections2.4-2.5. This construction explicitly includes constants and
retains infinity until finiteness is proved; it does not import the flawed
printed lower-semicontinuity argument. Existing Mathlib variation is used.

Mathlib Path.lean actual constant/reversal/concatenation and extension bodies,
BoundedVariation.lean partition definition, additivity and monotone/antitone
reparametrization proofs were read, as were the ENNReal infimum/addition and
finite-metric constructor bodies. Exact locators/hashes are recorded.

For AC13, the remaining work is finiteness on open balls, local equality
with the ambient metric and topology, and preservation of rectifiable path
lengths/continuity for the induced metric. Thus neither full AC13 nor full
ALG06 is claimed here. Earlier mathematical leaves and blueprint207 remain
unchanged; no PC migration interface is introduced.
