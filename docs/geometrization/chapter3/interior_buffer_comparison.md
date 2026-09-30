# ALG05: comparison inside a complete interior buffer

Four public theorems in two leaves prove ALG05 with the exact project
constant 20. A locally compact metric space has the explicit length property:
continuous unit-interval curves between every pair with variation less than
distance plus every positive epsilon. Every point has a local open four-point
comparison neighborhood for the SAME metric, with kappa>=0 representing
curvature -kappa. Only closedBall(o,L) is required complete. No ambient
CompleteSpace instance or all-pairs minimizing-segment hypothesis is used.

Every supplied actual MinimizingHinge with first endpoint o and arm sum
less than L/20 satisfies the model-side bound, including zero arms.
Positive arms give comparison angle <= the SAME hinge's canonical germ angle.
The endpoint-property theorem quantifies all supplied positive-arm germs and
preserves them through the accepted germ adapter. No positivity restriction
on L is necessary in the API: nonpositive L makes the positive-arm premise
empty; positive relevant arm sums force L>0.

The proof uses capped comparison radii and epsilon=1/4 almost minimization.
The selected point satisfies d(p*,o)<=16r0 and r*<=r0<L/20. With
ell=17r*/16, d(p*,o)+3ell<= (16+51/16)r0<20r0<L. Completeness transfers to
that closed ball. The existing LocalHopfRinow proof supplies actual minimizing
curves between points of B(p*,ell), lying in B(p*,2ell). The new isometric
segment adapter applies the earlier rescaling theorem inside that ball's
subtype, preserving the complete range and zero-length case. The same
cradle enlargement and supremum contradiction as ALG04 then apply.

This uses the ambient length property and complete buffer to produce joins;
it does not assume a closed ball is a length space. The fixed constant20
is the blueprint's sufficient bound, not KL's sharper2D criterion.

Sources actually checked: blueprint207A ALG05 full statement/proof7486-7534,
including the recentered complete-ball arithmetic and compact-curve step;
accepted LocalHopfRinow.lean full1-251, HopfRinow.lean full1-113 and
SegmentConcatenation.lean full1-137. Pinned AKP vol1
ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245 defs-CBB.tex951-1218 and the retained
July12,2026 errata checks are reused for the unchanged cradle/almost-minimum
route. Revision140's source comparison keeps the20 and256 project constants
distinct from quoted source results. Exact hashes/locators are recorded.

ALG06 intrinsic/ambient transfer, endpoint-free global recognition and uniform
covering production remain open. Blueprint207 and earlier mathematical leaves
are unchanged; Chapters3-4 and the PC migration are not claimed complete.
