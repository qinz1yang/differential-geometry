# Endpoint small-hinge comparison and its actual cradle consumer

Four public theorems and one definition in two leaves make the endpoint-
based comparison assumption of ALG01/02 explicit and usable. The property
endpointHingeComparison kappa p r quantifies over EVERY specified pair of
minimizing positive-length germs with common center, first endpoint p, and
sum of arms less than r. It asserts the actual endpoint comparison angle
is bounded by their canonical joint germ angle. There is no selected chart,
chosen hinge, assumed output angle, or completeness requirement in the
property. Curvature is -kappa, with kappa>=0 in the geometric theorems.

The property is monotone in radius. A local open four-point neighborhood
produces one positive radius a such that EVERY endpoint q in B(p,a)
satisfies endpointHingeComparison kappa q a. The SAME a is used for endpoint
neighborhood and hinge arm-sum bound. The model-side consumer proves the
actual opposite-side lower bound from this comparison property; it derives
the triangle window from the two supplied radial identities.

The cradle consumer takes the actual original joins eta:[0,d(x,u)] -> X,
sigma:[0,d(x,v)] -> X and the new join tau:[0,d(sigma(h),u)] -> X. Each is
a supplied isometry with its exact endpoints. Both auxiliary hinges must
have arm sums below r, as proved for the chosen h in the preceding metric
cradle construction. The new center is interior to sigma and distinct from
u. Endpoint comparison at u now PRODUCES both short comparison inequalities.
Local four-point comparison at the new center produces the adjacent bound,
and the actual new model side is no greater than the original. No scalar
short-angle inequalities are assumed in this theorem.

The implementation uses the SAME original sigma for its forward/backward
parts and retains the actual original eta and chosen tau. Other endpoint
and small-hinge stopping cases are handled by earlier consumers. Assembling
all cases, sorting actual hinges, constructing an infinite sequence and
final globalization remain open. This milestone does not claim full ALG02.

Sources: unchanged source-checked blueprint207A ALG01/02 bodies7264-7415,
especially endpoint-based uniformity7331-7337 and the two short hinges7353-
7389; pinned AKP vol1 ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245
 defs-CBB.tex307-386,951-1090. These exact passages and source/errata version
comparisons were checked in the preceding milestones and are reused. The
new endpoint property follows the frozen blueprint's specified minimizing
germs and positive arms; degenerate stopping cases remain separate. Exact
source hashes and evidence links are in the source record.

Blueprint207, previous mathematical leaves and PC migration interfaces remain
unchanged. Endpoint-free recognition, intrinsic adaptation and uniform
curvature-to-covering production remain open.
