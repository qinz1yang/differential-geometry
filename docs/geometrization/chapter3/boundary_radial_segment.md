# Full AC62: actual radial geodesics to the boundary sphere

Two public theorems produce an actual isometric segment from p to the specified
endpoint a. The original-input theorem assumes a complete finite metric space,
arbitrarily short continuous curves between every pair, L>0, local compactness
of the OPEN ball B(p,L), and dist(p,a)=L. Its segment is defined on [0,L], starts
at p and ends exactly at a. No local compactness at a, no compactness of the
closed L-ball, and no global properness is assumed.

The shared auxiliary needs only compact closed balls of all radii strictly below
dist(p,a), and arbitrarily short curves from that ONE p to that ONE a. It does
not require completeness or local compactness elsewhere. It includes p=a.
Actual AC58 short-curve prefixes q_n:[0,dist(p,a)]->X are used, with positive
errors 1/(n+1). A SINGLE ultrafilter below atTop is fixed for all parameters.
Every interior time lies in its own compact strictly smaller centered ball.
At the final time, the actual remaining-distance estimate gives q_n(L)->a
directly. Thus the endpoint limit does not use a missing compactness hypothesis.
Passing both upper and lower pairwise distance estimates through this same
ultrafilter gives an isometry on the entire closed interval. Uniqueness of limits
identifies the exact basepoint and endpoint.

This is an alternative to the blueprint rational diagonal and completion
extension. No lower-semicontinuity theorem, dense-extension completeness premise,
or ordinary subsequence at every time is silently imported. The original-input
wrapper gets the strictly smaller compact balls from the accepted local
Hopf-Rinow theorem, whose use of completeness is explicit.

Fresh source bodies: blueprint207A AC62 full5276-5301; BBI natural
parametrization2.5.7/9 printed45-46/PDF60-61; Proposition2.5.22 statement
printed49/PDF64 and full proof49-50/PDF64-65. The latter precise locator corrects
a looser historical50-51 locator. Retained July6,2024 BBI errata PDF2 supplies
the finite-metric qualification and PDF3 the natural-length correction. The
accepted LocalHopfRinow116-122 and ShortCurvePrefix proofs are inspected and
reused. No current remote errata clearance or wider book audit is claimed.

One agent implemented the proof; another independently inspected the actual
ultrafilter, boundary and compactness uses and prepares concrete integration.
Root reviewed the statements and proof and runs the combined checks. AC62 is
complete. Original long-strainer orthogonality must use these SAME minimizing
segments for both angle passage and coordinate extraction. The upcoming AC63
numerical first shortening and ALG08 L/1024 buffer route remain separate.
Blueprint207, earlier mathematical leaves and migration interfaces are unchanged.
