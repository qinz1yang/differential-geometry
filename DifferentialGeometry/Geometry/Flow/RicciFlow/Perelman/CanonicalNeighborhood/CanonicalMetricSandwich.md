# CanonicalMetricSandwich

SOURCE-ONLY/UNCHECKED, following the book's buffered-canonical domain transport.
Claim bbcb76bc-0e72-48d5-b160-85d62e225498. The shared dead foreign
elaboration lock is not bypassed.

First prove an actual image-ball upper bound from the differential metric
upper bound, using arbitrarily short smooth paths and showing every prefix
stays in the controlled reference ball. Combine this with the existing
CrossModelBallCapture first-exit lower bound on a compact inner ball to obtain
the actual image domain's two-sided ball sandwich. The strict radius condition
then gives a positive factor-two reserve in the source.

Reuse CollarMetricControl.metricPathELength_map_le and the actual
CompactDomain.map constructor. All metric comparisons are on explicitly
contained sets; no global Lipschitz map or source Toponogov is assumed.
This step does not prove higher-jet, volume or neck/cap stability and does not
choose a uniform tolerance over the ancient model family.

Two public declarations, both SOURCE-WRITTEN/UNCHECKED. This imports the new
CompactDomainTransport, which must be independently checked and refreshed
first. The compact inner ball is obtained as a closed subset of the existing
compact domain; no extra complete or proper metric hypothesis is introduced.
The two length factors A and L give source radii a/A and L*b. Their strict
inequality L*b<2*(a/A) gives a positive source margin by elementary arithmetic.
