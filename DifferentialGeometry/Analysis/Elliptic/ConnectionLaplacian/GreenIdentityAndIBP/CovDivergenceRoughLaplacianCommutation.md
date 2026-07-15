# Covariant divergence and rough-Laplacian commutation

## 2026-07-13 operator-field divergence rule

`covDiv_appCc` packages the divergence of an endomorphism applied to a covector
as the sum of the traced derivative of the endomorphism and the traced
passenger derivative.  It uses the existing positive trace-of-gradient
realization and `covGrad_appCc_eq`; no new geometric assumption is introduced.

Focused verification passed.  The first proof normal form repeated two
whole-Hom composition extensionality arguments and hit a deterministic kernel
timeout even in an isolated probe.  Replacing those repetitions by the
lower-layer `appCc_assoc` theorem made both the isolated probe and the full
source check pass.  The post-merge dependency cache was refreshed narrowly;
no independently claimed source was edited or force-released.
