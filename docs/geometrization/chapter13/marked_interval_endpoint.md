# Finite intervals with the original marked height

Source checked: frozen Blueprint 207A, LFR43, `lem:collapse-strong-border-lift`, lines 28535–28618, particularly the finite-interval case D=C/r and the original coverage argument. Tracked snapshot SHA256: 277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b. This uses the project's expanded contract and retained source-check records. No fresh reading of the scanned KL Astérisque PDF or author errata is claimed.

MarkedIntervalTargetRescaling handles an actual KL approximation into [0,C] based at an arbitrary original marked point q, which need not be zero. It keeps the original source type and metric scaled by c, rebases at the chosen point a, and constructs the actual map to [0,cC] based at zero. The whole map sends a to zero and every other point x to c times f(x). There is no extension or truncation of the finite interval.

The hypotheses separately record the old source-test inclusion, old target coverage inclusion (including q's height), and the small-error budget. Coverage witnesses are proved to belong to the actual new source ball. The point repair is included in both distortion and target approximation. The proof even needs only one repair cost for distortion, because two distinct points cannot both equal a; the stated sufficient budget is 3c epsilon+c f(a)≤delta, the same budget used by the ray adapter.

The strong-edge specialization uses the original smallness hypotheses, c in [1/2,2], C>500Delta and the original upper bounds for the recentered source distance, marked height and f(a). It proves the strict endpoint inequality cC>200Delta and records the formula at every other point. It reuses the already proved RayRescalingBounds numerical domain/budget theorem; its ray-only endpoint conclusions are unnecessary here. No small-model tolerance depends on the separate splitting accuracy b_E.

Together with RayTargetRescaling, this completes the finite-interval and ray target adapters of LFR43 for arbitrary original marked height. Producing the actual border lift, residual-factor input map, and inherited geometric edge predicates remains a separate assembly obligation. The older zero-based IntervalTargetRescaling and all other accepted mathematical leaves remain unchanged.

Fresh silent builds/lints, canonical signatures, standard-axiom closure, concrete applications and the unchanged scoped gate are recorded in evidence/marked_interval_endpoint. The full migrated Poincare root is not claimed checked.
