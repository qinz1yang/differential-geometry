# PerpFrame notes

## 2026-07-08

- Added `exists_time_clip`, a reusable smooth bounded time reparametrization
  equal to the identity on `Icc 0 L`.  It is the low-layer smooth-extension
  brick needed when a downstream curve is only controlled on a compact time
  interval but an existing frame API asks for a globally smooth time parameter.
- Verification passed for the focused file check and the targeted module
  refresh.  The remaining volume-comparison frontier is downstream: use this
  time clip to build either a global smooth radial extension that stays inside
  the exponential smoothness radius, or localize the parallel-frame API to
  `Icc 0 b`.

- Added `exists_time_window_clip`, the same cutoff-times-identity idea but for
  any closed window strictly inside `(-lam, lam)`.  This is the stronger brick
  needed for endpoint-safe transport: downstream curves can agree on a
  neighborhood of `Icc 0 b`, not merely on the closed interval itself.
  Verification passed.  The downstream volume bridge consumed it through
  `RadialGronwall.exists_rclip_nbhd`.

## 2026-07-18 positive-speed perpendicular frame

- Added `exists_perp_pos`, producing the required perpendicular orthonormal
  family along a positive-speed curve while retaining the existing local-frame
  conventions.
- Focused verification and the exported module refresh passed.
- The result is consumed by the assembled radial comparison producer; it does
  not resolve the global cut-locus transfer.
