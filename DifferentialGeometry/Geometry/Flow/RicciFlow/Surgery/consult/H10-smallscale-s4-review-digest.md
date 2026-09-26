# Review H10 (single statement: S4′, spatial witness ⇒ ball volume lower bound), digested

Date: 2026-09-26. Reviewer: GPT, on `codex/pc-consult-j` @ 48aed2c67 (`DESIGN_SMALLSCALE.md` §3 S4, §6.3 S4′),
not compiled. Overall: **S4 (non-round) and S4′ hold in the compact-stage setting with `κ = κ(ε, C1, C2)`;
the listed proof route is FIX and must not be assembled as written.**

| Item | Verdict | Content, checked by the lead |
|---|---|---|
| (b) radius constant | OK | With `Q = R(x)`, `N = ‖Rm‖²(x)`: in 3D `scalar_abs_le_rm` gives `Q ≤ 9√N`, so `r⁴N ≤ 1 ⇒ Qr² ≤ 9 ⇒ r ≤ 3Q^{-1/2}` (`BallVolume.lean` already proves it this way; do not misremember it as a coefficient-3 estimate). |
| neck | OK | `exists_pos_mul_cube_le_spatialNeck_ball_volume_of_curvature_bound`; `SpatialNeck` carries `ε < 1/11`. |
| positive / (c) | OK, align radii | Finite Riemannian distance means a connecting curve, so a finite ball stays in the component: `B(x, r) ⊆ U`. The witness gives `C1, C2 ≥ 1`; take the outer radius `L = 3C1·Q^{-1/2}` covering both `U` and `r`; BG with `Ric ≥ 0` gives `κ_pos = 1/(27C1³C2)`. |
| cap / (a) | holds; boundary fields suffice | `outer_boundary` and `tube_eq` give `∂U ⊂ tube`. `10⁴ ≤ D√Q < 2C1` only forces `C1 > 5000` for a nonempty cap. The neck centre `v ∈ tube ⊂ U`, so `Q/C2 ≤ Q_v ≤ C2·Q`; `s = (2√Q_v)⁻¹` is legal; the normalized-ball theorem needs `|z₂| + 1/2 ≤ 3/2 < ε⁻¹`. More robust capture: any curve leaving `U`, after its last crossing of the inner boundary, must traverse the neck tube from axial coordinate `0` to `1`, costing length `≥ √(1−ε)·Q_v^{-1/2} > s`, having already spent `≥ D`; hence `B(x, D+s) ⊂ U` with no curvature control outside the chart (obligation: formalize the first-exit / last-crossing argument). |
| cap, illegal S3 call | FIX | Calling the current S3 at `L = D + s` violates its input: `L⁴N(x) ≥ 10¹⁶/81 > 1`. Use the general BG with `Ric ≥ −a·C2·Q·g`; with `L√Q ≤ 2C1 + √C2/2` and `vol B(w, s) ≥ ν/(8C2^{3/2})·Q^{-3/2}` the comparison constant depends only on `C1, C2`. |
| round | OK, interface | R1's delivered constant is `4√3π·Q^{-3/2}`; the design's R2 additionally assumes `ε < 1/11`, which a round witness does NOT guarantee: S4′ should use R1, `W.rm_bound` and the general negative-Ricci BG directly, adding no hypothesis. |
| (d) counterexamples | none for the full statement | "Small `U`, ball overflows" fails: the cap target radius is `< D`, positive/round are whole components. Lens-space volumes `→ 0` refute only the version that drops simple connectivity while admitting round; S4 excludes round, S4′ excludes that configuration. |

Decision: S4′ (and S4) to proof with: general Ricci-lower-bound BG in the cap and round cases (no S3 call at
`D + s`), the last-crossing capture `B(x, D+s) ⊂ U`, `L = 3C1·Q^{-1/2}` in the positive case, R2 without
`ε < 1/11`.
