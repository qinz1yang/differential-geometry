# JacobiRiccati notes

## 2026-07-18 scaled mean comparison

- Proved `mean_riccati_le` for a constant-speed radial curve. A Ricci lower
  bound with parameter `q` compares against the model parameter `q * a`, where
  `a` is the radial speed.
- Focused verification and the exported module refresh passed.
- This closes the scalar Riccati inequality used by the radial producer; it
  does not itself prove a volume-ratio theorem.
