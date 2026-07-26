# CoordinateTowerRegularity

## 2026-07-14

- `coordTowerSmooth` is the narrow assembly of the existing coordinate-frame
  Christoffel producer, the level-zero Riemann producer, and the pure recursive
  tower regularity engine.
- It proves joint spacetime `C-infinity` regularity for every finite
  `iteratedRmComp` level at regular points in `chartLeviCivitaGoodSet`.
- This theorem does not prove the mixed time/space derivative swap used by Shi
  and does not transfer the tower to an arbitrary orthonormal local frame.
  Those remain separate downstream producers.
- Focused verification passed without warnings. The theorem is complete; the
  downstream mixed derivative swap and arbitrary-frame transfer remain
  separate, unfinished theorems.

## 2026-07-19

- `coordTowerSmooth` no longer assumes `[CompactSpace M]`.  The recursive
  proof is pointwise and now consumes the correspondingly weakened
  coordinate-Riemann base API.
- Focused and targeted verification passed.  This closes only the noncompact
  regularity transport; it does not prove `exists_rmTowerSol`.
