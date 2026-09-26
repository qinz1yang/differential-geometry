# Fill log A3: entry 18c, arms from a local bidirectional neck chain

## 2026-09-26

- New file `Topology/LocalNeckChainAxialArms.lean` (imports only `NeckChainAxialArms`). It has three
  theorems:
  - `FiniteHorn.mul_metricDistance_ge_of_neckChain`: for a chain segment `i < n`, the normalized
    distance satisfies `(√(1-ε)·L - 14)·(n-i)/2 ≤ √R(x)·d(c i, c n)`. It needs `R(c k) ≤ 4R(x)` on the
    segment. It cites `metricDistance_ge_of_separating_slices` and does not re-prove it.
  - `FiniteHorn.exists_minimizingArms_of_localNeckChain`: the chain is `c 0 … c (2m)` with centre
    `c m`. The hypotheses are the 18b step clause, the 18b separation clause (both restricted to
    `k < 2m`) and two-sided scalar comparability with the centre, inside the chain only. `hlong` is
    `2D ≤ (√(1-ε)·L - 14)·m`. The theorem gives the 18b arm data at `c m` with the same angle
    `arccos(9/2·14/(√(1-ε)L) - 1)`. The proof derives 18b's `hlow` and `hhigh` from the lemma above
    and then calls `exists_minimizingArms_of_neckNecklace` with `i₀ := m`.
  - `IncomingSlab.exists_strongNeck_threshold_of_localNeckChain`: accuracy `1/3000`, step `100`,
    `m₀(D) = D/40`, meaning the hypothesis is `D ≤ 40·m`. The comparison angle is `θ₀ = π/2`, the
    same as 18b. The only geometric input to the horn theorem is the local chain.
- Root finding: the 18b proof never uses the root. `c 0` is only the far end of the chain. The factory
  problem came from 18b's hypotheses (`hlow`/`hhigh` as distance clauses and the scalar clause over
  the whole chain), not from its argument. The 18b separation clause, quantified over all `i < k`, is
  already the local orientation-consistency clause, so it is kept unchanged.
- Scalar comparability: the new theorem adds the direction `R(c k) ≤ 4R(c m)`, which the chain-length
  lower bound needs (a step of normalized length `≥ √(1-ε)L/2`). 18b's direction
  `R(c m) ≤ 4R(c k)` is kept because 18b's step bound `√R·ℓ ≤ D` uses it. Both hold only within the
  chain.
- One-slab restriction kept: the threshold theorem is still stated on one `IncomingSlab` with
  `a ≤ t - θ/R`. The history version, with windows across an event, is a later brick.
- Compile: `LEAN_NUM_THREADS=2 lake env lean` on the file. The first attempt was blocked by a missing
  olean while a lead build was running. The retry 10 minutes later was clean, with no output. Axioms,
  checked on a scratch copy outside the repo: `propext`, `Classical.choice` and `Quot.sound` for all
  three theorems. Not registered in the root aggregate.
