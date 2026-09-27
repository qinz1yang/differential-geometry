# X2 — Crossing room missing step (2026-09-26)

New file `Topology/BackwardTraceDistortion.lean`: compiles clean read-only
(`LEAN_NUM_THREADS=2 lake env lean`, 0 diagnostics); `#lint` (14 linters) clean on a scratch copy;
axioms propext/choice/Quot.sound for all public theorems. No sorry, no set_option overrides.

Public theorems (namespace `...Surgery.Topology.RetainedCoreHistory`, event-slab case
`activeStage t = i.castSucc`; final slab not covered):
- `exists_cap_capture_of_ball_point_without_trace`: z ∈ B_t(y,r) untraceable to activeStage u ⇒
  latest failing event j*, captured ball point zs (trace from j*.succ, no crossing at j*, lands at
  window xc with ‖xc‖ ≤ transitionEnd), y's trace lands at window x with ‖x‖ < Dcap,
  d_{g(j*.succ)}(window xc, y@birth) ≤ exp(9Λ(t−u))·r, scale ≤ 4M, scale·(t − birth) ≤ 4M(t−u);
  Λ = 8√3(1+φ1+φ0)M.
- `capWindowPoint_of_ball_point_without_trace`: corollary, adds `4M(t−u) ≤ θcap`.
- `exists_parabolicallyRmControlledBall_or_capWindowPoint`: room lemma, r = c/√R, M = 4R;
  `16c² ≤ θcap`, `2·transitionEnd + √32·c·exp(288√3(1+φ1+φ0)c²) < Dcap`.
Constant conditions: `p.modelAccuracy ≤ 1/2` (all the closeness step needs; closeness is used only
on ‖x‖ < Dcap), core radius `Dcap ≤ Dstar ≤ p.modelRadius`,
`2·transitionEnd + √(8M)·exp(9Λ(t−u))·r < Dcap` (forces transitionEnd < Dcap).

Duplicate for the lead to merge: public `Geometry.Metric.riemannianEDistOf_restrictOpen_lt_of_
riemannianBallOf_subset` plus a private copy of the private
`riemannianEDistOf_restrictOpen_le_pathELength` of `Geometry/Metric/RestrictionDistance.lean`;
both belong in RestrictionDistance.
Ingredient (2): the transition is used only as a regular-crossing local isometry (survivor map);
no isometry of the retained core outside the window is claimed or needed.
