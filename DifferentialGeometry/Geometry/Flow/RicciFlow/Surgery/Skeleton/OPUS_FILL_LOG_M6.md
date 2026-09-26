# M6 log (Crossing leaf: δmax ρmax εcap after qcan)

- `CrossingContinuation` now reads `∃ (Dcap θcap q₀ : ℝ) (mcap : ℕ), 0 < Dcap ∧ θcap < 1 ∧ 0 < q₀ ∧
  ∀ qcan, q₀ ≤ qcan → ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ ∀ qs, …` (same order
  as `CapWindowContinuation`; `Dcap θcap mcap` stay before `qcan`, since the cap leaf consumes
  `Dcap θcap` before its own `qcan`). Body unchanged.
- C3 assembly: crossing's `δx ρx εx` are now obtained at the common `qcan := max qfloor (max qd (max qw qx))`
  next to the cap leaf's; the `min` combination is unchanged. C3 definition, strong assembly and
  PoincareEndgame unchanged (C3 already binds `qcan δmax ρmax εcap` in one `∃`).
- Compile: Leaves via `lake env lean -o` into a hard-link mirror E:\m6-scratch-olean of
  E:\differential-geometry-pc3-lake\build\lib\lean (Leaves link replaced); PoincareEndgame and an
  axiom probe compiled with the toolchain `lean` and LEAN_PATH=mirror;… (`lake env` overrides LEAN_PATH,
  so it must not wrap the downstream call). Leaves clean (standard linter set on); PoincareEndgame:
  8 `sorry` warnings only. Axioms: C3 assembly and strong-of-leaves [propext, Classical.choice,
  Quot.sound]; smoothPoincareConjecture_holds adds sorryAx (via the 8 leaves). Mirror removed.
- Cbirth: `CrossingContinuation` needs no `Cbirth` binder (θcap/Θ and ρmax are the prover's choices;
  ρmax now follows qcan). What B5 needs is the republish of the supplier lemmas
  (`exists_standard_comparison_of_cap_window_trace`, and the B5 statements in
  TracedRegionOrCapWindow.lean:32/112/547/666 of shape `∃ c, 0 < c ∧ ∀ Θ, 0 < Θ → Θ < 1 → ∀ C : ℝ≥0,
  ∃ Cbirth, 0 < Cbirth ∧ …`) in the form `∀ C : ℝ≥0, ∃ c Cbirth : ℝ, 0 < c ∧ 0 < Cbirth ∧ ∀ Θ, 0 < Θ →
  Θ < 1 → …`, so the leaf fixes `Cbirth` from `Ctime` before choosing `Θ(T, Q)` and then sets
  `ρmax² ≤ min (Cbirth / (4·qcan)) (a₀ / 2)` after `qcan`.
