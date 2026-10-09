import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.CanonicalConstantsC11RD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E

/-!
# Raising the shared canonical constants of the enhanced tuple (C12X, S16F G5)

R-S16 Q5 §2: the uniform pair `C1* C2*` of S16 must be fixed before the natives, and the enhanced
tuple (`a12Enhanced_of_chain_C11P2`, `hext`) quantifies `∃ ε C1 C2` once for four supplies that
share the pair: S4 `CanonicalConstantsSupply_C11S`, S5 `HistoryCanonicalSupply_C11S`,
S15 `LargerBallCanonicalLateSupply_C11E`, S16 `StrongCanonicalSupplyV2_C11E`.  Every one of them
is stable under raising `C1 C2` (`SpatialCanonicalWitness.enlargeConstants`; for S16 the neck
alternative and the strong-neck data do not see `C1 C2`).

* `historyCanonicalSupply_mono_C12X`, `largerBallCanonicalLateSupply_mono_C12X`,
  `strongCanonicalSupplyV2_mono_C12X` : monotone transport
  (S4 already: `canonicalConstantsSupply_mono_C11RD`).
* `sharedCanonicalSupplies_max_C12X` : S4/S5/S15 at `(C1, C2)` and S16 at `(C1s, C2s)` hold together
  at `(max C1 C1s, max C2 C2s)` — the single common pair `hext` needs.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

/-- S5 is stable under raising `C1 C2`. -/
theorem historyCanonicalSupply_mono_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {ε C1 C2 C1' C2' : ℝ}
    (h : HistoryCanonicalSupply_C11S F ρ ε C1 C2) (h1 : C1 ≤ C1') (h2 : C2 ≤ C2') :
    HistoryCanonicalSupply_C11S F ρ ε C1' C2' := by
  intro n t x hx
  obtain ⟨W, hW⟩ := h n t x hx
  exact ⟨W.enlargeConstants h1 h2, hW.enlarge_constants h1 h2⟩

/-- S15 is stable under raising `C1 C2` (same `K₁ T`). -/
theorem largerBallCanonicalLateSupply_mono_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 C1' C2' : ℝ}
    (h : LargerBallCanonicalLateSupply_C11E F ε C1 C2) (h1 : C1 ≤ C1') (h2 : C2 ≤ C2') :
    LargerBallCanonicalLateSupply_C11E F ε C1' C2' := by
  intro A hA
  obtain ⟨K₁, T, hK₁, hT, hS⟩ := h A hA
  refine ⟨K₁, T, hK₁, hT, fun s hs p r hr hpc hvol y hy hK => ?_⟩
  obtain ⟨W, hW⟩ := hS s hs p r hr hpc hvol y hy hK
  exact ⟨W.enlargeConstants h1 h2, hW.enlarge_constants h1 h2⟩

/-- S16 (v2) is stable under raising `C1 C2`: the strong-neck data do not involve `C1 C2`. -/
theorem strongCanonicalSupplyV2_mono_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {ε C1 C2 C1' C2' : ℝ}
    (h : StrongCanonicalSupplyV2_C11E F ρ ε C1 C2) (h1 : C1 ≤ C1') (h2 : C2 ≤ C2') :
    StrongCanonicalSupplyV2_C11E F ρ ε C1' C2' := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun s hs x hR => ?_⟩
  obtain ⟨W, hW, hn⟩ := hT s hs x hR
  refine ⟨W.enlargeConstants h1 h2, hW.enlarge_constants h1 h2, fun nk hnk => ?_⟩
  change W.alternative.monoConstant (zero_lt_one.trans_le W.one_le_comparison_constant) h2
    W.Q_pos.le = SpatialCanonicalAlternative.neck nk at hnk
  cases halt : W.alternative with
  | neck data => exact hn data halt
  | cap data deep =>
    rw [halt] at hnk
    cases hnk
  | positive whole data sec =>
    rw [halt] at hnk
    cases hnk
  | round whole data =>
    rw [halt] at hnk
    cases hnk

/-- **One common pair for `hext`**: the astra supplies S4/S5/S15 at `(C1, C2)` and an S16 supply
at `(C1s, C2s)` (e.g. the uniform `C1* C2*` of `strong_necks_full_uniform_of_window_C12X`) hold
simultaneously at `(max C1 C1s, max C2 C2s)`. -/
theorem sharedCanonicalSupplies_max_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {ε C1 C2 C1s C2s : ℝ}
    (h4 : CanonicalConstantsSupply_C11S ε C1 C2) (h5 : HistoryCanonicalSupply_C11S F ρ ε C1 C2)
    (h15 : LargerBallCanonicalLateSupply_C11E F ε C1 C2)
    (h16 : StrongCanonicalSupplyV2_C11E F ρ ε C1s C2s) :
    CanonicalConstantsSupply_C11S ε (max C1 C1s) (max C2 C2s) ∧
      HistoryCanonicalSupply_C11S F ρ ε (max C1 C1s) (max C2 C2s) ∧
      LargerBallCanonicalLateSupply_C11E F ε (max C1 C1s) (max C2 C2s) ∧
      StrongCanonicalSupplyV2_C11E F ρ ε (max C1 C1s) (max C2 C2s) :=
  ⟨canonicalConstantsSupply_mono_C11RD h4 (le_max_left _ _) (le_max_left _ _),
    historyCanonicalSupply_mono_C12X h5 (le_max_left _ _) (le_max_left _ _),
    largerBallCanonicalLateSupply_mono_C12X h15 (le_max_left _ _) (le_max_left _ _),
    strongCanonicalSupplyV2_mono_C12X h16 (le_max_right _ _) (le_max_right _ _)⟩

end GC.LongTime.Ch11

end
