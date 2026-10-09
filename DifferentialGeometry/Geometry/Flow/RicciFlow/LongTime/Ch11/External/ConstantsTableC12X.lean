import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStatePortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNeckFullLeafDefsC12X

/-!
# Constants compatibility table (C12X, S-C12X-CONST G2)

Lean mirror of `docs/geometrization/chapter8/out/CH12X-CONSTANTS-TABLE.md`: the pairs and the
inequalities that the P6 line quotes when it takes a `max`.  Everything here is arithmetic on
reals; no analytic input.  Notation (`C : ClosedBirthConstants`, `ε = C.epsilon`):

* `εStrong_C12X ≤ coneAccuracy, crossingStrongEpsW_C12X, crossingNeckAccuracy,
  crossingWindowNeckAccuracy` (`le_εStrong_C12X_iff`);
* S16B per-native pair `C1h = max C1 (max Cs Cx)`, `C2h = max C2 (max (max Cs Cgrad) Cx)`
  (`StrongNeckFullClassC12X:75`);
* S16F uniform pair `Ccore = max Cs₀ Cx`, `C1S = max C.C1 (max Ccore Cu)`,
  `C2S = max C.C2 (max (max Ccore Cu) Cgrad)` (`StrongUniformClassC12X`);
* astra pair `C1⁰ = max C.C1s C.Cbirth`, `C2⁰ = max C.C2s (max C.Cbirth Cgrad)`
  (`SupplyFourOfClosedBirthC11A:25`) and the shared pair `C1* = max C1⁰ C1S`,
  `C2* = max C2⁰ C2S` (`sharedCanonicalSupplies_max_C12X`);
* P6 primed constants for the `C(ε)` of the P6 main form (`goodConstants_accommodate_P6P`):
  `C1' = max C1* Cε`, `C2' = max C2* Cε`, `Ctime' = max C.Ctime Cε.toNNReal`, and the single real
  `p6Constant_C12X` dominating all of them.

`Cu` (the window-minus-core constant, open obligation `hwin`) and `Ccore` enter as free reals.
The bridge `C1h ≤ C1S` is *not* a theorem of the tree; `C1h_le_C1S_of_Cs_le_C12X` states exactly
what is missing (`Cs ≤ max Ccore Cu`).
-/

set_option autoImplicit false

noncomputable section

open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- The minimum defining `εStrong_C12X`, unfolded: `ε ≤ εStrong` iff `ε` is below all four
accuracies (cone, crossing blow-up `epsW`, crossing neck, crossing window neck). -/
theorem le_εStrong_C12X_iff {ε : ℝ} :
    ε ≤ εStrong_C12X.{u} ↔ ε ≤ coneAccuracy ∧
      ε ≤ ObservedHistory.crossingStrongEpsW_C12X.{u} ∧ ε ≤ crossingNeckAccuracy.{u} ∧
      ε ≤ crossingWindowNeckAccuracy.{u} := by
  unfold εStrong_C12X
  simp only [le_min_iff]

theorem εStrong_C12X_le_crossingStrongEpsW_C12X :
    εStrong_C12X.{u} ≤ ObservedHistory.crossingStrongEpsW_C12X.{u} :=
  ((le_εStrong_C12X_iff (ε := εStrong_C12X.{u})).mp le_rfl).2.1

theorem εStrong_C12X_le_crossingNeckAccuracy :
    εStrong_C12X.{u} ≤ crossingNeckAccuracy.{u} :=
  ((le_εStrong_C12X_iff (ε := εStrong_C12X.{u})).mp le_rfl).2.2.1

theorem εStrong_C12X_le_crossingWindowNeckAccuracy :
    εStrong_C12X.{u} ≤ crossingWindowNeckAccuracy.{u} :=
  ((le_εStrong_C12X_iff (ε := εStrong_C12X.{u})).mp le_rfl).2.2.2

/-- The three accuracy premises of the P6 main form (`ε ≤ crossingWindowNeckAccuracy`,
`ε ≤ crossingNeckAccuracy`, `ε ≤ coneAccuracy`) follow from `ε ≤ εStrong_C12X`; the fourth,
`ε ≤ epsW` (P6's own existential), does not. -/
theorem p6_accuracy_hyps_of_strong_C12X {ε : ℝ} (h : ε ≤ εStrong_C12X.{u}) :
    ε < 1 / 11 ∧ ε ≤ crossingWindowNeckAccuracy.{u} ∧ ε ≤ crossingNeckAccuracy.{u} ∧
      ε ≤ coneAccuracy :=
  ⟨(h.trans_lt εStrong_C12X_lt).trans (by norm_num),
    h.trans εStrong_C12X_le_crossingWindowNeckAccuracy,
    h.trans εStrong_C12X_le_crossingNeckAccuracy, h.trans εStrong_C12X_le_coneAccuracy⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.GeneralFlow

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-! ### Accuracy -/

/-- `C.epsilon ≤ εStrong_C12X` (first conjunct of `exists_closedBirthConstants_strong_C12X`)
recovers the structure field `epsilon_cone`. -/
theorem epsilon_le_coneAccuracy_of_strong_C12X (C : ClosedBirthConstants)
    (h : C.epsilon ≤ εStrong_C12X.{u}) : C.epsilon ≤ coneAccuracy :=
  h.trans εStrong_C12X_le_coneAccuracy

theorem epsilon_lt_eleventh_C12X (C : ClosedBirthConstants) : C.epsilon < 1 / 11 :=
  C.epsilon_small.trans (by norm_num)

/-- The P6 accuracy premises supplied by the chosen constants (all but `ε ≤ epsW`). -/
theorem epsilon_p6_hyps_of_strong_C12X (C : ClosedBirthConstants)
    (h : C.epsilon ≤ εStrong_C12X.{u}) :
    C.epsilon < 1 / 11 ∧ C.epsilon ≤ crossingWindowNeckAccuracy.{u} ∧
      C.epsilon ≤ crossingNeckAccuracy.{u} ∧ C.epsilon ≤ coneAccuracy :=
  p6_accuracy_hyps_of_strong_C12X h

/-! ### S16B per-native pair -/

/-- `C1h` of `strong_necks_full_of_cutoff_class_C12X` (`StrongNeckFullClassC12X:75`). -/
def C1h_C12X (C1 Cs Cx : ℝ) : ℝ := max C1 (max Cs Cx)

/-- `C2h` of `strong_necks_full_of_cutoff_class_C12X` (`StrongNeckFullClassC12X:76`). -/
def C2h_C12X (C2 Cs Cx : ℝ) (Cgrad : ℝ≥0) : ℝ := max C2 (max (max Cs (Cgrad : ℝ)) Cx)

theorem C1_le_C1h_C12X (C1 Cs Cx : ℝ) : C1 ≤ C1h_C12X C1 Cs Cx := le_max_left _ _

theorem Cs_le_C1h_C12X (C1 Cs Cx : ℝ) : Cs ≤ C1h_C12X C1 Cs Cx :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem Cx_le_C1h_C12X (C1 Cs Cx : ℝ) : Cx ≤ C1h_C12X C1 Cs Cx :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem one_le_C1h_C12X {C1 : ℝ} (h : 1 ≤ C1) (Cs Cx : ℝ) : 1 ≤ C1h_C12X C1 Cs Cx :=
  h.trans (C1_le_C1h_C12X C1 Cs Cx)

theorem C2_le_C2h_C12X (C2 Cs Cx : ℝ) (Cgrad : ℝ≥0) : C2 ≤ C2h_C12X C2 Cs Cx Cgrad :=
  le_max_left _ _

theorem Cs_le_C2h_C12X (C2 Cs Cx : ℝ) (Cgrad : ℝ≥0) : Cs ≤ C2h_C12X C2 Cs Cx Cgrad :=
  (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))

theorem Cgrad_le_C2h_C12X (C2 Cs Cx : ℝ) (Cgrad : ℝ≥0) :
    (Cgrad : ℝ) ≤ C2h_C12X C2 Cs Cx Cgrad :=
  (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))

theorem Cx_le_C2h_C12X (C2 Cs Cx : ℝ) (Cgrad : ℝ≥0) : Cx ≤ C2h_C12X C2 Cs Cx Cgrad :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem one_le_C2h_C12X {C2 : ℝ} (h : 1 ≤ C2) (Cs Cx : ℝ) (Cgrad : ℝ≥0) :
    1 ≤ C2h_C12X C2 Cs Cx Cgrad :=
  h.trans (C2_le_C2h_C12X C2 Cs Cx Cgrad)

/-! ### S16F uniform pair -/

/-- `Ccore := max Cs₀ Cx` (`StrongUniformClassC12X:92`). -/
def Ccore_C12X (Cs₀ Cx : ℝ) : ℝ := max Cs₀ Cx

/-- `C1S := max C.C1 (max Ccore Cu)`, the first component of the S16F conclusion
(`StrongUniformClassC12X:75`) with `C1 := C.C1`. -/
def C1S_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) : ℝ := max C.C1 (max Ccore Cu)

/-- `C2S := max C.C2 (max (max Ccore Cu) C.Cgrad)`, the second component. -/
def C2S_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) : ℝ :=
  max C.C2 (max (max Ccore Cu) (C.Cgrad : ℝ))

theorem Cs0_le_Ccore_C12X (Cs₀ Cx : ℝ) : Cs₀ ≤ Ccore_C12X Cs₀ Cx := le_max_left _ _

theorem Cx_le_Ccore_C12X (Cs₀ Cx : ℝ) : Cx ≤ Ccore_C12X Cs₀ Cx := le_max_right _ _

theorem one_le_Ccore_C12X {Cs₀ : ℝ} (h : 1 ≤ Cs₀) (Cx : ℝ) : 1 ≤ Ccore_C12X Cs₀ Cx :=
  h.trans (Cs0_le_Ccore_C12X Cs₀ Cx)

theorem C1_le_C1S_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    C.C1 ≤ C1S_C12X C Ccore Cu :=
  le_max_left _ _

theorem Ccore_le_C1S_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    Ccore ≤ C1S_C12X C Ccore Cu :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem Cu_le_C1S_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    Cu ≤ C1S_C12X C Ccore Cu :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem Cs0_le_C1S_C12X (C : ClosedBirthConstants) (Cs₀ Cx Cu : ℝ) :
    Cs₀ ≤ C1S_C12X C (Ccore_C12X Cs₀ Cx) Cu :=
  (Cs0_le_Ccore_C12X Cs₀ Cx).trans (Ccore_le_C1S_C12X C _ Cu)

theorem Cx_le_C1S_C12X (C : ClosedBirthConstants) (Cs₀ Cx Cu : ℝ) :
    Cx ≤ C1S_C12X C (Ccore_C12X Cs₀ Cx) Cu :=
  (Cx_le_Ccore_C12X Cs₀ Cx).trans (Ccore_le_C1S_C12X C _ Cu)

theorem one_le_C1S_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) : 1 ≤ C1S_C12X C Ccore Cu :=
  C.C1_ge_one.trans (C1_le_C1S_C12X C Ccore Cu)

theorem C2_le_C2S_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    C.C2 ≤ C2S_C12X C Ccore Cu :=
  le_max_left _ _

theorem Ccore_le_C2S_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    Ccore ≤ C2S_C12X C Ccore Cu :=
  (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))

theorem Cu_le_C2S_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    Cu ≤ C2S_C12X C Ccore Cu :=
  (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))

theorem Cgrad_le_C2S_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    (C.Cgrad : ℝ) ≤ C2S_C12X C Ccore Cu :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem Cs0_le_C2S_C12X (C : ClosedBirthConstants) (Cs₀ Cx Cu : ℝ) :
    Cs₀ ≤ C2S_C12X C (Ccore_C12X Cs₀ Cx) Cu :=
  (Cs0_le_Ccore_C12X Cs₀ Cx).trans (Ccore_le_C2S_C12X C _ Cu)

theorem Cx_le_C2S_C12X (C : ClosedBirthConstants) (Cs₀ Cx Cu : ℝ) :
    Cx ≤ C2S_C12X C (Ccore_C12X Cs₀ Cx) Cu :=
  (Cx_le_Ccore_C12X Cs₀ Cx).trans (Ccore_le_C2S_C12X C _ Cu)

theorem one_le_C2S_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) : 1 ≤ C2S_C12X C Ccore Cu :=
  C.C2_ge_one.trans (C2_le_C2S_C12X C Ccore Cu)

/-- **The missing bridge** `C1h ≤ C1S`: it holds as soon as the per-native cap-window constant
satisfies `Cs ≤ max Ccore Cu` (and `Cx ≤ Ccore`).  `Cs ≤ max Ccore Cu` is not a theorem of the
tree (`Cs` and `Cs₀` are independent existential outputs). -/
theorem C1h_le_C1S_of_Cs_le_C12X (C : ClosedBirthConstants) {Cs Cx Ccore Cu : ℝ}
    (hCs : Cs ≤ max Ccore Cu) (hCx : Cx ≤ Ccore) :
    C1h_C12X C.C1 Cs Cx ≤ C1S_C12X C Ccore Cu :=
  max_le (C1_le_C1S_C12X C Ccore Cu)
    (max_le (hCs.trans (max_le (Ccore_le_C1S_C12X C Ccore Cu) (Cu_le_C1S_C12X C Ccore Cu)))
      (hCx.trans (Ccore_le_C1S_C12X C Ccore Cu)))

theorem C2h_le_C2S_of_Cs_le_C12X (C : ClosedBirthConstants) {Cs Cx Ccore Cu : ℝ}
    (hCs : Cs ≤ max Ccore Cu) (hCx : Cx ≤ Ccore) :
    C2h_C12X C.C2 Cs Cx C.Cgrad ≤ C2S_C12X C Ccore Cu :=
  max_le (C2_le_C2S_C12X C Ccore Cu)
    (max_le (max_le (hCs.trans (max_le (Ccore_le_C2S_C12X C Ccore Cu)
      (Cu_le_C2S_C12X C Ccore Cu))) (Cgrad_le_C2S_C12X C Ccore Cu))
      (hCx.trans (Ccore_le_C2S_C12X C Ccore Cu)))

/-! ### Astra pair and shared pair -/

/-- `C1⁰ := max C.C1s C.Cbirth` (astra pair, `SupplyFourOfClosedBirthC11A:25`). -/
def C1zero_C12X (C : ClosedBirthConstants) : ℝ := max C.C1s C.Cbirth

/-- `C2⁰ := max C.C2s (max C.Cbirth C.Cgrad)`. -/
def C2zero_C12X (C : ClosedBirthConstants) : ℝ := max C.C2s (max C.Cbirth (C.Cgrad : ℝ))

/-- `C1* := max C1⁰ C1S`: the `C1` of `hext` once S16 is supplied
(`sharedCanonicalSupplies_max_C12X` at `(C1⁰, C2⁰)` and `(C1S, C2S)`). -/
def C1star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) : ℝ :=
  max (C1zero_C12X C) (C1S_C12X C Ccore Cu)

/-- `C2* := max C2⁰ C2S`. -/
def C2star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) : ℝ :=
  max (C2zero_C12X C) (C2S_C12X C Ccore Cu)

/-- The output pair of `sharedCanonicalSupplies_max_C12X` is `(C1*, C2*)`. -/
theorem sharedPair_eq_star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    (max (C1zero_C12X C) (C1S_C12X C Ccore Cu), max (C2zero_C12X C) (C2S_C12X C Ccore Cu)) =
      (C1star_C12X C Ccore Cu, C2star_C12X C Ccore Cu) :=
  rfl

theorem C1zero_le_C1star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    C1zero_C12X C ≤ C1star_C12X C Ccore Cu :=
  le_max_left _ _

theorem C1S_le_C1star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    C1S_C12X C Ccore Cu ≤ C1star_C12X C Ccore Cu :=
  le_max_right _ _

theorem C1s_le_C1star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    C.C1s ≤ C1star_C12X C Ccore Cu :=
  (le_max_left _ _).trans (C1zero_le_C1star_C12X C Ccore Cu)

theorem Cbirth_le_C1star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    C.Cbirth ≤ C1star_C12X C Ccore Cu :=
  (le_max_right _ _).trans (C1zero_le_C1star_C12X C Ccore Cu)

theorem C1_le_C1star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    C.C1 ≤ C1star_C12X C Ccore Cu :=
  (C1_le_C1S_C12X C Ccore Cu).trans (C1S_le_C1star_C12X C Ccore Cu)

theorem Ccore_le_C1star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    Ccore ≤ C1star_C12X C Ccore Cu :=
  (Ccore_le_C1S_C12X C Ccore Cu).trans (C1S_le_C1star_C12X C Ccore Cu)

theorem Cu_le_C1star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    Cu ≤ C1star_C12X C Ccore Cu :=
  (Cu_le_C1S_C12X C Ccore Cu).trans (C1S_le_C1star_C12X C Ccore Cu)

theorem Cx_le_C1star_C12X (C : ClosedBirthConstants) (Cs₀ Cx Cu : ℝ) :
    Cx ≤ C1star_C12X C (Ccore_C12X Cs₀ Cx) Cu :=
  (Cx_le_C1S_C12X C Cs₀ Cx Cu).trans (C1S_le_C1star_C12X C _ Cu)

theorem one_le_C1star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    1 ≤ C1star_C12X C Ccore Cu :=
  C.C1_ge_one.trans (C1_le_C1star_C12X C Ccore Cu)

/-- `C1*` is the least upper bound of `C.C1s, C.Cbirth, C.C1, Ccore, Cu`
(the six-term formula of R-S16-2 D-1; `Cx ≤ Ccore`). -/
theorem C1star_le_of_forall_C12X (C : ClosedBirthConstants) {Ccore Cu K : ℝ}
    (h1 : C.C1s ≤ K) (h2 : C.Cbirth ≤ K) (h3 : C.C1 ≤ K) (h4 : Ccore ≤ K) (h5 : Cu ≤ K) :
    C1star_C12X C Ccore Cu ≤ K :=
  max_le (max_le h1 h2) (max_le h3 (max_le h4 h5))

theorem C1h_le_C1star_of_Cs_le_C12X (C : ClosedBirthConstants) {Cs Cx Ccore Cu : ℝ}
    (hCs : Cs ≤ max Ccore Cu) (hCx : Cx ≤ Ccore) :
    C1h_C12X C.C1 Cs Cx ≤ C1star_C12X C Ccore Cu :=
  (C1h_le_C1S_of_Cs_le_C12X C hCs hCx).trans (C1S_le_C1star_C12X C Ccore Cu)

theorem C2zero_le_C2star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    C2zero_C12X C ≤ C2star_C12X C Ccore Cu :=
  le_max_left _ _

theorem C2S_le_C2star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    C2S_C12X C Ccore Cu ≤ C2star_C12X C Ccore Cu :=
  le_max_right _ _

theorem C2s_le_C2star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    C.C2s ≤ C2star_C12X C Ccore Cu :=
  (le_max_left _ _).trans (C2zero_le_C2star_C12X C Ccore Cu)

theorem Cbirth_le_C2star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    C.Cbirth ≤ C2star_C12X C Ccore Cu :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans (C2zero_le_C2star_C12X C Ccore Cu)

theorem Cgrad_le_C2star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    (C.Cgrad : ℝ) ≤ C2star_C12X C Ccore Cu :=
  (Cgrad_le_C2S_C12X C Ccore Cu).trans (C2S_le_C2star_C12X C Ccore Cu)

theorem C2_le_C2star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    C.C2 ≤ C2star_C12X C Ccore Cu :=
  (C2_le_C2S_C12X C Ccore Cu).trans (C2S_le_C2star_C12X C Ccore Cu)

theorem Ccore_le_C2star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    Ccore ≤ C2star_C12X C Ccore Cu :=
  (Ccore_le_C2S_C12X C Ccore Cu).trans (C2S_le_C2star_C12X C Ccore Cu)

theorem Cu_le_C2star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    Cu ≤ C2star_C12X C Ccore Cu :=
  (Cu_le_C2S_C12X C Ccore Cu).trans (C2S_le_C2star_C12X C Ccore Cu)

theorem Cx_le_C2star_C12X (C : ClosedBirthConstants) (Cs₀ Cx Cu : ℝ) :
    Cx ≤ C2star_C12X C (Ccore_C12X Cs₀ Cx) Cu :=
  (Cx_le_C2S_C12X C Cs₀ Cx Cu).trans (C2S_le_C2star_C12X C _ Cu)

theorem one_le_C2star_C12X (C : ClosedBirthConstants) (Ccore Cu : ℝ) :
    1 ≤ C2star_C12X C Ccore Cu :=
  C.C2_ge_one.trans (C2_le_C2star_C12X C Ccore Cu)

/-- `C2*` is the least upper bound of `C.C2s, C.Cbirth, C.Cgrad, C.C2, Ccore, Cu`. -/
theorem C2star_le_of_forall_C12X (C : ClosedBirthConstants) {Ccore Cu K : ℝ}
    (h1 : C.C2s ≤ K) (h2 : C.Cbirth ≤ K) (h3 : (C.Cgrad : ℝ) ≤ K) (h4 : C.C2 ≤ K)
    (h5 : Ccore ≤ K) (h6 : Cu ≤ K) : C2star_C12X C Ccore Cu ≤ K :=
  max_le (max_le h1 (max_le h2 h3)) (max_le h4 (max_le (max_le h5 h6) h3))

theorem C2h_le_C2star_of_Cs_le_C12X (C : ClosedBirthConstants) {Cs Cx Ccore Cu : ℝ}
    (hCs : Cs ≤ max Ccore Cu) (hCx : Cx ≤ Ccore) :
    C2h_C12X C.C2 Cs Cx C.Cgrad ≤ C2star_C12X C Ccore Cu :=
  (C2h_le_C2S_of_Cs_le_C12X C hCs hCx).trans (C2S_le_C2star_C12X C Ccore Cu)

/-! ### P6 primed constants -/

/-- P6 primed `C1' := max C1* Cε` (`goodConstants_accommodate_P6P` with `C1 := C1*`);
`Cε` is the `C(ε)` of the P6 main form. -/
def p6C1_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) : ℝ :=
  max (C1star_C12X C Ccore Cu) Cε

/-- P6 primed `C2' := max C2* Cε`. -/
def p6C2_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) : ℝ :=
  max (C2star_C12X C Ccore Cu) Cε

/-- P6 primed `Ctime' := max C.Ctime Cε.toNNReal`
(`E.Ctime = C.Ctime`, `A12FullConsumerC12X:73`). -/
def p6Ctime_C12X (C : ClosedBirthConstants) (Cε : ℝ) : ℝ≥0 := max C.Ctime Cε.toNNReal

/-- One real dominating `C1*`, `C2*`, `C.Ctime` and `Cε`: take `C1' = C2' = K`,
`Ctime' = K.toNNReal` in the P6 main form. -/
def p6Constant_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) : ℝ :=
  max (max (C1star_C12X C Ccore Cu) (C2star_C12X C Ccore Cu)) (max Cε (C.Ctime : ℝ))

theorem C1star_le_p6C1_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) :
    C1star_C12X C Ccore Cu ≤ p6C1_C12X C Ccore Cu Cε :=
  le_max_left _ _

theorem Ceps_le_p6C1_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) :
    Cε ≤ p6C1_C12X C Ccore Cu Cε :=
  le_max_right _ _

theorem one_le_p6C1_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) :
    1 ≤ p6C1_C12X C Ccore Cu Cε :=
  (one_le_C1star_C12X C Ccore Cu).trans (C1star_le_p6C1_C12X C Ccore Cu Cε)

theorem C2star_le_p6C2_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) :
    C2star_C12X C Ccore Cu ≤ p6C2_C12X C Ccore Cu Cε :=
  le_max_left _ _

theorem Ceps_le_p6C2_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) :
    Cε ≤ p6C2_C12X C Ccore Cu Cε :=
  le_max_right _ _

theorem one_le_p6C2_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) :
    1 ≤ p6C2_C12X C Ccore Cu Cε :=
  (one_le_C2star_C12X C Ccore Cu).trans (C2star_le_p6C2_C12X C Ccore Cu Cε)

theorem Ctime_le_p6Ctime_C12X (C : ClosedBirthConstants) (Cε : ℝ) :
    C.Ctime ≤ p6Ctime_C12X C Cε :=
  le_max_left _ _

theorem Ceps_toNNReal_le_p6Ctime_C12X (C : ClosedBirthConstants) (Cε : ℝ) :
    Cε.toNNReal ≤ p6Ctime_C12X C Cε :=
  le_max_right _ _

/-- The eight accommodation facts of `goodConstants_accommodate_P6P` for the frozen constants
`(C1*, C2*, C.Ctime)`: raising and absorbing `Cε`, with `1 ≤ C1'`, `1 ≤ C2'`. -/
theorem p6_accommodate_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) :
    C1star_C12X C Ccore Cu ≤ p6C1_C12X C Ccore Cu Cε ∧
      C2star_C12X C Ccore Cu ≤ p6C2_C12X C Ccore Cu Cε ∧
      C.Ctime ≤ p6Ctime_C12X C Cε ∧ Cε ≤ p6C1_C12X C Ccore Cu Cε ∧
      Cε ≤ p6C2_C12X C Ccore Cu Cε ∧ Cε.toNNReal ≤ p6Ctime_C12X C Cε ∧
      1 ≤ p6C1_C12X C Ccore Cu Cε ∧ 1 ≤ p6C2_C12X C Ccore Cu Cε :=
  ⟨C1star_le_p6C1_C12X C Ccore Cu Cε, C2star_le_p6C2_C12X C Ccore Cu Cε,
    Ctime_le_p6Ctime_C12X C Cε, Ceps_le_p6C1_C12X C Ccore Cu Cε,
    Ceps_le_p6C2_C12X C Ccore Cu Cε, Ceps_toNNReal_le_p6Ctime_C12X C Cε,
    one_le_p6C1_C12X C Ccore Cu Cε, one_le_p6C2_C12X C Ccore Cu Cε⟩

theorem C1star_le_p6Constant_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) :
    C1star_C12X C Ccore Cu ≤ p6Constant_C12X C Ccore Cu Cε :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem C2star_le_p6Constant_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) :
    C2star_C12X C Ccore Cu ≤ p6Constant_C12X C Ccore Cu Cε :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem Ceps_le_p6Constant_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) :
    Cε ≤ p6Constant_C12X C Ccore Cu Cε :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem Ctime_le_p6Constant_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) :
    (C.Ctime : ℝ) ≤ p6Constant_C12X C Ccore Cu Cε :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem one_le_p6Constant_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) :
    1 ≤ p6Constant_C12X C Ccore Cu Cε :=
  (one_le_C1star_C12X C Ccore Cu).trans (C1star_le_p6Constant_C12X C Ccore Cu Cε)

theorem Ceps_toNNReal_le_p6Constant_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) :
    Cε.toNNReal ≤ (p6Constant_C12X C Ccore Cu Cε).toNNReal :=
  Real.toNNReal_le_toNNReal (Ceps_le_p6Constant_C12X C Ccore Cu Cε)

theorem Ctime_le_p6Constant_toNNReal_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) :
    C.Ctime ≤ (p6Constant_C12X C Ccore Cu Cε).toNNReal := by
  simpa using Real.toNNReal_le_toNNReal (Ctime_le_p6Constant_C12X C Ccore Cu Cε)

/-- The shape of the P6 main form's constant clause: with `C1' = C2' = K`, `Ctime' = K.toNNReal`
one has `Cε ≤ C1'`, `Cε ≤ C2'`, `Cε.toNNReal ≤ Ctime'`, and `K` dominates the frozen
`C1*`, `C2*`, `C.Ctime`. -/
theorem p6Constant_accommodates_C12X (C : ClosedBirthConstants) (Ccore Cu Cε : ℝ) :
    Cε ≤ p6Constant_C12X C Ccore Cu Cε ∧ Cε ≤ p6Constant_C12X C Ccore Cu Cε ∧
      Cε.toNNReal ≤ (p6Constant_C12X C Ccore Cu Cε).toNNReal ∧
      C1star_C12X C Ccore Cu ≤ p6Constant_C12X C Ccore Cu Cε ∧
      C2star_C12X C Ccore Cu ≤ p6Constant_C12X C Ccore Cu Cε ∧
      C.Ctime ≤ (p6Constant_C12X C Ccore Cu Cε).toNNReal :=
  ⟨Ceps_le_p6Constant_C12X C Ccore Cu Cε, Ceps_le_p6Constant_C12X C Ccore Cu Cε,
    Ceps_toNNReal_le_p6Constant_C12X C Ccore Cu Cε, C1star_le_p6Constant_C12X C Ccore Cu Cε,
    C2star_le_p6Constant_C12X C Ccore Cu Cε, Ctime_le_p6Constant_toNNReal_C12X C Ccore Cu Cε⟩

end GC.GeneralFlow

end
