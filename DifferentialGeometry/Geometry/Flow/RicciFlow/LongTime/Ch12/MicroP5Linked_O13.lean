import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileHypotheses

/-!
# CH12-O13, group 1: `P5Linked_O13` (late cap-window records with linked canonical windows)

`P5Linked_O13 Hp` is `P5_O3 Hp` (same quantifier order `(D ζ m) → T → n → p`, records only for
late events `T ≤ time i.succ`) with two additions required for the cap-window branch (Z3) of the
micro glue (review CH12-R2 Q2(a), disposition D-R2-2):

* `p.recenterConstant = Hp.parameters.recenterConstant` (uniform recentring constant, so that `hdec`
  controls the static neck accuracy of the new records);
* `linkedCanonicalWindow_O2` on every returned static cap (insertion datum `(δ', k)` tied to the
  static neck: `δ' ≤ S.delta`, `2⌊δ'⁻¹⌋ ≤ k`), replacing `hasCanonicalWindow`.

`P5Linked_O13.toP5_O3` shows it implies `P5_O3`.  Supply: chapter 11 (as for P5).
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **P5Linked** (hypothesis shape, authorised by D-R2-2): `P5_O3` plus the recentring-constant
equality and linked canonical windows on the returned late records. -/
def P5Linked_O13 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) : Prop :=
  ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T : ℝ, ∀ n, ∃ p : CutoffParameters,
    p.delta = Hp.parameters.delta ∧ p.neckRadius = Hp.parameters.neckRadius ∧
    p.fixed = Hp.parameters.fixed ∧ p.recenterConstant = Hp.parameters.recenterConstant ∧
    D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
    ∃ records : ∀ i : Fin (F.tower.history n).eventCount,
        T ≤ (F.tower.history n).time i.succ →
        GeometricCutoffRecord (F.tower.history n).toHistory i p,
      ∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)

/-- `P5Linked_O13` implies `P5_O3` (linked windows are canonical windows). -/
theorem P5Linked_O13.toP5_O3 {Hp : GC.LongTime.AnalyticSurgeryProfile F δ}
    (h : P5Linked_O13 Hp) : P5_O3 Hp := by
  intro D ζ m hζ
  obtain ⟨T, hT⟩ := h D ζ m hζ
  refine ⟨T, fun n => ?_⟩
  obtain ⟨p, h1, h2, h3, -, h5, h6, h7, records, hlink⟩ := hT n
  exact ⟨p, h1, h2, h3, h5, h6, h7, records,
    fun i hi b => linkedCanonicalWindow_hasCanonicalWindow_O2 _ (hlink i hi b)⟩

end GC.LongTime.Ch12
