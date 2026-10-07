import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.RecentCutoffSupplyC11RC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfSuppliesC11S

set_option autoImplicit false

/-!
# S-CH11-REPROVE-C (G3 consumer)：chain 级 S9 喂进 A12 的数据级总装

`exists_surgery_with_decaying_accuracy_of_chain_C11RC`：把 SKEL
`exists_surgery_with_decaying_accuracy_of_data_C11S` 里的 `hrcs : RecentCutoffSupply_C11S records`
换成 chain 级的性质型 binder（`Hs / ps / recs / r` 与 `hpref … hbridge`），其余 S1–S8 binder 原样。
结论逐字是 A12 `exists_surgery_with_decaying_accuracy` 的陈述。
-/

noncomputable section

open Set DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

universe u

/-- **consumer**：S1–S8 数据级 binder + S9 的 chain 级 binder ⇒ A12 的结论。 -/
theorem exists_surgery_with_decaying_accuracy_of_chain_C11RC {P : OrientedThreeStage.{u}}
    {g : P.Metric} (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : CutoffRecords_C11S F q) (eps C1 C2 : ℝ) (κ : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (hδ : AccuracyDecaySupply_C11S q.delta)
    (hrad : RadiusAntitoneSupply_C11S q) (hwin : CanonicalWindowsSupply_C11S records)
    (hconst : CanonicalConstantsSupply_C11S eps C1 C2)
    (hcan : CanonicalSupply_C11S F q.neckRadius eps C1 C2)
    (hnc : NoncollapseSupply_C11S F κ eps)
    (hacc : LargerBallAccuracySupply_C11S q.delta α)
    (hLB : LargerBallScalarLargeSupply_C11S F q.delta α)
    (Hs : ℕ → ObservedHistory.{u}) (ps : ℕ → CutoffParameters)
    (recs : ∀ m (i : Fin (Hs m).eventCount), GeometricCutoffRecord (Hs m) i (ps m))
    (r : ℕ → ℝ) (hr_pos : ∀ k, 0 < r k) (hr_succ : ∀ m, r (m + 1) ≤ r m)
    (hhor : ∀ m, (Hs m).horizon = fullHorizon_C11RC m)
    (hpref : ∀ m, (Hs m).IsPrefixOf (Hs (m + 1)))
    (hpres : ∀ m (i : Fin (Hs m).eventCount),
      HEq (recs (m + 1) (i.castLE (eventCount_le_of_isPrefixOf_C11RC (hpref m)))).nominalRadius
        (recs m i).nominalRadius)
    (hrecent : ∀ k (i : Fin (Hs (k + 1)).eventCount),
      (Hs k).horizon < (Hs (k + 1)).time i.succ →
      ∀ h, (recs (k + 1) i).nominalRadius h ≤ (1 / ((k : ℝ) + 2)) * r (k + 1))
    (hbefore : ∀ m t, t ≤ activation_C11RC m →
      (ps (m + 1)).neckRadius t = (ps m).neckRadius t)
    (hafter : ∀ m t, activation_C11RC m < t → (ps (m + 1)).neckRadius t = r (m + 1))
    (hq : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ), q.neckRadius t = (ps (n + 1)).neckRadius t)
    (hbridge : ∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount),
      ∃ j : Fin (Hs (n + 1)).eventCount,
        ((F.tower.history n).toHistory.event i).SamePresentation ((Hs (n + 1)).event j) ∧
        HEq (records n i).nominalRadius (recs (n + 1) j).nominalRadius) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ :=
  exists_surgery_with_decaying_accuracy_of_data_C11S F q records eps C1 C2 κ α hδ hrad hwin
    hconst hcan hnc hacc hLB
    (recentCutoffSupply_of_chain_C11RC records Hs ps recs r hr_pos hr_succ hhor hpref hpres
      hrecent hbefore hafter hq hbridge)

/-- **consumer（参数级路线）**：S9 由 common-profile 型比较式给出时同样得到 A12 的结论。 -/
theorem exists_surgery_with_decaying_accuracy_of_accuracy_C11RC {P : OrientedThreeStage.{u}}
    {g : P.Metric} (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : CutoffRecords_C11S F q) (eps C1 C2 : ℝ) (κ : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (hδ : AccuracyDecaySupply_C11S q.delta)
    (hrad : RadiusAntitoneSupply_C11S q) (hwin : CanonicalWindowsSupply_C11S records)
    (hconst : CanonicalConstantsSupply_C11S eps C1 C2)
    (hcan : CanonicalSupply_C11S F q.neckRadius eps C1 C2)
    (hnc : NoncollapseSupply_C11S F κ eps)
    (hacc : LargerBallAccuracySupply_C11S q.delta α)
    (hLB : LargerBallScalarLargeSupply_C11S F q.delta α)
    (haccuracy : ∀ u : ℝ, 0 ≤ u →
      q.delta u ^ 2 * q.neckRadius u < q.neckRadius (2 * u) / (u + 1)) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ :=
  exists_surgery_with_decaying_accuracy_of_data_C11S F q records eps C1 C2 κ α hδ hrad hwin
    hconst hcan hnc hacc hLB (recentCutoffSupply_of_accuracy_C11RC records hrad haccuracy)

end GC.LongTime.Ch11
