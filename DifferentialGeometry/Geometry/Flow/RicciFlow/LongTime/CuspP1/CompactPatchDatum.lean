import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.CompactPatchEmbed

set_option autoImplicit false

/-!
# CP1-D6 (4): local survivor-family data, uniqueness and finite gluing
-/

noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1

universe u v

section Restrict

variable (H : ObservedHistory.{u})

/-- restricting the range `[F, L]` of a survivor domain to a subrange `[F', L']` -/
def restrictDom_CPD6 {F L F' L' : Fin (H.eventCount + 1)} (hFL : F ≤ L) (hFL' : F' ≤ L')
    (hF : F ≤ F') (hL : L' ≤ L) :
    C(H.backwardSurvivorDomain F L hFL, H.backwardSurvivorDomain F' L' hFL') :=
  ⟨fun w => ⟨H.backwardSurvivorMap F L hFL L' (hF.trans hFL') hL w,
      ⟨((Classical.choice w.property).restrictLast (hF.trans hFL') hL).restrictFirst hF hFL'⟩⟩,
    Continuous.subtype_mk
      (survivorCM H F L hFL L' (hF.trans hFL') hL).continuous _⟩

theorem survivorMap_restrictDom_CPD6 {F L F' L' : Fin (H.eventCount + 1)} (hFL : F ≤ L)
    (hFL' : F' ≤ L') (hF : F ≤ F') (hL : L' ≤ L) (j : Fin (H.eventCount + 1)) (hj : F' ≤ j)
    (hl : j ≤ L') (w : H.backwardSurvivorDomain F L hFL) :
    H.backwardSurvivorMap F' L' hFL' j hj hl (restrictDom_CPD6 H hFL hFL' hF hL w) =
      H.backwardSurvivorMap F L hFL j (hF.trans hj) (hl.trans hL) w := by
  rw [H.backwardSurvivorMap_eq_point _ _ _ _ _ _ _
      (((Classical.choice w.property).restrictLast (hF.trans hFL') hL).restrictFirst hF hFL'),
    H.backwardSurvivorMap_eq_point _ _ _ _ _ _ _ (Classical.choice w.property)]
  rfl

end Restrict

section Datum

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g)
  {X : Type v} [TopologicalSpace X] (T₀ : ℝ)
  (m : ∀ t : ℝ, T₀ ≤ t → X → (postStage T t).Carrier)

/-- A continuous family of points of the survivor domain of the `N`-th history, over the time set
`J` and the space-set `U`, whose survivor image at the active stage is the actual map `m t`. -/
structure LocalDatum_CPD6 (N : ℕ) (J : Set ℝ) (U : Set X)
    (F L : Fin ((T.history N).eventCount + 1)) (hFL : F ≤ L) where
  hJ : ∀ t ∈ J, T₀ ≤ t ∧ 0 ≤ t ∧ t ≤ (T.history N).horizon
  stages : ∀ t (ht : t ∈ J),
    F ≤ (T.history N).activeStage ⟨t, (hJ t ht).2.1, (hJ t ht).2.2⟩ ∧
    (T.history N).activeStage ⟨t, (hJ t ht).2.1, (hJ t ht).2.2⟩ ≤ L
  z : ℝ × X → (T.history N).backwardSurvivorDomain F L hFL
  cont : ContinuousOn z (J ×ˢ U)
  agrees : ∀ t (ht : t ∈ J) (y : X), y ∈ U →
    HEq ((T.history N).backwardSurvivorMap F L hFL
        ((T.history N).activeStage ⟨t, (hJ t ht).2.1, (hJ t ht).2.2⟩)
        (stages t ht).1 (stages t ht).2 (z (t, y))) (m t (hJ t ht).1 y)

variable {T T₀ m}

/-- shrink the time set and space set -/
def LocalDatum_CPD6.mono {N : ℕ} {J J' : Set ℝ} {U U' : Set X}
    {F L : Fin ((T.history N).eventCount + 1)} {hFL : F ≤ L}
    (D : LocalDatum_CPD6 T T₀ m N J U F L hFL) (hJ : J' ⊆ J) (hU : U' ⊆ U) :
    LocalDatum_CPD6 T T₀ m N J' U' F L hFL where
  hJ t ht := D.hJ t (hJ ht)
  stages t ht := D.stages t (hJ ht)
  z := D.z
  cont := D.cont.mono (prod_mono hJ hU)
  agrees t ht y hy := D.agrees t (hJ ht) y (hU hy)

/-- restrict the range of the survivor domain -/
def LocalDatum_CPD6.restrictRange {N : ℕ} {J : Set ℝ} {U : Set X}
    {F L : Fin ((T.history N).eventCount + 1)} {hFL : F ≤ L}
    (D : LocalDatum_CPD6 T T₀ m N J U F L hFL)
    {F' L' : Fin ((T.history N).eventCount + 1)} (hFL' : F' ≤ L') (hF : F ≤ F') (hL : L' ≤ L)
    (hst : ∀ t (ht : t ∈ J),
      F' ≤ (T.history N).activeStage ⟨t, (D.hJ t ht).2.1, (D.hJ t ht).2.2⟩ ∧
      (T.history N).activeStage ⟨t, (D.hJ t ht).2.1, (D.hJ t ht).2.2⟩ ≤ L') :
    LocalDatum_CPD6 T T₀ m N J U F' L' hFL' where
  hJ := D.hJ
  stages := hst
  z q := restrictDom_CPD6 (T.history N) hFL hFL' hF hL (D.z q)
  cont := (restrictDom_CPD6 (T.history N) hFL hFL' hF hL).continuous.comp_continuousOn D.cont
  agrees t ht y hy := by
    have := D.agrees t ht y hy
    refine HEq.trans ?_ this
    rw [survivorMap_restrictDom_CPD6]

/-- Uniqueness: two data over the same time set agree wherever both are defined. -/
theorem LocalDatum_CPD6.unique {N : ℕ} {J : Set ℝ} {U U' : Set X}
    {F L : Fin ((T.history N).eventCount + 1)} {hFL : F ≤ L}
    (D : LocalDatum_CPD6 T T₀ m N J U F L hFL) (D' : LocalDatum_CPD6 T T₀ m N J U' F L hFL)
    {t : ℝ} (ht : t ∈ J) {y : X} (hy : y ∈ U) (hy' : y ∈ U') : D.z (t, y) = D'.z (t, y) := by
  apply (T.history N).backwardSurvivorMap_injective F L hFL
    ((T.history N).activeStage ⟨t, (D.hJ t ht).2.1, (D.hJ t ht).2.2⟩) (D.stages t ht).1
    (D.stages t ht).2
  exact eq_of_heq ((D.agrees t ht y hy).trans (D'.agrees t ht y hy').symm)

/-- Gluing: local data over an open cover of `X`, all on the same time set and range, glue to a
datum over all of `X`. -/
def LocalDatum_CPD6.glue {κ : Type*} [Nonempty κ] {N : ℕ} {J : Set ℝ} (U : κ → Set X)
    (hU : ∀ k, IsOpen (U k)) (hcov : ∀ y : X, ∃ k, y ∈ U k)
    {F L : Fin ((T.history N).eventCount + 1)} {hFL : F ≤ L}
    (D : ∀ k, LocalDatum_CPD6 T T₀ m N J (U k) F L hFL) :
    LocalDatum_CPD6 T T₀ m N J univ F L hFL where
  hJ := (D (Classical.arbitrary κ)).hJ
  stages := (D (Classical.arbitrary κ)).stages
  z q := (D (Classical.choose (hcov q.2))).z q
  cont := by
    apply continuousOn_of_locally_continuousOn
    rintro ⟨t, y⟩ ⟨ht, -⟩
    obtain ⟨k, hk⟩ := hcov y
    refine ⟨univ ×ˢ U k, isOpen_univ.prod (hU k), ⟨mem_univ _, hk⟩, ?_⟩
    refine ((D k).cont.mono (fun q hq => ⟨hq.1.1, hq.2.2⟩)).congr ?_
    rintro ⟨t', y'⟩ ⟨⟨ht', -⟩, ⟨-, hy'⟩⟩
    exact (D (Classical.choose (hcov y'))).unique (D k) ht' (Classical.choose_spec (hcov y')) hy'
  agrees t ht y _ :=
    (D (Classical.choose (hcov y))).agrees t ht y (Classical.choose_spec (hcov y))

end Datum

end GC.LongTime.CuspP1
