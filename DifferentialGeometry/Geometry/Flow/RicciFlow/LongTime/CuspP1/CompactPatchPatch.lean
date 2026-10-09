import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.CompactPatchDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PersistentHyperbolicCores

set_option autoImplicit false

/-!
# CP1-D6 (5): a `PersistentModelPatch` gives a local datum in any later history `N`
-/

noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1

universe u v

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {Hm : FiniteVolumeHyperbolicModel.{u}} {T₀ : ℝ} {α : ℝ → ℝ}
  {domain : ℝ → TopologicalSpace.Opens Hm.Carrier}
  {f : (t : ℝ) → T₀ ≤ t → Hm.Carrier → (postStage F.observation t).Carrier}
  {t₀ : ℝ} {x₀ : Hm.Carrier} {X : Type v} [TopologicalSpace X]

/-- The local datum of a patch, transported to the `N`-th history (`p.n ≤ N`) over the time set
`(a, b) ∩ [T₀, ∞)` and the set `ι ⁻¹ (neighbourhood)`. -/
def patchDatum_CPD6 (p : PersistentModelPatch F Hm T₀ α domain f t₀ x₀) (ι : C(X, Hm.Carrier))
    (N : ℕ) (hnN : p.n ≤ N) :
    LocalDatum_CPD6 F.observation T₀ (fun t hT y => f t hT (ι y)) N
      (Ioo p.a p.b ∩ Ici T₀) (ι ⁻¹' (p.neighborhood : Set Hm.Carrier))
      (embIdx_CPD6 (towerEmb_CPD6 F.observation p.n N hnN).le p.first)
      (embIdx_CPD6 (towerEmb_CPD6 F.observation p.n N hnN).le p.last)
      (embIdx_le_CPD6 _ p.ordered) := by
  let E := towerEmb_CPD6 F.observation p.n N hnN
  have hN : ∀ t : ℝ, t ≤ (p.n : ℝ) → t ≤ ((F.observation.history N).horizon) := by
    intro t ht
    rw [F.observation.horizon_eq]
    exact ht.trans (by exact_mod_cast hnN)
  have hb : p.b ≤ (p.n : ℝ) := by
    have h : p.b ≤ (F.observation.history p.n).horizon := p.horizon
    rwa [F.observation.horizon_eq] at h
  have hJ : ∀ t ∈ Ioo p.a p.b ∩ Ici T₀,
      T₀ ≤ t ∧ 0 ≤ t ∧ t ≤ (F.observation.history N).horizon := fun t ht =>
    ⟨ht.2, p.a_nonneg.trans ht.1.1.le, hN t (ht.1.2.le.trans hb)⟩
  let tn : ∀ t, t ∈ Ioo p.a p.b ∩ Ici T₀ → Icc (0 : ℝ) (F.tower.history p.n).horizon :=
    fun t ht => patchTime_CPD2 p ht.1
  have hact : ∀ t (ht : t ∈ Ioo p.a p.b ∩ Ici T₀),
      embIdx_CPD6 E.le ((F.observation.history p.n).activeStage (tn t ht)) =
        (F.observation.history N).activeStage ⟨t, (hJ t ht).2.1, (hJ t ht).2.2⟩ :=
    fun t ht => E.activeStage_CPD6 (tn t ht)
  refine
    { hJ := hJ
      stages := ?_
      z := fun q => E.domMap p.first p.last p.ordered (p.map (q.1, ι q.2))
      cont := ?_
      agrees := ?_ }
  · intro t ht
    rw [← hact t ht]
    exact ⟨embIdx_le_CPD6 E.le (p.stages (tn t ht) ht.1).1,
      embIdx_le_CPD6 E.le (p.stages (tn t ht) ht.1).2⟩
  · refine (E.domMap p.first p.last p.ordered).continuous.comp_continuousOn ?_
    refine p.smooth.continuousOn.comp (by fun_prop) ?_
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    exact ⟨ht.1, hy⟩
  · intro t ht y hy
    have key : ∀ j (e : embIdx_CPD6 E.le ((F.observation.history p.n).activeStage (tn t ht)) = j)
        (h1 : embIdx_CPD6 E.le p.first ≤ j) (h2 : j ≤ embIdx_CPD6 E.le p.last),
        HEq ((F.observation.history N).backwardSurvivorMap _ _ (embIdx_le_CPD6 _ p.ordered) j h1 h2
          (E.domMap p.first p.last p.ordered (p.map (t, ι y)))) (f t ht.2 (ι y)) := by
      intro j e
      subst e
      intro h1 h2
      exact (heq_of_eq (E.survivorMap_domMap p.first p.last p.ordered _
        (p.stages (tn t ht) ht.1).1 (p.stages (tn t ht) ht.1).2 (p.map (t, ι y)))).trans
        ((carrierHomeo_heq_CPD2 _ _).trans (p.agrees (tn t ht) ht.1 ht.2 (ι y) hy))
    exact key _ (hact t ht) _ _

end GC.LongTime.CuspP1
