import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorWindowBasic
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.CompactPatchMain

/-!
# CP1-D7 (3): smooth survivor families over open sets
-/

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

theorem contMDiff_carrierHomeo_CPD7 {A B : OrientedThreeStage.{u}} (h : A = B) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (carrierHomeo_CPD2 h) := by
  subst h
  exact contMDiff_id

theorem contMDiff_restrictDom_CPD7 (H : ObservedHistory.{u}) {F L F' L' : Fin (H.eventCount + 1)}
    (hFL : F ≤ L) (hFL' : F' ≤ L') (hF : F ≤ F') (hL : L' ≤ L) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (restrictDom_CPD6 H hFL hFL' hF hL) :=
  (ContMDiff.subtypeVal_comp_iff _ _).mp
    (contMDiff_survivorMap_CPD7 H F L hFL L' (hF.trans hFL') hL)

theorem contMDiff_domMap_CPD7 {H K : ObservedHistory.{u}} (E : HistEmb_CPD6 H K)
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (E.domMap first last hle) := by
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  exact (contMDiff_carrierHomeo_CPD7 (E.stage_eq last)).comp contMDiff_subtype_val

section Datum

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g)
  {H : FiniteVolumeHyperbolicModel.{u}} (T₀ : ℝ)
  (m : ∀ t : ℝ, T₀ ≤ t → H.Carrier → (postStage T t).Carrier)

/-- a local datum that is smooth in `(t, y)` on the open time set `J` and the set `U` -/
structure SmoothDatum_CPD7 (N : ℕ) (J : Set ℝ) (U : Set H.Carrier)
    (F L : Fin ((T.history N).eventCount + 1)) (hFL : F ≤ L) extends
    LocalDatum_CPD6 T T₀ m N J U F L hFL where
  isOpen_J : IsOpen J
  smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ z (J ×ˢ U)

variable {T T₀ m}

def SmoothDatum_CPD7.mono {N : ℕ} {J J' : Set ℝ} {U U' : Set H.Carrier}
    {F L : Fin ((T.history N).eventCount + 1)} {hFL : F ≤ L}
    (D : SmoothDatum_CPD7 T T₀ m N J U F L hFL) (hJ : J' ⊆ J) (hJ' : IsOpen J') (hU : U' ⊆ U) :
    SmoothDatum_CPD7 T T₀ m N J' U' F L hFL where
  toLocalDatum_CPD6 := D.toLocalDatum_CPD6.mono hJ hU
  isOpen_J := hJ'
  smooth := D.smooth.mono (prod_mono hJ hU)

def SmoothDatum_CPD7.restrictRange {N : ℕ} {J : Set ℝ} {U : Set H.Carrier}
    {F L : Fin ((T.history N).eventCount + 1)} {hFL : F ≤ L}
    (D : SmoothDatum_CPD7 T T₀ m N J U F L hFL)
    {F' L' : Fin ((T.history N).eventCount + 1)} (hFL' : F' ≤ L') (hF : F ≤ F') (hL : L' ≤ L)
    (hst : ∀ t (ht : t ∈ J),
      F' ≤ (T.history N).activeStage ⟨t, (D.hJ t ht).2.1, (D.hJ t ht).2.2⟩ ∧
      (T.history N).activeStage ⟨t, (D.hJ t ht).2.1, (D.hJ t ht).2.2⟩ ≤ L') :
    SmoothDatum_CPD7 T T₀ m N J U F' L' hFL' where
  toLocalDatum_CPD6 := D.toLocalDatum_CPD6.restrictRange hFL' hF hL hst
  isOpen_J := D.isOpen_J
  smooth := (contMDiff_restrictDom_CPD7 (T.history N) hFL hFL' hF hL).comp_contMDiffOn D.smooth

/-- gluing over a family of open sets -/
def SmoothDatum_CPD7.glue {κ : Type*} [Nonempty κ] {N : ℕ} {J : Set ℝ} (U : κ → Set H.Carrier)
    (hU : ∀ k, IsOpen (U k))
    {F L : Fin ((T.history N).eventCount + 1)} {hFL : F ≤ L}
    (D : ∀ k, SmoothDatum_CPD7 T T₀ m N J (U k) F L hFL) :
    SmoothDatum_CPD7 T T₀ m N J (⋃ k, U k) F L hFL := by
  classical
  let k0 : κ := Classical.arbitrary κ
  let zz : ℝ × H.Carrier → (T.history N).backwardSurvivorDomain F L hFL := fun q =>
    if h : ∃ k, q.2 ∈ U k then (D (Classical.choose h)).z q else (D k0).z q
  have hzz : ∀ k, ∀ q : ℝ × H.Carrier, q.1 ∈ J → q.2 ∈ U k → zz q = (D k).z q := by
    intro k q hq1 hq2
    have h : ∃ k, q.2 ∈ U k := ⟨k, hq2⟩
    simp only [zz, h, ↓reduceDIte]
    exact (D (Classical.choose h)).toLocalDatum_CPD6.unique (D k).toLocalDatum_CPD6 hq1
      (Classical.choose_spec h) hq2
  have hsm : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ zz (J ×ˢ ⋃ k, U k) := by
    apply contMDiffOn_of_locally_contMDiffOn
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    refine ⟨univ ×ˢ U k, isOpen_univ.prod (hU k), ⟨mem_univ _, hk⟩, ?_⟩
    refine ((D k).smooth.mono ?_).congr ?_
    · rintro ⟨t', y'⟩ ⟨⟨h1, _⟩, ⟨_, h2⟩⟩
      exact ⟨h1, h2⟩
    · rintro ⟨t', y'⟩ ⟨⟨h1, _⟩, ⟨_, h2⟩⟩
      exact hzz k (t', y') h1 h2
  exact
    { hJ := (D k0).hJ
      stages := (D k0).stages
      z := zz
      cont := hsm.continuousOn
      agrees := fun t ht y hy => by
        obtain ⟨k, hk⟩ := mem_iUnion.mp hy
        have := (D k).agrees t ht y hk
        rw [hzz k (t, y) ht hk]
        exact (by
          have h2 := (D k0).hJ t ht
          have e1 : (T.history N).activeStage ⟨t, (D k).hJ t ht |>.2.1, (D k).hJ t ht |>.2.2⟩ =
            (T.history N).activeStage ⟨t, (D k0).hJ t ht |>.2.1, (D k0).hJ t ht |>.2.2⟩ := rfl
          exact this)
      isOpen_J := (D k0).isOpen_J
      smooth := hsm }

end Datum

section Patch

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {Hm : FiniteVolumeHyperbolicModel.{u}} {T₀ : ℝ} {α : ℝ → ℝ}
  {domain : ℝ → TopologicalSpace.Opens Hm.Carrier}
  {f : (t : ℝ) → T₀ ≤ t → Hm.Carrier → (postStage F.observation t).Carrier}
  {t₀ : ℝ} {x₀ : Hm.Carrier}

/-- the smooth datum of a patch over the open time set `(a, b) ∩ (T₀, ∞)` and its neighbourhood -/
def patchSmoothDatum_CPD7 (p : PersistentModelPatch F Hm T₀ α domain f t₀ x₀)
    (N : ℕ) (hnN : p.n ≤ N) :
    SmoothDatum_CPD7 F.observation T₀ f N (Ioo p.a p.b ∩ Ioi T₀)
      (p.neighborhood : Set Hm.Carrier)
      (embIdx_CPD6 (towerEmb_CPD6 F.observation p.n N hnN).le p.first)
      (embIdx_CPD6 (towerEmb_CPD6 F.observation p.n N hnN).le p.last)
      (embIdx_le_CPD6 _ p.ordered) where
  toLocalDatum_CPD6 :=
    (patchDatum_CPD6 p (ContinuousMap.id Hm.Carrier) N hnN).mono
      (fun t ht => ⟨ht.1, mem_Ici.mpr (le_of_lt ht.2)⟩) (fun y hy => hy)
  isOpen_J := isOpen_Ioo.inter isOpen_Ioi
  smooth := by
    refine (contMDiff_domMap_CPD7 (towerEmb_CPD6 F.observation p.n N hnN) p.first p.last
      p.ordered).comp_contMDiffOn (p.smooth.mono ?_)
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    exact ⟨ht.1, hy⟩

end Patch


end GC.LongTime.CuspP1
