import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorWindowMain

/-!
# CP1-D8 (G1, 1): smooth survivor families over an arbitrary (not open) time set

Variant of `SmoothDatum_CPD7` without `isOpen_J` (smoothness is `ContMDiffOn`, i.e. within `J ×ˢ U`),
so that time sets such as `[start, c)` are allowed.
-/

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

section Datum

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g)
  {H : FiniteVolumeHyperbolicModel.{u}} (T₀ : ℝ)
  (m : ∀ t : ℝ, T₀ ≤ t → H.Carrier → (postStage T t).Carrier)

structure SmoothDatumC_CPD8 (N : ℕ) (J : Set ℝ) (U : Set H.Carrier)
    (F L : Fin ((T.history N).eventCount + 1)) (hFL : F ≤ L) extends
    LocalDatum_CPD6 T T₀ m N J U F L hFL where
  smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ z (J ×ˢ U)

variable {T T₀ m}

def SmoothDatumC_CPD8.mono {N : ℕ} {J J' : Set ℝ} {U U' : Set H.Carrier}
    {F L : Fin ((T.history N).eventCount + 1)} {hFL : F ≤ L}
    (D : SmoothDatumC_CPD8 T T₀ m N J U F L hFL) (hJ : J' ⊆ J) (hU : U' ⊆ U) :
    SmoothDatumC_CPD8 T T₀ m N J' U' F L hFL where
  toLocalDatum_CPD6 := D.toLocalDatum_CPD6.mono hJ hU
  smooth := D.smooth.mono (prod_mono hJ hU)

def SmoothDatumC_CPD8.restrictRange {N : ℕ} {J : Set ℝ} {U : Set H.Carrier}
    {F L : Fin ((T.history N).eventCount + 1)} {hFL : F ≤ L}
    (D : SmoothDatumC_CPD8 T T₀ m N J U F L hFL)
    {F' L' : Fin ((T.history N).eventCount + 1)} (hFL' : F' ≤ L') (hF : F ≤ F') (hL : L' ≤ L)
    (hst : ∀ t (ht : t ∈ J),
      F' ≤ (T.history N).activeStage ⟨t, (D.hJ t ht).2.1, (D.hJ t ht).2.2⟩ ∧
      (T.history N).activeStage ⟨t, (D.hJ t ht).2.1, (D.hJ t ht).2.2⟩ ≤ L') :
    SmoothDatumC_CPD8 T T₀ m N J U F' L' hFL' where
  toLocalDatum_CPD6 := D.toLocalDatum_CPD6.restrictRange hFL' hF hL hst
  smooth := (contMDiff_restrictDom_CPD7 (T.history N) hFL hFL' hF hL).comp_contMDiffOn D.smooth

/-- smoothness of a time slice -/
theorem SmoothDatumC_CPD8.slice_smooth {N : ℕ} {J : Set ℝ} {U : Set H.Carrier}
    {F L : Fin ((T.history N).eventCount + 1)} {hFL : F ≤ L}
    (D : SmoothDatumC_CPD8 T T₀ m N J U F L hFL) {τ : ℝ} (hτ : τ ∈ J) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun y => D.z (τ, y)) U :=
  D.smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun y hy => ⟨hτ, hy⟩)

def SmoothDatumC_CPD8.glue {κ : Type*} [Nonempty κ] {N : ℕ} {J : Set ℝ} (U : κ → Set H.Carrier)
    (hU : ∀ k, IsOpen (U k))
    {F L : Fin ((T.history N).eventCount + 1)} {hFL : F ≤ L}
    (D : ∀ k, SmoothDatumC_CPD8 T T₀ m N J (U k) F L hFL) :
    SmoothDatumC_CPD8 T T₀ m N J (⋃ k, U k) F L hFL := by
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
        exact this
      smooth := hsm }

end Datum

section Patch

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {Hm : FiniteVolumeHyperbolicModel.{u}} {T₀ : ℝ} {α : ℝ → ℝ}
  {domain : ℝ → TopologicalSpace.Opens Hm.Carrier}
  {f : (t : ℝ) → T₀ ≤ t → Hm.Carrier → (postStage F.observation t).Carrier}
  {t₀ : ℝ} {x₀ : Hm.Carrier}

/-- the smooth datum of a patch over `(a, b) ∩ [T₀, ∞)` (closed at `T₀`) -/
def patchSmoothDatumC_CPD8 (p : PersistentModelPatch F Hm T₀ α domain f t₀ x₀)
    (N : ℕ) (hnN : p.n ≤ N) :
    SmoothDatumC_CPD8 F.observation T₀ f N (Ioo p.a p.b ∩ Ici T₀)
      (p.neighborhood : Set Hm.Carrier)
      (embIdx_CPD6 (towerEmb_CPD6 F.observation p.n N hnN).le p.first)
      (embIdx_CPD6 (towerEmb_CPD6 F.observation p.n N hnN).le p.last)
      (embIdx_le_CPD6 _ p.ordered) where
  toLocalDatum_CPD6 :=
    (patchDatum_CPD6 p (ContinuousMap.id Hm.Carrier) N hnN).mono
      (fun t ht => ht) (fun y hy => hy)
  smooth := by
    refine (contMDiff_domMap_CPD7 (towerEmb_CPD6 F.observation p.n N hnN) p.first p.last
      p.ordered).comp_contMDiffOn (p.smooth.mono ?_)
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    exact ⟨ht.1, hy⟩

def smoothDatumC_ofPatches_CPD8 {ι : Type*} [Nonempty ι] (c : ι → Hm.Carrier)
    (p : ∀ k, PersistentModelPatch F Hm T₀ α domain f t₀ (c k)) (N : ℕ)
    (hN : ∀ k, (p k).n ≤ N) (J : Set ℝ)
    (hJ : ∀ k, J ⊆ Ioo (p k).a (p k).b ∩ Ici T₀)
    (F' L' : Fin ((F.observation.history N).eventCount + 1)) (hFL' : F' ≤ L')
    (hF : ∀ k, embIdx_CPD6 (towerEmb_CPD6 F.observation (p k).n N (hN k)).le (p k).first ≤ F')
    (hL : ∀ k, L' ≤ embIdx_CPD6 (towerEmb_CPD6 F.observation (p k).n N (hN k)).le (p k).last)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
      F' ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
      (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ L') :
    SmoothDatumC_CPD8 F.observation T₀ f N J (⋃ k, ((p k).neighborhood : Set Hm.Carrier))
      F' L' hFL' :=
  SmoothDatumC_CPD8.glue (fun k => ((p k).neighborhood : Set Hm.Carrier))
    (fun k => (p k).neighborhood.isOpen)
    (fun k =>
      (((patchSmoothDatumC_CPD8 (p k) N (hN k)).mono (hJ k) subset_rfl).restrictRange hFL'
        (hF k) (hL k) (fun t ht => hst t
          ((((patchSmoothDatumC_CPD8 (p k) N (hN k)).mono (hJ k) subset_rfl).hJ t ht).2.1)
          ((((patchSmoothDatumC_CPD8 (p k) N (hN k)).mono (hJ k) subset_rfl).hJ t ht).2.2) ht)))

end Patch

end GC.LongTime.CuspP1
