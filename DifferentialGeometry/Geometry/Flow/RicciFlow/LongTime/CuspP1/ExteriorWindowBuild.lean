import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorWindowDatum

/-!
# CP1-D7 (4): one smooth window for finitely many patches around compact sets
-/

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

section Lemma1

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {Hm : FiniteVolumeHyperbolicModel.{u}} {T₀ : ℝ} {α : ℝ → ℝ}
  {domain : ℝ → TopologicalSpace.Opens Hm.Carrier}
  {f : (t : ℝ) → T₀ ≤ t → Hm.Carrier → (postStage F.observation t).Carrier}
  {τ₀ : ℝ}

/-- patches around the points `c k`, restricted to a common time set `J` and a common stage range
`[F', L']` of the `N`-th history, glue to one smooth datum over the union of the neighbourhoods. -/
def smoothDatum_ofPatches_CPD7 {ι : Type*} [Nonempty ι] (c : ι → Hm.Carrier)
    (p : ∀ k, PersistentModelPatch F Hm T₀ α domain f τ₀ (c k)) (N : ℕ)
    (hN : ∀ k, (p k).n ≤ N) (J : Set ℝ) (hJo : IsOpen J)
    (hJ : ∀ k, J ⊆ Ioo (p k).a (p k).b ∩ Ioi T₀)
    (F' L' : Fin ((F.observation.history N).eventCount + 1)) (hFL' : F' ≤ L')
    (hF : ∀ k, embIdx_CPD6 (towerEmb_CPD6 F.observation (p k).n N (hN k)).le (p k).first ≤ F')
    (hL : ∀ k, L' ≤ embIdx_CPD6 (towerEmb_CPD6 F.observation (p k).n N (hN k)).le (p k).last)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
      F' ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
      (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ L') :
    SmoothDatum_CPD7 F.observation T₀ f N J (⋃ k, ((p k).neighborhood : Set Hm.Carrier))
      F' L' hFL' :=
  SmoothDatum_CPD7.glue (fun k => ((p k).neighborhood : Set Hm.Carrier))
    (fun k => (p k).neighborhood.isOpen)
    (fun k =>
      (((patchSmoothDatum_CPD7 (p k) N (hN k)).mono (hJ k) hJo subset_rfl).restrictRange hFL'
        (hF k) (hL k) (fun t ht => hst t
          ((((patchSmoothDatum_CPD7 (p k) N (hN k)).mono (hJ k) hJo subset_rfl).hJ t ht).2.1)
          ((((patchSmoothDatum_CPD7 (p k) N (hN k)).mono (hJ k) hJo subset_rfl).hJ t ht).2.2) ht)))

end Lemma1


section Global

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

theorem basepoint_mem_domain_CPD7 (cores : PersistentHyperbolicCores F K) (i : Fin cores.count)
    {t : ℝ} (ht : cores.start ≤ t) : (cores.model i).basepoint ∈ cores.domain i t := by
  apply cores.advertised_ball i t ht
  have hpos := inv_pos.mpr (cores.accuracy_pos t ht)
  unfold DifferentialGeometry.riemannianBallOf
  simp only [Set.mem_ofPred_eq]
  rw [riemannianEDistOf_self]
  exact ENNReal.ofReal_pos.mpr hpos


theorem exists_smoothWindow_CPD7 (cores : PersistentHyperbolicCores F K) {τ₀ : ℝ}
    (hτ₀ : cores.start < τ₀) (S : ∀ i, Set (cores.model i).Carrier) (hS : ∀ i, IsCompact (S i))
    (hdom : ∀ i, S i ⊆ cores.domain i τ₀) :
    ∃ (N : ℕ) (Fs Ls : Fin ((F.observation.history N).eventCount + 1)) (hFL : Fs ≤ Ls)
      (J : Set ℝ) (U : ∀ i, Set (cores.model i).Carrier)
      (_ : ∀ i, SmoothDatum_CPD7 F.observation cores.start (cores.map i) N J (U i) Fs Ls hFL),
      τ₀ ∈ J ∧ IsOpen J ∧ J ⊆ Ioi cores.start ∧ J.OrdConnected ∧ (∀ i, IsOpen (U i)) ∧
      (∀ i, S i ⊆ U i) ∧ (∀ i, ∀ t ∈ J, ∀ (_ : cores.start ≤ t), U i ⊆ cores.domain i t) ∧
      (∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon) ∧
      (∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
        Fs ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
        (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls) := by
  classical
  set S' : ∀ i, Set (cores.model i).Carrier := fun i => insert (cores.model i).basepoint (S i)
    with hS'def
  have hS'c : ∀ i, IsCompact (S' i) := fun i => (hS i).insert _
  have hS'd : ∀ i, S' i ⊆ cores.domain i τ₀ := fun i =>
    insert_subset (basepoint_mem_domain_CPD7 cores i hτ₀.le) (hdom i)
  have hex : ∀ i (y : (cores.model i).Carrier), y ∈ S' i →
      ∃ _ : PersistentModelPatch F (cores.model i) cores.start cores.accuracy (cores.domain i)
        (cores.map i) τ₀ y, True := fun i y hy =>
    ⟨(cores.static_patches i τ₀ hτ₀.le y (hS'd i hy)).some, trivial⟩
  choose p0 _ using hex
  have hcov : ∀ i, ∃ Ti : Finset ↥(S' i), S' i ⊆ ⋃ y ∈ Ti, ((p0 i y.1 y.2).neighborhood : Set _) :=
    fun i => (hS'c i).elim_nhds_subcover' (fun y hy => ((p0 i y hy).neighborhood : Set _))
      (fun y hy => (p0 i y hy).neighborhood.isOpen.mem_nhds (p0 i y hy).mem_neighborhood)
  choose T hT using hcov
  let κ := Σ i : Fin cores.count, {y // y ∈ T i}
  let pk : ∀ k : κ, PersistentModelPatch F (cores.model k.1) cores.start cores.accuracy
      (cores.domain k.1) (cores.map k.1) τ₀ k.2.1.1 := fun k => p0 k.1 k.2.1.1 k.2.1.2
  let nn : κ → ℕ := fun k => (pk k).n
  let N : ℕ := max (⌈τ₀⌉₊ + 1) (Finset.univ.sup nn)
  have hN : ∀ k : κ, (pk k).n ≤ N := fun k =>
    (Finset.le_sup (f := nn) (Finset.mem_univ k)).trans (le_max_right _ _)
  have hτN : τ₀ < (N : ℝ) := by
    have h1 : τ₀ ≤ (⌈τ₀⌉₊ : ℝ) := Nat.le_ceil τ₀
    have h2 : (⌈τ₀⌉₊ + 1 : ℕ) ≤ N := le_max_left _ _
    have h3 : ((⌈τ₀⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast h2
    push_cast at h3
    linarith
  let J : Set ℝ := Ioo cores.start (N : ℝ) ∩ ⋂ k : κ, Ioo (pk k).a (pk k).b
  have hJo : IsOpen J := isOpen_Ioo.inter (isOpen_iInter_of_finite fun k => isOpen_Ioo)
  have hτJ : τ₀ ∈ J := ⟨⟨hτ₀, hτN⟩, mem_iInter.mpr fun k => ⟨(pk k).before, (pk k).after⟩⟩
  have hJk : ∀ k : κ, J ⊆ Ioo (pk k).a (pk k).b ∩ Ioi cores.start := fun k t ht =>
    ⟨mem_iInter.mp ht.2 k, ht.1.1⟩
  have hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon := by
    intro t ht
    refine ⟨(cores.start_pos.trans ht.1.1).le, ?_⟩
    rw [F.observation.horizon_eq]; exact ht.1.2.le
  let Fk : κ → Fin ((F.observation.history N).eventCount + 1) := fun k =>
    embIdx_CPD6 (towerEmb_CPD6 F.observation (pk k).n N (hN k)).le (pk k).first
  let Lk : κ → Fin ((F.observation.history N).eventCount + 1) := fun k =>
    embIdx_CPD6 (towerEmb_CPD6 F.observation (pk k).n N (hN k)).le (pk k).last
  let Fs := Finset.univ.sup Fk
  let Ls := Finset.univ.inf Lk
  have hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ J →
      Fs ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
      (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls := by
    intro t h0 h1 ht
    refine ⟨Finset.sup_le fun k _ => ?_, Finset.le_inf fun k _ => ?_⟩
    · exact ((patchSmoothDatum_CPD7 (pk k) N (hN k)).stages t (hJk k ht)).1
    · exact ((patchSmoothDatum_CPD7 (pk k) N (hN k)).stages t (hJk k ht)).2
  have hFL : Fs ≤ Ls :=
    let h := hst τ₀ (hJh τ₀ hτJ).1 (hJh τ₀ hτJ).2 hτJ
    h.1.trans h.2
  have hne : ∀ i, Nonempty {y // y ∈ T i} := by
    intro i
    have hb : (cores.model i).basepoint ∈ S' i := mem_insert _ _
    have := hT i hb
    simp only [mem_iUnion] at this
    obtain ⟨y, hy, _⟩ := this
    exact ⟨⟨y, hy⟩⟩
  refine ⟨N, Fs, Ls, hFL, J, fun i => ⋃ k : {y // y ∈ T i}, ((pk ⟨i, k⟩).neighborhood : Set _),
    fun i => ?_, hτJ, hJo, fun t ht => ht.1.1, ?_, fun i => ?_, fun i => ?_, ?_, hJh, hst⟩
  · haveI := hne i
    exact smoothDatum_ofPatches_CPD7 (F := F) (Hm := cores.model i) (T₀ := cores.start)
      (α := cores.accuracy) (domain := cores.domain i) (f := cores.map i) (τ₀ := τ₀)
      (ι := {y // y ∈ T i}) (fun k => k.1.1)
      (fun k : {y // y ∈ T i} => pk ⟨i, k⟩) N (fun k : {y // y ∈ T i} => hN ⟨i, k⟩) J hJo
      (fun k : {y // y ∈ T i} => hJk ⟨i, k⟩) Fs Ls hFL
      (fun k : {y // y ∈ T i} => by exact Finset.le_sup (f := Fk) (Finset.mem_univ (⟨i, k⟩ : κ)))
      (fun k : {y // y ∈ T i} => by exact Finset.inf_le (f := Lk) (Finset.mem_univ (⟨i, k⟩ : κ))) hst
  · exact ordConnected_Ioo.inter (ordConnected_iInter fun k => ordConnected_Ioo)
  · exact isOpen_iUnion fun k => (pk ⟨i, k⟩).neighborhood.isOpen
  · intro y hy
    have := hT i (mem_insert_of_mem _ hy)
    simp only [mem_iUnion] at this
    obtain ⟨z, hz, hyz⟩ := this
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, hyz⟩
  · intro i t ht hst' y hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    exact (pk ⟨i, k⟩).in_domain t (hJk ⟨i, k⟩ ht).1 hst' hk

end Global

end GC.LongTime.CuspP1
