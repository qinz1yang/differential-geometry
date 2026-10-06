import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryExteriorBoundaryDatum

/-!
# CP1-D8 (G1, 2): the smooth window at the base time `cores.start`
-/

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

theorem exists_boundaryWindow_CPD8 (cores : PersistentHyperbolicCores F K)
    (S : ∀ i, Set (cores.model i).Carrier) (hS : ∀ i, IsCompact (S i))
    (hdom : ∀ i, S i ⊆ cores.domain i cores.start) :
    ∃ (N : ℕ) (Fs Ls : Fin ((F.observation.history N).eventCount + 1)) (hFL : Fs ≤ Ls)
      (c : ℝ) (U : ∀ i, Set (cores.model i).Carrier)
      (_ : ∀ i, SmoothDatumC_CPD8 F.observation cores.start (cores.map i) N (Ico cores.start c)
        (U i) Fs Ls hFL),
      cores.start < c ∧ (∀ i, IsOpen (U i)) ∧
      (∀ i, S i ⊆ U i) ∧
      (∀ i, ∀ t ∈ Ico cores.start c, ∀ (_ : cores.start ≤ t), U i ⊆ cores.domain i t) ∧
      (∀ t ∈ Ico cores.start c, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon) ∧
      (∀ t (h0 : 0 ≤ t) (h1 : t ≤ (F.observation.history N).horizon), t ∈ Ico cores.start c →
        Fs ≤ (F.observation.history N).activeStage ⟨t, h0, h1⟩ ∧
        (F.observation.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls) := by
  classical
  set τ₀ := cores.start with hτ₀def
  have hτ₀ : τ₀ ≤ τ₀ := le_rfl
  set S' : ∀ i, Set (cores.model i).Carrier := fun i => insert (cores.model i).basepoint (S i)
    with hS'def
  have hS'c : ∀ i, IsCompact (S' i) := fun i => (hS i).insert _
  have hS'd : ∀ i, S' i ⊆ cores.domain i τ₀ := fun i =>
    insert_subset (basepoint_mem_domain_CPD7 cores i le_rfl) (hdom i)
  have hex : ∀ i (y : (cores.model i).Carrier), y ∈ S' i →
      ∃ _ : PersistentModelPatch F (cores.model i) cores.start cores.accuracy (cores.domain i)
        (cores.map i) τ₀ y, True := fun i y hy =>
    ⟨(cores.static_patches i τ₀ le_rfl y (hS'd i hy)).some, trivial⟩
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
  let V : Set ℝ := Iio (N : ℝ) ∩ ⋂ k : κ, Ioo (pk k).a (pk k).b
  have hVo : IsOpen V := isOpen_Iio.inter (isOpen_iInter_of_finite fun k => isOpen_Ioo)
  have hτV : τ₀ ∈ V := ⟨hτN, mem_iInter.mpr fun k => ⟨(pk k).before, (pk k).after⟩⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVo τ₀ hτV
  let c : ℝ := τ₀ + ε / 2
  have hc : τ₀ < c := by simp only [c]; linarith
  let J : Set ℝ := Ico τ₀ c
  have hJV : ∀ t ∈ J, t ∈ V := fun t ht => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, show c = τ₀ + ε / 2 from rfl])
  have hJk : ∀ k : κ, J ⊆ Ioo (pk k).a (pk k).b ∩ Ici τ₀ := fun k t ht =>
    ⟨mem_iInter.mp (hJV t ht).2 k, ht.1⟩
  have hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (F.observation.history N).horizon := by
    intro t ht
    refine ⟨(cores.start_pos.trans_le ht.1).le, ?_⟩
    rw [F.observation.horizon_eq]; exact (hJV t ht).1.le
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
    · exact ((patchSmoothDatumC_CPD8 (pk k) N (hN k)).stages t (hJk k ht)).1
    · exact ((patchSmoothDatumC_CPD8 (pk k) N (hN k)).stages t (hJk k ht)).2
  have hFL : Fs ≤ Ls :=
    let h := hst τ₀ (hJh τ₀ ⟨le_rfl, hc⟩).1 (hJh τ₀ ⟨le_rfl, hc⟩).2 ⟨le_rfl, hc⟩
    h.1.trans h.2
  have hne : ∀ i, Nonempty {y // y ∈ T i} := by
    intro i
    have hb : (cores.model i).basepoint ∈ S' i := mem_insert _ _
    have := hT i hb
    simp only [mem_iUnion] at this
    obtain ⟨y, hy, _⟩ := this
    exact ⟨⟨y, hy⟩⟩
  refine ⟨N, Fs, Ls, hFL, c, fun i => ⋃ k : {y // y ∈ T i}, ((pk ⟨i, k⟩).neighborhood : Set _),
    fun i => ?_, hc, fun i => ?_, fun i => ?_, ?_, hJh, hst⟩
  · haveI := hne i
    exact smoothDatumC_ofPatches_CPD8 (F := F) (Hm := cores.model i) (T₀ := cores.start)
      (α := cores.accuracy) (domain := cores.domain i) (f := cores.map i) (t₀ := τ₀)
      (ι := {y // y ∈ T i}) (fun k => k.1.1)
      (fun k : {y // y ∈ T i} => pk ⟨i, k⟩) N (fun k : {y // y ∈ T i} => hN ⟨i, k⟩) J
      (fun k : {y // y ∈ T i} => hJk ⟨i, k⟩) Fs Ls hFL
      (fun k : {y // y ∈ T i} => by exact Finset.le_sup (f := Fk) (Finset.mem_univ (⟨i, k⟩ : κ)))
      (fun k : {y // y ∈ T i} => by exact Finset.inf_le (f := Lk) (Finset.mem_univ (⟨i, k⟩ : κ))) hst
  · exact isOpen_iUnion fun k => (pk ⟨i, k⟩).neighborhood.isOpen
  · intro y hy
    have := hT i (mem_insert_of_mem _ hy)
    simp only [mem_iUnion] at this
    obtain ⟨z, hz, hyz⟩ := this
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, hyz⟩
  · intro i t ht hst' y hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    exact (pk ⟨i, k⟩).in_domain t (hJk ⟨i, k⟩ ht).1 hst' hk

end GC.LongTime.CuspP1
