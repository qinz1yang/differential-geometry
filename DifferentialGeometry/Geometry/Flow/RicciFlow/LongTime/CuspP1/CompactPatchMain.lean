import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.CompactPatchKernel

set_option autoImplicit false

/-!
# CP1-D6 (7): compact-set strengthening of `static_patches` and the global kernel statement
-/

noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1

universe u v

section Main

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {Hm : FiniteVolumeHyperbolicModel.{u}} {T₀ : ℝ} {α : ℝ → ℝ}
  {domain : ℝ → TopologicalSpace.Opens Hm.Carrier}
  {f : (t : ℝ) → T₀ ≤ t → Hm.Carrier → (postStage F.observation t).Carrier}
  {X : Type v} [TopologicalSpace X]

/-- A single glued window datum around a time `τ₀`, built from finitely many patches. -/
theorem exists_window_CPD6 [CompactSpace X] (ι : C(X, Hm.Carrier)) (x : X) {τ₀ : ℝ}
    (hτ₀ : T₀ ≤ τ₀)
    (hpt : ∀ y : X, ∃ (x₀ : Hm.Carrier) (p : PersistentModelPatch F Hm T₀ α domain f τ₀ x₀),
      ι y ∈ p.neighborhood) :
    ∃ (W : Set ℝ) (J : Set ℝ) (N : ℕ) (F' L' : Fin ((F.observation.history N).eventCount + 1))
      (hFL : F' ≤ L')
      (D : LocalDatum_CPD6 F.observation T₀ (fun t hT y => f t hT (ι y)) N J univ F' L' hFL),
      IsOpen W ∧ τ₀ ∈ W ∧ τ₀ ∈ J ∧ J.OrdConnected ∧ W ∩ Ici T₀ ⊆ J := by
  choose x₀ p hp using hpt
  have hV : ∀ y, ι ⁻¹' (p y).neighborhood ∈ nhds y := fun y =>
    ((p y).neighborhood.isOpen.preimage ι.continuous).mem_nhds (hp y)
  obtain ⟨S, hS⟩ := CompactSpace.elim_nhds_subcover _ hV
  let κ := {y // y ∈ S}
  have hcov : ∀ y : X, ∃ k : κ, y ∈ ι ⁻¹' (p k.1).neighborhood := by
    intro y
    have : y ∈ (⊤ : Set X) := trivial
    rw [← hS] at this
    simp only [mem_iUnion] at this
    obtain ⟨k, hk, hy⟩ := this
    exact ⟨⟨k, hk⟩, hy⟩
  have : Nonempty κ := (hcov x).elim fun k _ => ⟨k⟩
  let N : ℕ := S.sup fun y => (p y).n
  have hnN : ∀ k : κ, (p k.1).n ≤ N := fun k => Finset.le_sup (f := fun y => (p y).n) k.2
  have hmem : ∀ k : κ, τ₀ ∈ Ioo (p k.1).a (p k.1).b ∩ Ici T₀ := fun k =>
    ⟨⟨(p k.1).before, (p k.1).after⟩, hτ₀⟩
  have hex : ∀ k : κ, ∃ (Fk Lk : Fin ((F.observation.history N).eventCount + 1)) (hk : Fk ≤ Lk),
      Nonempty (LocalDatum_CPD6 F.observation T₀ (fun t hT y => f t hT (ι y)) N
        (Ioo (p k.1).a (p k.1).b ∩ Ici T₀) (ι ⁻¹' ((p k.1).neighborhood : Set Hm.Carrier))
        Fk Lk hk) := fun k =>
    ⟨_, _, _, ⟨patchDatum_CPD6 (p k.1) ι N (hnN k)⟩⟩
  choose Fk Lk hFLk Dk using hex
  let Dk' := fun k => (Dk k).some
  let Fs : Fin ((F.observation.history N).eventCount + 1) := Finset.univ.sup Fk
  let Ls : Fin ((F.observation.history N).eventCount + 1) := Finset.univ.inf Lk
  let J : Set ℝ := ⋂ k : κ, (Ioo (p k.1).a (p k.1).b ∩ Ici T₀)
  have hJsub : ∀ k : κ, J ⊆ (Ioo (p k.1).a (p k.1).b ∩ Ici T₀) := fun k => iInter_subset _ k
  have hτJ : τ₀ ∈ J := mem_iInter.mpr hmem
  have hst : ∀ t (ht : t ∈ J) (k : κ),
      Fk k ≤ (F.observation.history N).activeStage
        ⟨t, ((Dk' k).hJ t (hJsub k ht)).2.1, ((Dk' k).hJ t (hJsub k ht)).2.2⟩ ∧
      (F.observation.history N).activeStage
        ⟨t, ((Dk' k).hJ t (hJsub k ht)).2.1, ((Dk' k).hJ t (hJsub k ht)).2.2⟩ ≤ Lk k :=
    fun t ht k => (Dk' k).stages t (hJsub k ht)
  have hFLs : Fs ≤ Ls := by
    let k0 : κ := Classical.arbitrary κ
    let j0 := (F.observation.history N).activeStage
      ⟨τ₀, ((Dk' k0).hJ τ₀ (hJsub k0 hτJ)).2.1, ((Dk' k0).hJ τ₀ (hJsub k0 hτJ)).2.2⟩
    have h0 : ∀ k : κ, Fk k ≤ j0 ∧ j0 ≤ Lk k := fun k => hst τ₀ hτJ k
    exact (Finset.sup_le fun k _ => (h0 k).1).trans (Finset.le_inf fun k _ => (h0 k).2)
  let D'' : ∀ k : κ, LocalDatum_CPD6 F.observation T₀ (fun t hT y => f t hT (ι y)) N J
      (ι ⁻¹' ((p k.1).neighborhood : Set Hm.Carrier)) Fs Ls hFLs := fun k =>
    ((Dk' k).mono (hJsub k) subset_rfl).restrictRange hFLs
      (Finset.le_sup (f := Fk) (Finset.mem_univ k)) (Finset.inf_le (f := Lk) (Finset.mem_univ k))
      (fun t ht => ⟨Finset.sup_le fun k' _ => (hst t ht k').1,
        Finset.le_inf fun k' _ => (hst t ht k').2⟩)
  refine ⟨⋂ k : κ, Ioo (p k.1).a (p k.1).b, J, N, Fs, Ls, hFLs,
    LocalDatum_CPD6.glue (fun k : κ => ι ⁻¹' ((p k.1).neighborhood : Set Hm.Carrier))
      (fun k => (p k.1).neighborhood.isOpen.preimage ι.continuous) hcov D'', ?_, ?_, hτJ, ?_, ?_⟩
  · exact isOpen_iInter_of_finite fun k => isOpen_Ioo
  · exact mem_iInter.mpr fun k => ⟨(p k.1).before, (p k.1).after⟩
  · exact ordConnected_iInter fun k => ordConnected_Ioo.inter ordConnected_Ici
  · intro t ht
    exact mem_iInter.mpr fun k => ⟨mem_iInter.mp ht.1 k, ht.2⟩

/-- IMS01 on `[T₀, ∞)` for a compact preconnected marked space: patches around every point of
`ι (X)` at every time `τ ≥ T₀` suffice (no common patch needed). -/
theorem kernel_const_Ici_pointwise_CPD6 [CompactSpace X] [PreconnectedSpace X]
    (ι : C(X, Hm.Carrier))
    (hpt : ∀ τ : ℝ, T₀ ≤ τ → ∀ y : X, ∃ (x₀ : Hm.Carrier)
      (p : PersistentModelPatch F Hm T₀ α domain f τ x₀), ι y ∈ p.neighborhood)
    (mc : ∀ t (ht : T₀ ≤ t), C(X, (postStage F.observation t).Carrier))
    (hm : ∀ t ht y, mc t ht y = f t ht (ι y)) (x : X) {s t : ℝ} (hs : T₀ ≤ s) (ht : T₀ ≤ t) :
    (FundamentalGroup.map (mc s hs) x).ker = (FundamentalGroup.map (mc t ht) x).ker := by
  let K : Ici T₀ → Subgroup (FundamentalGroup X x) :=
    fun τ => (FundamentalGroup.map (mc τ.1 τ.2) x).ker
  have hloc : IsLocallyConstant K := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro τ0
    obtain ⟨W, J, N, F', L', hFL, D, hWo, hτW, hτJ, hJord, hWJ⟩ :=
      exists_window_CPD6 (f := f) (α := α) (domain := domain) ι x τ0.2 (hpt τ0.1 τ0.2)
    filter_upwards [(hWo.preimage continuous_subtype_val).mem_nhds hτW] with τ hτ
    exact D.kernel_const hJord mc hm x (hWJ ⟨hτ, τ.2⟩) hτJ
  have : PreconnectedSpace (Ici T₀) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ici
  exact hloc.apply_eq_of_preconnectedSpace ⟨s, hs⟩ ⟨t, ht⟩

end Main

section Cores

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {X : Type v} [TopologicalSpace X]

/-- Compact-set strengthening of `static_patches` in the form needed for IMS01: for a compact
preconnected marked space `X` mapped into the `i`-th model so that it lies in the domain at all
times `t ≥ start`, the kernel of `π₁ X → π₁ M_t` induced by the actual cores is constant on
`[start, ∞)`. -/
theorem kernel_const_Ici_compact_CPD6 (cores : PersistentHyperbolicCores F K)
    (i : Fin cores.count) [CompactSpace X] [PreconnectedSpace X]
    (ι : C(X, (cores.model i).Carrier))
    (hdom : ∀ t (ht : cores.start ≤ t) (y : X), ι y ∈ cores.domain i t)
    (mc : ∀ t (ht : cores.start ≤ t), C(X, (postStage F.observation t).Carrier))
    (hm : ∀ t ht y, mc t ht y = cores.map i t ht (ι y)) (x : X) {s t : ℝ}
    (hs : cores.start ≤ s) (ht : cores.start ≤ t) :
    (FundamentalGroup.map (mc s hs) x).ker = (FundamentalGroup.map (mc t ht) x).ker :=
  kernel_const_Ici_pointwise_CPD6 (F := F) (domain := cores.domain i) (f := cores.map i)
    (α := cores.accuracy) ι
    (fun τ hτ y => ⟨ι y, (cores.static_patches i τ hτ (ι y) (hdom τ hτ y)).some,
      (cores.static_patches i τ hτ (ι y) (hdom τ hτ y)).some.mem_neighborhood⟩) mc hm x hs ht

end Cores

end GC.LongTime.CuspP1
