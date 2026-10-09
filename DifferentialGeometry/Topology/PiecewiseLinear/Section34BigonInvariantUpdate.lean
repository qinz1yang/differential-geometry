/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonExterior
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {H : Finset Ea → Set M₂}

theorem Section34CutFrame.disjoint_vertexBallImage_of_nonincident_of_local_pair
    {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {η : M₁ → ℝ}
    {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {s : Section34SimplexIndex 𝒦 3} {w v : Section34VertexIndex 𝒦 𝒦'}
    {e : Section34EdgeIndex 𝒦 𝒦'} {O : Set M₂}
    (hwi : Section34Incident w.1 s.1) (hvi : Section34Incident v.1 s.1)
    (hei : Section34Incident e.1 s.1)
    (hOV : O ∩ (⋃ z, section34VertexBallImage src f₁ z) =
      O ∩ (section34VertexBallImage src f₁ w ∪ section34VertexBallImage src f₁ v))
    (hOE : ∀ e', e' ≠ e → Disjoint O (section34SplitDiskImage src f₁ e')) :
    ∀ z : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident z.1 s.1 →
      Disjoint O (section34VertexBallImage src f₁ z) := by
  obtain ⟨-, -, hf₁, -, -, -, -, -, -, -, -, -, -, -⟩ := hgraph
  intro z hz
  refine disjoint_left.mpr fun x hxO hxz => ?_
  have hpair := ((Set.ext_iff.mp hOV x).mp ⟨hxO, mem_iUnion.mpr ⟨z, hxz⟩⟩).2
  have hmeet : ∃ e', x ∈ section34SplitDiskImage src f₁ e' := by
    rcases hpair with hxw | hxv
    · exact hcut.exists_mem_splitDiskImage_of_ne hf₁.injOn
        (fun (hwz : w = z) => hz (hwz ▸ hwi)) hxw hxz
    · exact hcut.exists_mem_splitDiskImage_of_ne hf₁.injOn
        (fun (hvz : v = z) => hz (hvz ▸ hvi)) hxv hxz
  obtain ⟨e', hxe'⟩ := hmeet
  have he : e' = e := by
    by_contra he
    exact disjoint_left.mp (hOE e' he) hxO hxe'
  subst e'
  exact hz ((Finset.coe_subset.mpr
    (hcut.subset_of_mem_splitDiskImage hf₁.injOn hxe' hxz)).trans hei)

open Classical in
theorem section34FaceBallInvariants_update_of_supported_image
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd fbl fblBd)
    {s : Section34SimplexIndex 𝒦 3} {w v : Section34VertexIndex 𝒦 𝒦'}
    (hwi : Section34Incident w.1 s.1) (hvi : Section34Incident v.1 s.1)
    (Ψ : M₂ ≃ₜ M₂) {O : Set M₂} (hfix : EqOn Ψ id Oᶜ)
    (hV : Ψ '' (⋃ z, tgtV z) = ⋃ z, tgtV z)
    (hOV : O ∩ (⋃ z, tgtV z) = O ∩ (tgtV w ∪ tgtV v))
    (hOH : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      O ⊆ interior (H t.1))
    (hOf : Disjoint O (⋃ s' ≠ s, fbl s'))
    (hOrim : Disjoint O (h '' simplexRim 𝒦 s.1))
    (hforeign : ∀ z : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident z.1 s.1 →
      Disjoint O (tgtV z))
    (hcell : IsPLCellOn 3 (Ψ '' fbl s) (Ψ '' fblBd s))
    (h5 : ∀ y ∈ (Ψ '' fblBd s) ∩ frontier (⋃ z, tgtV z),
      ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
        HasPLCrossingAt (c '' ((Ψ '' fblBd s) ∩ c.source))
          (c '' (frontier (⋃ z, tgtV z) ∩ c.source)) (c y))
    (h6 : ∀ e : Section34EdgeIndex 𝒦 𝒦', ∀ y ∈ (Ψ '' fblBd s) ∩ tgtEBd e,
      ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
        HasPLCurveCrossingOnAt (c '' (frontier (⋃ z, tgtV z) ∩ c.source))
          (c '' ((Ψ '' fblBd s) ∩ frontier (⋃ z, tgtV z) ∩ c.source))
          (c '' (tgtEBd e ∩ c.source)) (c y))
    (h7 : CarriesFirstHomologyOnto ((Ψ '' fblBd s) ∩ frontier (section34FaceTorus tgtV s))
      (section34FaceTorus tgtV s))
    (h8 : ((Ψ '' fblBd s) ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e).Finite)
    (h9 : ((fun y => connectedComponentIn ((Ψ '' fblBd s) ∩ frontier (⋃ z, tgtV z)) y) ''
      ((Ψ '' fblBd s) ∩ frontier (⋃ z, tgtV z))).Finite) :
    Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd
      (Function.update fbl s (Ψ '' fbl s)) (Function.update fblBd s (Ψ '' fblBd s)) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10⟩ := hinv
  have hmem : ∀ x ∈ Oᶜ, x ∈ Ψ '' fbl s ↔ x ∈ fbl s := by
    intro x hx
    constructor
    · rintro ⟨z, hz, hzx⟩
      exact Ψ.injective (hzx.trans (hfix hx).symm) ▸ hz
    · intro hxF
      exact ⟨x, hxF, hfix hx⟩
  have hinter : ∀ s', s' ≠ s → (Ψ '' fbl s) ∩ fbl s' = fbl s ∩ fbl s' := by
    intro s' hs'
    ext x
    have hxO : x ∈ fbl s' → x ∈ Oᶜ := fun hx hxO =>
      disjoint_left.mp hOf hxO (mem_iUnion₂.mpr ⟨s', hs', hx⟩)
    exact ⟨fun hx => ⟨(hmem x (hxO hx.2)).mp hx.1, hx.2⟩,
      fun hx => ⟨(hmem x (hxO hx.2)).mpr hx.1, hx.2⟩⟩
  refine ⟨fun s' => ?_, fun s' => ?_, fun s' z hz => ?_, fun s₁ s₂ hne => ?_,
    fun s' => ?_, fun s' e => ?_, fun s' => ?_, fun s' => ?_, fun s' => ?_,
    hc10.update_image_of_supported hwi hvi Ψ hfix hV hOV hOH hOf⟩
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using hcell
    · simpa only [Function.update_of_ne hs] using hc1 s'
  · rcases eq_or_ne s' s with rfl | hs
    · rw [Function.update_self, ← Ψ.image_interior]
      intro x hx
      exact ⟨x, hc2 s' hx, hfix (fun hxO => disjoint_left.mp hOrim hxO hx)⟩
    · simpa only [Function.update_of_ne hs] using hc2 s'
  · rcases eq_or_ne s' s with rfl | hs
    · rw [Function.update_self]
      refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      have hxO : x ∈ Oᶜ := fun hxO => disjoint_left.mp (hforeign z hz) hxO hx.2
      exact notMem_empty x ((hc3 s' z hz) ▸ ⟨(hmem x hxO).mp hx.1, hx.2⟩)
    · simpa only [Function.update_of_ne hs] using hc3 s' z hz
  · rcases eq_or_ne s₁ s with rfl | hs₁
    · have hs₂ : s₂ ≠ s₁ := Ne.symm hne
      rw [Function.update_self, Function.update_of_ne hs₂, hinter s₂ hs₂]
      exact hc4 s₁ s₂ hne
    · rcases eq_or_ne s₂ s with rfl | hs₂
      · rw [Function.update_of_ne hs₁, Function.update_self, inter_comm,
          hinter s₁ hs₁, inter_comm]
        exact hc4 s₁ s₂ hne
      · simpa only [Function.update_of_ne hs₁, Function.update_of_ne hs₂] using hc4 s₁ s₂ hne
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h5
    · simpa only [Function.update_of_ne hs] using hc5 s'
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h6 e
    · simpa only [Function.update_of_ne hs] using hc6 s' e
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h7
    · simpa only [Function.update_of_ne hs] using hc7 s'
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h8
    · simpa only [Function.update_of_ne hs] using hc8 s'
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [section34TraceComponents, Function.update_self] using h9
    · simpa only [section34TraceComponents, Function.update_of_ne hs] using hc9 s'

end DifferentialGeometry.Topology.PiecewiseLinear
