/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Attachment.Basic
import DifferentialGeometry.Topology.Handle.SmoothStage
import DifferentialGeometry.Topology.Manifold.Attachment.AdjunctionSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.ConcaveCornerChart
import DifferentialGeometry.Topology.PiecewiseLinear.SmoothChartFamilyGluing

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Topology.Manifold.Attachment (adjunctionLower_injective
  adjunctionCell_eq_lower_iff adjunction_inclusions_cover adjunction_t2Space
  isClosedEmbedding_adjunctionLower isClosedEmbedding_adjunctionCell)

theorem continuousOn_toHalfSpace :
    ContinuousOn toHalfSpace {v : EuclideanSpace ℝ (Fin 3) | 0 ≤ v 0} := by
  refine (Topology.IsInducing.subtypeVal
    (t := {x : EuclideanSpace ℝ (Fin 3) | 0 ≤ x 0})).continuousOn_iff.mpr ?_
  exact continuousOn_id.congr fun v hv => toHalfSpace_val hv

theorem contMDiffAt_toHalfSpace_comp {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {I : ModelWithCorners ℝ EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {g : N → EuclideanSpace ℝ (Fin 3)} {x : N}
    (hg : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ g x)
    (hpos : ∀ᶠ x' in 𝓝 x, 0 ≤ g x' 0) :
    ContMDiffAt I (𝓡∂ 3) ∞ (fun x' => toHalfSpace (g x')) x := by
  have heq : (fun x' => (toHalfSpace (g x')).val) =ᶠ[𝓝 x] g := by
    filter_upwards [hpos] with x' hx'
    exact toHalfSpace_val hx'
  rw [contMDiffAt_iff_target]
  refine ⟨?_, ?_⟩
  · refine (Topology.IsInducing.subtypeVal
      (t := {v : EuclideanSpace ℝ (Fin 3) | 0 ≤ v 0})).continuousAt_iff.mpr ?_
    exact hg.continuousAt.congr heq.symm
  · simp only [extChartAt_self_eq]
    exact hg.congr_of_eventuallyEq heq

theorem exists_openPartialHomeomorph_of_modelChart {X Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Z] {γ : X → Z} {Γ : Z → X} {C : Set X} {W : Set Z} (hC : IsOpen C)
    (hγc : ContinuousOn γ C) (hΓc : ContinuousOn Γ W) (hγW : MapsTo γ C W) (hΓC : MapsTo Γ W C)
    (hΓγ : ∀ x ∈ C, Γ (γ x) = x) (hγΓ : ∀ p ∈ W, γ (Γ p) = p) {D : Set Z} (hD : IsOpen D)
    {Tg : Set (EuclideanHalfSpace 3)} (hTg : IsOpen Tg) {ζ : Z → EuclideanSpace ℝ (Fin 3)}
    {ζinv : EuclideanSpace ℝ (Fin 3) → Z}
    (hζ : ∀ p ∈ D, p ∈ W → 0 ≤ ζ p 0 ∧ toHalfSpace (ζ p) ∈ Tg)
    (hζinv : ∀ y ∈ Tg, ζinv y.val ∈ D ∧ ζinv y.val ∈ W)
    (hleft : ∀ p ∈ D, p ∈ W → ζinv (ζ p) = p) (hright : ∀ y ∈ Tg, ζ (ζinv y.val) = y.val)
    (hζc : ContinuousOn ζ (D ∩ W))
    (hζinvc : ContinuousOn (fun y : EuclideanHalfSpace 3 => ζinv y.val) Tg) :
    ∃ κ : OpenPartialHomeomorph X (EuclideanHalfSpace 3), κ.source = C ∩ γ ⁻¹' D ∧
      κ.target = Tg ∧ (∀ x, κ x = toHalfSpace (ζ (γ x))) ∧ ∀ y, κ.symm y = Γ (ζinv y.val) := by
  have hto : ContinuousOn (fun x => toHalfSpace (ζ (γ x))) (C ∩ γ ⁻¹' D) := by
    have h1 : ContinuousOn (fun x => ζ (γ x)) (C ∩ γ ⁻¹' D) :=
      hζc.comp (hγc.mono inter_subset_left) fun x hx => ⟨hx.2, hγW hx.1⟩
    exact continuousOn_toHalfSpace.comp h1 fun x hx => (hζ _ hx.2 (hγW hx.1)).1
  have hinv : ContinuousOn (fun y : EuclideanHalfSpace 3 => Γ (ζinv y.val)) Tg :=
    hΓc.comp hζinvc fun y hy => (hζinv y hy).2
  refine ⟨{ toFun := fun x => toHalfSpace (ζ (γ x))
            invFun := fun y => Γ (ζinv y.val)
            source := C ∩ γ ⁻¹' D
            target := Tg
            map_source' := fun x hx => (hζ _ hx.2 (hγW hx.1)).2
            map_target' := fun y hy => by
              obtain ⟨h1, h2⟩ := hζinv y hy
              refine ⟨hΓC h2, ?_⟩
              change γ (Γ (ζinv y.val)) ∈ D
              rw [hγΓ _ h2]
              exact h1
            left_inv' := fun x hx => by
              obtain ⟨h0, -⟩ := hζ _ hx.2 (hγW hx.1)
              rw [toHalfSpace_val h0, hleft _ hx.2 (hγW hx.1), hΓγ x hx.1]
            right_inv' := fun y hy => by
              obtain ⟨-, h2⟩ := hζinv y hy
              rw [hγΓ _ h2, hright y hy]
              exact Subtype.ext (toHalfSpace_val y.2)
            open_source := hγc.isOpen_inter_preimage hC hD
            open_target := hTg
            continuousOn_toFun := hto
            continuousOn_invFun := hinv }, rfl, rfl, fun x => rfl, fun y => rfl⟩

theorem exists_modelCoordinates_of_collar {M A P Z : Type*} [TopologicalSpace M]
    [TopologicalSpace A] [TopologicalSpace P] [TopologicalSpace Z] [CompactSpace A] [T2Space P]
    [T2Space M] {i : A → P} (hi : IsClosedEmbedding i) {ψ : A → M} (hψ : IsClosedEmbedding ψ)
    {Ext : P → Z} (hExt : IsClosedEmbedding Ext) {O : Set Z}
    (hHO : ∀ p ∈ O, p ∈ range Ext → p ∈ range (Ext ∘ i)) (hiO : ∀ z, Ext (i z) ∈ O)
    (hOcl : closure O ∩ range Ext ⊆ O) {V : Set M} (hV : IsOpen V) {θ : M → Z} {Θ : Z → M}
    (hθV : MapsTo θ V O) (hΘO : MapsTo Θ O V) (hΘθ : ∀ m ∈ V, Θ (θ m) = m)
    (hθΘ : ∀ p ∈ O, θ (Θ p) = p) (hΘi : ∀ z, Θ (Ext (i z)) = ψ z) (hθc : ContinuousOn θ V)
    (hΘc : ContinuousOn Θ O) :
    ∃ (γ : AdjunctionSpace i ψ → Z) (Γ : Z → AdjunctionSpace i ψ),
      IsOpen (range (adjunctionCell i ψ) ∪ adjunctionLower ψ '' V) ∧
      ContinuousOn γ (range (adjunctionCell i ψ) ∪ adjunctionLower ψ '' V) ∧
      ContinuousOn Γ (range Ext ∪ O) ∧
      MapsTo γ (range (adjunctionCell i ψ) ∪ adjunctionLower ψ '' V) (range Ext ∪ O) ∧
      MapsTo Γ (range Ext ∪ O) (range (adjunctionCell i ψ) ∪ adjunctionLower ψ '' V) ∧
      (∀ x ∈ range (adjunctionCell i ψ) ∪ adjunctionLower ψ '' V, Γ (γ x) = x) ∧
      (∀ p ∈ range Ext ∪ O, γ (Γ p) = p) ∧
      (∀ b, γ (adjunctionCell i ψ b) = Ext b) ∧ (∀ m, γ (adjunctionLower ψ m) = θ m) ∧
      (∀ b, Γ (Ext b) = adjunctionCell i ψ b) ∧
      ∀ p, p ∉ range Ext → Γ p = adjunctionLower ψ (Θ p) := by
  classical
  have hθψ : ∀ z, θ (ψ z) = Ext (i z) := by
    intro z
    rw [← hΘi z]
    exact hθΘ _ (hiO z)
  have hψV : ∀ z, ψ z ∈ V := by
    intro z
    rw [← hΘi z]
    exact hΘO (hiO z)
  have hlowCE : IsClosedEmbedding (adjunctionLower (i := i) ψ) :=
    isClosedEmbedding_adjunctionLower i ψ hi.injective hψ.injective hi.continuous hψ.continuous
  have hcellCE : IsClosedEmbedding (adjunctionCell i ψ) :=
    isClosedEmbedding_adjunctionCell i ψ hi.injective hψ.injective hi.continuous hψ.continuous
  have hlowinj : Function.Injective (adjunctionLower (i := i) ψ) :=
    adjunctionLower_injective i ψ hi.injective
  have hcl : ∀ b m, adjunctionCell i ψ b = adjunctionLower ψ m → ∃ z, i z = b ∧ ψ z = m :=
    fun b m h => (adjunctionCell_eq_lower_iff i ψ hi.injective b m).mp h
  let C : Set (AdjunctionSpace i ψ) := range (adjunctionCell i ψ) ∪ adjunctionLower ψ '' V
  have hClow : ∀ m, adjunctionLower (i := i) ψ m ∈ C ↔ m ∈ V := by
    intro m
    constructor
    · rintro (⟨b, hb⟩ | ⟨m', hm', he⟩)
      · obtain ⟨z, -, hz⟩ := hcl b m hb
        rw [← hz]
        exact hψV z
      · rwa [hlowinj he] at hm'
    · intro hm
      exact Or.inr ⟨m, hm, rfl⟩
  have hq := isQuotientMap_adjunctionMk i ψ
  have hCopen : IsOpen C := by
    rw [← hq.isOpen_preimage, isOpen_sum_iff]
    constructor
    · have h : Sum.inl ⁻¹' (adjunctionMk i ψ ⁻¹' C) = univ :=
        eq_univ_of_forall fun b => Or.inl ⟨b, rfl⟩
      rw [h]
      exact isOpen_univ
    · have h : Sum.inr ⁻¹' (adjunctionMk i ψ ⁻¹' C) = V := by
        ext m
        exact hClow m
      rw [h]
      exact hV
  let γ : AdjunctionSpace i ψ → Z :=
    Quot.lift (Sum.elim Ext θ) (by
      rintro _ _ ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact (hθψ z).symm
      · exact hθψ z)
  let Γ : Z → AdjunctionSpace i ψ := fun p =>
    if h : p ∈ range Ext then adjunctionCell i ψ h.choose else adjunctionLower ψ (Θ p)
  have hγc : ∀ b, γ (adjunctionCell i ψ b) = Ext b := fun b => rfl
  have hγl : ∀ m, γ (adjunctionLower ψ m) = θ m := fun m => rfl
  have hΓc : ∀ b, Γ (Ext b) = adjunctionCell i ψ b := by
    intro b
    have h : Ext b ∈ range Ext := ⟨b, rfl⟩
    simp only [Γ, dite_eq_left h]
    rw [hExt.injective h.choose_spec]
  have hΓl : ∀ p, p ∉ range Ext → Γ p = adjunctionLower ψ (Θ p) := fun p hp => dite_eq_right hp
  have hγΓ : ∀ p ∈ range Ext ∪ O, γ (Γ p) = p := by
    intro p hp
    by_cases hpe : p ∈ range Ext
    · obtain ⟨b, rfl⟩ := hpe
      rw [hΓc, hγc]
    · rw [hΓl p hpe, hγl]
      exact hθΘ p (hp.resolve_left hpe)
  have hΓγ : ∀ x ∈ C, Γ (γ x) = x := by
    rintro _ (⟨b, rfl⟩ | ⟨m, hm, rfl⟩)
    · rw [hγc, hΓc]
    · rw [hγl]
      by_cases hpe : θ m ∈ range Ext
      · obtain ⟨z, hz⟩ := hHO _ (hθV hm) hpe
        have hmz : m = ψ z := by
          rw [← hΘθ m hm, ← hz]
          exact hΘi z
        rw [← hz, Function.comp_apply, hΓc, hmz, adjunction_coherence]
      · rw [hΓl _ hpe, hΘθ m hm]
  have hγW : MapsTo γ C (range Ext ∪ O) := by
    rintro _ (⟨b, rfl⟩ | ⟨m, hm, rfl⟩)
    · exact Or.inl ⟨b, rfl⟩
    · exact Or.inr (hθV hm)
  have hΓC : MapsTo Γ (range Ext ∪ O) C := by
    intro p hp
    by_cases hpe : p ∈ range Ext
    · obtain ⟨b, rfl⟩ := hpe
      rw [hΓc]
      exact Or.inl ⟨b, rfl⟩
    · rw [hΓl p hpe]
      exact Or.inr ⟨Θ p, hΘO (hp.resolve_left hpe), rfl⟩
  have hγcell : ContinuousOn γ (range (adjunctionCell i ψ)) := by
    rw [← image_univ]
    exact hcellCE.isInducing.continuousOn_image_iff.mpr hExt.continuous.continuousOn
  have hγlow : ContinuousOn γ (adjunctionLower ψ '' V) :=
    hlowCE.isInducing.continuousOn_image_iff.mpr hθc
  have hγcont : ContinuousOn γ C := by
    intro x hx
    have h1 : ContinuousWithinAt γ (range (adjunctionCell i ψ)) x := by
      by_cases hxc : x ∈ range (adjunctionCell i ψ)
      · exact hγcell x hxc
      · exact continuousWithinAt_of_notMem_closure (by rwa [hcellCE.isClosed_range.closure_eq])
    have h2 : ContinuousWithinAt γ (adjunctionLower ψ '' V) x := by
      by_cases hxl : x ∈ adjunctionLower ψ '' V
      · exact hγlow x hxl
      · apply continuousWithinAt_of_notMem_closure
        intro hcl'
        have hxr : x ∈ range (adjunctionLower (i := i) ψ) :=
          hlowCE.isClosed_range.closure_subset (closure_mono (image_subset_range _ _) hcl')
        obtain ⟨m, rfl⟩ := hxr
        exact hxl ⟨m, (hClow m).mp hx, rfl⟩
    exact h1.union h2
  have hΓcont : ContinuousOn Γ (range Ext ∪ O) := by
    have h1 : ContinuousOn Γ (range Ext) := by
      rw [← image_univ]
      refine hExt.isInducing.continuousOn_image_iff.mpr ?_
      have h : Γ ∘ Ext = adjunctionCell i ψ := funext hΓc
      rw [h]
      exact (continuous_adjunctionCell i ψ).continuousOn
    have h2 : ContinuousOn Γ O := by
      have heq : EqOn Γ (fun p => adjunctionLower ψ (Θ p)) O := by
        intro p hp
        by_cases hpe : p ∈ range Ext
        · obtain ⟨z, hz⟩ := hHO p hp hpe
          rw [← hz, Function.comp_apply, hΓc, adjunction_coherence i ψ z]
          exact congrArg (adjunctionLower ψ) (hΘi z).symm
        · exact hΓl p hpe
      exact ((continuous_adjunctionLower i ψ).comp_continuousOn hΘc).congr heq
    intro p hp
    apply ContinuousWithinAt.union
    · by_cases hpe : p ∈ range Ext
      · exact h1 p hpe
      · exact continuousWithinAt_of_notMem_closure (by rwa [hExt.isClosed_range.closure_eq])
    · by_cases hpO : p ∈ O
      · exact h2 p hpO
      · apply continuousWithinAt_of_notMem_closure
        intro hcl'
        rcases hp with hpe | hpO'
        · exact hpO (hOcl ⟨hcl', hpe⟩)
        · exact hpO hpO'
  exact ⟨γ, Γ, hCopen, hγcont, hΓcont, hγW, hΓC, hΓγ, hγΓ, hγc, hγl, hΓc, hΓl⟩

theorem adjunctionLower_boundary_sdiff_union_eq {M A P : Type*} {i : A → P} {ψ : A → M}
    {Bm : Set M} {R : Set A} {Fr : Set P} (hRFr : ∀ z, z ∉ R → i z ∈ Fr) :
    adjunctionLower ψ '' (Bm \ ψ '' R) ∪ adjunctionCell i ψ '' Fr =
      adjunctionLower ψ '' (Bm \ range ψ) ∪ adjunctionCell i ψ '' Fr := by
  ext x
  constructor
  · rintro (⟨m, ⟨hmB, hmR⟩, rfl⟩ | hx)
    · by_cases hm : m ∈ range ψ
      · obtain ⟨z, rfl⟩ := hm
        have hz : z ∉ R := fun hz => hmR ⟨z, hz, rfl⟩
        refine Or.inr ⟨i z, hRFr z hz, ?_⟩
        exact adjunction_coherence i ψ z
      · exact Or.inl ⟨m, ⟨hmB, hm⟩, rfl⟩
    · exact Or.inr hx
  · rintro (⟨m, ⟨hmB, hm⟩, rfl⟩ | hx)
    · exact Or.inl ⟨m, ⟨hmB, fun ⟨z, _, hz⟩ => hm ⟨z, hz⟩⟩, rfl⟩
    · exact Or.inr hx

theorem isSmoothHandleStage_adjunction_of_modelCharts
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    {A P : Type} [TopologicalSpace A] [TopologicalSpace P] [CompactSpace A] [CompactSpace P]
    [T2Space P] {i : A → P} (hi : IsClosedEmbedding i) {ψ : A → M} (hψ : IsClosedEmbedding ψ)
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {Ext : P → Z}
    (hExt : IsClosedEmbedding Ext) {O : Set Z}
    (hHO : ∀ p ∈ O, p ∈ range Ext → p ∈ range (Ext ∘ i)) (hiO : ∀ z, Ext (i z) ∈ O)
    (hOcl : closure O ∩ range Ext ⊆ O) {V : Set M} (hV : IsOpen V) {θ : M → Z} {Θ : Z → M}
    (hθV : MapsTo θ V O) (hΘO : MapsTo Θ O V) (hΘθ : ∀ m ∈ V, Θ (θ m) = m)
    (hθΘ : ∀ p ∈ O, θ (Θ p) = p) (hΘi : ∀ z, Θ (Ext (i z)) = ψ z)
    (hθs : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, Z) ∞ θ V) (hΘs : ContMDiffOn 𝓘(ℝ, Z) (𝓡∂ 3) ∞ Θ O)
    {J : Type} (D : J → Set Z) (hD : ∀ j, IsOpen (D j))
    (Tg : J → Set (EuclideanHalfSpace 3)) (hTg : ∀ j, IsOpen (Tg j))
    (ζ : J → Z → EuclideanSpace ℝ (Fin 3)) (ζinv : J → EuclideanSpace ℝ (Fin 3) → Z)
    (hζ : ∀ j, ∀ p ∈ D j, p ∈ range Ext ∪ O → 0 ≤ ζ j p 0 ∧ toHalfSpace (ζ j p) ∈ Tg j)
    (hζinv : ∀ j, ∀ y ∈ Tg j, ζinv j y.val ∈ D j ∧ ζinv j y.val ∈ range Ext ∪ O)
    (hleft : ∀ j, ∀ p ∈ D j, p ∈ range Ext ∪ O → ζinv j (ζ j p) = p)
    (hright : ∀ j, ∀ y ∈ Tg j, ζ j (ζinv j y.val) = y.val)
    (hζc : ∀ j, ContinuousOn (ζ j) (D j ∩ (range Ext ∪ O)))
    (hζinvc : ∀ j, ContinuousOn (fun y : EuclideanHalfSpace 3 => ζinv j y.val) (Tg j))
    {Rim : Set Z} (hRim : Rim ⊆ range Ext)
    (hA : ∀ j, ∀ y ∈ Tg j, ζinv j y.val ∉ Rim →
      ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, Z) ∞ (fun y : EuclideanHalfSpace 3 => ζinv j y.val) y)
    (hB : ∀ j, ∀ p ∈ D j, p ∈ range Ext ∪ O → p ∉ Rim → ContDiffAt ℝ ∞ (ζ j) p)
    (ρ : Z → J) (hρ : ∀ j, ∀ p ∈ D j, p ∈ Rim → j = ρ p) (hDcov : ∀ b, ∃ j, Ext b ∈ D j)
    {Fr : Set P} (hFr : ∀ j b, Ext b ∈ D j → (ζ j (Ext b) 0 = 0 ↔ b ∈ Fr)) :
    IsSmoothHandleStage (AdjunctionSpace i ψ)
      (adjunctionLower ψ '' ((𝓡∂ 3).boundary M \ range ψ) ∪ adjunctionCell i ψ '' Fr) := by
  classical
  obtain ⟨γ, Γ, hCopen, hγcont, hΓcont, hγW, hΓC, hΓγ, hγΓ, hγc, hγl, hΓc, hΓl⟩ :=
    exists_modelCoordinates_of_collar hi hψ hExt hHO hiO hOcl hV hθV hΘO hΘθ hθΘ hΘi
      hθs.continuousOn hΘs.continuousOn
  have hchart : ∀ j, ∃ κ : OpenPartialHomeomorph (AdjunctionSpace i ψ) (EuclideanHalfSpace 3),
      κ.source = (range (adjunctionCell i ψ) ∪ adjunctionLower ψ '' V) ∩ γ ⁻¹' D j ∧
      κ.target = Tg j ∧ (∀ x, κ x = toHalfSpace (ζ j (γ x))) ∧
      ∀ y, κ.symm y = Γ (ζinv j y.val) := fun j =>
    exists_openPartialHomeomorph_of_modelChart hCopen hγcont hΓcont hγW hΓC hΓγ hγΓ (hD j)
      (hTg j) (hζ j) (hζinv j) (hleft j) (hright j) (hζc j) (hζinvc j)
  choose κ hκs hκt hκf hκi using hchart
  have hθψ : ∀ z, θ (ψ z) = Ext (i z) := by
    intro z
    rw [← hΘi z]
    exact hθΘ _ (hiO z)
  have hT2 : T2Space (AdjunctionSpace i ψ) :=
    adjunction_t2Space i ψ hi.injective hψ.injective hi.continuous hψ.continuous
  have hlowCE : IsClosedEmbedding (adjunctionLower (i := i) ψ) :=
    isClosedEmbedding_adjunctionLower i ψ hi.injective hψ.injective hi.continuous hψ.continuous
  have hcellinj : Function.Injective (adjunctionCell i ψ) :=
    (isClosedEmbedding_adjunctionCell i ψ hi.injective hψ.injective hi.continuous
      hψ.continuous).injective
  have hlowinj : Function.Injective (adjunctionLower (i := i) ψ) :=
    adjunctionLower_injective i ψ hi.injective
  have hcl : ∀ b m, adjunctionCell i ψ b = adjunctionLower ψ m → ∃ z, i z = b ∧ ψ z = m :=
    fun b m h => (adjunctionCell_eq_lower_iff i ψ hi.injective b m).mp h
  have hcover : ∀ x : AdjunctionSpace i ψ,
      x ∈ range (adjunctionCell i ψ) ∨ x ∈ range (adjunctionLower (i := i) ψ) := by
    intro x
    have hx : x ∈ range (adjunctionCell i ψ) ∪ range (adjunctionLower (i := i) ψ) := by
      rw [adjunction_inclusions_cover i ψ]
      trivial
    exact hx
  let Mc : TopologicalSpace.Opens M := ⟨(range ψ)ᶜ, hψ.isClosed_range.isOpen_compl⟩
  have hLlow : ∀ m, adjunctionLower (i := i) ψ m ∈ adjunctionLower ψ '' (Mc : Set M) ↔
      m ∉ range ψ := by
    intro m
    constructor
    · rintro ⟨m', hm', he⟩
      rw [hlowinj he] at hm'
      exact hm'
    · intro hm
      exact ⟨m, hm, rfl⟩
  have hLcell : ∀ b, adjunctionCell i ψ b ∉ adjunctionLower ψ '' (Mc : Set M) := by
    rintro b ⟨m, hm, he⟩
    obtain ⟨z, -, hz⟩ := hcl b m he.symm
    exact hm ⟨z, hz⟩
  have hLopen : IsOpen (adjunctionLower (i := i) ψ '' (Mc : Set M)) := by
    rw [← (isQuotientMap_adjunctionMk i ψ).isOpen_preimage, isOpen_sum_iff]
    constructor
    · have h : Sum.inl ⁻¹' (adjunctionMk i ψ ⁻¹' (adjunctionLower ψ '' (Mc : Set M))) = ∅ :=
        eq_empty_of_forall_notMem fun b hb => hLcell b hb
      rw [h]
      exact isOpen_empty
    · have h : Sum.inr ⁻¹' (adjunctionMk i ψ ⁻¹' (adjunctionLower ψ '' (Mc : Set M))) =
          (range ψ)ᶜ := by
        ext m
        exact hLlow m
      rw [h]
      exact hψ.isClosed_range.isOpen_compl
  have hLE : IsOpenEmbedding (fun p : Mc => adjunctionLower (i := i) ψ p.val) := by
    refine ⟨hlowCE.isEmbedding.comp IsEmbedding.subtypeVal, ?_⟩
    have h : range (fun p : Mc => adjunctionLower (i := i) ψ p.val) =
        adjunctionLower ψ '' (Mc : Set M) := by
      ext x
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨p.val, p.2, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨⟨m, hm⟩, rfl⟩
    rw [h]
    exact hLopen
  have hcellsrc : ∀ b j, Ext b ∈ D j → adjunctionCell i ψ b ∈ (κ j).source := by
    intro b j hj
    rw [hκs]
    refine ⟨Or.inl ⟨b, rfl⟩, ?_⟩
    rw [mem_preimage, hγc]
    exact hj
  have hcov : ∀ x, x ∈ adjunctionLower ψ '' (Mc : Set M) ∨ ∃ j, x ∈ (κ j).source := by
    intro x
    rcases hcover x with ⟨b, rfl⟩ | ⟨m, rfl⟩
    · obtain ⟨j, hj⟩ := hDcov b
      exact Or.inr ⟨j, hcellsrc b j hj⟩
    · by_cases hm : m ∈ range ψ
      · obtain ⟨z, rfl⟩ := hm
        obtain ⟨j, hj⟩ := hDcov (i z)
        refine Or.inr ⟨j, ?_⟩
        rw [← adjunction_coherence i ψ z]
        exact hcellsrc (i z) j hj
      · exact Or.inl ⟨m, hm, rfl⟩
  have hκκ : ∀ j k, ContMDiffOn (𝓡∂ 3) (𝓡∂ 3) ∞ ((κ j).symm.trans (κ k))
      ((κ j).symm.trans (κ k)).source := by
    intro j k
    by_cases hjk : j = k
    · subst hjk
      exact contMDiffOn_id.congr fun y hy => (κ j).right_inv hy.1
    · intro y hy
      apply ContMDiffAt.contMDiffWithinAt
      have hsrc : ∀ y' ∈ ((κ j).symm.trans (κ k)).source,
          y' ∈ Tg j ∧ ζinv j y'.val ∈ D j ∧ ζinv j y'.val ∈ D k ∧
            ζinv j y'.val ∈ range Ext ∪ O := by
        intro y' hy'
        have h1 : y' ∈ Tg j := by
          rw [← hκt j]
          exact hy'.1
        obtain ⟨h2, h3⟩ := hζinv j y' h1
        have h4 : (κ j).symm y' ∈ (κ k).source := hy'.2
        rw [hκs, hκi, mem_inter_iff, mem_preimage, hγΓ _ h3] at h4
        exact ⟨h1, h2, h4.2, h3⟩
      have hval : ∀ y' ∈ ((κ j).symm.trans (κ k)).source,
          ((κ j).symm.trans (κ k)) y' = toHalfSpace (ζ k (ζinv j y'.val)) := by
        intro y' hy'
        obtain ⟨-, -, -, h3⟩ := hsrc y' hy'
        rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hκf, hκi, hγΓ _ h3]
      obtain ⟨hy1, hDj, hDk, hW⟩ := hsrc y hy
      have hrim : ζinv j y.val ∉ Rim := fun h =>
        hjk ((hρ j _ hDj h).trans (hρ k _ hDk h).symm)
      have hg : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
          (fun y' : EuclideanHalfSpace 3 => ζ k (ζinv j y'.val)) y :=
        (hB k _ hDk hW hrim).contMDiffAt.comp y (hA j y hy1 hrim)
      have hpos : ∀ᶠ y' in 𝓝 y, 0 ≤ ζ k (ζinv j y'.val) 0 := by
        filter_upwards [((κ j).symm.trans (κ k)).open_source.mem_nhds hy] with y' hy'
        obtain ⟨-, -, h2, h3⟩ := hsrc y' hy'
        exact (hζ k _ h2 h3).1
      refine (contMDiffAt_toHalfSpace_comp hg hpos).congr_of_eventuallyEq ?_
      filter_upwards [((κ j).symm.trans (κ k)).open_source.mem_nhds hy] with y' hy'
      exact hval y' hy'
  have hfwd : ∀ j, ∀ m ∈ Mc, adjunctionLower (i := i) ψ m ∈ (κ j).source →
      ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (fun m => κ j (adjunctionLower ψ m)) m := by
    intro j m hm hmS
    rw [hκs] at hmS
    obtain ⟨hmC, hmD⟩ := hmS
    have hmV : m ∈ V := by
      rcases hmC with ⟨b, hb⟩ | ⟨m', hm', he⟩
      · obtain ⟨z, -, hz⟩ := hcl b m hb
        exact absurd ⟨z, hz⟩ hm
      · rwa [hlowinj he] at hm'
    have hmD' : θ m ∈ D j := by
      rw [mem_preimage, hγl] at hmD
      exact hmD
    have hfun : (fun m => κ j (adjunctionLower ψ m)) = fun m => toHalfSpace (ζ j (θ m)) := by
      funext m'
      rw [hκf, hγl]
    rw [hfun]
    have hθO : θ m ∈ O := hθV hmV
    have hrim : θ m ∉ Rim := by
      intro h
      obtain ⟨z, hz⟩ := hHO _ hθO (hRim h)
      have hmz : m = ψ z := by
        rw [← hΘθ m hmV, ← hz]
        exact hΘi z
      exact hm ⟨z, hmz.symm⟩
    have hθm : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, Z) ∞ θ m := hθs.contMDiffAt (hV.mem_nhds hmV)
    have hg := (hB j _ hmD' (Or.inr hθO) hrim).contMDiffAt.comp m hθm
    refine contMDiffAt_toHalfSpace_comp hg ?_
    filter_upwards [hV.mem_nhds hmV, hθm.continuousAt.preimage_mem_nhds ((hD j).mem_nhds hmD')]
      with m' h1 h2
    exact (hζ j _ h2 (Or.inr (hθV h1))).1
  let Θj : J → EuclideanHalfSpace 3 → M := fun j y => Θ (ζinv j y.val)
  have hbwd : ∀ j, ∀ y ∈ (κ j).target, (κ j).symm y ∈ adjunctionLower ψ '' (Mc : Set M) →
      Θj j y ∈ Mc ∧ (κ j).symm y = adjunctionLower ψ (Θj j y) ∧
        ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (Θj j) y := by
    intro j y hy hyU
    rw [hκt] at hy
    obtain ⟨-, hyW⟩ := hζinv j y hy
    rw [hκi] at hyU
    have hne : ζinv j y.val ∉ range Ext := by
      rintro ⟨b, hb⟩
      rw [← hb, hΓc] at hyU
      exact hLcell b hyU
    have hO : ζinv j y.val ∈ O := hyW.resolve_left hne
    refine ⟨?_, by rw [hκi, hΓl _ hne], ?_⟩
    · rintro ⟨z, hz⟩
      apply hne
      refine ⟨i z, ?_⟩
      rw [← hθΘ _ hO]
      rw [← hθψ z]
      exact congrArg θ hz
    · have hN : IsOpen (Tg j ∩
          (fun y' : EuclideanHalfSpace 3 => ζinv j y'.val) ⁻¹' (range Ext)ᶜ) :=
        (hζinvc j).isOpen_inter_preimage (hTg j) hExt.isClosed_range.isOpen_compl
      have hmaps : MapsTo (fun y' : EuclideanHalfSpace 3 => ζinv j y'.val)
          (Tg j ∩ (fun y' : EuclideanHalfSpace 3 => ζinv j y'.val) ⁻¹' (range Ext)ᶜ) O :=
        fun y' hy' => ((hζinv j y' hy'.1).2).resolve_left hy'.2
      have hc := (hΘs _ hO).comp y (hA j y hy fun h => hne (hRim h)).contMDiffWithinAt hmaps
      exact hc.contMDiffAt (hN.mem_nhds ⟨hy, hne⟩)
  obtain ⟨cs, hman, hbd⟩ := exists_isManifold_of_isOpenEmbedding_of_charts Mc
    (adjunctionLower ψ) hLE κ hcov hκκ hfwd Θj hbwd
  refine ⟨AdjunctionSpace i ψ, inferInstance, cs, hman, hT2, inferInstance,
    Homeomorph.refl _, ?_⟩
  have himg : ∀ s : Set (AdjunctionSpace i ψ), (Homeomorph.refl (AdjunctionSpace i ψ)) '' s = s :=
    fun s => image_id s
  rw [himg]
  have hcellcase : ∀ b, (𝓡∂ 3).IsBoundaryPoint (adjunctionCell i ψ b) ↔ b ∈ Fr := by
    intro b
    obtain ⟨j, hj⟩ := hDcov b
    have h1 := isBoundaryPoint_iff_any_chart_real (𝓡∂ 3) (hcellsrc b j hj)
    rw [frontier_range_modelWithCornersEuclideanHalfSpace] at h1
    have hval : (𝓡∂ 3) (κ j (adjunctionCell i ψ b)) = ζ j (Ext b) := by
      rw [hκf, hγc]
      exact toHalfSpace_val (hζ j _ hj (Or.inl ⟨b, rfl⟩)).1
    rw [hval] at h1
    rw [h1, ← hFr j b hj]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hcellmem : ∀ b, adjunctionCell i ψ b ∈
      adjunctionLower ψ '' ((𝓡∂ 3).boundary M \ range ψ) ∪ adjunctionCell i ψ '' Fr ↔
        b ∈ Fr := by
    intro b
    constructor
    · rintro (⟨m, hm, he⟩ | ⟨b', hb', he⟩)
      · obtain ⟨z, -, hz⟩ := hcl b m he.symm
        exact absurd ⟨z, hz⟩ hm.2
      · rwa [← hcellinj he]
    · intro hb
      exact Or.inr ⟨b, hb, rfl⟩
  ext x
  rcases hcover x with ⟨b, rfl⟩ | ⟨m, rfl⟩
  · rw [hcellmem]
    exact (hcellcase b).symm
  · by_cases hm : m ∈ range ψ
    · obtain ⟨z, rfl⟩ := hm
      rw [← adjunction_coherence i ψ z, hcellmem]
      exact (hcellcase (i z)).symm
    · have h := hbd m hm
      change _ ↔ (𝓡∂ 3).IsBoundaryPoint (adjunctionLower ψ m)
      rw [h]
      constructor
      · rintro (⟨m', hm', he⟩ | ⟨b, -, he⟩)
        · rw [← hlowinj he]
          exact hm'.1
        · obtain ⟨z, -, hz⟩ := hcl b m he
          exact absurd ⟨z, hz⟩ hm
      · intro hb
        exact Or.inl ⟨m, ⟨hb, hm⟩, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
