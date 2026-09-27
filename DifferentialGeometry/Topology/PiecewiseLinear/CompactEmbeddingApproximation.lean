/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Transition361
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem continuousOn_invFunOn_image_of_isCompact {X Y : Type*} [Nonempty X] [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {f : X → Y} {s : Set X} (hs : IsCompact s)
    (hf : ContinuousOn f s) (hinj : InjOn f s) :
    ContinuousOn (Function.invFunOn f s) (f '' s) := by
  rw [continuousOn_iff_isClosed]
  intro C hC
  refine ⟨f '' (C ∩ s), (hs.inter_left hC).image_of_continuousOn (hf.mono inter_subset_right)
    |>.isClosed, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, x, hx, rfl⟩
    rw [mem_preimage, hinj.leftInvOn_invFunOn hx] at hy
    exact ⟨⟨x, ⟨hy, hx⟩, rfl⟩, ⟨x, hx, rfl⟩⟩
  · rintro ⟨⟨x, ⟨hxC, hxs⟩, rfl⟩, -⟩
    exact ⟨by rw [mem_preimage, hinj.leftInvOn_invFunOn hxs]; exact hxC, ⟨x, hxs, rfl⟩⟩

theorem exists_pos_forall_le_of_continuousOn {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {φ : X → ℝ} (hφ : ContinuousOn φ K) (hpos : ∀ x ∈ K, 0 < φ x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ε ≤ φ x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun x hx => hx.elim⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hφ
  exact ⟨φ x₀, hpos x₀ hx₀, fun x hx => isMinOn_iff.mp hmin x hx⟩

section Embedding

variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂] [T2Space M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
  [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]

theorem IsPLOn.isPLHomeomorphInto {f : M₁ → M₂} {K : Set M₁} (hf : IsPLOn n n f K)
    (hK : IsCompact K) (hinj : InjOn f K) : IsPLHomeomorphInto n f K := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact isPLHomeomorphInto_empty f
  have hne : Nonempty M₁ := ⟨hKne.choose⟩
  have hcont : ContinuousOn f K := fun z hz => (hf z hz).continuousWithinAt
  have hleft : LeftInvOn (Function.invFunOn f K) f K := hinj.leftInvOn_invFunOn
  have hgcont : ContinuousOn (Function.invFunOn f K) (f '' K) :=
    continuousOn_invFunOn_image_of_isCompact hK hcont hinj
  rw [isPLHomeomorphInto_iff_exists_inverse]
  refine ⟨hf, hinj, Function.invFunOn f K, ?_, hleft⟩
  rintro _ ⟨x, hx, rfl⟩
  change IsPLWithinAt n n (Function.invFunOn f K) (f '' K) (f x)
  set e := chartAt (EuclideanSpace ℝ (Fin n)) x with he_def
  set e' := chartAt (EuclideanSpace ℝ (Fin n)) (f x) with he'_def
  have hex : x ∈ e.source := mem_chart_source _ x
  have hey : f x ∈ e'.source := mem_chart_source _ (f x)
  have hmaxe : e ∈ (plGroupoid n).maximalAtlas M₁ :=
    StructureGroupoid.chart_mem_maximalAtlas _ x
  have hmaxe' : e' ∈ (plGroupoid n).maximalAtlas M₂ :=
    StructureGroupoid.chart_mem_maximalAtlas _ (f x)
  have hgy : Function.invFunOn f K (f x) ∈ e.source := by rw [hleft hx]; exact hex
  rw [isPLWithinAt_iff_of_mem_maximalAtlas hmaxe' hey hmaxe hgy]
  refine ⟨hgcont (f x) ⟨x, hx, rfl⟩, ?_⟩
  have hfx : IsPLWithinAt n n f K x := hf x hx
  rw [isPLWithinAt_iff_of_mem_maximalAtlas hmaxe hex hmaxe' hey] at hfx
  obtain ⟨-, hFpa⟩ := hfx
  obtain ⟨U₀, hU₀open, hxU₀, hU₀sub⟩ := mem_nhdsWithin.mp
    ((hcont x hx).preimage_mem_nhdsWithin (e'.open_source.mem_nhds hey))
  have hT₀open : IsOpen (e.target ∩ e.symm ⁻¹' U₀) := e.isOpen_inter_preimage_symm hU₀open
  have hexT : e x ∈ e.target ∩ e.symm ⁻¹' U₀ :=
    ⟨e.map_source hex, by simp only [mem_preimage, e.left_inv hex]; exact hxU₀⟩
  obtain ⟨ι, hι, C, A, hCprop, hCnhds⟩ := hFpa.inter_of_mem_nhds (hT₀open.mem_nhds hexT)
  have hPpoly : IsPolyhedron (⋃ i, C i) := ⟨ι, hι, C, fun i => (hCprop i).1, rfl⟩
  have hPsub : (⋃ i, C i) ⊆ e.symm ⁻¹' K ∩ (e.target ∩ e.symm ⁻¹' U₀) :=
    iUnion_subset fun i => (hCprop i).2.1
  have hPtarget : ∀ z ∈ ⋃ i, C i, z ∈ e.target := fun z hz => (hPsub hz).2.1
  have hPK : ∀ z ∈ ⋃ i, C i, e.symm z ∈ K := fun z hz => (hPsub hz).1
  have hPsrc : ∀ z ∈ ⋃ i, C i, f (e.symm z) ∈ e'.source := fun z hz =>
    hU₀sub ⟨(hPsub hz).2.2, hPK z hz⟩
  have hFP : IsPiecewiseAffineOn (e' ∘ f ∘ e.symm) (⋃ i, C i) := by
    intro z _
    exact ⟨ι, hι, C, A, fun i => ⟨(hCprop i).1, subset_iUnion C i, (hCprop i).2.2⟩,
      self_mem_nhdsWithin⟩
  have hFinj : InjOn (e' ∘ f ∘ e.symm) (⋃ i, C i) := by
    intro z hz w hw hzw
    simp only [Function.comp_apply] at hzw
    have h1 : f (e.symm z) = f (e.symm w) := by
      rw [← e'.left_inv (hPsrc z hz), ← e'.left_inv (hPsrc w hw), hzw]
    rw [← e.right_inv (hPtarget z hz), ← e.right_inv (hPtarget w hw),
      hinj (hPK z hz) (hPK w hw) h1]
  have hinvpa : IsPiecewiseAffineOn (Function.invFunOn (e' ∘ f ∘ e.symm) (⋃ i, C i))
      ((e' ∘ f ∘ e.symm) '' ⋃ i, C i) :=
    (isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hPpoly hFP hFinj.bijOn_image).2.2
  have hFPsub : (e' ∘ f ∘ e.symm) '' (⋃ i, C i) ⊆ e'.symm ⁻¹' (f '' K) := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [mem_preimage, Function.comp_apply, e'.left_inv (hPsrc z hz)]
    exact ⟨e.symm z, hPK z hz, rfl⟩
  have hGeq : EqOn (e ∘ Function.invFunOn f K ∘ e'.symm)
      (Function.invFunOn (e' ∘ f ∘ e.symm) (⋃ i, C i)) ((e' ∘ f ∘ e.symm) '' ⋃ i, C i) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hFinj.leftInvOn_invFunOn hz]
    simp only [Function.comp_apply, e'.left_inv (hPsrc z hz), hleft (hPK z hz),
      e.right_inv (hPtarget z hz)]
  have hexS : e x ∈ e.symm ⁻¹' K ∩ (e.target ∩ e.symm ⁻¹' U₀) := by
    refine ⟨?_, hexT⟩
    simp only [mem_preimage, e.left_inv hex]
    exact hx
  have hexP : e x ∈ ⋃ i, C i := mem_of_mem_nhdsWithin hexS hCnhds
  have hyP : e' (f x) ∈ (e' ∘ f ∘ e.symm) '' ⋃ i, C i := by
    refine ⟨e x, hexP, ?_⟩
    simp only [Function.comp_apply, e.left_inv hex]
  obtain ⟨V₁, hV₁open, hexV₁, hV₁sub⟩ := mem_nhdsWithin.mp hCnhds
  have hVopen : IsOpen (e.source ∩ e ⁻¹' (V₁ ∩ (e.target ∩ e.symm ⁻¹' U₀))) :=
    e.isOpen_inter_preimage (hV₁open.inter hT₀open)
  have hxV : x ∈ e.source ∩ e ⁻¹' (V₁ ∩ (e.target ∩ e.symm ⁻¹' U₀)) := ⟨hex, hexV₁, hexT⟩
  have hKV : ∀ z ∈ K, z ∈ e.source ∩ e ⁻¹' (V₁ ∩ (e.target ∩ e.symm ⁻¹' U₀)) →
      z ∈ e.symm '' ⋃ i, C i := by
    intro z hz hzV
    refine ⟨e z, hV₁sub ⟨hzV.2.1, ?_, hzV.2.2⟩, e.left_inv hzV.1⟩
    simp only [mem_preimage, e.left_inv hzV.1]
    exact hz
  have hclosed : IsClosed
      (f '' (K \ (e.source ∩ e ⁻¹' (V₁ ∩ (e.target ∩ e.symm ⁻¹' U₀))))) :=
    ((hK.diff hVopen).image_of_continuousOn (hcont.mono Set.sdiff_subset)).isClosed
  have hynot : f x ∉ f '' (K \ (e.source ∩ e ⁻¹' (V₁ ∩ (e.target ∩ e.symm ⁻¹' U₀)))) := by
    rintro ⟨z, hz, hzy⟩
    exact hz.2 (hinj hz.1 hx hzy ▸ hxV)
  have hO'open : IsOpen (e'.target ∩ e'.symm ⁻¹'
      (f '' (K \ (e.source ∩ e ⁻¹' (V₁ ∩ (e.target ∩ e.symm ⁻¹' U₀)))))ᶜ) :=
    e'.isOpen_inter_preimage_symm hclosed.isOpen_compl
  have hyO' : e' (f x) ∈ e'.target ∩ e'.symm ⁻¹'
      (f '' (K \ (e.source ∩ e ⁻¹' (V₁ ∩ (e.target ∩ e.symm ⁻¹' U₀)))))ᶜ :=
    ⟨e'.map_source hey, by simp only [mem_preimage, e'.left_inv hey]; exact hynot⟩
  have hkey : e'.symm ⁻¹' (f '' K) ∩ (e'.target ∩ e'.symm ⁻¹'
      (f '' (K \ (e.source ∩ e ⁻¹' (V₁ ∩ (e.target ∩ e.symm ⁻¹' U₀)))))ᶜ) ⊆
      (e' ∘ f ∘ e.symm) '' ⋃ i, C i := by
    rintro w ⟨⟨z, hz, hzw⟩, hw2, hw3⟩
    have hzV : z ∈ e.source ∩ e ⁻¹' (V₁ ∩ (e.target ∩ e.symm ⁻¹' U₀)) := by
      by_contra hcon
      exact hw3 ⟨z, ⟨hz, hcon⟩, hzw⟩
    obtain ⟨u, huP, hu⟩ := hKV z hz hzV
    refine ⟨u, huP, ?_⟩
    simp only [Function.comp_apply, hu, hzw]
    exact e'.right_inv hw2
  obtain ⟨κ, hκ, D, B, hDprop, hDnhds⟩ := hinvpa (e' (f x)) hyP
  obtain ⟨V₂, hV₂open, hyV₂, hV₂sub⟩ := mem_nhdsWithin.mp hDnhds
  refine ⟨κ, hκ, D, B, fun j => ⟨(hDprop j).1, ((hDprop j).2.1).trans hFPsub, ?_⟩, ?_⟩
  · exact fun w hw => (hGeq ((hDprop j).2.1 hw)).trans ((hDprop j).2.2 hw)
  · refine mem_nhdsWithin.mpr ⟨V₂ ∩ (e'.target ∩ e'.symm ⁻¹'
      (f '' (K \ (e.source ∩ e ⁻¹' (V₁ ∩ (e.target ∩ e.symm ⁻¹' U₀)))))ᶜ),
      hV₂open.inter hO'open, ⟨hyV₂, hyO'⟩, ?_⟩
    rintro w ⟨⟨hw2, hw3⟩, hw1⟩
    exact hV₂sub ⟨hw2, hkey ⟨hw1, hw3⟩⟩

end Embedding

section Reduction

variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [MetricSpace M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
  [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]

theorem exists_isPLHomeomorphInto_dist_lt_of_forall_exists_injective {K : Set M₁}
    (hK : IsCompact K) {h : M₁ → M₂} {φ : M₁ → ℝ} (hφ : ContinuousOn φ K)
    (hpos : ∀ x ∈ K, 0 < φ x)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ f : M₁ → M₂, IsPLOn n n f K ∧ InjOn f K ∧
      ∀ x ∈ K, dist (f x) (h x) < ε) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto n f K ∧ ∀ x ∈ K, dist (f x) (h x) < φ x := by
  obtain ⟨ε, hε, hle⟩ := exists_pos_forall_le_of_continuousOn hK hφ hpos
  obtain ⟨f, hf, hinj, hdist⟩ := happrox ε hε
  exact ⟨f, hf.isPLHomeomorphInto hK hinj, fun x hx => (hdist x hx).trans_le (hle x hx)⟩

end Reduction

end DifferentialGeometry.Topology.PiecewiseLinear
