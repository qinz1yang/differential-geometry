/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SkeletonReduction
import DifferentialGeometry.Topology.PiecewiseLinear.InwardPushStages

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section PointwiseInverse

variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [Nonempty M₁] [TopologicalSpace M₂]
  [T2Space M₂] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂] [HasGroupoid M₁ (plGroupoid n)]
  [HasGroupoid M₂ (plGroupoid n)]

theorem isPLWithinAt_invFunOn_image_of_isCompact {f : M₁ → M₂} {K : Set M₁} (hK : IsCompact K)
    (hcont : ContinuousOn f K) (hinj : InjOn f K) {x : M₁} (hx : x ∈ K)
    (hfK : IsPLWithinAt n n f K x) :
    IsPLWithinAt n n (Function.invFunOn f K) (f '' K) (f x) := by
  classical
  have hleft : LeftInvOn (Function.invFunOn f K) f K := hinj.leftInvOn_invFunOn
  have hgcont : ContinuousOn (Function.invFunOn f K) (f '' K) :=
    continuousOn_invFunOn_image_of_isCompact hK hcont hinj
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
  have hfx : IsPLWithinAt n n f K x := hfK
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

end PointwiseInverse

theorem IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isCompact_mem_nhdsWithin {n m : ℕ}
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {K : Set X}
    (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) m K) {x : X} (hx : x ∈ K) :
    ∃ A ⊆ K, IsCompact A ∧ x ∈ A ∧ A ∈ 𝓝[K] x := by
  obtain ⟨T, -⟩ := hK
  have hmem : x ∈ ⋃ i, T.N i := by rw [T.iUnion_eq]; exact hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
  refine ⟨T.coreSpace (i + 2), T.core_space_subset_union _, T.isCompact_core_space _, ?_,
    T.core_space_mem_nhdsWithin hi⟩
  exact T.core_space_monotone (by omega : i + 1 ≤ i + 2) (T.subset_core i hi)

section Transport

variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂] [T2Space M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
  [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]

theorem isPLHomeomorphInto_comp_of_leftInvOn {K W : Set M₁} {p q : M₁ → M₁} {g : M₁ → M₂}
    (hKloc : ∀ x ∈ K, ∃ A ⊆ K, IsCompact A ∧ x ∈ A ∧ A ∈ 𝓝[K] x) (hW : IsOpen W)
    (hpmaps : MapsTo p K W) (hppl : IsPLOn n n p K) (hpinj : InjOn p K) (hqpl : IsPLOn n n q W)
    (hqp : LeftInvOn q p K) (hg : IsPLHomeomorphInto n g W) :
    IsPLHomeomorphInto n (g ∘ p) K := by
  classical
  have hFpl : IsPLOn n n (g ∘ p) K := hg.isPLOn.comp_of_mapsTo hppl hpmaps
  have hFinj : InjOn (g ∘ p) K := hg.injOn.comp hpinj hpmaps
  have hFcont : ContinuousOn (g ∘ p) K := fun z hz => (hFpl z hz).continuousWithinAt
  refine ⟨hFpl, hFinj, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have : Nonempty M₁ := ⟨x⟩
  have hGleft : LeftInvOn (Function.invFunOn (g ∘ p) K) (g ∘ p) K := hFinj.leftInvOn_invFunOn
  obtain ⟨A, hAK, hAcomp, hxA, hAnhds⟩ := hKloc x hx
  have hFA : IsPLWithinAt n n (g ∘ p) A x :=
    IsPLWithinAt.mono_of_mem_nhdsWithin (hFpl x hx) hAK hAnhds
  have hbase : IsPLWithinAt n n (Function.invFunOn (g ∘ p) A) ((g ∘ p) '' A) ((g ∘ p) x) :=
    isPLWithinAt_invFunOn_image_of_isCompact hAcomp (hFcont.mono hAK) (hFinj.mono hAK) hxA hFA
  have hGeq : ∀ z ∈ (g ∘ p) '' A, Function.invFunOn (g ∘ p) K z =
      Function.invFunOn (g ∘ p) A z := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hGleft (hAK hw), (hFinj.mono hAK).leftInvOn_invFunOn hw]
  have hbase' : IsPLWithinAt n n (Function.invFunOn (g ∘ p) K) ((g ∘ p) '' A) ((g ∘ p) x) :=
    piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem hbase hGeq
      ⟨x, hxA, rfl⟩
  have hYopen : IsOpen (g '' W) := hg.isOpen_image hW
  have hg₀left : LeftInvOn (Function.invFunOn g W) g W := hg.injOn.leftInvOn_invFunOn
  have hg₀cont : ContinuousOn (Function.invFunOn g W) (g '' W) :=
    fun y hy => ((hg.isPLOn_inverse hg₀left) y hy).continuousWithinAt
  have hg₀maps : MapsTo (Function.invFunOn g W) (g '' W) W := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hg₀left hw]
    exact hw
  have hqcont : ContinuousOn q W := fun y hy => (hqpl y hy).continuousWithinAt
  have hQcont : ContinuousOn (q ∘ Function.invFunOn g W) (g '' W) :=
    hqcont.comp hg₀cont hg₀maps
  have hQF : ∀ z ∈ K, (q ∘ Function.invFunOn g W) ((g ∘ p) z) = z := by
    intro z hz
    change q (Function.invFunOn g W (g (p z))) = z
    rw [hg₀left (hpmaps hz), hqp hz]
  have hyY : (g ∘ p) x ∈ g '' W := ⟨p x, hpmaps hx, rfl⟩
  obtain ⟨V, hVopen, hxV, hVA⟩ := mem_nhdsWithin.mp hAnhds
  have hpre0 : (q ∘ Function.invFunOn g W) ⁻¹' V ∈ 𝓝[g '' W] ((g ∘ p) x) :=
    (hQcont _ hyY).preimage_mem_nhdsWithin (hVopen.mem_nhds (by rw [hQF x hx]; exact hxV))
  have hpre : (q ∘ Function.invFunOn g W) ⁻¹' V ∈ 𝓝 ((g ∘ p) x) := by
    rwa [hYopen.nhdsWithin_eq hyY] at hpre0
  have hnb : (g ∘ p) '' A ∈ 𝓝[(g ∘ p) '' K] ((g ∘ p) x) := by
    refine Filter.mem_of_superset
      (Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hpre)) ?_
    rintro _ ⟨⟨z, hz, rfl⟩, hy2⟩
    rw [mem_preimage, hQF z hz] at hy2
    exact ⟨z, hVA ⟨hy2, hz⟩, rfl⟩
  refine ⟨Function.invFunOn (g ∘ p) K, ?_, hGleft⟩
  refine (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_inter' hnb).mp ?_
  rw [inter_eq_right.mpr (image_mono hAK)]
  exact hbase'

end Transport

def Moise352Open (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {U : Set M₁}, IsOpen U →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (U.domRestrict h) →
    ∀ φ : M₁ → ℝ, ContinuousOn φ U → (∀ x ∈ U, 0 < φ x) →
    ∃ f : M₁ → M₂, IsPLHomeomorphInto n f U ∧ ∀ x ∈ U, dist (f x) (h x) < φ x

theorem moise352Open_of_moise352 {m : ℕ} (h352 : Moise352.{u} (m + 1)) :
    Moise352Open.{u} (m + 1) := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ U hU h hh φ hφ hpos
  exact h352.exists_approx_of_isOpen hU hh φ hφ hpos

theorem moise352_of_inwardPush_of_open {n : ℕ} (hpush : Moise352InwardPush.{u} n)
    (hopen : Moise352Open.{u} n) : Moise352.{u} n := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ K hK h hh φ hφ hpos
  obtain ⟨p, q, W, hW, hWint, hpmaps, hppl, hpinj, hqpl, hqmaps, hqp, hclose⟩ :=
    hpush hK hh (fun x => φ x / 2) (hφ.div_const 2) fun x hx => half_pos (hpos x hx)
  have hWK : W ⊆ K := hWint.trans interior_subset
  have hhW : Topology.IsEmbedding (W.domRestrict h) :=
    hh.comp (Topology.IsEmbedding.inclusion hWK)
  have hqcont : ContinuousOn q W := fun y hy => (hqpl y hy).continuousWithinAt
  have hηcont : ContinuousOn (fun y => φ (q y) / 2) W :=
    (show ContinuousOn (fun y => φ (q y)) W from hφ.comp hqcont hqmaps).div_const 2
  have hηpos : ∀ y ∈ W, 0 < φ (q y) / 2 := fun y hy => half_pos (hpos (q y) (hqmaps hy))
  obtain ⟨g, hg, hgclose⟩ := hopen hW hhW (fun y => φ (q y) / 2) hηcont hηpos
  refine ⟨g ∘ p, isPLHomeomorphInto_comp_of_leftInvOn
    (fun x hx => hK.exists_isCompact_mem_nhdsWithin hx) hW hpmaps hppl hpinj hqpl hqp hg,
    fun x hx => ?_⟩
  have h1 : dist (g (p x)) (h (p x)) < φ x / 2 := by
    have h0 : dist (g (p x)) (h (p x)) < φ (q (p x)) / 2 := hgclose (p x) (hpmaps hx)
    rwa [hqp hx] at h0
  have h2 : dist (h (p x)) (h x) < φ x / 2 := hclose x hx
  change dist (g (p x)) (h x) < φ x
  calc dist (g (p x)) (h x) ≤ dist (g (p x)) (h (p x)) + dist (h (p x)) (h x) :=
        dist_triangle _ _ _
    _ < φ x := by linarith

theorem isEmbedding_domRestrict_id_and_exists_isPLHomeomorphInto_dist_lt_univ :
    IsOpen (univ : Set (EuclideanSpace ℝ (Fin 3))) ∧
      Topology.IsEmbedding ((univ : Set (EuclideanSpace ℝ (Fin 3))).domRestrict id) ∧
      ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphInto 3 f univ ∧
          ∀ x ∈ (univ : Set (EuclideanSpace ℝ (Fin 3))), dist (f x) (id x) < 1 := by
  refine ⟨isOpen_univ, ?_, exists_isPLHomeomorphInto_dist_lt_id_of_isOpen isOpen_univ
    fun _ _ => one_pos⟩
  rw [Set.domRestrict_id]
  exact Topology.IsEmbedding.subtypeVal

end DifferentialGeometry.Topology.PiecewiseLinear
