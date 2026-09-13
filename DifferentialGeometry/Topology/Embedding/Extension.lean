/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import DifferentialGeometry.Topology.Embedding.Retraction
import DifferentialGeometry.Analysis.Calculus.CompactCutoff
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.HalfSpace
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Instances.Real

section
open scoped ContDiff Manifold Topology

namespace Manifold

open Set

private theorem exists_contDiff_extension_of_local
    {M : Type*} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞} {f : M → V} {g : M → F} {K : Set M}
    (hK : IsClosed (f '' K))
    (hloc : ∀ x ∈ K, ∃ U ∈ 𝓝 (f x), ∃ G : V → F, ContDiffOn ℝ n G U ∧
      ∀ y ∈ K, f y ∈ U → G (f y) = g y) :
    ∃ G : V → F, ContDiff ℝ n G ∧ EqOn (G ∘ f) g K := by
  let C : V → Set F := fun z => {v | ∀ x ∈ K, f x = z → v = g x}
  have hC (z : V) : Convex ℝ (C z) := by
    rw [convex_iff_add_mem]
    intro a ha b hb s t _ _ hsum x hx hfx
    rw [ha x hx hfx, hb x hx hfx, ← add_smul, hsum, one_smul]
  have hlocal (z : V) : ∃ U ∈ 𝓝 z, ∃ G : V → F,
      ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, F) n G U ∧ ∀ y ∈ U, G y ∈ C y := by
    by_cases hz : z ∈ f '' K
    · obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨U, hU, G, hG, hGf⟩ := hloc x hx
      refine ⟨U, hU, G, hG.contMDiffOn, ?_⟩
      intro y hy x' hx' hxy
      subst y
      exact hGf x' hx' hy
    · refine ⟨(f '' K)ᶜ, hK.isOpen_compl.mem_nhds hz, 0, contMDiffOn_const, ?_⟩
      intro y hy x hx hxy
      exact False.elim (hy ⟨x, hx, hxy⟩)
  obtain ⟨G, hG⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    (I := 𝓘(ℝ, V)) (n := n) hC hlocal
  exact ⟨G, G.contMDiff.contDiff, fun x hx => hG (f x) x hx rfl⟩

private theorem exists_contDiff_compact_extension_of_eqOn
    {M : Type*} [TopologicalSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞} {f : M → V} {g : M → F} {K : Set M}
    {G : V → F} (hG : ContDiff ℝ n G) (hGf : EqOn (G ∘ f) g K)
    (hA : IsCompact (f '' (K ∩ tsupport g))) {O : Set V} (hO : IsOpen O)
    (hAO : f '' (K ∩ tsupport g) ⊆ O) :
    ∃ G : V → F, ContDiff ℝ n G ∧ HasCompactSupport G ∧
      tsupport G ⊆ O ∧ EqOn (G ∘ f) g K := by
  obtain ⟨χ, hχ, hχc, hχone, hχO, -⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hA hO hAO
  have hχn : ContDiff ℝ n χ := hχ.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨fun z => χ z • G z, hχn.smul hG, hχc.smul_right,
    (tsupport_smul_subset_left χ G).trans hχO, ?_⟩
  intro x hx
  change χ (f x) • G (f x) = g x
  rw [show G (f x) = g x from hGf hx]
  by_cases hxg : x ∈ tsupport g
  · rw [hχone.self_of_nhdsSet (mem_image_of_mem f ⟨hx, hxg⟩), Pi.one_apply, one_smul]
  · rw [image_eq_zero_of_notMem_tsupport hxg, smul_zero]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ∞} {f : M → V} {g : M → F} {K : Set M}

theorem IsSmoothEmbedding.exists_contDiff_extension_of_isClosed_image
    (hf : IsSmoothEmbedding I 𝓘(ℝ, V) n f) (hg : ContMDiff I 𝓘(ℝ, F) n g)
    (hK : IsClosed (f '' K)) :
    ∃ G : V → F, ContDiff ℝ n G ∧ EqOn (G ∘ f) g K := by
  apply exists_contDiff_extension_of_local hK
  intro x _
  obtain ⟨U, hxU, r, hr, _, hfix⟩ := hf.exists_contMDiff_local_retraction x
  let G : V → F := Subtype.val.extend (fun q : U => g (r q)) 0
  have hG (q : U) : G q = g (r q) :=
    Subtype.val_injective.extend_apply (fun q : U => g (r q)) 0 q
  have hGU : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, F) n (fun q : U => G q) :=
    (hg.comp hr).congr hG
  refine ⟨U, U.isOpen.mem_nhds hxU, G, ?_, ?_⟩
  · apply contMDiffOn_iff_contDiffOn.mp
    intro y hy
    exact (contMDiffAt_subtype_iff.mp (hGU ⟨y, hy⟩)).contMDiffWithinAt
  · intro y _ hy
    rw [hG ⟨f y, hy⟩, hfix y hy]

theorem IsSmoothEmbedding.exists_contDiff_compact_extension_of_tsupport_image_subset
    (hf : IsSmoothEmbedding I 𝓘(ℝ, V) n f) (hg : ContMDiff I 𝓘(ℝ, F) n g)
    (hK : IsCompact K) {O : Set V} (hO : IsOpen O)
    (hKO : f '' (K ∩ tsupport g) ⊆ O) :
    ∃ G : V → F, ContDiff ℝ n G ∧ HasCompactSupport G ∧
      tsupport G ⊆ O ∧ EqOn (G ∘ f) g K := by
  have himage : IsCompact (f '' K) := hK.image hf.isEmbedding.continuous
  obtain ⟨G, hG, hGf⟩ := hf.exists_contDiff_extension_of_isClosed_image hg himage.isClosed
  have hA : IsCompact (f '' (K ∩ tsupport g)) :=
    (hK.inter_right (isClosed_tsupport g)).image hf.isEmbedding.continuous
  exact exists_contDiff_compact_extension_of_eqOn hG hGf hA hO hKO

theorem IsSmoothEmbedding.exists_contDiff_compact_extension_eq_zero_nhds
    (hf : IsSmoothEmbedding I 𝓘(ℝ, V) n f) (hg : ContMDiff I 𝓘(ℝ, F) n g)
    (hK : IsCompact K) {O : Set V} (hO : IsOpen O)
    (hKO : f '' (K ∩ tsupport g) ⊆ O)
    {D : Set V} (hD : IsClosed D) (hDA : Disjoint D (f '' (K ∩ tsupport g))) :
    ∃ G : V → F, ContDiff ℝ n G ∧ HasCompactSupport G ∧ tsupport G ⊆ O ∧
      EqOn (G ∘ f) g K ∧ ∃ W : Set V, IsOpen W ∧ D ⊆ W ∧ EqOn G 0 W := by
  have hAO : f '' (K ∩ tsupport g) ⊆ O ∩ Dᶜ := by
    intro z hz
    exact ⟨hKO hz, fun hzD => Set.disjoint_left.mp hDA hzD hz⟩
  obtain ⟨G, hG, hGc, hGO, hGf⟩ :=
    hf.exists_contDiff_compact_extension_of_tsupport_image_subset hg hK
      (hO.inter hD.isOpen_compl) hAO
  refine ⟨G, hG, hGc, hGO.trans inter_subset_left, hGf,
    (tsupport G)ᶜ, (isClosed_tsupport G).isOpen_compl, ?_, ?_⟩
  · intro z hz hzG
    exact (hGO hzG).2 hz
  · exact fun z hz => image_eq_zero_of_notMem_tsupport hz

theorem IsSmoothEmbedding.exists_contDiff_compact_extension
    (hf : IsSmoothEmbedding I 𝓘(ℝ, V) n f) (hg : ContMDiff I 𝓘(ℝ, F) n g)
    (hK : IsCompact K) {O : Set V} (hO : IsOpen O) (hKO : f '' K ⊆ O) :
    ∃ G : V → F, ContDiff ℝ n G ∧ HasCompactSupport G ∧
      tsupport G ⊆ O ∧ EqOn (G ∘ f) g K :=
  hf.exists_contDiff_compact_extension_of_tsupport_image_subset hg hK hO
    ((image_mono inter_subset_left).trans hKO)

end Manifold

end

section
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis

open Set Filter

private theorem exists_contDiff_extension_prod_halfspace_local
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : P × EuclideanSpace ℝ (Fin (d + 1)) → F}
    {U : Set (P × EuclideanSpace ℝ (Fin (d + 1)))}
    (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (U ∩ (univ ×ˢ range (𝓡∂ (d + 1)))))
    {x : P × EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ U) :
    ∃ G : P × EuclideanSpace ℝ (Fin (d + 1)) → F, ContDiff ℝ ∞ G ∧
      G =ᶠ[𝓝[univ ×ˢ range (𝓡∂ (d + 1))] x] f := by
  let κ : (ℝ × (Fin d → ℝ)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
    (Fin.consEquivL ℝ (fun _ : Fin (d + 1) => ℝ)).trans
      (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm
  have hκzero (z : ℝ × (Fin d → ℝ)) : κ z 0 = z.1 := by
    simp [κ]
  let k : ℝ × (P × (Fin d → ℝ)) → P × EuclideanSpace ℝ (Fin (d + 1)) :=
    fun q => (q.2.1, κ (q.1, q.2.2))
  let j : P × EuclideanSpace ℝ (Fin (d + 1)) → ℝ × (P × (Fin d → ℝ)) :=
    fun q => ((κ.symm q.2).1, (q.1, (κ.symm q.2).2))
  have hk : ContDiff ℝ ∞ k :=
    contDiff_snd.fst.prodMk (κ.contDiff.comp (contDiff_fst.prodMk contDiff_snd.snd))
  have hj : ContDiff ℝ ∞ j :=
    (κ.symm.contDiff.comp contDiff_snd).fst.prodMk
      (contDiff_fst.prodMk (κ.symm.contDiff.comp contDiff_snd).snd)
  have hkj (z : P × EuclideanSpace ℝ (Fin (d + 1))) : k (j z) = z := by
    change (z.1, κ (κ.symm z.2)) = z
    rw [κ.apply_symm_apply]
  have hread : ContDiffOn ℝ ∞ (f ∘ k) ((Ici 0 ×ˢ univ) ∩ (k ⁻¹' U)) := by
    apply hf.comp hk.contDiffOn
    intro z hz
    refine ⟨hz.2, mem_univ _, ?_⟩
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ κ (z.1, z.2.2) 0
    rw [hκzero]
    exact mem_Ici.mp hz.1.1
  obtain ⟨G, hG, hGf⟩ := hread.exists_contDiff_extension_Ici_prod_nhdsWithin
    (hU.preimage hk.continuous) (show j x ∈ k ⁻¹' U by
      change k (j x) ∈ U
      rw [hkj]
      exact hx)
  refine ⟨G ∘ j, hG.comp hj, ?_⟩
  have hjH (z : P × EuclideanSpace ℝ (Fin (d + 1)))
      (hz : z ∈ univ ×ˢ range (𝓡∂ (d + 1))) :
      j z ∈ Ici (0 : ℝ) ×ˢ (univ : Set (P × (Fin d → ℝ))) := by
    refine ⟨mem_Ici.mpr ?_, mem_univ _⟩
    change 0 ≤ (κ.symm z.2).1
    rw [← hκzero _, κ.apply_symm_apply]
    simpa only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hz.2
  have ht : Tendsto j (𝓝[univ ×ˢ range (𝓡∂ (d + 1))] x)
      (𝓝[Ici (0 : ℝ) ×ˢ (univ : Set (P × (Fin d → ℝ)))] j x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hj.continuous.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hjH z hz
  filter_upwards [hGf.comp_tendsto ht] with z hz
  change G (j z) = f z
  simpa only [Function.comp_apply, hkj] using hz

private theorem exists_contDiff_extension_halfspace_local
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : EuclideanSpace ℝ (Fin (n + 1)) → F} {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f (U ∩ range (𝓡∂ (n + 1))))
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ U) :
    ∃ G : EuclideanSpace ℝ (Fin (n + 1)) → F, ContDiff ℝ ∞ G ∧
      G =ᶠ[𝓝[range (𝓡∂ (n + 1))] x] f := by
  let φ : PUnit.{1} × EuclideanSpace ℝ (Fin (n + 1)) → F := fun q => f q.2
  have hφ : ContDiffOn ℝ ∞ φ ((univ ×ˢ U) ∩ (univ ×ˢ range (𝓡∂ (n + 1)))) :=
    hf.comp contDiff_snd.contDiffOn (fun _ hq => ⟨hq.1.2, hq.2.2⟩)
  obtain ⟨G, hG, hGeq⟩ := exists_contDiff_extension_prod_halfspace_local
    (isOpen_univ.prod hU) hφ
      (show (PUnit.unit, x) ∈ univ ×ˢ U from ⟨mem_univ _, hx⟩)
  refine ⟨fun z => G (PUnit.unit, z), hG.comp (contDiff_const.prodMk contDiff_id), ?_⟩
  have ht : Tendsto (fun z : EuclideanSpace ℝ (Fin (n + 1)) => ((PUnit.unit : PUnit.{1}), z))
      (𝓝[range (𝓡∂ (n + 1))] x)
      (𝓝[univ ×ˢ range (𝓡∂ (n + 1))] (PUnit.unit, x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuousAt_const.prodMk continuousAt_id).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact ⟨mem_univ _, hz⟩
  exact hGeq.comp_tendsto ht

end DifferentialGeometry.Analysis

namespace Manifold

open Set Filter Topology

private theorem IsImmersionAtOfComplement.exists_contDiffOn_local_extension_of_model_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {V C : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M → V} {g : M → F} {x : M}
    (h : IsImmersionAtOfComplement C I 𝓘(ℝ, V) ∞ f x)
    (hf : IsInducing f) (hg : ContMDiff I 𝓘(ℝ, F) ∞ g)
    (hext : ∀ {W : Set E} {φ : E → F} {z : E}, IsOpen W →
      ContDiffOn ℝ ∞ φ (W ∩ range I) → z ∈ W →
        ∃ G : E → F, ContDiff ℝ ∞ G ∧ G =ᶠ[𝓝[range I] z] φ) :
    ∃ U : Set V, IsOpen U ∧ f x ∈ U ∧ ∃ G : V → F,
      ContDiffOn ℝ ∞ G U ∧ ∀ y, f y ∈ U → G (f y) = g y := by
  let A : Set E := I.symm ⁻¹' h.domChart.target
  have hA : IsOpen A := h.domChart.open_target.preimage I.continuous_symm
  have hxA : (h.domChart.extend I) x ∈ A := by
    change I.symm (I (h.domChart x)) ∈ h.domChart.target
    rw [I.left_inv]
    exact h.domChart.map_source h.mem_domChart_source
  have hread : ContDiffOn ℝ ∞ (g ∘ (h.domChart.extend I).symm) (A ∩ range I) := by
    change ContDiffOn ℝ ∞ (g ∘ (h.domChart.extend I).symm)
      ((I.symm ⁻¹' h.domChart.target) ∩ range I)
    rw [← I.image_eq]
    exact (hg.comp_contMDiffOn
      (contMDiffOn_extend_symm h.domChart_mem_maximalAtlas)).contDiffOn
  obtain ⟨G₀, hG₀, hG₀eq⟩ :=
    hext hA hread hxA
  let Ψ : V → E × C :=
    h.equiv.symm ∘ h.codChart.extend 𝓘(ℝ, V)
  have hΨ : ContDiffOn ℝ ∞ Ψ h.codChart.source :=
    (h.equiv.symm.contDiff.contMDiff.comp_contMDiffOn
      (h.codChart.contMDiffOn_extend h.codChart_mem_maximalAtlas)).contDiffOn
  have hkey (y : M) (hy : y ∈ h.domChart.source) :
      Ψ (f y) = ((h.domChart.extend I) y, 0) := by
    have hy' : y ∈ (h.domChart.extend I).source := by rwa [h.domChart.extend_source]
    have hwritten := h.writtenInCharts ((h.domChart.extend I).map_source hy')
    change (h.codChart.extend 𝓘(ℝ, V))
      (f ((h.domChart.extend I).symm ((h.domChart.extend I) y))) =
        h.equiv ((h.domChart.extend I) y, 0) at hwritten
    rw [(h.domChart.extend I).left_inv hy'] at hwritten
    change h.equiv.symm ((h.codChart.extend 𝓘(ℝ, V)) (f y)) = _
    rw [hwritten, ContinuousLinearEquiv.symm_apply_apply]
  let G : V → F := fun z => G₀ (Ψ z).1
  have hG : ContDiffOn ℝ ∞ G h.codChart.source := hG₀.comp_contDiffOn hΨ.fst
  have ht : Tendsto (h.domChart.extend I) (𝓝 x)
      (𝓝[range I] (h.domChart.extend I) x) :=
    le_of_eq (h.domChart.map_extend_nhds h.mem_domChart_source)
  have heq : ∀ᶠ y in 𝓝 x, G (f y) = g y := by
    filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source,
      hG₀eq.comp_tendsto ht] with y hy hyeq
    change G₀ (Ψ (f y)).1 = g y
    rw [hkey y hy]
    change G₀ ((h.domChart.extend I) y) =
      g ((h.domChart.extend I).symm ((h.domChart.extend I) y)) at hyeq
    rwa [(h.domChart.extend I).left_inv (by rwa [h.domChart.extend_source])] at hyeq
  obtain ⟨W, hW, hWA⟩ := hf.isOpen_iff.1 (isOpen_interior (s := {y | G (f y) = g y}))
  have hxW : f x ∈ W := by
    change x ∈ f ⁻¹' W
    rw [hWA]
    exact mem_interior_iff_mem_nhds.mpr heq
  refine ⟨h.codChart.source ∩ W, h.codChart.open_source.inter hW,
    ⟨h.mem_codChart_source, hxW⟩, G, hG.mono inter_subset_left, ?_⟩
  intro y hy
  have hyA : y ∈ interior {z | G (f z) = g z} := by
    rw [← hWA]
    exact hy.2
  exact (interior_subset (s := {z | G (f z) = g z})) hyA

theorem IsImmersionAtOfComplement.exists_contDiffOn_local_extension_halfspace
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M]
    {V C : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : M → V} {g : M → F} {x : M}
    (h : IsImmersionAtOfComplement C (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ f x)
    (hf : IsInducing f) (hg : ContMDiff (𝓡∂ (d + 1)) 𝓘(ℝ, F) ∞ g) :
    ∃ U : Set V, IsOpen U ∧ f x ∈ U ∧ ∃ G : V → F,
      ContDiffOn ℝ ∞ G U ∧ ∀ y, f y ∈ U → G (f y) = g y := by
  apply h.exists_contDiffOn_local_extension_of_model_extension hf hg
  intro W φ z hW hφ hz
  exact DifferentialGeometry.Analysis.exists_contDiff_extension_halfspace_local hW hφ hz

theorem IsSmoothEmbedding.exists_contDiffOn_local_extension_halfspace
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : M → V} {g : M → F}
    (hf : IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ f)
    (hg : ContMDiff (𝓡∂ (d + 1)) 𝓘(ℝ, F) ∞ g) (x : M) :
    ∃ U : Set V, IsOpen U ∧ f x ∈ U ∧ ∃ G : V → F,
      ContDiffOn ℝ ∞ G U ∧ ∀ y, f y ∈ U → G (f y) = g y :=
  (hf.isImmersion.isImmersionOfComplement_complement x).exists_contDiffOn_local_extension_halfspace
    hf.isEmbedding.isInducing hg

end Manifold

end

section
open scoped ContDiff Manifold Topology

namespace Manifold

open Set

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (d + 1)) M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : M → V} {g : M → F} {K : Set M}

theorem IsSmoothEmbedding.exists_contDiff_extension_halfspace_of_isClosed_image
    (hf : IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ f)
    (hg : ContMDiff (𝓡∂ (d + 1)) 𝓘(ℝ, F) ∞ g) (hK : IsClosed (f '' K)) :
    ∃ G : V → F, ContDiff ℝ ∞ G ∧ EqOn (G ∘ f) g K := by
  apply exists_contDiff_extension_of_local (n := (⊤ : ℕ∞)) hK
  intro x _
  obtain ⟨U, hU, hxU, G, hG, hGf⟩ := hf.exists_contDiffOn_local_extension_halfspace hg x
  exact ⟨U, hU.mem_nhds hxU, G, hG, fun y _ hy => hGf y hy⟩

theorem IsSmoothEmbedding.exists_contDiff_compact_extension_halfspace_of_tsupport_image_subset
    (hf : IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ f)
    (hg : ContMDiff (𝓡∂ (d + 1)) 𝓘(ℝ, F) ∞ g)
    (hK : IsCompact K) {O : Set V} (hO : IsOpen O)
    (hKO : f '' (K ∩ tsupport g) ⊆ O) :
    ∃ G : V → F, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      tsupport G ⊆ O ∧ EqOn (G ∘ f) g K := by
  have himage : IsCompact (f '' K) := hK.image hf.isEmbedding.continuous
  obtain ⟨G, hG, hGf⟩ :=
    hf.exists_contDiff_extension_halfspace_of_isClosed_image hg himage.isClosed
  have hA : IsCompact (f '' (K ∩ tsupport g)) :=
    (hK.inter_right (isClosed_tsupport g)).image hf.isEmbedding.continuous
  exact exists_contDiff_compact_extension_of_eqOn (n := (⊤ : ℕ∞)) hG hGf hA hO hKO

theorem IsSmoothEmbedding.exists_contDiff_compact_extension_halfspace
    (hf : IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ f)
    (hg : ContMDiff (𝓡∂ (d + 1)) 𝓘(ℝ, F) ∞ g)
    (hK : IsCompact K) {O : Set V} (hO : IsOpen O) (hKO : f '' K ⊆ O) :
    ∃ G : V → F, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      tsupport G ⊆ O ∧ EqOn (G ∘ f) g K :=
  hf.exists_contDiff_compact_extension_halfspace_of_tsupport_image_subset hg hK hO
    ((image_mono inter_subset_left).trans hKO)

end Manifold

end

section
open scoped ContDiff Manifold Topology

namespace Manifold

open Set Filter

private theorem exists_contDiff_extension_prod_halfspace_chart
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {c : OpenPartialHomeomorph M (EuclideanHalfSpace (d + 1))}
    (hc : c ∈ IsManifold.maximalAtlas (𝓡∂ (d + 1)) ∞ M)
    {e : P × M → F}
    (he : ContMDiff (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, F) ∞ e)
    {p : P} {x : M} (hx : x ∈ c.source) :
    ∃ H : P × EuclideanSpace ℝ (Fin (d + 1)) → F, ContDiff ℝ ∞ H ∧
      ∀ᶠ q : P × M in 𝓝 (p, x), H (q.1, (c.extend (𝓡∂ (d + 1))) q.2) = e q := by
  let I := 𝓡∂ (d + 1)
  let B : Set (EuclideanSpace ℝ (Fin (d + 1))) := I.symm ⁻¹' c.target
  have hB : IsOpen B := c.open_target.preimage I.continuous_symm
  have hxB : (c.extend I) x ∈ B := by
    change I.symm (I (c x)) ∈ c.target
    rw [I.left_inv]
    exact c.map_source hx
  let f : P × EuclideanSpace ℝ (Fin (d + 1)) → F :=
    fun q => e (q.1, (c.extend I).symm q.2)
  have hΨ : ContMDiffOn 𝓘(ℝ, P × EuclideanSpace ℝ (Fin (d + 1)))
      (𝓘(ℝ, P).prod I) ∞
      (fun q : P × EuclideanSpace ℝ (Fin (d + 1)) => (q.1, (c.extend I).symm q.2))
      (univ ×ˢ (I '' c.target)) :=
    (contDiff_fst.contMDiff.contMDiffOn).prodMk
      ((contMDiffOn_extend_symm hc).comp contDiff_snd.contMDiff.contMDiffOn
        (fun _ hq => hq.2))
  have hread' : ContDiffOn ℝ ∞ f (univ ×ˢ (I '' c.target)) := by
    exact (he.comp_contMDiffOn hΨ).contDiffOn
  have hread : ContDiffOn ℝ ∞ f ((univ ×ˢ B) ∩ (univ ×ˢ range I)) := by
    apply hread'.mono
    intro q hq
    refine ⟨mem_univ _, ?_⟩
    rw [I.image_eq]
    exact ⟨hq.1.2, hq.2.2⟩
  obtain ⟨H, hH, hHeq⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_extension_prod_halfspace_local
      (isOpen_univ.prod hB) hread (show (p, (c.extend I) x) ∈ univ ×ˢ B from ⟨mem_univ _, hxB⟩)
  refine ⟨H, hH, ?_⟩
  have ht : Tendsto (fun q : P × M => (q.1, (c.extend I) q.2)) (𝓝 (p, x))
      (𝓝[univ ×ˢ range I] (p, (c.extend I) x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuousAt_fst.prodMk ((c.continuousAt_extend hx).comp continuousAt_snd), ?_⟩
    exact Filter.Eventually.of_forall (fun q => ⟨mem_univ _, mem_range_self (c q.2)⟩)
  have hmem : ∀ᶠ q : P × M in 𝓝 (p, x), q.2 ∈ c.source :=
    continuous_snd.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hx)
  filter_upwards [hmem, hHeq.comp_tendsto ht] with q hq hqeq
  change H (q.1, (c.extend I) q.2) =
    e (q.1, (c.extend I).symm ((c.extend I) q.2)) at hqeq
  rwa [(c.extend I).left_inv (by rwa [c.extend_source])] at hqeq

theorem IsImmersionAtOfComplement.exists_contDiffOn_parametric_extension_halfspace
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M]
    {V C : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {e : P × M → V} {p : P} {x : M}
    (h : IsImmersionAtOfComplement C (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun y => e (p, y)) x)
    (he : ContMDiff (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e) :
    ∃ U : Set V, IsOpen U ∧ e (p, x) ∈ U ∧ ∃ A : P × V → V,
      ContDiffOn ℝ ∞ A (univ ×ˢ U) ∧ (∀ v, A (p, v) = v) ∧
        ∀ᶠ q : P × M in 𝓝 (p, x), A (q.1, e (p, q.2)) = e q := by
  let I := 𝓡∂ (d + 1)
  obtain ⟨H, hH, hHeq⟩ := exists_contDiff_extension_prod_halfspace_chart
    h.domChart_mem_maximalAtlas he (p := p) h.mem_domChart_source
  let Ψ : V → EuclideanSpace ℝ (Fin (d + 1)) × C :=
    h.equiv.symm ∘ h.codChart.extend 𝓘(ℝ, V)
  have hΨ : ContDiffOn ℝ ∞ Ψ h.codChart.source :=
    (h.equiv.symm.contDiff.contMDiff.comp_contMDiffOn
      (h.codChart.contMDiffOn_extend h.codChart_mem_maximalAtlas)).contDiffOn
  have hkey (y : M) (hy : y ∈ h.domChart.source) :
      Ψ (e (p, y)) = ((h.domChart.extend I) y, 0) := by
    have hy' : y ∈ (h.domChart.extend I).source := by rwa [h.domChart.extend_source]
    have hwritten := h.writtenInCharts ((h.domChart.extend I).map_source hy')
    change (h.codChart.extend 𝓘(ℝ, V))
      (e (p, (h.domChart.extend I).symm ((h.domChart.extend I) y))) =
        h.equiv ((h.domChart.extend I) y, 0) at hwritten
    rw [(h.domChart.extend I).left_inv hy'] at hwritten
    change h.equiv.symm ((h.codChart.extend 𝓘(ℝ, V)) (e (p, y))) = _
    rw [hwritten, ContinuousLinearEquiv.symm_apply_apply]
  let A : P × V → V := fun q => q.2 + H (q.1, (Ψ q.2).1) - H (p, (Ψ q.2).1)
  have hproj : ContDiffOn ℝ ∞ (fun q : P × V => (Ψ q.2).1)
      (univ ×ˢ h.codChart.source) :=
    hΨ.fst.comp contDiff_snd.contDiffOn (fun _ hq => hq.2)
  have hA : ContDiffOn ℝ ∞ A (univ ×ˢ h.codChart.source) :=
    (contDiff_snd.contDiffOn.add
      (hH.comp_contDiffOn (contDiff_fst.contDiffOn.prodMk hproj))).sub
        (hH.comp_contDiffOn (contDiff_const.contDiffOn.prodMk hproj))
  refine ⟨h.codChart.source, h.codChart.open_source, h.mem_codChart_source, A, hA,
    fun v => add_sub_cancel_right v _, ?_⟩
  have hmem : ∀ᶠ q : P × M in 𝓝 (p, x), q.2 ∈ h.domChart.source :=
    continuous_snd.continuousAt.preimage_mem_nhds
      (h.domChart.open_source.mem_nhds h.mem_domChart_source)
  have hHbase :=
    (show Tendsto (fun q : P × M => (p, q.2)) (𝓝 (p, x)) (𝓝 (p, x)) from
      continuousAt_const.prodMk continuousAt_snd).eventually hHeq
  filter_upwards [hmem, hHeq, hHbase] with q hq hqeq hqbase
  change e (p, q.2) + H (q.1, (Ψ (e (p, q.2))).1) -
    H (p, (Ψ (e (p, q.2))).1) = e q
  rw [hkey q.2 hq]
  change H (p, (h.domChart.extend I) q.2) = e (p, q.2) at hqbase
  rw [hqeq, hqbase]
  exact add_sub_cancel_left _ _

end Manifold

end

section
open scoped ContDiff Manifold Topology

namespace Manifold

open Set Filter Topology

theorem IsImmersionAtOfComplement.exists_contDiffOn_local_extension_prod_halfspace
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ModelProd P (EuclideanHalfSpace (d + 1))) M]
    {V C : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : M → V} {g : M → F} {x : M}
    (h : IsImmersionAtOfComplement C (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ f x)
    (hf : IsInducing f) (hg : ContMDiff (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, F) ∞ g) :
    ∃ U : Set V, IsOpen U ∧ f x ∈ U ∧ ∃ G : V → F,
      ContDiffOn ℝ ∞ G U ∧ ∀ y, f y ∈ U → G (f y) = g y := by
  apply h.exists_contDiffOn_local_extension_of_model_extension hf hg
  intro W φ z hW hφ hz
  rw [ModelWithCorners.range_prod, (𝓘(ℝ, P)).range_eq_univ] at hφ ⊢
  exact DifferentialGeometry.Analysis.exists_contDiff_extension_prod_halfspace_local hW hφ hz

theorem IsSmoothEmbedding.exists_contDiffOn_local_extension_prod_halfspace
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ModelProd P (EuclideanHalfSpace (d + 1))) M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : M → V} {g : M → F}
    (hf : IsSmoothEmbedding (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ f)
    (hg : ContMDiff (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, F) ∞ g) (x : M) :
    ∃ U : Set V, IsOpen U ∧ f x ∈ U ∧ ∃ G : V → F,
      ContDiffOn ℝ ∞ G U ∧ ∀ y, f y ∈ U → G (f y) = g y :=
  (hf.isImmersion.isImmersionOfComplement_complement x).exists_contDiffOn_local_extension_prod_halfspace
    hf.isEmbedding.isInducing hg

theorem IsSmoothEmbedding.exists_contDiff_extension_prod_halfspace_of_isClosed_image
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ModelProd P (EuclideanHalfSpace (d + 1))) M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : M → V} {g : M → F} {K : Set M}
    (hf : IsSmoothEmbedding (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ f)
    (hg : ContMDiff (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, F) ∞ g)
    (hK : IsClosed (f '' K)) :
    ∃ G : V → F, ContDiff ℝ ∞ G ∧ EqOn (G ∘ f) g K := by
  apply exists_contDiff_extension_of_local (n := (⊤ : ℕ∞)) hK
  intro x _
  obtain ⟨U, hU, hxU, G, hG, hGf⟩ := hf.exists_contDiffOn_local_extension_prod_halfspace hg x
  exact ⟨U, hU.mem_nhds hxU, G, hG, fun y _ hy => hGf y hy⟩

theorem IsSmoothEmbedding.exists_contDiff_compact_extension_prod_halfspace_of_tsupport_image_subset
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ModelProd P (EuclideanHalfSpace (d + 1))) M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : M → V} {g : M → F} {K : Set M}
    (hf : IsSmoothEmbedding (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ f)
    (hg : ContMDiff (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, F) ∞ g)
    (hK : IsCompact K) {O : Set V} (hO : IsOpen O)
    (hKO : f '' (K ∩ tsupport g) ⊆ O) :
    ∃ G : V → F, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      tsupport G ⊆ O ∧ EqOn (G ∘ f) g K := by
  have himage : IsCompact (f '' K) := hK.image hf.isEmbedding.continuous
  obtain ⟨G, hG, hGf⟩ :=
    hf.exists_contDiff_extension_prod_halfspace_of_isClosed_image hg himage.isClosed
  have hA : IsCompact (f '' (K ∩ tsupport g)) :=
    (hK.inter_right (isClosed_tsupport g)).image hf.isEmbedding.continuous
  exact exists_contDiff_compact_extension_of_eqOn (n := (⊤ : ℕ∞)) hG hGf hA hO hKO

end Manifold

end
