import DifferentialGeometry.Topology.Embedding.Compact
import DifferentialGeometry.Topology.Embedding.GraphNeighborhood
import DifferentialGeometry.Topology.Embedding.Lift
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.LeftInverse
import Mathlib.Topology.MetricSpace.Thickening

open Set Manifold Metric Filter Topology
open scoped Manifold ContDiff

namespace Topology.IsInducing

theorem exists_cthickening_inter_range_eq_graph_of_smooth_parametrization
    {E P F T H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [PseudoMetricSpace T] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ F H} [I.Boundaryless] [IsManifold I ∞ M]
    {e : M → E × T} (he : IsInducing e)
    (B : P ≃ₘ[ℝ] E) {β : P → M} {U : Set P}
    (hU : IsOpen U) (hβ : ContMDiffOn 𝓘(ℝ, P) I ∞ β U)
    (hefst : ∀ z ∈ U, ContMDiffAt I 𝓘(ℝ, E) ∞ (fun x => (e x).1) (β z))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ F)
    {q : P → T} (hgraph : ∀ z ∈ U, e (β z) = (B z, q z))
    {K : Set P} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ V : Set (E × T), IsOpen V ∧ (fun z => (B z, q z)) '' U ⊆ V ∧
      V ⊆ (fun z => B.symm z.1) ⁻¹' U ∧
      V ∩ range e = V ∩ {z | z.2 = q (B.symm z.1)} ∧
      e ⁻¹' V = β '' U ∧
      ∃ δ : ℝ, 0 < δ ∧ cthickening δ (e '' (β '' K)) ⊆ V := by
  let G : M → P := fun x => B.symm (e x).1
  have hleft : LeftInvOn G β U := by
    intro z hz
    change B.symm (e (β z)).1 = z
    rw [hgraph z hz]
    exact B.symm_apply_apply z
  obtain ⟨χ, hsource, htarget, hχ, _⟩ := hleft.exists_partialDiffeomorph hU hβ
    (fun z hz => B.symm.contMDiff.contMDiffAt.comp (β z) (hefst z hz)) hdim
  let D : (E × T) ≃ₜ (P × T) := B.symm.toHomeomorph.prodCongr (Homeomorph.refl T)
  have hDe : IsInducing (D ∘ e) := D.isEmbedding.isInducing.comp he
  have hDgraph (z : P) (hz : z ∈ U) : (D ∘ e) (χ z) = (z, q z) := by
    change (B.symm (e (χ z)).1, (e (χ z)).2) = (z, q z)
    rw [hχ, hgraph z hz, B.symm_apply_apply]
  obtain ⟨W, hW, hgraphW, hWU, hWeq⟩ := hDe.exists_isOpen_inter_range_eq_graph
    χ.toOpenPartialHomeomorph hU (fun z hz => hsource.symm ▸ hz) hDgraph
  let V : Set (E × T) := D ⁻¹' W
  have hV : IsOpen V := hW.preimage D.continuous
  have hgraphV : (fun z => (B z, q z)) '' U ⊆ V := by
    rintro p ⟨z, hz, rfl⟩
    change (B.symm (B z), q z) ∈ W
    rw [B.symm_apply_apply]
    exact hgraphW (mem_image_of_mem _ hz)
  have hVU : V ⊆ (fun z => B.symm z.1) ⁻¹' U := fun z hz => (hWU hz).1
  have hVeq : V ∩ range e = V ∩ {z | z.2 = q (B.symm z.1)} := by
    ext z
    constructor
    · rintro ⟨hz, x, hx⟩
      have hm : D z ∈ W ∩ range (D ∘ e) := ⟨hz, x, congrArg D hx⟩
      rw [hWeq] at hm
      exact ⟨hz, hm.2⟩
    · rintro ⟨hz, hq⟩
      have hm : D z ∈ W ∩ {w | w.2 = q w.1} := ⟨hz, hq⟩
      rw [← hWeq] at hm
      obtain ⟨x, hx⟩ := hm.2
      exact ⟨hz, x, D.injective hx⟩
  have hpreV : e ⁻¹' V = β '' U := by
    obtain ⟨O, _, hpreO⟩ := he.isOpen_iff.mp (htarget ▸ χ.open_target)
    apply Subset.antisymm
    · intro x hx
      have hz : B.symm (e x).1 ∈ U := hVU hx
      have hq : (e x).2 = q (B.symm (e x).1) := by
        have hm : e x ∈ V ∩ range e := ⟨hx, mem_range_self x⟩
        rw [hVeq] at hm
        exact hm.2
      have heq : e (β (B.symm (e x).1)) = e x := by
        rw [hgraph _ hz, B.apply_symm_apply]
        exact Prod.ext rfl hq.symm
      have hβO : β (B.symm (e x).1) ∈ e ⁻¹' O := by
        rw [hpreO]
        exact mem_image_of_mem _ hz
      rw [mem_preimage, heq] at hβO
      rw [← hpreO]
      exact hβO
    · rintro x ⟨z, hz, rfl⟩
      change e (β z) ∈ V
      rw [hgraph z hz]
      exact hgraphV (mem_image_of_mem _ hz)
  have himage : IsCompact (e '' (β '' K)) :=
    (hK.image_of_continuousOn (hβ.continuousOn.mono hKU)).image he.continuous
  have himageV : e '' (β '' K) ⊆ V := by
    rintro z ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    rw [hgraph y (hKU hy)]
    exact hgraphV (mem_image_of_mem _ (hKU hy))
  obtain ⟨δ, hδ, hδV⟩ := himage.exists_cthickening_subset_open hV himageV
  exact ⟨V, hV, hgraphV, hVU, hVeq, hpreV, δ, hδ, hδV⟩

theorem exists_prod_closedBall_mem_range_iff_of_smooth_parametrization
    {E P F T H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [PseudoMetricSpace T] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ F H} [I.Boundaryless] [IsManifold I ∞ M]
    {e : M → E × T} (he : IsInducing e)
    (B : P ≃ₘ[ℝ] E) {β : P → M} {U : Set P}
    (hU : IsOpen U) (hβ : ContMDiffOn 𝓘(ℝ, P) I ∞ β U)
    (hefst : ∀ z ∈ U, ContMDiffAt I 𝓘(ℝ, E) ∞ (fun x => (e x).1) (β z))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ F)
    {q : P → T} (hgraph : ∀ z ∈ U, e (β z) = (B z, q z))
    {p : P} (hp : p ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∃ t : ℝ, 0 < t ∧ closedBall p r ⊆ U ∧
      (∀ z ∈ closedBall p r, q z ∈ ball (q p) t) ∧
      ∀ z ∈ closedBall p r, ∀ w ∈ closedBall (q p) t,
        (B z, w) ∈ range e ↔ w = q z := by
  let G : M → P := fun x => B.symm (e x).1
  have hleft : LeftInvOn G β U := by
    intro z hz
    change B.symm (e (β z)).1 = z
    rw [hgraph z hz]
    exact B.symm_apply_apply z
  obtain ⟨χ, hsource, _, hχ, _⟩ := hleft.exists_partialDiffeomorph hU hβ
    (fun z hz => B.symm.contMDiff.contMDiffAt.comp (β z) (hefst z hz)) hdim
  let D : (E × T) ≃ₜ (P × T) := B.symm.toHomeomorph.prodCongr (Homeomorph.refl T)
  have hDe : IsInducing (D ∘ e) := D.isEmbedding.isInducing.comp he
  have hDgraph (z : P) (hz : z ∈ U) : (D ∘ e) (χ z) = (z, q z) := by
    change (B.symm (e (χ z)).1, (e (χ z)).2) = (z, q z)
    rw [hχ, hgraph z hz, B.symm_apply_apply]
  have hq : ContinuousAt q p := by
    have hc : ContinuousAt (fun z => (e (β z)).2) p :=
      (he.continuous.continuousAt.comp
        (hβ.continuousOn.continuousAt (hU.mem_nhds hp))).snd
    apply hc.congr
    filter_upwards [hU.mem_nhds hp] with z hz
    exact congrArg Prod.snd (hgraph z hz)
  obtain ⟨r, hr, t, ht, hrU, hqt, hbox⟩ :=
    hDe.exists_prod_closedBall_inter_range_eq_graph χ.toOpenPartialHomeomorph hU
      (fun z hz => hsource.symm ▸ hz) hDgraph hp hq
  refine ⟨r, hr, t, ht, hrU, hqt, ?_⟩
  intro z hz w hw
  constructor
  · rintro ⟨x, hx⟩
    have hm : (z, w) ∈ (closedBall p r ×ˢ closedBall (q p) t) ∩ range (D ∘ e) := by
      refine ⟨⟨hz, hw⟩, x, ?_⟩
      change (B.symm (e x).1, (e x).2) = (z, w)
      rw [hx, B.symm_apply_apply]
    rw [hbox] at hm
    obtain ⟨y, _, hy⟩ := hm
    have hyz : y = z := congrArg Prod.fst hy
    simpa only [hyz] using (congrArg Prod.snd hy).symm
  · intro hwq
    exact ⟨β z, (hgraph z (hrU hz)).trans (Prod.ext rfl hwq.symm)⟩

end Topology.IsInducing

theorem Manifold.IsSmoothEmbedding.exists_isOpen_inter_range_eq_graph
    {E F P H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ P H} [I.Boundaryless] [IsManifold I ∞ M]
    {e : M → E × F} (he : IsSmoothEmbedding I 𝓘(ℝ, E × F) ∞ e)
    {U : Set E} (hU : IsOpen U) {q : E → F} (hq : ContDiffOn ℝ ∞ q U)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ P)
    (hgraph : (fun y => (y, q y)) '' U ⊆ range e) :
    ∃ V : Set (E × F), IsOpen V ∧ (fun y => (y, q y)) '' U ⊆ V ∧
      V ⊆ U ×ˢ univ ∧ V ∩ range e = V ∩ {z | z.2 = q z.1} := by
  let O : TopologicalSpace.Opens E := ⟨U, hU⟩
  let g : O → E × F := fun y => (y, q y)
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E × F) ∞ g :=
    contMDiff_subtype_val.prodMk_space
      (hq.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun y : O => y.property))
  have hgrange : range g ⊆ range e := by
    rintro z ⟨y, rfl⟩
    exact hgraph (mem_image_of_mem _ y.property)
  let β := he.lift g hgrange
  have hβ : ContMDiff 𝓘(ℝ, E) I ∞ β := he.contMDiff_lift hg hgrange
  have hβgraph (y : O) : e (β y) = (y.val, q y) := he.comp_lift hgrange y
  have hβfst : (fun x => (e x).1) ∘ β = (Subtype.val : O → E) := by
    funext y
    exact congrArg Prod.fst (hβgraph y)
  have hβcomp : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ((fun x => (e x).1) ∘ β) := by
    rw [hβfst]
    exact IsSmoothEmbedding.of_opens O
  have hβemb : IsSmoothEmbedding 𝓘(ℝ, E) I ∞ β :=
    hβcomp.of_comp (by simp) hβ (contDiff_fst.contMDiff.comp he.contMDiff)
  have hβopen : IsOpen (range β) :=
    _root_.Manifold.isOpen_range_of_isSmoothEmbedding
      hdim hβemb
  obtain ⟨W, hW, hpre⟩ := he.isEmbedding.isInducing.isOpen_iff.mp hβopen
  let V : Set (E × F) := W ∩ U ×ˢ univ
  have hV : IsOpen V := hW.inter (hU.prod isOpen_univ)
  have hgraphV : (fun y => (y, q y)) '' U ⊆ V := by
    rintro z ⟨y, hy, rfl⟩
    refine ⟨?_, hy, mem_univ _⟩
    have hmem : e (β ⟨y, hy⟩) ∈ W := by
      change β ⟨y, hy⟩ ∈ e ⁻¹' W
      rw [hpre]
      exact mem_range_self _
    simpa only [hβgraph] using hmem
  have hVeq : V ∩ range e = V ∩ {z | z.2 = q z.1} := by
    ext z
    constructor
    · rintro ⟨hz, x, hx⟩
      have hxW : x ∈ e ⁻¹' W := by rw [mem_preimage, hx]; exact hz.1
      rw [hpre] at hxW
      obtain ⟨y, hy⟩ := hxW
      have hyz : (y.val, q y) = z := (hβgraph y).symm.trans ((congrArg e hy).trans hx)
      exact ⟨hz, hyz ▸ rfl⟩
    · rintro ⟨hz, hqz⟩
      exact ⟨hz, β ⟨z.1, hz.2.1⟩, (hβgraph _).trans (Prod.ext rfl hqz.symm)⟩
  exact ⟨V, hV, hgraphV, inter_subset_right, hVeq⟩

theorem Manifold.IsSmoothEmbedding.exists_cthickening_inter_range_eq_graph
    {E F P H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ P H} [I.Boundaryless] [IsManifold I ∞ M]
    {e : M → E × F} (he : IsSmoothEmbedding I 𝓘(ℝ, E × F) ∞ e)
    {U : Set E} (hU : IsOpen U) {q : E → F} (hq : ContDiffOn ℝ ∞ q U)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ P)
    (hgraph : (fun y => (y, q y)) '' U ⊆ range e)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ V : Set (E × F), IsOpen V ∧ (fun y => (y, q y)) '' U ⊆ V ∧
      V ⊆ U ×ˢ univ ∧ V ∩ range e = V ∩ {z | z.2 = q z.1} ∧
      ∃ δ : ℝ, 0 < δ ∧ cthickening δ ((fun y => (y, q y)) '' K) ⊆ V := by
  obtain ⟨V, hV, hgraphV, hVU, hVeq⟩ := he.exists_isOpen_inter_range_eq_graph hU hq hdim hgraph
  have hcompact : IsCompact ((fun y => (y, q y)) '' K) :=
    hK.image_of_continuousOn (continuous_id.continuousOn.prodMk (hq.continuousOn.mono hKU))
  obtain ⟨δ, hδ, hδV⟩ := hcompact.exists_cthickening_subset_open hV
    ((image_mono hKU).trans hgraphV)
  exact ⟨V, hV, hgraphV, hVU, hVeq, δ, hδ, hδV⟩

namespace DifferentialGeometry.Topology

theorem exists_partialDiffeomorph_projection_of_graph_neighborhood
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (B : E ≃ₘ[ℝ] F) (A : (F × ℝ) ≃ₘ[ℝ] (F × ℝ))
    {q : E → ℝ} (hq : ContDiff ℝ ∞ q) {V : Set E} (hV : IsOpen V)
    {g : F → ℝ} {O : Set F} (hO : IsOpen O) (hg : ContDiffOn ℝ ∞ g O)
    {W : Set (F × ℝ)} (hW : IsOpen W) (hWO : W ⊆ {p | p.1 ∈ O})
    (hgraph : ∀ z ∈ V, A (B z, q z) ∈ W → (A (B z, q z)).2 = g (A (B z, q z)).1) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞,
      χ.source = V ∩ (fun z => A (B z, q z)) ⁻¹' W ∧
      (χ : E → F) = (fun z => (A (B z, q z)).1) ∧
      (χ.symm : F → E) = (fun x => B.symm (A.symm (x, g x)).1) := by
  let f : E → F := fun z => (A (B z, q z)).1
  let i : F → E := fun x => B.symm (A.symm (x, g x)).1
  let U := V ∩ (fun z => A (B z, q z)) ⁻¹' W
  have hU : IsOpen U :=
    hV.inter (hW.preimage (A.continuous.comp (B.continuous.prodMk hq.continuous)))
  have hleft : LeftInvOn i f U := by
    intro z hz
    have he : (f z, g (f z)) = A (B z, q z) :=
      Prod.ext rfl (hgraph z hz.1 hz.2).symm
    change B.symm (A.symm (f z, g (f z))).1 = z
    rw [he, A.symm_apply_apply, B.symm_apply_apply]
  have hf : ContDiff ℝ ∞ f :=
    (A.contDiff.comp (B.contDiff.prodMk hq)).fst
  have hi (z : E) (hz : z ∈ U) : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ i (f z) := by
    have hzO : f z ∈ O := hWO hz.2
    have hgAt := hg.contDiffAt (hO.mem_nhds hzO)
    exact (B.symm.contDiff.contDiffAt.comp _
      ((A.symm.contDiff.contDiffAt.comp _ (contDiffAt_id.prodMk hgAt)).fst)).contMDiffAt
  obtain ⟨χ, hsource, _, hfun, hinv⟩ :=
    hleft.exists_partialDiffeomorph hU hf.contMDiff.contMDiffOn hi
    (B.mfderivToContinuousLinearEquiv (by simp) (0 : E)).toLinearEquiv.finrank_eq
  exact ⟨χ, hsource, hfun, hinv⟩

theorem exists_isOpen_contDiffOn_graph_of_isCompact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}
    {S K : Set (E × F)} (hK : IsCompact K) (hKS : K ⊆ S)
    (hinj : InjOn (Prod.fst : E × F → E) K)
    (hloc : ∀ p ∈ K, ∃ O : Set E, IsOpen O ∧ ∃ g : E → F, ContDiffOn ℝ n g O ∧
      ∃ W : Set (E × F), IsOpen W ∧ p ∈ W ∧ W ⊆ O ×ˢ univ ∧
        W ∩ S = W ∩ {q | q.2 = g q.1}) :
    ∃ O : Set E, IsOpen O ∧ ∃ g : E → F, ContDiffOn ℝ n g O ∧
      ∃ W : Set (E × F), IsOpen W ∧ K ⊆ W ∧ W ⊆ O ×ˢ univ ∧
        W ∩ S = W ∩ {q | q.2 = g q.1} := by
  classical
  let L : Set (E × F) := {p | ∃ O : Set E, IsOpen O ∧ ∃ g : E → F, ContDiffOn ℝ n g O ∧
    ∃ W : Set (E × F), IsOpen W ∧ p ∈ W ∧ W ⊆ O ×ˢ univ ∧
      W ∩ S = W ∩ {q | q.2 = g q.1}}
  have hL : IsOpen L := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    obtain ⟨O, hO, g, hg, W, hW, hpW, hWO, hWeq⟩ := hp
    apply mem_of_superset (hW.mem_nhds hpW)
    intro q hq
    exact ⟨O, hO, g, hg, W, hW, hq, hWO, hWeq⟩
  let Ksub : Set S := Subtype.val ⁻¹' K
  have hKsub : IsCompact Ksub :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK
      (by simpa only [Subtype.range_coe] using hKS)
  have hsubinj : InjOn (fun p : S => p.val.1) Ksub := by
    intro p hp q hq heq
    exact Subtype.ext (hinj hp hq heq)
  have hsublocal (p : S) (hp : p ∈ Ksub) :
      ∃ V ∈ 𝓝 p, InjOn (fun q : S => q.val.1) V := by
    obtain ⟨O, _, g, _, W, hW, hpW, _, hWeq⟩ := hloc p.val hp
    refine ⟨Subtype.val ⁻¹' W, (hW.preimage continuous_subtype_val).mem_nhds hpW, ?_⟩
    intro q hq z hz heq
    change q.val.1 = z.val.1 at heq
    apply Subtype.ext
    apply Prod.ext heq
    have hqg := (hWeq.subset ⟨hq, q.property⟩).2
    have hzg := (hWeq.subset ⟨hz, z.property⟩).2
    change q.val.2 = g q.val.1 at hqg
    change z.val.2 = g z.val.1 at hzg
    rw [hqg, hzg, heq]
  obtain ⟨V, hV, hKV, hVinj⟩ := hsubinj.exists_isOpen_superset hKsub
    (fun _ _ => continuous_subtype_val.fst.continuousAt) hsublocal
  obtain ⟨N₀, hN₀, hN₀V⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hV
  let N : Set (E × F) := N₀ ∩ L
  have hN : IsOpen N := hN₀.inter hL
  have hKN : K ⊆ N := by
    intro p hp
    have hpV := hKV (show (⟨p, hKS hp⟩ : S) ∈ Ksub from hp)
    refine ⟨?_, hloc p hp⟩
    change (⟨p, hKS hp⟩ : S) ∈ Subtype.val ⁻¹' N₀
    rwa [hN₀V]
  have hNinj : InjOn (Prod.fst : E × F → E) (N ∩ S) := by
    intro p hp q hq heq
    have hpV : (⟨p, hp.2⟩ : S) ∈ V := by rw [← hN₀V]; exact hp.1.1
    have hqV : (⟨q, hq.2⟩ : S) ∈ V := by rw [← hN₀V]; exact hq.1.1
    exact congrArg Subtype.val (hVinj hpV hqV heq)
  have hlocal (p : E × F) (hp : p ∈ N ∩ S) :
      ∃ g : E → F, ContDiffAt ℝ n g p.1 ∧ g p.1 = p.2 ∧
        ∀ᶠ x in 𝓝 p.1, (x, g x) ∈ N ∩ S := by
    obtain ⟨O, hO, g, hg, W, hW, hpW, hWO, hWeq⟩ := hp.1.2
    have hpO : p.1 ∈ O := (hWO hpW).1
    have hgp : g p.1 = p.2 := (hWeq.subset ⟨hpW, hp.2⟩).2.symm
    have hgat : ContDiffAt ℝ n g p.1 := hg.contDiffAt (hO.mem_nhds hpO)
    have hcont : ContinuousAt (fun x => (x, g x)) p.1 := continuousAt_id.prodMk hgat.continuousAt
    have hmemN : ∀ᶠ x in 𝓝 p.1, (x, g x) ∈ N :=
      hcont (hN.mem_nhds (by simpa only [hgp, Prod.eta] using hp.1))
    have hmemW : ∀ᶠ x in 𝓝 p.1, (x, g x) ∈ W :=
      hcont (hW.mem_nhds (by simpa only [hgp, Prod.eta] using hpW))
    refine ⟨g, hgat, hgp, ?_⟩
    filter_upwards [hmemN, hmemW] with x hxN hxW
    exact ⟨hxN, (hWeq.symm.subset ⟨hxW, rfl⟩).2⟩
  let O : Set E := {x | ∃ y : F, (x, y) ∈ N ∩ S}
  let g : E → F := fun x => if hx : x ∈ O then Classical.choose hx else 0
  have hspec (x : E) (hx : x ∈ O) : (x, g x) ∈ N ∩ S := by
    dsimp only [g]
    rw [dif_pos hx]
    exact Classical.choose_spec hx
  have huniq (x : E) (hx : x ∈ O) (y : F) (hy : (x, y) ∈ N ∩ S) : y = g x :=
    congrArg Prod.snd (hNinj hy (hspec x hx) rfl)
  have hO : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨f, _, _, hf⟩ := hlocal (x, g x) (hspec x hx)
    exact mem_of_superset hf (fun y hy => ⟨f y, hy⟩)
  have hg : ContDiffOn ℝ n g O := by
    intro x hx
    obtain ⟨f, hf, _, hfmem⟩ := hlocal (x, g x) (hspec x hx)
    have heq : g =ᶠ[𝓝 x] f := by
      filter_upwards [hfmem] with y hy
      exact (huniq y ⟨f y, hy⟩ (f y) hy).symm
    exact (hf.congr_of_eventuallyEq heq).contDiffWithinAt
  have hgraph : N ∩ S = {p : E × F | p.1 ∈ O ∧ p.2 = g p.1} := by
    ext p
    constructor
    · intro hp
      exact ⟨⟨p.2, hp⟩, huniq p.1 ⟨p.2, hp⟩ p.2 hp⟩
    · rintro ⟨hp, heq⟩
      have h := hspec p.1 hp
      simpa only [← heq, Prod.eta] using h
  let W : Set (E × F) := N ∩ (O ×ˢ univ)
  refine ⟨O, hO, g, hg, W, hN.inter (hO.prod isOpen_univ), ?_, inter_subset_right, ?_⟩
  · intro p hp
    exact ⟨hKN hp, ⟨p.2, hKN hp, hKS hp⟩, mem_univ _⟩
  · ext p
    constructor
    · rintro ⟨hpW, hpS⟩
      exact ⟨hpW, (hgraph.subset ⟨hpW.1, hpS⟩).2⟩
    · rintro ⟨hpW, hpg⟩
      exact ⟨hpW, (hgraph.symm.subset ⟨hpW.2.1, hpg⟩).2⟩


end DifferentialGeometry.Topology
