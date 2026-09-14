import DifferentialGeometry.Topology.Embedding.SliceChart
import Mathlib.Topology.Homeomorph.Lemmas

open scoped ContDiff Manifold

namespace Manifold

open Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N}

theorem IsSmoothEmbedding.exists_contMDiff_local_retraction [I.Boundaryless] [J.Boundaryless]
    (h : IsSmoothEmbedding I J n f) (x : M) :
    ∃ U : TopologicalSpace.Opens N, f x ∈ U ∧
      ∃ r : U → M, ContMDiff J I n r ∧ (∀ q, f (r q) ∈ U) ∧
        ∀ y (hy : f y ∈ U), r ⟨f y, hy⟩ = y := by
  obtain ⟨Φ, hx, hforward, hinverse, hslice⟩ := h.exists_contMDiffOn_slice_chart x
  let F := h.isImmersion.complement
  let P : E × F → E × F := fun z => (z.1, 0)
  have hP : ContDiff 𝕜 n P := contDiff_fst.prodMk contDiff_const
  have hzero {y : M} (hy : f y ∈ Φ.source) : P (Φ (f y)) = Φ (f y) := by
    have hz : Φ (f y) ∈ Φ.target ∩ (range I ×ˢ ({0} : Set F)) := by
      rw [← hslice]
      exact ⟨f y, ⟨hy, mem_range_self y⟩, rfl⟩
    exact Prod.ext rfl (hz.2.2 : (Φ (f y)).2 = 0).symm
  let U : TopologicalSpace.Opens N :=
    ⟨Φ.source ∩ (P ∘ Φ) ⁻¹' Φ.target,
      Φ.isOpen_inter_preimage (Φ.open_target.preimage hP.continuous)⟩
  have hxU : f x ∈ U := by
    refine ⟨hx, ?_⟩
    change P (Φ (f x)) ∈ Φ.target
    rw [hzero hx]
    exact Φ.map_source hx
  let R : U → N := fun q => Φ.symm (P (Φ q))
  have hRchart (q : U) : Φ (R q) = P (Φ q) := Φ.right_inv q.prop.2
  have hRrange (q : U) : R q ∈ range f := by
    have hz : P (Φ q) ∈ Φ.target ∩ (range I ×ˢ ({0} : Set F)) := by
      refine ⟨q.prop.2, ?_⟩
      change (Φ q).1 ∈ range I ∧ (0 : F) ∈ ({0} : Set F)
      rw [I.range_eq_univ]
      exact ⟨mem_univ _, rfl⟩
    rw [← hslice] at hz
    obtain ⟨p, ⟨hp, hpf⟩, hpz⟩ := hz
    have hRp : R q = p := by
      change Φ.symm (P (Φ q)) = p
      rw [← hpz, Φ.left_inv hp]
    rwa [hRp]
  have hRU (q : U) : R q ∈ U := by
    refine ⟨Φ.map_target q.prop.2, ?_⟩
    change P (Φ (R q)) ∈ Φ.target
    rw [hRchart]
    exact q.prop.2
  have hRf (y : M) (hy : f y ∈ U) : R ⟨f y, hy⟩ = f y := by
    change Φ.symm (P (Φ (f y))) = f y
    rw [hzero hy.1, Φ.left_inv hy.1]
  have hΦU : ContMDiff J 𝓘(𝕜, E × F) n (fun q : U => Φ q) :=
    hforward.comp_contMDiff contMDiff_subtype_val (fun q => q.prop.1)
  have hRsmooth : ContMDiff J J n R :=
    hinverse.comp_contMDiff (hP.contMDiff.comp hΦU) (fun q => q.prop.2)
  let r : U → M := fun q => h.isEmbedding.toHomeomorph.symm ⟨R q, hRrange q⟩
  have hfr (q : U) : f (r q) = R q := by
    exact congrArg Subtype.val
      (h.isEmbedding.toHomeomorph.apply_symm_apply ⟨R q, hRrange q⟩)
  have hrsmooth : ContMDiff J I n r := by
    apply (ContMDiff.iff_comp_isImmersion h.isImmersion).2
    refine ⟨?_, hRsmooth.congr hfr⟩
    exact h.isEmbedding.toHomeomorph.symm.continuous.comp
      (hRsmooth.continuous.subtype_mk hRrange)
  refine ⟨U, hxU, r, hrsmooth, fun q => ?_, fun y hy => ?_⟩
  · rw [hfr]
    exact hRU q
  · apply h.isEmbedding.injective
    rw [hfr, hRf]

end Manifold
