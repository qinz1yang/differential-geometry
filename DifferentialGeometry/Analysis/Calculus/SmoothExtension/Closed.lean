import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Comp
import DifferentialGeometry.Bundle.TangentSection.Spacetime

section

open Set Filter
open scoped ContDiff Manifold Topology

theorem Set.EqOn.fderiv_eq_of_mem_closure_interior
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f g : E → F} {s : Set E} (h : EqOn f g s) {x : E}
    (hx : x ∈ closure (interior s)) (hf : ContDiffAt 𝕜 1 f x) (hg : ContDiffAt 𝕜 1 g x) :
    fderiv 𝕜 f x = fderiv 𝕜 g x := by
  have heq : EqOn (fderiv 𝕜 f) (fderiv 𝕜 g) (interior s) := by
    intro y hy
    exact ((h.mono interior_subset).eventuallyEq_of_mem
      (isOpen_interior.mem_nhds hy)).fderiv_eq
  let _ : (𝓝[interior s] x).NeBot := mem_closure_iff_clusterPt.mp hx
  exact tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[interior s] x)
    ((hf.continuousAt_fderiv (by simp)).mono_left inf_le_left)
    ((hg.continuousAt_fderiv (by simp)).mono_left inf_le_left)
    (heq.eventuallyEq_of_mem self_mem_nhdsWithin)

namespace DifferentialGeometry.Analysis

theorem exists_contDiff_extension_of_local
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

end DifferentialGeometry.Analysis

end

section


noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_contDiff_eqOn_of_localCover {ι : Type*} {K : Set (ℝ × E)} (hK : IsCompact K)
    (s : Finset ι) (U : ι → Set (ℝ × E)) (hUo : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i ∈ s, U i) {g : ι → ℝ × E → E} (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i))
    (hcons : ∀ i ∈ s, ∀ j ∈ s, ∀ q ∈ (K ∩ U i) ∩ U j, g i q = g j q) :
    ∃ G : ℝ × E → E, ContDiff ℝ ∞ G ∧ ∀ i ∈ s, ∀ q ∈ K ∩ U i, G q = g i q := by
  classical
  have hchoice : ∀ q : K, ∃ i : ι, i ∈ s ∧ q.1 ∈ U i := by
    intro q
    obtain ⟨i, his, hqi⟩ := mem_iUnion₂.mp (hcover q.2)
    exact ⟨i, his, hqi⟩
  choose index hindex hmem using hchoice
  let value : ℝ × E → E := fun q => if hq : q ∈ K then g (index ⟨q, hq⟩) q else 0
  have hlocal : ∀ q ∈ K, ∃ V ∈ 𝓝 q, ∃ G : ℝ × E → E,
      ContDiffOn ℝ ∞ G V ∧ ∀ y ∈ K, y ∈ V → G y = value y := by
    intro q hq
    let i := index ⟨q, hq⟩
    refine ⟨U i, (hUo i).mem_nhds (hmem ⟨q, hq⟩), g i, hg i, ?_⟩
    intro y hy hyU
    have hcons' := hcons i (hindex ⟨q, hq⟩) (index ⟨y, hy⟩) (hindex ⟨y, hy⟩)
      y ⟨⟨hy, hyU⟩, hmem ⟨y, hy⟩⟩
    simpa only [value, dite_eq_left hy] using hcons'
  obtain ⟨G, hG, hGeq⟩ := DifferentialGeometry.Analysis.exists_contDiff_extension_of_local
    (M := ℝ × E) (V := ℝ × E) (F := E)
    (f := id) (g := value) (K := K) (by simpa only [id_eq, image_id'] using hK.isClosed)
    (by simpa only [id_eq] using hlocal)
  refine ⟨G, hG, ?_⟩
  intro i his q hq
  have hval : value q = g i q := by
    have h := hcons (index ⟨q, hq.1⟩) (hindex ⟨q, hq.1⟩) i his
      q ⟨⟨hq.1, hmem ⟨q, hq.1⟩⟩, hq.2⟩
    simpa only [value, dite_eq_left hq.1] using h
  exact (hGeq hq.1).trans hval

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end


section


noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_contMDiff_tangentSection_eqOn_of_localCover {ι : Type*} {K : Set (ℝ × E)}
    (hK : IsCompact K) (s : Finset ι) (U : ι → Set (ℝ × E)) (hUo : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i ∈ s, U i) {g : ι → ℝ × E → E}
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i))
    (hcons : ∀ i ∈ s, ∀ j ∈ s, ∀ q ∈ (K ∩ U i) ∩ U j, g i q = g j q) :
    ∃ G : ℝ × E → E,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × E =>
          (TotalSpace.mk' E q.2 (G q) : TangentBundle 𝓘(ℝ, E) E)) ∧
      ∀ i ∈ s, ∀ q ∈ K ∩ U i, G q = g i q := by
  obtain ⟨G, hG, hGeq⟩ := exists_contDiff_eqOn_of_localCover hK s U hUo hcover hg hcons
  exact ⟨G, contMDiff_tangentSection_of_contDiff (X := fun t p => G (t, p))
    (by simpa using hG), hGeq⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end
