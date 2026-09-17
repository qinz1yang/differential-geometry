import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Topology.Separation.Hausdorff

open Set
open scoped ContDiff Manifold Topology

namespace Manifold

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {H G M N : Type*} [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
  [TopologicalSpace N] [ChartedSpace G N] [T2Space N]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  [I.Boundaryless] [J.Boundaryless] {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]

theorem IsSmoothEmbedding.exists_replacement_of_partialDiffeomorph
    {e : M → N} (he : IsSmoothEmbedding I J n e) (hn : n ≠ 0)
    (φ : PartialDiffeomorph 𝓘(𝕜, E) I E M n)
    {K : Set E} (hK : IsCompact K) (hKφ : K ⊆ φ.source)
    {g : E → N} (hg : IsSmoothEmbedding 𝓘(𝕜, E) J n g)
    (hcollar : ∀ x ∈ frontier K, g =ᶠ[nhds x] e ∘ φ)
    (hdisj : Disjoint (g '' K) (e '' (φ '' K)ᶜ)) :
    ∃ f : M → N, IsSmoothEmbedding I J n f ∧
      (∀ x ∈ K, f (φ x) = g x) ∧ EqOn f e (φ '' K)ᶜ ∧
      ∀ y ∈ φ '' K, f =ᶠ[nhds y] g ∘ φ.symm := by
  classical
  let _ : T2Space M := he.isEmbedding.t2Space
  let L : Set M := φ '' K
  let f : M → N := L.piecewise (g ∘ φ.symm) e
  have hLc : IsClosed L := (hK.image_of_continuousOn
    (φ.contMDiffOn.continuousOn.mono hKφ)).isClosed
  have hLφ : L ⊆ φ.target := by
    rintro y ⟨x, hx, rfl⟩
    exact φ.map_source (hKφ hx)
  have hformula (x : E) (hx : x ∈ K) : f (φ x) = g x := by
    rw [show f (φ x) = g (φ.symm (φ x)) from
      piecewise_eq_of_mem L (g ∘ φ.symm) e (mem_image_of_mem φ hx)]
    exact congrArg g (φ.left_inv (hKφ hx))
  have hfix : EqOn f e Lᶜ := fun y hy => piecewise_eq_of_notMem L (g ∘ φ.symm) e hy
  have hnear (y : M) (hy : y ∈ L) : f =ᶠ[nhds y] g ∘ φ.symm := by
    obtain ⟨x, hx, rfl⟩ := hy
    have hyT : φ x ∈ φ.target := φ.map_source (hKφ hx)
    have hi := φ.symm.contMDiffOn.contMDiffAt (φ.open_target.mem_nhds hyT)
    have hback : φ.symm (φ x) = x := φ.left_inv (hKφ hx)
    by_cases hxi : x ∈ interior K
    · have hn : ∀ᶠ z in nhds (φ x), φ.symm z ∈ interior K := by
        apply hi.continuousAt.preimage_mem_nhds
        rw [hback]
        exact isOpen_interior.mem_nhds hxi
      filter_upwards [φ.open_target.mem_nhds hyT, hn] with z hz hzK
      apply piecewise_eq_of_mem
      exact ⟨φ.symm z, interior_subset hzK, φ.right_inv hz⟩
    · have hxfront : x ∈ frontier K := ⟨hK.isClosed.closure_eq.symm.subset hx, hxi⟩
      have hn : ∀ᶠ z in nhds (φ x), g (φ.symm z) = e (φ (φ.symm z)) := by
        have hh := hi.continuousAt.tendsto.eventually (hback.symm ▸ hcollar x hxfront)
        exact hh
      filter_upwards [φ.open_target.mem_nhds hyT, hn] with z hz hzg
      by_cases hzL : z ∈ L
      · exact piecewise_eq_of_mem L (g ∘ φ.symm) e hzL
      · rw [hfix hzL]
        exact (hzg.trans (congrArg e (φ.right_inv hz))).symm
  have hnear_compl (y : M) (hy : y ∉ L) : f =ᶠ[nhds y] e :=
    Filter.eventuallyEq_of_mem (hLc.isOpen_compl.mem_nhds hy) hfix
  have hglocal (y : M) (hy : y ∈ L) : ContMDiffAt I J n (g ∘ φ.symm) y :=
    hg.contMDiff.contMDiffAt.comp y
      (φ.symm.contMDiffOn.contMDiffAt (φ.open_target.mem_nhds (hLφ hy)))
  have hf : ContMDiff I J n f := by
    intro y
    by_cases hy : y ∈ L
    · exact (hglocal y hy).congr_of_eventuallyEq (hnear y hy)
    · exact he.contMDiff.contMDiffAt.congr_of_eventuallyEq (hnear_compl y hy)
  have himm : IsImmersion I J n f := by
    apply DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv hn hf
    intro y
    by_cases hy : y ∈ L
    · rw [(hnear y hy).mfderiv_eq]
      have hi := φ.symm.isLocalDiffeomorphAt I 𝓘(𝕜, E) n (hLφ hy)
      rw [mfderiv_comp y (hg.contMDiff.mdifferentiableAt hn)
        (hi.mdifferentiableAt hn)]
      exact ((hg.isImmersion.isImmersionAt (φ.symm y)).injective_mfderiv hn).comp
        (hi.mfderivToContinuousLinearEquiv hn).injective
    · rw [(hnear_compl y hy).mfderiv_eq]
      exact (he.isImmersion.isImmersionAt y).injective_mfderiv hn
  have hinj : Function.Injective f := by
    intro x y hxy
    by_cases hx : x ∈ L
    · obtain ⟨u, hu, rfl⟩ := hx
      rw [hformula u hu] at hxy
      by_cases hy : y ∈ L
      · obtain ⟨v, hv, rfl⟩ := hy
        rw [hformula v hv] at hxy
        exact congrArg φ (hg.isEmbedding.injective hxy)
      · exact False.elim (Set.disjoint_left.mp hdisj (mem_image_of_mem g hu)
          ⟨y, hy, (hfix hy).symm.trans hxy.symm⟩)
    · by_cases hy : y ∈ L
      · obtain ⟨v, hv, rfl⟩ := hy
        rw [hformula v hv] at hxy
        exact False.elim (Set.disjoint_left.mp hdisj (mem_image_of_mem g hv)
          ⟨x, hx, (hfix hx).symm.trans hxy⟩)
      · exact he.isEmbedding.injective ((hfix hx).symm.trans (hxy.trans (hfix hy)))
  exact ⟨f, ⟨himm, (hf.continuous.isClosedEmbedding hinj).isEmbedding⟩, hformula, hfix, hnear⟩

end Manifold
