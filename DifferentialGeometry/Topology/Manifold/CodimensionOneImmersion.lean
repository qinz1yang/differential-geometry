/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

open Manifold Metric Topology
open scoped Manifold ContDiff

noncomputable section

universe u v w x y z

namespace DifferentialGeometry.Topology

theorem nonempty_continuousLinearEquiv_complement_real_of_finrank_succ
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {E' : Type w} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    (hdim : Module.finrank ℝ E' = Module.finrank ℝ E + 1)
    (e : (E × F) ≃L[ℝ] E') : Nonempty (F ≃L[ℝ] ℝ) := by
  let i : F →ₗ[ℝ] E' := e.toLinearMap.comp (LinearMap.inr ℝ E F)
  have hi : Function.Injective i := e.injective.comp LinearMap.inr_injective
  let _ : FiniteDimensional ℝ F := FiniteDimensional.of_injective i hi
  have hprod : Module.finrank ℝ (E × F) = Module.finrank ℝ E' :=
    e.toLinearEquiv.finrank_eq
  have hF : Module.finrank ℝ F = 1 := by
    rw [Module.finrank_prod, hdim] at hprod
    omega
  exact ⟨ContinuousLinearEquiv.ofFinrankEq (by simpa using hF)⟩

theorem isImmersionOfComplement_real_of_finrank_succ
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H : Type w} [TopologicalSpace H] {G : Type x} [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' G}
    {M : Type y} [TopologicalSpace M] [ChartedSpace H M] [Nonempty M]
    {N : Type z} [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} {f : M → N}
    (hdim : Module.finrank ℝ E' = Module.finrank ℝ E + 1)
    (hf : IsImmersion I J n f) : IsImmersionOfComplement ℝ I J n f := by
  let x₀ : M := Classical.choice inferInstance
  let hlocal := hf.isImmersionOfComplement_complement x₀
  let normalEquiv : hf.complement ≃L[ℝ] ℝ := Classical.choice
    (nonempty_continuousLinearEquiv_complement_real_of_finrank_succ hdim hlocal.equiv)
  exact hf.isImmersionOfComplement_complement.trans_F normalEquiv

theorem isImmersionOfComplement_real_of_isSmoothEmbedding_finrank_succ
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H : Type w} [TopologicalSpace H] {G : Type x} [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' G}
    {M : Type y} [TopologicalSpace M] [ChartedSpace H M] [Nonempty M]
    {N : Type z} [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} {f : M → N}
    (hf : IsSmoothEmbedding I J n f)
    (hdim : Module.finrank ℝ E' = Module.finrank ℝ E + 1) :
    IsImmersionOfComplement ℝ I J n f :=
  DifferentialGeometry.Topology.isImmersionOfComplement_real_of_finrank_succ hdim hf.isImmersion

theorem isImmersionOfComplement_real_of_isSmoothEmbedding_sphereTwo
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {n : ℕ∞ω}
    {e : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M}
    (he : IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) n e) :
    IsImmersionOfComplement ℝ
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) n e := by
  let _ : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
  exact isImmersionOfComplement_real_of_isSmoothEmbedding_finrank_succ he (by simp)

noncomputable def realNormalFormPartialHomeomorph
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N} {x₀ : M}
    (h : IsImmersionAtOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f x₀) :
    OpenPartialHomeomorph (M × ℝ) N :=
  (h.domChart.prod (OpenPartialHomeomorph.refl ℝ)).trans
    (h.equiv.toHomeomorph.toOpenPartialHomeomorph.trans h.codChart.symm)

theorem codChart_apply_eq_equiv_domChart_zero
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N} {x₀ : M}
    (h : IsImmersionAtOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f x₀)
    {y : M} (hy : y ∈ h.domChart.source) :
    h.codChart (f y) = h.equiv (h.domChart y, 0) := by
  have hycoord : h.domChart y ∈
      (h.domChart.extend (modelWithCornersSelf ℝ E)).target := by
    simpa [OpenPartialHomeomorph.extend_target] using
      h.domChart.map_source hy
  have hnormal := h.writtenInCharts hycoord
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, id_eq] at hnormal
  rw [h.domChart.left_inv hy] at hnormal
  exact hnormal

theorem realNormalFormPartialHomeomorph_zero_mem_source
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N} {x₀ : M}
    (h : IsImmersionAtOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f x₀)
    {y : M} (hy : y ∈ h.domChart.source) :
    (y, 0) ∈ (realNormalFormPartialHomeomorph h).source := by
  rw [realNormalFormPartialHomeomorph, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.trans_source]
  refine ⟨⟨hy, trivial⟩, ?_⟩
  refine ⟨by simp, ?_⟩
  change h.equiv (h.domChart y, 0) ∈ h.codChart.target
  rw [← codChart_apply_eq_equiv_domChart_zero h hy]
  exact h.codChart.map_source (h.source_subset_preimage_source hy)

theorem realNormalFormPartialHomeomorph_apply_zero
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N} {x₀ : M}
    (h : IsImmersionAtOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f x₀)
    {y : M} (hy : y ∈ h.domChart.source) :
    realNormalFormPartialHomeomorph h (y, 0) = f y := by
  change h.codChart.symm (h.equiv (h.domChart y, 0)) = f y
  rw [← codChart_apply_eq_equiv_domChart_zero h hy]
  exact h.codChart.left_inv (h.source_subset_preimage_source hy)

theorem fst_mem_domChart_source_of_mem_realNormalFormPartialHomeomorph_source
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N} {x₀ : M}
    (h : IsImmersionAtOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f x₀)
    {q : M × ℝ} (hq : q ∈ (realNormalFormPartialHomeomorph h).source) :
    q.1 ∈ h.domChart.source := by
  rw [realNormalFormPartialHomeomorph, OpenPartialHomeomorph.trans_source] at hq
  exact hq.1.1

theorem contMDiffOn_realNormalFormPartialHomeomorph
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N} {x₀ : M}
    (h : IsImmersionAtOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f x₀) :
    ContMDiffOn
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ E') n
      (realNormalFormPartialHomeomorph h)
      (realNormalFormPartialHomeomorph h).source := by
  intro q hq
  have hqdom : q.1 ∈ h.domChart.source :=
    fst_mem_domChart_source_of_mem_realNormalFormPartialHomeomorph_source h hq
  have hdom : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) n
      h.domChart q.1 :=
    contMDiffAt_of_mem_maximalAtlas h.domChart_mem_maximalAtlas hqdom
  have hprod : ContMDiffAt
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ (E × ℝ)) n
      (fun q : M × ℝ ↦ (h.domChart q.1, q.2)) q := by
    rw [contMDiffAt_prod_module_iff]
    constructor
    · exact hdom.comp q
        (contMDiff_fst (I := modelWithCornersSelf ℝ E)
          (J := modelWithCornersSelf ℝ ℝ) (n := n)).contMDiffAt
    · exact (contMDiff_snd (I := modelWithCornersSelf ℝ E)
        (J := modelWithCornersSelf ℝ ℝ) (n := n)).contMDiffAt
  have hequiv : ContMDiffAt
      (modelWithCornersSelf ℝ (E × ℝ)) (modelWithCornersSelf ℝ E') n
      h.equiv (h.domChart q.1, q.2) :=
    h.equiv.contDiff.contMDiff.contMDiffAt
  have hcodmem : h.equiv (h.domChart q.1, q.2) ∈ h.codChart.target := by
    rw [realNormalFormPartialHomeomorph, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hq
    exact hq.2.2
  have hcod : ContMDiffAt (modelWithCornersSelf ℝ E') (modelWithCornersSelf ℝ E') n
      h.codChart.symm (h.equiv (h.domChart q.1, q.2)) :=
    contMDiffAt_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas hcodmem
  change ContMDiffWithinAt
    ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ ℝ))
    (modelWithCornersSelf ℝ E') n
    (fun q : M × ℝ ↦ h.codChart.symm (h.equiv (h.domChart q.1, q.2)))
    (realNormalFormPartialHomeomorph h).source q
  exact (hcod.comp q (hequiv.comp q hprod)).contMDiffWithinAt

theorem contMDiffOn_symm_realNormalFormPartialHomeomorph
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N} {x₀ : M}
    (h : IsImmersionAtOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f x₀) :
    ContMDiffOn
      (modelWithCornersSelf ℝ E')
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ ℝ)) n
      (realNormalFormPartialHomeomorph h).symm
      (realNormalFormPartialHomeomorph h).target := by
  intro q hq
  have hqcod : q ∈ h.codChart.source := by
    rw [realNormalFormPartialHomeomorph, OpenPartialHomeomorph.trans_target,
      OpenPartialHomeomorph.trans_target] at hq
    exact hq.1.1
  have hcoord : h.equiv.symm (h.codChart q) ∈
      (h.domChart.prod (OpenPartialHomeomorph.refl ℝ)).target := by
    rw [realNormalFormPartialHomeomorph, OpenPartialHomeomorph.trans_target,
      OpenPartialHomeomorph.trans_target] at hq
    exact hq.2
  have hfstmem : (h.equiv.symm (h.codChart q)).1 ∈ h.domChart.target := by
    simpa using hcoord.1
  have hcod : ContMDiffAt (modelWithCornersSelf ℝ E') (modelWithCornersSelf ℝ E') n
      h.codChart q :=
    contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas hqcod
  have hequiv : ContMDiffAt
      (modelWithCornersSelf ℝ E') (modelWithCornersSelf ℝ (E × ℝ)) n
      h.equiv.symm (h.codChart q) :=
    h.equiv.symm.contDiff.contMDiff.contMDiffAt
  have hpre : ContMDiffAt
      (modelWithCornersSelf ℝ E') (modelWithCornersSelf ℝ (E × ℝ)) n
      (fun z : N ↦ h.equiv.symm (h.codChart z)) q :=
    hequiv.comp q hcod
  have hcomponents :
      ContMDiffAt (modelWithCornersSelf ℝ E') (modelWithCornersSelf ℝ E) n
          (fun z : N ↦ (h.equiv.symm (h.codChart z)).1) q ∧
        ContMDiffAt (modelWithCornersSelf ℝ E') (modelWithCornersSelf ℝ ℝ) n
          (fun z : N ↦ (h.equiv.symm (h.codChart z)).2) q := by
    exact (contMDiffAt_prod_module_iff _).mp hpre
  have hdom : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) n
      h.domChart.symm (h.equiv.symm (h.codChart q)).1 :=
    contMDiffAt_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas hfstmem
  change ContMDiffWithinAt
    (modelWithCornersSelf ℝ E')
    ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ ℝ)) n
    (fun z : N ↦
      (h.domChart.symm (h.equiv.symm (h.codChart z)).1,
        (h.equiv.symm (h.codChart z)).2))
    (realNormalFormPartialHomeomorph h).target q
  exact ((hdom.comp q hcomponents.1).prodMk hcomponents.2).contMDiffWithinAt

theorem exists_embeddingAdapted_realNormalFormPartialHomeomorph
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type w} [TopologicalSpace M] [ChartedSpace E M]
    {N : Type x} [TopologicalSpace N] [ChartedSpace E' N]
    {n : ℕ∞ω} {f : M → N} {x₀ : M}
    (hf : IsEmbedding f)
    (h : IsImmersionAtOfComplement ℝ
      (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') n f x₀) :
    ∃ phi : OpenPartialHomeomorph (M × ℝ) N,
      ((∀ {y : M}, y ∈ h.domChart.source →
          (y, 0) ∈ phi.source ∧ phi (y, 0) = f y) ∧
        ∀ q ∈ phi.source, phi q ∈ Set.range f ↔ q.2 = 0) ∧
      ContMDiffOn
        ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ ℝ))
        (modelWithCornersSelf ℝ E') n phi phi.source ∧
      ContMDiffOn
        (modelWithCornersSelf ℝ E')
        ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ ℝ)) n
        phi.symm phi.target := by
  obtain ⟨W, hWopen, hWpreimage⟩ :=
    hf.isInducing.isOpen_iff.mp h.domChart.open_source
  let normal := realNormalFormPartialHomeomorph h
  let phi := normal.trans (OpenPartialHomeomorph.ofSet W hWopen)
  refine ⟨phi, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro y hy
    have hyNormal : (y, 0) ∈ normal.source :=
      realNormalFormPartialHomeomorph_zero_mem_source h hy
    have hfyW : f y ∈ W := by
      change y ∈ f ⁻¹' W
      rw [hWpreimage]
      exact hy
    constructor
    · change (y, 0) ∈
        (normal.trans (OpenPartialHomeomorph.ofSet W hWopen)).source
      rw [OpenPartialHomeomorph.trans_source]
      exact ⟨hyNormal, by simpa [normal,
        realNormalFormPartialHomeomorph_apply_zero h hy]⟩
    · change normal (y, 0) = f y
      exact realNormalFormPartialHomeomorph_apply_zero h hy
  · intro q hq
    have hq' : q ∈ normal.source ∧ normal q ∈ W := by
      simpa only [phi, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.ofSet_source, Set.mem_inter_iff, Set.mem_preimage] using hq
    constructor
    · rintro ⟨z, hz⟩
      have hfzW : f z ∈ W := by
        rw [hz]
        exact hq'.2
      have hzdom : z ∈ h.domChart.source := by
        rw [← hWpreimage]
        exact hfzW
      have hzNormal : (z, 0) ∈ normal.source :=
        realNormalFormPartialHomeomorph_zero_mem_source h hzdom
      have hqeq : q = (z, 0) := normal.injOn hq'.1 hzNormal <| by
        rw [show normal (z, 0) = f z by
          exact realNormalFormPartialHomeomorph_apply_zero h hzdom]
        exact hz.symm
      exact congrArg Prod.snd hqeq
    · intro hqzero
      have hqdom : q.1 ∈ h.domChart.source :=
        fst_mem_domChart_source_of_mem_realNormalFormPartialHomeomorph_source h hq'.1
      refine ⟨q.1, ?_⟩
      change f q.1 = normal q
      rw [← realNormalFormPartialHomeomorph_apply_zero h hqdom]
      exact congrArg normal (Prod.ext rfl hqzero.symm)
  · change ContMDiffOn
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ E') n normal phi.source
    exact (contMDiffOn_realNormalFormPartialHomeomorph h).mono <| by
      intro q hq
      change q ∈ normal.source ∩ normal ⁻¹' W at hq
      exact hq.1
  · change ContMDiffOn
      (modelWithCornersSelf ℝ E')
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ ℝ)) n
      normal.symm phi.target
    exact (contMDiffOn_symm_realNormalFormPartialHomeomorph h).mono <| by
      intro q hq
      change q ∈ W ∩ normal.target at hq
      exact hq.2

end DifferentialGeometry.Topology
