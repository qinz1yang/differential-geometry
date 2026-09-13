import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpaceProd
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.SmoothEmbedding

set_option autoImplicit false
noncomputable section
open Set Function
open Manifold (IsImmersionAtOfComplement IsImmersionOfComplement IsImmersion IsSmoothEmbedding)
open scoped Manifold ContDiff
namespace DifferentialGeometry.Manifold

variable {𝕜 E F H H' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace H']

variable (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
  (e : H ≃ₜ H') (L : E ≃L[𝕜] F)
  (hcompat : ∀ y, J (e y) = L (I y))

include hcompat in
private theorem symm_apply_eq (z : E) (hz : z ∈ Set.range I) :
    J.symm (L z) = e (I.symm z) := by
  have h : J (e (I.symm z)) = L z := by rw [hcompat, I.right_inv hz]
  rw [← h, J.left_inv]

include hcompat in
private theorem inv_aux (x : F) (hx : x ∈ Set.range J) :
    I.symm (L.symm x) = e.symm (J.symm x) := by
  obtain ⟨y, rfl⟩ := hx
  have hy : J y = L (I (e.symm y)) := by rw [← hcompat, e.apply_symm_apply]
  rw [hy, L.symm_apply_apply, I.left_inv]
  rw [← hy, J.left_inv]

include hcompat in
private theorem contDiffOn_conj_iff {n : ℕ∞ω} {ψ : OpenPartialHomeomorph H H} {s : Set H} :
    ContDiffOn 𝕜 n (fun x => J (e (ψ (e.symm (J.symm x)))))
        (J.symm ⁻¹' (e.symm ⁻¹' s) ∩ Set.range J) ↔
      ContDiffOn 𝕜 n (fun x => I (ψ (I.symm x))) (I.symm ⁻¹' s ∩ Set.range I) := by
  have hrange : Set.range J = L '' Set.range I :=
    range_model_transHomeomorph I J e L.toHomeomorph hcompat
  have hdom : J.symm ⁻¹' (e.symm ⁻¹' s) ∩ Set.range J =
      L '' (I.symm ⁻¹' s ∩ Set.range I) := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      rw [hrange] at hx2
      obtain ⟨z, hz, rfl⟩ := hx2
      have hzx : J.symm (L z) = e (I.symm z) := symm_apply_eq I J e L hcompat z hz
      refine ⟨z, ⟨?_, hz⟩, rfl⟩
      change e.symm (J.symm (L z)) ∈ s at hx1
      rwa [hzx, e.symm_apply_apply] at hx1
    · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
      have hzx : J.symm (L z) = e (I.symm z) := symm_apply_eq I J e L hcompat z hz2
      refine ⟨?_, ?_⟩
      · change e.symm (J.symm (L z)) ∈ s
        rw [hzx, e.symm_apply_apply]
        exact hz1
      · rw [hrange]
        exact ⟨z, hz2, rfl⟩
  have heq : EqOn (fun x => J (e (ψ (e.symm (J.symm x)))))
      (fun x => L (I (ψ (I.symm (L.symm x))))) (L '' (I.symm ⁻¹' s ∩ Set.range I)) := by
    rintro x ⟨z, ⟨hz1, hz2⟩, rfl⟩
    have hzx : J.symm (L z) = e (I.symm z) := symm_apply_eq I J e L hcompat z hz2
    change J (e (ψ (e.symm (J.symm (L z))))) = L (I (ψ (I.symm (L.symm (L z)))))
    rw [hzx, e.symm_apply_apply, L.symm_apply_apply, hcompat]
  have hset : L '' (I.symm ⁻¹' s ∩ Set.range I) =
      L.symm ⁻¹' (I.symm ⁻¹' s ∩ Set.range I) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨L.symm x, hx, L.apply_symm_apply x⟩
  rw [hdom, contDiffOn_congr heq]
  have h1 : ContDiffOn 𝕜 n (fun x => L (I (ψ (I.symm (L.symm x)))))
        (L '' (I.symm ⁻¹' s ∩ Set.range I)) ↔
      ContDiffOn 𝕜 n (fun x => I (ψ (I.symm (L.symm x))))
        (L '' (I.symm ⁻¹' s ∩ Set.range I)) :=
    ContinuousLinearEquiv.comp_contDiffOn_iff
      (f := fun x : F => I (ψ (I.symm (L.symm x))))
      (s := L '' (I.symm ⁻¹' s ∩ Set.range I)) (L : E ≃L[𝕜] F)
  have h2 : ContDiffOn 𝕜 n (fun x => I (ψ (I.symm (L.symm x))))
        (L '' (I.symm ⁻¹' s ∩ Set.range I)) ↔
      ContDiffOn 𝕜 n (fun x => I (ψ (I.symm x))) (I.symm ⁻¹' s ∩ Set.range I) := by
    rw [hset]
    exact ContinuousLinearEquiv.contDiffOn_comp_iff
      (f := fun x : E => I (ψ (I.symm x)))
      (s := I.symm ⁻¹' s ∩ Set.range I) (L.symm : F ≃L[𝕜] E)
  exact h1.trans h2

private theorem conj_coe (e : H ≃ₜ H') (ψ : OpenPartialHomeomorph H H) :
    ⇑(e.toOpenPartialHomeomorph.symm ≫ₕ ψ ≫ₕ e.toOpenPartialHomeomorph) =
      fun x => e (ψ (e.symm x)) := by
  funext x
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    ← Homeomorph.symm_toOpenPartialHomeomorph, Homeomorph.toOpenPartialHomeomorph_apply]

private theorem conj_source (e : H ≃ₜ H') (ψ : OpenPartialHomeomorph H H) :
    (e.toOpenPartialHomeomorph.symm ≫ₕ ψ ≫ₕ e.toOpenPartialHomeomorph).source =
      e.symm ⁻¹' ψ.source := by
  simp only [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    ← Homeomorph.symm_toOpenPartialHomeomorph, Homeomorph.toOpenPartialHomeomorph_apply,
    Set.preimage_univ, Set.inter_univ, Set.univ_inter]

private theorem conj_target (e : H ≃ₜ H') (ψ : OpenPartialHomeomorph H H) :
    (e.toOpenPartialHomeomorph.symm ≫ₕ ψ ≫ₕ e.toOpenPartialHomeomorph).target =
      e.symm ⁻¹' ψ.target := by
  simp only [OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
    ← Homeomorph.symm_toOpenPartialHomeomorph, Homeomorph.toOpenPartialHomeomorph_apply,
    Set.preimage_univ, Set.inter_univ, Set.univ_inter]

private theorem conj_symm (e : H ≃ₜ H') (ψ : OpenPartialHomeomorph H H) :
    (e.toOpenPartialHomeomorph.symm ≫ₕ ψ ≫ₕ e.toOpenPartialHomeomorph).symm =
      e.toOpenPartialHomeomorph.symm ≫ₕ ψ.symm ≫ₕ e.toOpenPartialHomeomorph := by
  simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.trans_assoc]

include hcompat in
theorem mem_contDiffGroupoid_conj_iff {n : ℕ∞ω} {ψ : OpenPartialHomeomorph H H} :
    (e.toOpenPartialHomeomorph.symm ≫ₕ ψ ≫ₕ e.toOpenPartialHomeomorph) ∈
        contDiffGroupoid n J ↔
      ψ ∈ contDiffGroupoid n I := by
  have hsymm := conj_symm e ψ
  simp only [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h1' : ContDiffOn 𝕜 n (↑J ∘ (fun x => e (ψ (e.symm x))) ∘ ↑J.symm)
          (J.symm ⁻¹' (e.symm ⁻¹' ψ.source) ∩ Set.range J) := by
        simpa only [conj_coe e ψ, conj_source e ψ, contDiffPregroupoid] using h1
      rw [show (↑J ∘ (fun x => e (ψ (e.symm x))) ∘ ↑J.symm) =
        (fun x => J (e (ψ (e.symm (J.symm x))))) from funext fun _ => rfl] at h1'
      exact (contDiffOn_conj_iff I J e L hcompat (ψ := ψ) (s := ψ.source)).mp h1'
    · have h2' : ContDiffOn 𝕜 n (↑J ∘ (fun x => e (ψ.symm (e.symm x))) ∘ ↑J.symm)
          (J.symm ⁻¹' (e.symm ⁻¹' ψ.target) ∩ Set.range J) := by
        simpa only [hsymm, conj_coe e ψ.symm, conj_target e ψ, contDiffPregroupoid] using h2
      rw [show (↑J ∘ (fun x => e (ψ.symm (e.symm x))) ∘ ↑J.symm) =
        (fun x => J (e (ψ.symm (e.symm (J.symm x))))) from funext fun _ => rfl] at h2'
      exact (contDiffOn_conj_iff I J e L hcompat (ψ := ψ.symm) (s := ψ.target)).mp h2'
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h1' := (contDiffOn_conj_iff I J e L hcompat (ψ := ψ) (s := ψ.source)).mpr h1
      rw [show (fun x => J (e (ψ (e.symm (J.symm x))))) =
        (↑J ∘ (fun x => e (ψ (e.symm x))) ∘ ↑J.symm) from funext fun _ => rfl] at h1'
      simpa only [conj_coe e ψ, conj_source e ψ, contDiffPregroupoid] using h1'
    · have h2' := (contDiffOn_conj_iff I J e L hcompat (ψ := ψ.symm) (s := ψ.target)).mpr h2
      rw [show (fun x => J (e (ψ.symm (e.symm (J.symm x))))) =
        (↑J ∘ (fun x => e (ψ.symm (e.symm x))) ∘ ↑J.symm) from funext fun _ => rfl] at h2'
      simpa only [hsymm, conj_coe e ψ.symm, conj_target e ψ, contDiffPregroupoid] using h2'

variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

theorem atlas_chartedSpaceTransHomeomorph (e : H ≃ₜ H') :
    let _ := chartedSpaceTransHomeomorph (M := N) e
    atlas H' N = (atlas H N).image (fun φ => φ.trans e.toOpenPartialHomeomorph) := by
  let _ := chartedSpaceTransHomeomorph (M := N) e
  dsimp only []
  unfold DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph
  ext f
  simp only [Set.mem_image]
  constructor
  · rintro ⟨φ, hφ, E', rfl, rfl⟩
    exact ⟨φ, hφ, rfl⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨φ, hφ, e.toOpenPartialHomeomorph, rfl, rfl⟩

include hcompat in
theorem mem_maximalAtlas_chartedSpaceTransHomeomorph {n : ℕ∞ω}
    {φ : OpenPartialHomeomorph N H} :
    let _ := chartedSpaceTransHomeomorph (M := N) e
    φ.trans e.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas J n N ↔
      φ ∈ IsManifold.maximalAtlas I n N := by
  let _ := chartedSpaceTransHomeomorph (M := N) e
  dsimp only []
  have hconj : ∀ {ρ σ : OpenPartialHomeomorph N H},
      (ρ.trans e.toOpenPartialHomeomorph).symm ≫ₕ (σ.trans e.toOpenPartialHomeomorph) =
        e.toOpenPartialHomeomorph.symm ≫ₕ (ρ.symm ≫ₕ σ) ≫ₕ
          e.toOpenPartialHomeomorph := by
    intro ρ σ
    simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc]
  rw [IsManifold.mem_maximalAtlas_iff, IsManifold.mem_maximalAtlas_iff]
  constructor
  · intro h g hg
    have h' := h (g.trans e.toOpenPartialHomeomorph) (by
      rw [atlas_chartedSpaceTransHomeomorph]; exact ⟨g, hg, rfl⟩)
    rw [hconj, hconj] at h'
    exact ⟨(mem_contDiffGroupoid_conj_iff I J e L hcompat).mp h'.1,
      (mem_contDiffGroupoid_conj_iff I J e L hcompat).mp h'.2⟩
  · intro h f' hf'
    rw [atlas_chartedSpaceTransHomeomorph] at hf'
    obtain ⟨g, hg, rfl⟩ := hf'
    have h' := h g hg
    rw [hconj, hconj]
    exact ⟨(mem_contDiffGroupoid_conj_iff I J e L hcompat).mpr h'.1,
      (mem_contDiffGroupoid_conj_iff I J e L hcompat).mpr h'.2⟩

variable {E₀ H₀ M : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
  [TopologicalSpace H₀] [TopologicalSpace M] [ChartedSpace H₀ M]

omit [ChartedSpace H N] in
include hcompat in
private theorem extend_trans_homeomorph_apply (φ : OpenPartialHomeomorph N H) (y : N) :
    (φ.trans e.toOpenPartialHomeomorph).extend J y = L (φ.extend I y) := by
  rw [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
    Function.comp_apply, OpenPartialHomeomorph.trans_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, hcompat]

omit [ChartedSpace H N] in
include hcompat in
private theorem extend_trans_homeomorph_target (φ : OpenPartialHomeomorph N H) :
    ((φ.trans e.toOpenPartialHomeomorph).extend J).target = L '' (φ.extend I).target := by
  have h1 : (φ.trans e.toOpenPartialHomeomorph).target = e '' φ.target := by
    rw [OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
      Set.univ_inter, ← Homeomorph.symm_toOpenPartialHomeomorph,
      Homeomorph.toOpenPartialHomeomorph_apply]
    ext x
    constructor
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [OpenPartialHomeomorph.extend_target', OpenPartialHomeomorph.extend_target', h1,
    ← Set.image_comp, ← Set.image_comp]
  exact congrArg (· '' φ.target) (funext fun y => hcompat y)

omit [ChartedSpace H N] in
include hcompat in
private theorem extend_trans_homeomorph_symm_apply (φ : OpenPartialHomeomorph N H) {z : E}
    (hz : z ∈ (φ.extend I).target) :
    ((φ.trans e.toOpenPartialHomeomorph).extend J).symm (L z) = (φ.extend I).symm z := by
  have hzI : z ∈ Set.range I := OpenPartialHomeomorph.extend_target_subset_range φ hz
  have hzJ : L z ∈ Set.range J := by
    rw [range_model_transHomeomorph I J e L.toHomeomorph hcompat]
    exact ⟨z, hzI, rfl⟩
  have hkey : e.symm (J.symm (L z)) = I.symm z := by
    have := inv_aux I J e L hcompat (L z) hzJ
    rw [L.symm_apply_apply] at this
    exact this.symm
  rw [OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe_symm,
    Function.comp_apply, Function.comp_apply, OpenPartialHomeomorph.coe_trans_symm,
    Function.comp_apply, ← Homeomorph.symm_toOpenPartialHomeomorph,
    Homeomorph.toOpenPartialHomeomorph_apply, hkey]

omit [ChartedSpace H N] [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] in
include hcompat in
private theorem eqOn_writtenInExtend_trans {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (φ : OpenPartialHomeomorph N H) (g : N → E₀) (Ξ : E × G → E₀) (Ξ' : F × G → E₀)
    (hΞ : ∀ (z : E) (c : G), Ξ' (L z, c) = Ξ (z, c))
    (h : EqOn (g ∘ (φ.extend I).symm) (fun z : E => Ξ (z, 0)) (φ.extend I).target) :
    EqOn (g ∘ ((φ.trans e.toOpenPartialHomeomorph).extend J).symm) (fun z : F => Ξ' (z, 0))
      ((φ.trans e.toOpenPartialHomeomorph).extend J).target := by
  intro w hw
  rw [extend_trans_homeomorph_target I J e L hcompat φ] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  rw [Function.comp_apply, extend_trans_homeomorph_symm_apply I J e L hcompat φ hz]
  exact (h hz).trans (hΞ z 0).symm

include hcompat in
theorem isImmersionAtOfComplement_chartedSpaceTransHomeomorph_source_iff {F₀ : Type*}
    [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀]
    (I₀ : ModelWithCorners 𝕜 E₀ H₀) {n : ℕ∞ω} {f : N → M} {x : N} :
    let _ := chartedSpaceTransHomeomorph (M := N) e
    IsImmersionAtOfComplement F₀ J I₀ n f x ↔
      IsImmersionAtOfComplement F₀ I I₀ n f x := by
  let _ := chartedSpaceTransHomeomorph (M := N) e
  dsimp only []
  constructor
  · intro h
    have hcompat' : ∀ y : H', I (e.symm y) = L.symm (J y) := by
      intro y
      have h1 : J y = L (I (e.symm y)) := by rw [← hcompat (e.symm y), e.apply_symm_apply]
      exact (L.symm_apply_apply (I (e.symm y))).symm.trans (congrArg (fun z => L.symm z) h1).symm
    have heq : (h.domChart.trans e.toOpenPartialHomeomorph.symm).trans
        e.toOpenPartialHomeomorph ≈ h.domChart := by
      have h2 : e.toOpenPartialHomeomorph.symm.trans e.toOpenPartialHomeomorph ≈
          OpenPartialHomeomorph.ofSet e.toOpenPartialHomeomorph.target
            e.toOpenPartialHomeomorph.open_target :=
        OpenPartialHomeomorph.symm_trans_self _
      have h3 : h.domChart.trans (OpenPartialHomeomorph.ofSet e.toOpenPartialHomeomorph.target
          e.toOpenPartialHomeomorph.open_target) ≈ h.domChart := by
        refine ⟨?_, ?_⟩
        · simp only [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_target,
            OpenPartialHomeomorph.ofSet_source, Set.preimage_univ, Set.inter_univ]
        · intro y _
          rfl
      rw [OpenPartialHomeomorph.trans_assoc]
      exact Setoid.trans
        (OpenPartialHomeomorph.EqOnSource.trans' (OpenPartialHomeomorph.eqOnSource_refl _) h2) h3
    have hmem : ((h.domChart.trans e.toOpenPartialHomeomorph.symm).trans
        e.toOpenPartialHomeomorph) ∈ IsManifold.maximalAtlas J n N :=
      StructureGroupoid.mem_maximalAtlas_of_eqOnSource (G := contDiffGroupoid n J) heq
        h.domChart_mem_maximalAtlas
    have hmax : (h.domChart.trans e.toOpenPartialHomeomorph.symm) ∈
        IsManifold.maximalAtlas I n N :=
      (mem_maximalAtlas_chartedSpaceTransHomeomorph I J e L hcompat
        (φ := h.domChart.trans e.toOpenPartialHomeomorph.symm)).mp hmem
    let e' : (E × F₀) ≃L[𝕜] E₀ :=
      (ContinuousLinearEquiv.prodCongr L.symm
        (ContinuousLinearEquiv.refl 𝕜 F₀)).symm.trans h.equiv
    refine IsImmersionAtOfComplement.mk_of_charts (F := F₀) e'
      (h.domChart.trans e.toOpenPartialHomeomorph.symm) h.codChart ?_ h.mem_codChart_source
      hmax h.codChart_mem_maximalAtlas ?_ ?_
    · simpa only [OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source, ← Homeomorph.symm_toOpenPartialHomeomorph,
        Set.preimage_univ, Set.inter_univ] using h.mem_domChart_source
    · simpa only [OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source, ← Homeomorph.symm_toOpenPartialHomeomorph,
        Set.preimage_univ, Set.inter_univ] using h.source_subset_preimage_source
    · exact eqOn_writtenInExtend_trans J I e.symm L.symm hcompat' h.domChart
        ((h.codChart.extend I₀) ∘ f) (fun z => h.equiv z) (fun z => e' z)
        (fun z c => by
          simp only [e', ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
            ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.symm_apply_apply]
          rfl)
        h.writtenInCharts
  · intro h
    let e' : (F × F₀) ≃L[𝕜] E₀ :=
      (ContinuousLinearEquiv.prodCongr L (ContinuousLinearEquiv.refl 𝕜 F₀)).symm.trans h.equiv
    refine IsImmersionAtOfComplement.mk_of_charts (F := F₀) e'
      (h.domChart.trans e.toOpenPartialHomeomorph) h.codChart ?_ h.mem_codChart_source
      ?_ h.codChart_mem_maximalAtlas ?_ ?_
    · simpa only [OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]
        using h.mem_domChart_source
    · exact (mem_maximalAtlas_chartedSpaceTransHomeomorph I J e L hcompat).mpr
        h.domChart_mem_maximalAtlas
    · simpa only [OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]
        using h.source_subset_preimage_source
    · exact eqOn_writtenInExtend_trans I J e L hcompat h.domChart
        ((h.codChart.extend I₀) ∘ f) (fun z => h.equiv z) (fun z => e' z)
        (fun z c => by
          simp only [e', ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
            ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.symm_apply_apply]
          rfl)
        h.writtenInCharts

include hcompat in
theorem isImmersionOfComplement_chartedSpaceTransHomeomorph_source_iff {F₀ : Type*}
    [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀]
    (I₀ : ModelWithCorners 𝕜 E₀ H₀) {n : ℕ∞ω} {f : N → M} :
    let _ := chartedSpaceTransHomeomorph (M := N) e
    IsImmersionOfComplement F₀ J I₀ n f ↔ IsImmersionOfComplement F₀ I I₀ n f := by
  let _ := chartedSpaceTransHomeomorph (M := N) e
  dsimp only []
  exact forall_congr' fun x =>
    isImmersionAtOfComplement_chartedSpaceTransHomeomorph_source_iff I J e L hcompat I₀

include hcompat in
theorem isImmersion_chartedSpaceTransHomeomorph_source_iff (I₀ : ModelWithCorners 𝕜 E₀ H₀)
    {n : ℕ∞ω} {f : N → M} :
    let _ := chartedSpaceTransHomeomorph (M := N) e
    IsImmersion J I₀ n f ↔ IsImmersion I I₀ n f := by
  let _ := chartedSpaceTransHomeomorph (M := N) e
  dsimp only []
  constructor
  · rintro ⟨F₀, h₁, h₂, h⟩
    exact ⟨F₀, h₁, h₂, fun x =>
      (isImmersionAtOfComplement_chartedSpaceTransHomeomorph_source_iff I J e L hcompat
        I₀).mp (h x)⟩
  · rintro ⟨F₀, h₁, h₂, h⟩
    exact ⟨F₀, h₁, h₂, fun x =>
      (isImmersionAtOfComplement_chartedSpaceTransHomeomorph_source_iff I J e L hcompat
        I₀).mpr (h x)⟩

include hcompat in
theorem isSmoothEmbedding_chartedSpaceTransHomeomorph_source_iff
    (I₀ : ModelWithCorners 𝕜 E₀ H₀) {n : ℕ∞ω} {f : N → M} :
    let _ := chartedSpaceTransHomeomorph (M := N) e
    IsSmoothEmbedding J I₀ n f ↔ IsSmoothEmbedding I I₀ n f := by
  let _ := chartedSpaceTransHomeomorph (M := N) e
  dsimp only []
  constructor
  · intro h
    exact ⟨(isImmersion_chartedSpaceTransHomeomorph_source_iff I J e L hcompat I₀).mp
      h.isImmersion, h.isEmbedding⟩
  · intro h
    exact ⟨(isImmersion_chartedSpaceTransHomeomorph_source_iff I J e L hcompat I₀).mpr
      h.isImmersion, h.isEmbedding⟩

include hcompat in
private theorem contMDiff_id_of_chartedSpaceTransHomeomorph {n : ℕ∞ω} :
    let _ := chartedSpaceTransHomeomorph (M := N) e
    ContMDiff J I n (id : N → N) := by
  let _ := chartedSpaceTransHomeomorph (M := N) e
  dsimp only []
  intro x
  rw [← contMDiffWithinAt_univ, contMDiffWithinAt_iff']
  refine ⟨continuous_id.continuousAt.continuousWithinAt, ?_⟩
  have htarget : (extChartAt J x).target = L '' (extChartAt I x).target := by
    change (((chartAt H' x).extend J)).target = L '' (((chartAt H x).extend I)).target
    rw [chartAt_transHomeomorph]
    exact extend_trans_homeomorph_target I J e L hcompat (chartAt H x)
  have hsymm : ∀ z ∈ (extChartAt I x).target,
      (extChartAt J x).symm (L z) = (extChartAt I x).symm z := by
    intro z hz
    change (((chartAt H' x).extend J)).symm (L z) = ((chartAt H x).extend I).symm z
    rw [chartAt_transHomeomorph]
    exact extend_trans_homeomorph_symm_apply I J e L hcompat (chartAt H x) hz
  have hEq : EqOn ((extChartAt I x) ∘ ⇑(extChartAt J x).symm) ⇑L.symm
      ((extChartAt J x).target ∩ (extChartAt J x).symm ⁻¹' (extChartAt I x).source) := by
    rintro y ⟨hy1, hy2⟩
    rw [htarget] at hy1
    obtain ⟨z, hz, rfl⟩ := hy1
    rw [Function.comp_apply, hsymm z hz, PartialEquiv.right_inv _ hz, L.symm_apply_apply]
  have hp : extChartAt J x x ∈
      (extChartAt J x).target ∩ (extChartAt J x).symm ⁻¹' (extChartAt I x).source := by
    refine ⟨PartialEquiv.map_source _ (by simp), ?_⟩
    rw [Set.mem_preimage, PartialEquiv.left_inv _ (by simp)]
    simp
  have hsm := L.symm.contDiff.contDiffWithinAt (n := n) (s := (extChartAt J x).target)
    (x := extChartAt J x x)
  have hsm' : ContDiffWithinAt 𝕜 n (⇑L.symm)
      ((extChartAt J x).target ∩ (extChartAt J x).symm ⁻¹' (extChartAt I x).source)
      (extChartAt J x x) := hsm.mono Set.inter_subset_left
  have hgoal : ContDiffWithinAt 𝕜 n ((extChartAt I x) ∘ id ∘ ⇑(extChartAt J x).symm)
      ((extChartAt J x).target ∩ (extChartAt J x).symm ⁻¹' (extChartAt I x).source)
      (extChartAt J x x) :=
    (contDiffWithinAt_congr (𝕜 := 𝕜) (n := n)
      (f₁ := (extChartAt I x) ∘ id ∘ ⇑(extChartAt J x).symm)
      (fun y hy => hEq hy) (hEq hp)).mpr hsm'
  simpa only [Set.univ_inter, Set.preimage_id, id_eq] using hgoal

include hcompat in
private theorem contMDiff_id_symm_of_chartedSpaceTransHomeomorph {n : ℕ∞ω} :
    let _ := chartedSpaceTransHomeomorph (M := N) e
    ContMDiff I J n (id : N → N) := by
  let _ := chartedSpaceTransHomeomorph (M := N) e
  dsimp only []
  intro x
  rw [← contMDiffWithinAt_univ, contMDiffWithinAt_iff']
  refine ⟨continuous_id.continuousAt.continuousWithinAt, ?_⟩
  have hEq : EqOn ((extChartAt J x) ∘ ⇑(extChartAt I x).symm) ⇑L
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (extChartAt J x).source) := by
    rintro y hy
    rw [Function.comp_apply,
      coe_extChartAt_chartedSpaceTransHomeomorph I J e L hcompat x, Function.comp_apply,
      PartialEquiv.right_inv _ hy.1]
  have hp : extChartAt I x x ∈
      (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (extChartAt J x).source := by
    refine ⟨PartialEquiv.map_source _ (by simp), ?_⟩
    rw [Set.mem_preimage, PartialEquiv.left_inv _ (by simp)]
    simp
  have hsm := L.contDiff.contDiffWithinAt (n := n) (s := (extChartAt I x).target)
    (x := extChartAt I x x)
  have hsm' : ContDiffWithinAt 𝕜 n (⇑L)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (extChartAt J x).source)
      (extChartAt I x x) := hsm.mono Set.inter_subset_left
  have hgoal : ContDiffWithinAt 𝕜 n ((extChartAt J x) ∘ id ∘ ⇑(extChartAt I x).symm)
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (extChartAt J x).source)
      (extChartAt I x x) :=
    (contDiffWithinAt_congr (𝕜 := 𝕜) (n := n)
      (f₁ := (extChartAt J x) ∘ id ∘ ⇑(extChartAt I x).symm)
      (fun y hy => hEq hy) (hEq hp)).mpr hsm'
  simpa only [Set.univ_inter, Set.preimage_id, id_eq] using hgoal

include hcompat in
theorem contMDiffWithinAt_chartedSpaceTransHomeomorph_source_iff
    (I₀ : ModelWithCorners 𝕜 E₀ H₀)
    {n : ℕ∞ω} {f : N → M} {s : Set N} {x : N} :
    let _ := chartedSpaceTransHomeomorph (M := N) e
    ContMDiffWithinAt J I₀ n f s x ↔ ContMDiffWithinAt I I₀ n f s x := by
  let _ := chartedSpaceTransHomeomorph (M := N) e
  dsimp only []
  constructor
  · intro h
    have hid : ContMDiffWithinAt I J n (id : N → N) s x :=
      (contMDiff_id_symm_of_chartedSpaceTransHomeomorph I J e L hcompat
        (n := n) x).contMDiffWithinAt
    simpa only [Function.comp_id, id_eq] using h.comp x hid (mapsTo_id s)
  · intro h
    have hid : ContMDiffWithinAt J I n (id : N → N) s x :=
      (contMDiff_id_of_chartedSpaceTransHomeomorph I J e L hcompat (n := n) x).contMDiffWithinAt
    simpa only [Function.comp_id, id_eq] using h.comp x hid (mapsTo_id s)

include hcompat in
theorem contMDiffAt_chartedSpaceTransHomeomorph_source_iff (I₀ : ModelWithCorners 𝕜 E₀ H₀)
    {n : ℕ∞ω} {f : N → M} {x : N} :
    let _ := chartedSpaceTransHomeomorph (M := N) e
    ContMDiffAt J I₀ n f x ↔ ContMDiffAt I I₀ n f x := by
  let _ := chartedSpaceTransHomeomorph (M := N) e
  dsimp only []
  rw [← contMDiffWithinAt_univ, ← contMDiffWithinAt_univ]
  exact contMDiffWithinAt_chartedSpaceTransHomeomorph_source_iff I J e L hcompat I₀

include hcompat in
theorem contMDiffOn_chartedSpaceTransHomeomorph_source_iff (I₀ : ModelWithCorners 𝕜 E₀ H₀)
    {n : ℕ∞ω} {f : N → M} {s : Set N} :
    let _ := chartedSpaceTransHomeomorph (M := N) e
    ContMDiffOn J I₀ n f s ↔ ContMDiffOn I I₀ n f s := by
  let _ := chartedSpaceTransHomeomorph (M := N) e
  dsimp only []
  exact forall₂_congr fun x _ =>
    contMDiffWithinAt_chartedSpaceTransHomeomorph_source_iff I J e L hcompat I₀

include hcompat in
theorem contMDiff_chartedSpaceTransHomeomorph_source_iff (I₀ : ModelWithCorners 𝕜 E₀ H₀)
    {n : ℕ∞ω} {f : N → M} :
    let _ := chartedSpaceTransHomeomorph (M := N) e
    ContMDiff J I₀ n f ↔ ContMDiff I I₀ n f := by
  let _ := chartedSpaceTransHomeomorph (M := N) e
  dsimp only []
  exact forall_congr' fun x =>
    contMDiffAt_chartedSpaceTransHomeomorph_source_iff I J e L hcompat I₀

abbrev EuclideanHalfSpaceProdModel : Type :=
  ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)

theorem isSmoothEmbedding_coreInclusion_of_euclideanHalfSpaceProd {core Carrier : Type*}
    [TopologicalSpace core] [ChartedSpace EuclideanHalfSpaceProdModel core]
    [IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ core]
    [TopologicalSpace Carrier] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Carrier]
    (f : core → Carrier)
    (h : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ f) :
    let _ := euclideanHalfSpaceProdChartedSpace core
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f :=
  (isSmoothEmbedding_chartedSpaceTransHomeomorph_source_iff ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
    euclideanHalfSpaceProdHomeomorph euclideanHalfSpaceProdCoordinates
    euclideanHalfSpaceProdHomeomorph_model (𝓡 3)).mpr h

theorem isSmoothEmbedding_coreSubtype_of_euclideanHalfSpaceProd {Carrier : Type*}
    [TopologicalSpace Carrier] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Carrier]
    {core : Set Carrier} [ChartedSpace EuclideanHalfSpaceProdModel core]
    [IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ core]
    (h : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞
      (Subtype.val : core → Carrier)) :
    let _ := euclideanHalfSpaceProdChartedSpace core
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : core → Carrier) :=
  isSmoothEmbedding_coreInclusion_of_euclideanHalfSpaceProd (Subtype.val : core → Carrier) h

theorem isSmoothEmbedding_id_of_euclideanHalfSpaceProd :
    let _ := euclideanHalfSpaceProdChartedSpace EuclideanHalfSpaceProdModel
    IsSmoothEmbedding (𝓡∂ 3) ((𝓡 2).prod (𝓡∂ 1)) ∞
      (id : EuclideanHalfSpaceProdModel → EuclideanHalfSpaceProdModel) :=
  (isSmoothEmbedding_chartedSpaceTransHomeomorph_source_iff ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
    euclideanHalfSpaceProdHomeomorph euclideanHalfSpaceProdCoordinates
    euclideanHalfSpaceProdHomeomorph_model ((𝓡 2).prod (𝓡∂ 1))).mpr
    (IsSmoothEmbedding.id :
      IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod (𝓡∂ 1)) ∞
        (id : EuclideanHalfSpaceProdModel → EuclideanHalfSpaceProdModel))

end DifferentialGeometry.Manifold
