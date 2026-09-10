import DifferentialGeometry.Topology.Manifold.RegularLevel.Coordinates
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.EmbeddedHypersurface

variable {m : ℕ} {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {S M : Type*} [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  (I : ModelWithCorners ℝ (MorseModel m) H)
  (J : ModelWithCorners ℝ (MorseModel (m + 1)) G)

theorem isImmersionAtOfComplement_real {e : S → M} {x : S}
    (he : Manifold.IsImmersionAt I J ∞ e x) :
    Manifold.IsImmersionAtOfComplement ℝ I J ∞ e x := by
  let F := he.complement
  let L : (MorseModel m × F) ≃L[ℝ] MorseModel (m + 1) := he.equiv
  let : FiniteDimensional ℝ F := FiniteDimensional.of_injective
    (L.toLinearMap.comp (LinearMap.inr ℝ (MorseModel m) F))
    (L.injective.comp LinearMap.inr_injective)
  have hdim := L.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod] at hdim
  have hF : Module.finrank ℝ F = Module.finrank ℝ ℝ := by
    simpa [MorseModel] using Nat.add_left_cancel
      (show m + Module.finrank ℝ F = m + 1 by simpa [MorseModel] using hdim)
  exact he.isImmersionAtOfComplement_complement.trans_F
    (LinearEquiv.ofFinrankEq F ℝ hF).toContinuousLinearEquiv

def extendedChartOfMemMaximalAtlas {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Type*} [TopologicalSpace K] {N : Type*} [TopologicalSpace N]
    [ChartedSpace K N] (L : ModelWithCorners ℝ E K) [L.Boundaryless]
    (c : OpenPartialHomeomorph N K) (hc : c ∈ IsManifold.maximalAtlas L ∞ N) :
    PartialDiffeomorph L 𝓘(ℝ, E) N E ∞ where
  toPartialEquiv := c.extend L
  open_source := c.isOpen_extend_source
  open_target := c.isOpen_extend_target
  contMDiffOn_toFun := by
    simpa only [OpenPartialHomeomorph.extend_source] using c.contMDiffOn_extend hc
  contMDiffOn_invFun := by
    change ContMDiffOn 𝓘(ℝ, E) L ∞ (c.extend L).symm (c.extend L).target
    rw [OpenPartialHomeomorph.extend_target']
    exact contMDiffOn_extend_symm hc

variable [I.Boundaryless] [J.Boundaryless]

theorem exists_local_definingFunction {e : S → M}
    (he : Manifold.IsSmoothEmbedding I J ∞ e) (x : S) :
    ∃ U : Set M, IsOpen U ∧ e x ∈ U ∧
      ∃ f : M → ℝ, ContMDiffOn J 𝓘(ℝ, ℝ) ∞ f U ∧
        (∀ y ∈ U, f y = 0 ↔ y ∈ range e) ∧
        ∀ y ∈ U, mfderiv J 𝓘(ℝ, ℝ) f y ≠ 0 := by
  let h := isImmersionAtOfComplement_real I J (he.isImmersion.isImmersionAt x)
  let d := extendedChartOfMemMaximalAtlas I h.domChart h.domChart_mem_maximalAtlas
  let c := extendedChartOfMemMaximalAtlas J h.codChart h.codChart_mem_maximalAtlas
  let Φ := c.trans h.equiv.symm.toDiffeomorph.toPartialDiffeomorph
  have hsource : Φ.source = h.codChart.source := by
    change (c.source ∩ c ⁻¹' univ) = h.codChart.source
    rw [preimage_univ, inter_univ]
    exact h.codChart.extend_source
  have hdsource : d.source = h.domChart.source := h.domChart.extend_source
  have hΦ (s : S) (hs : s ∈ d.source) : Φ (e s) = (d s, 0) := by
    have hh := h.writtenInCharts (d.map_source hs)
    change (h.codChart.extend J) (e (d.symm (d s))) = h.equiv (d s, 0) at hh
    erw [d.left_inv hs] at hh
    change h.equiv.symm ((h.codChart.extend J) (e s)) = (d s, 0)
    rw [hh, h.equiv.symm_apply_apply]
  obtain ⟨A, hA, hApre⟩ := he.isEmbedding.isInducing.isOpen_iff.mp h.domChart.open_source
  let U := Φ.source ∩ A ∩ Φ ⁻¹' (Prod.fst ⁻¹' d.target)
  have hU : IsOpen U := by
    have ho := (continuousOn_open_iff Φ.open_source).mp Φ.contMDiffOn.continuousOn
      (Prod.fst ⁻¹' d.target) (continuous_fst.isOpen_preimage _ d.open_target)
    convert ho.inter hA using 1
    ext y
    change ((y ∈ Φ.source ∧ y ∈ A) ∧ (Φ y).1 ∈ d.target) ↔
      ((y ∈ Φ.source ∧ (Φ y).1 ∈ d.target) ∧ y ∈ A)
    tauto
  have hxD : x ∈ d.source := by rw [hdsource]; exact h.mem_domChart_source
  have hxΦ : e x ∈ Φ.source := by rw [hsource]; exact h.mem_codChart_source
  have hxA : e x ∈ A := by
    change x ∈ e ⁻¹' A
    rw [hApre]
    exact h.mem_domChart_source
  have hxU : e x ∈ U := ⟨⟨hxΦ, hxA⟩, by
    change (Φ (e x)).1 ∈ d.target
    rw [hΦ x hxD]
    exact d.map_source hxD⟩
  let f : M → ℝ := fun y => (Φ y).2
  have hf : ContMDiffOn J 𝓘(ℝ, ℝ) ∞ f Φ.source :=
    (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : MorseModel m × ℝ → ℝ)).contMDiff.comp_contMDiffOn
      Φ.contMDiffOn
  refine ⟨U, hU, hxU, f, hf.mono (fun _ hy => hy.1.1), ?_, ?_⟩
  · intro y hy
    constructor
    · intro hz
      let s := d.symm (Φ y).1
      have hs : s ∈ d.source := d.map_target hy.2
      have hse : e s ∈ Φ.source := by
        rw [hsource]
        exact h.source_subset_preimage_source (hdsource ▸ hs)
      refine ⟨s, Φ.toPartialEquiv.injOn hse hy.1.1 ?_⟩
      rw [hΦ s hs]
      apply Prod.ext
      · exact d.right_inv hy.2
      · exact hz.symm
    · rintro ⟨s, rfl⟩
      have hs : s ∈ d.source := by
        rw [hdsource, ← hApre]
        exact hy.1.2
      exact congrArg Prod.snd (hΦ s hs)
  · intro y hy hz
    have hxy : Φ y ∈ Φ.target := Φ.map_source hy.1.1
    have hEq : f ∘ Φ.symm =ᶠ[𝓝 (Φ y)] Prod.snd :=
      Filter.eventuallyEq_of_mem (Φ.open_target.mem_nhds hxy) (fun z hz =>
        congrArg Prod.snd (Φ.right_inv hz))
    have hd := mfderiv_comp (Φ y)
      (show MDifferentiableAt J 𝓘(ℝ, ℝ) f (Φ.symm (Φ y)) from by
        erw [Φ.left_inv hy.1.1]
        exact (hf.contMDiffAt (Φ.open_source.mem_nhds hy.1.1)).mdifferentiableAt (by simp))
      (Φ.symm.mdifferentiableAt (by simp) hxy)
    erw [Φ.left_inv hy.1.1, hz, ContinuousLinearMap.zero_comp,
      hEq.mfderiv_eq, mfderiv_eq_fderiv, hasFDerivAt_snd.fderiv] at hd
    have hh := congrArg (fun L : (MorseModel m × ℝ) →L[ℝ] ℝ => L (0, 1)) hd
    change (1 : ℝ) = 0 at hh
    norm_num at hh

end DifferentialGeometry.Manifold.EmbeddedHypersurface
