import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.Tangent

open Set DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace Poincare.Manifold.EmbeddedHypersurface

variable {m : ℕ} {H G S M : Type*}
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  (I : ModelWithCorners ℝ (MorseModel m) H)
  (J : ModelWithCorners ℝ (MorseModel (m + 1)) G)
  [I.Boundaryless] [J.Boundaryless] [IsManifold J ∞ M]

theorem exists_defining_neighborhood_of_regular_vanishing {e : S → M} {x : S}
    (he : Manifold.IsImmersionAt I J ∞ e x) {f : M → ℝ}
    (hf : ContMDiff J 𝓘(ℝ, ℝ) ∞ f) (hz : ∀ s, f (e s) = 0)
    (hr : mfderiv J 𝓘(ℝ, ℝ) f (e x) ≠ 0) :
    ∃ U : Set M, IsOpen U ∧ e x ∈ U ∧ ∀ y ∈ U, f y = 0 ↔ y ∈ range e := by
  obtain ⟨Φ, hxΦ, _, hcoord⟩ := RegularLevel.exists_coordinates_of_contMDiffOn J
    isOpen_univ hf.contMDiffOn (mem_univ (e x)) hr 0
  let d := extendedChartOfMemMaximalAtlas I he.domChart he.domChart_mem_maximalAtlas
  have hxD : x ∈ d.source := by
    change x ∈ (he.domChart.extend I).source
    rw [OpenPartialHomeomorph.extend_source]
    exact he.mem_domChart_source
  let z₀ := d x
  have hzD : z₀ ∈ d.target := d.map_source hxD
  have hdx : d.symm z₀ = x := d.left_inv hxD
  let H₀ : MorseModel m → MorseModel (m + 1) := Φ ∘ e ∘ d.symm
  let q : MorseModel m → MorseModel m := levelSetSplitFst m ∘ H₀
  let B : MorseModel m →L[ℝ] MorseModel (m + 1) :=
    (levelSetSplit m).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ (MorseModel m) ℝ)
  have hd : ContMDiffAt 𝓘(ℝ, MorseModel m) I ∞ d.symm z₀ :=
    d.symm.contMDiffOn.contMDiffAt (d.open_target.mem_nhds hzD)
  have he' : ContMDiffAt I J ∞ e (d.symm z₀) := by rw [hdx]; exact he.contMDiffAt
  have hΦ' : ContMDiffAt J 𝓘(ℝ, MorseModel (m + 1)) ∞ Φ (e (d.symm z₀)) := by
    rw [hdx]
    exact Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds hxΦ)
  have hH : ContDiffAt ℝ ∞ H₀ z₀ :=
    contMDiffAt_iff_contDiffAt.mp (hΦ'.comp z₀ (he'.comp z₀ hd))
  have hq : ContDiffAt ℝ ∞ q z₀ := (levelSetSplitFst m).contDiff.contDiffAt.comp z₀ hH
  have hWnhds : d.target ∩ (e ∘ d.symm) ⁻¹' Φ.source ∈ 𝓝 z₀ :=
    Filter.inter_mem (d.open_target.mem_nhds hzD)
      ((he'.continuousAt.comp hd.continuousAt).preimage_mem_nhds
        (Φ.open_source.mem_nhds (by change e (d.symm z₀) ∈ Φ.source; rw [hdx]; exact hxΦ)))
  obtain ⟨W, hWsub, hW, hzW⟩ := mem_nhds_iff.mp hWnhds
  have hflat (z : MorseModel m) (hzW' : z ∈ W) : H₀ z = B (q z) := by
    have hlast : H₀ z (Fin.last m) = 0 := by
      have hh := hcoord (e (d.symm z)) (hWsub hzW').2
      change Φ (e (d.symm z)) (Fin.last m) = 0
      rw [hz] at hh
      exact hh.trans (sub_self 0)
    have hh := (levelSetSplit m).apply_symm_apply (H₀ z)
    change levelSetSplit m (levelSetSplitFst m (H₀ z), H₀ z (Fin.last m)) = H₀ z at hh
    rw [hlast] at hh
    exact hh.symm
  have hEq : H₀ =ᶠ[𝓝 z₀] B ∘ q :=
    Filter.eventuallyEq_of_mem (hW.mem_nhds hzW) hflat
  have hD : fderiv ℝ H₀ z₀ = B.comp (fderiv ℝ q z₀) := by
    rw [hEq.fderiv_eq, fderiv_comp z₀ B.differentiableAt (hq.differentiableAt (by simp))]
    rw [B.fderiv]
  have hHinj : Function.Injective (fderiv ℝ H₀ z₀) := by
    have hdc := mfderiv_comp z₀ (he'.mdifferentiableAt (by simp)) (hd.mdifferentiableAt (by simp))
    have hhc := mfderiv_comp z₀ (hΦ'.mdifferentiableAt (by simp))
      ((he'.comp z₀ hd).mdifferentiableAt (by simp))
    change mfderiv 𝓘(ℝ, MorseModel m) 𝓘(ℝ, MorseModel (m + 1)) H₀ z₀ = _ at hhc
    erw [mfderiv_eq_fderiv, hdc] at hhc
    rw [hhc]
    have hxΦ' : e (d.symm z₀) ∈ Φ.source := by erw [hdx]; exact hxΦ
    have hei : Function.Injective (mfderiv I J e (d.symm z₀)) := by
      erw [hdx]
      exact injective_mfderiv_of_isImmersionAt I J he
    exact ((Φ.isLocalDiffeomorphAt J 𝓘(ℝ, MorseModel (m + 1)) ∞ hxΦ').mfderivToContinuousLinearEquiv (by simp)).injective.comp
      (hei.comp
        ((d.symm.isLocalDiffeomorphAt 𝓘(ℝ, MorseModel m) I ∞ hzD).mfderivToContinuousLinearEquiv (by simp)).injective)
  have hqinj : Function.Injective (fderiv ℝ q z₀) := by
    intro v w hvw
    apply hHinj
    rw [hD]
    exact congrArg B hvw
  let L : MorseModel m ≃L[ℝ] MorseModel m :=
    (LinearEquiv.ofBijective (fderiv ℝ q z₀).toLinearMap
      ⟨hqinj, (LinearMap.injective_iff_surjective).mp hqinj⟩).toContinuousLinearEquiv
  have hqD : HasFDerivAt q (L : MorseModel m →L[ℝ] MorseModel m) z₀ :=
    (hq.differentiableAt (by simp)).hasFDerivAt
  let ψ₀ := hq.toOpenPartialHomeomorph q hqD (by simp)
  let ψ := ψ₀.restrOpen W hW
  have hzψ : z₀ ∈ ψ.source := ⟨hq.mem_toOpenPartialHomeomorph_source hqD (by simp), hzW⟩
  let U := Φ.source ∩ Φ ⁻¹' ((levelSetSplitFst m) ⁻¹' ψ.target)
  have hU : IsOpen U := Φ.contMDiffOn.continuousOn.isOpen_inter_preimage Φ.open_source
    ((levelSetSplitFst m).continuous.isOpen_preimage _ ψ.open_target)
  have hxU : e x ∈ U := by
    refine ⟨hxΦ, ?_⟩
    have hh := ψ.map_source hzψ
    change q z₀ ∈ ψ.target at hh
    change levelSetSplitFst m (Φ (e x)) ∈ ψ.target
    simpa only [q, H₀, Function.comp_apply, hdx] using hh
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy
  constructor
  · intro hfy
    let z := ψ.symm (levelSetSplitFst m (Φ y))
    have hzψ' : z ∈ ψ.source := ψ.map_target hy.2
    have hzW' : z ∈ W := hzψ'.2
    have hqz : q z = levelSetSplitFst m (Φ y) := ψ.right_inv hy.2
    have hyflat : Φ y = B (levelSetSplitFst m (Φ y)) := by
      have hlast : Φ y (Fin.last m) = 0 := by
        rw [hcoord y hy.1, hfy, sub_self]
      have hh := (levelSetSplit m).apply_symm_apply (Φ y)
      change levelSetSplit m (levelSetSplitFst m (Φ y), Φ y (Fin.last m)) = Φ y at hh
      rw [hlast] at hh
      exact hh.symm
    refine ⟨d.symm z, Φ.toPartialEquiv.injOn (hWsub hzW').2 hy.1 ?_⟩
    change H₀ z = Φ y
    rw [hflat z hzW', hqz, ← hyflat]
  · rintro ⟨s, rfl⟩
    exact hz s

end Poincare.Manifold.EmbeddedHypersurface
