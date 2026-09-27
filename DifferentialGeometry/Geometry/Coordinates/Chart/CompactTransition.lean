import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Mathlib.Analysis.Normed.Group.Bounded

section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem exists_compactly_supported_chart_transition
    {m : ℕ} (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (ΦA ΦB : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    {K : Set M} (hK : IsCompact K) (hKA : K ⊆ ΦA.target) (hKB : K ⊆ ΦB.target) :
    ∃ R : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      ContDiff ℝ ∞ R ∧ HasCompactSupport R ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖fderiv ℝ R y‖ ≤ C) ∧
      ∀ p ∈ K,
        R =ᶠ[𝓝 (L (ΦA.symm p))]
          (fun y => L (ΦB.symm (ΦA (L.symm y)))) ∧
        R (L (ΦA.symm p)) = L (ΦB.symm p) ∧
        fderiv ℝ R (L (ΦA.symm p)) =
          fderiv ℝ (fun y => L (ΦB.symm (ΦA (L.symm y)))) (L (ΦA.symm p)) := by
  let Ψ := ΦA.trans ΦB.symm
  let U : Set (EuclideanSpace ℝ (Fin m)) := L.symm ⁻¹' Ψ.source
  let T : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun y => L (ΦB.symm (ΦA (L.symm y)))
  let KA : Set (EuclideanSpace ℝ (Fin m)) := (fun p => L (ΦA.symm p)) '' K
  have hU : IsOpen U := Ψ.open_source.preimage L.symm.continuous
  have hKAcompact : IsCompact KA := hK.image_of_continuousOn
    (L.continuous.comp_continuousOn (ΦA.contMDiffOn_invFun.continuousOn.mono hKA))
  have hKAU : KA ⊆ U := by
    rintro y ⟨p, hp, rfl⟩
    change L.symm (L (ΦA.symm p)) ∈ ΦA.source ∩ ΦA ⁻¹' ΦB.target
    rw [L.symm_apply_apply]
    exact ⟨ΦA.toOpenPartialHomeomorph.map_target (hKA hp), by
      change ΦA (ΦA.symm p) ∈ ΦB.target
      rw [show ΦA (ΦA.symm p) = p from ΦA.toOpenPartialHomeomorph.right_inv (hKA hp)]
      exact hKB hp⟩
  have hΨ : ContDiffOn ℝ ∞ (fun z : E => ΦB.symm (ΦA z)) Ψ.source :=
    Ψ.contMDiffOn_toFun.contDiffOn
  have hT : ContDiffOn ℝ ∞ T U :=
    L.contDiff.comp_contDiffOn (hΨ.comp L.symm.contDiff.contDiffOn (fun _ hy => hy))
  obtain ⟨δ, η, hδ, _, hη, hηc, _, hηone, hηU⟩ :=
    Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood hKAcompact hU hKAU
  let R : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) := fun y => η y • T y
  have hR : ContDiff ℝ ∞ R := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport η
    · exact (hη.contDiffAt.smul (hT.contDiffAt (hU.mem_nhds (hηU hy))))
    · apply (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin m)))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      change η z • T z = 0
      simp only [hz, Pi.zero_apply, zero_smul]
  have hRc : HasCompactSupport R :=
    hηc.mono (Function.support_smul_subset_left η T)
  obtain ⟨C, hC⟩ := (hR.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hRc.fderiv ℝ)
  refine ⟨R, hR, hRc, ⟨max C 0, le_max_right _ _,
    fun y => (hC y).trans (le_max_left _ _)⟩, ?_⟩
  intro p hp
  have hpKA : L (ΦA.symm p) ∈ KA := ⟨p, hp, rfl⟩
  have heq : R =ᶠ[𝓝 (L (ΦA.symm p))] T := by
    filter_upwards [Metric.isOpen_thickening.mem_nhds
      (Metric.self_subset_thickening hδ KA hpKA)] with y hy
    change η y • T y = T y
    rw [hηone y (Metric.thickening_subset_cthickening δ KA hy), one_smul]
  refine ⟨heq, ?_, heq.fderiv_eq⟩
  rw [heq.eq_of_nhds]
  change L (ΦB.symm (ΦA (L.symm (L (ΦA.symm p))))) = L (ΦB.symm p)
  rw [L.symm_apply_apply, show ΦA (ΦA.symm p) = p from
    ΦA.toOpenPartialHomeomorph.right_inv (hKA hp)]

variable [IsManifold I ∞ M]

theorem pullbackMetricCoefficients_chart_transition
    {m : ℕ} (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (g : SmoothRiemannianMetric I M)
    (ΦA ΦB : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    {p : M} (hpA : p ∈ ΦA.target) (hpB : p ∈ ΦB.target)
    (z w : EuclideanSpace ℝ (Fin m)) :
    let T := fun y => L (ΦB.symm (ΦA (L.symm y)))
    pullbackMetricCoefficients g ΦB (ΦB.symm p)
      (L.symm (fderiv ℝ T (L (ΦA.symm p)) z))
      (L.symm (fderiv ℝ T (L (ΦA.symm p)) w)) =
        pullbackMetricCoefficients g ΦA (ΦA.symm p) (L.symm z) (L.symm w) := by
  let a := ΦA.symm p
  have ha : a ∈ ΦA.source := ΦA.toOpenPartialHomeomorph.map_target hpA
  have hap : ΦA a = p := ΦA.toOpenPartialHomeomorph.right_inv hpA
  have hA : MDifferentiableAt 𝓘(ℝ, E) I ΦA a := ΦA.mdifferentiableAt (by simp) ha
  have hB : MDifferentiableAt I 𝓘(ℝ, E) ΦB.symm (ΦA a) := by
    apply ΦB.symm.mdifferentiableAt (by simp)
    change ΦA a ∈ ΦB.target
    rwa [hap]
  have hS : DifferentiableAt ℝ (fun y => ΦB.symm (ΦA y)) a :=
    (hB.comp a hA).differentiableAt
  have hsA : HasFDerivAt (fun y => ΦB.symm (ΦA y))
      (fderiv ℝ (fun y => ΦB.symm (ΦA y)) a) (L.symm (L a)) := by
    simpa only [L.symm_apply_apply] using hS.hasFDerivAt
  have hcomp := L.hasFDerivAt.comp (L a) (hsA.comp (L a) L.symm.hasFDerivAt)
  have hlin : fderiv ℝ (fun y => L (ΦB.symm (ΦA (L.symm y)))) (L (ΦA.symm p)) =
      L.toContinuousLinearMap.comp ((fderiv ℝ (fun y => ΦB.symm (ΦA y)) a).comp
        L.symm.toContinuousLinearMap) := by
    simpa only [Function.comp_def, a] using hcomp.fderiv
  have hmetric := pullbackMetricCoefficients_fderiv_symm g ΦB hA
    (by rwa [hap]) (L.symm z) (L.symm w)
  change pullbackMetricCoefficients g ΦB (ΦB.symm (ΦA a))
      ((fderiv ℝ (fun y => ΦB.symm (ΦA y)) a) (L.symm z))
      ((fderiv ℝ (fun y => ΦB.symm (ΦA y)) a) (L.symm w)) =
        pullbackMetricCoefficients g ΦA a (L.symm z) (L.symm w) at hmetric
  rw [hap] at hmetric
  dsimp only
  rw [hlin]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    L.symm_apply_apply] using hmetric

theorem exists_compactly_supported_chart_transition_pullback_metric
    {m : ℕ} (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (g : SmoothRiemannianMetric I M)
    (ΦA ΦB : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    {K : Set M} (hK : IsCompact K) (hKA : K ⊆ ΦA.target) (hKB : K ⊆ ΦB.target) :
    ∃ R : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      ContDiff ℝ ∞ R ∧ HasCompactSupport R ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖fderiv ℝ R y‖ ≤ C) ∧
      ∀ p ∈ K, R (L (ΦA.symm p)) = L (ΦB.symm p) ∧
        ∀ z w : EuclideanSpace ℝ (Fin m),
          pullbackMetricCoefficients g ΦB (ΦB.symm p)
            (L.symm (fderiv ℝ R (L (ΦA.symm p)) z))
            (L.symm (fderiv ℝ R (L (ΦA.symm p)) w)) =
              pullbackMetricCoefficients g ΦA (ΦA.symm p) (L.symm z) (L.symm w) := by
  obtain ⟨R, hR, hRc, hC, heq⟩ :=
    exists_compactly_supported_chart_transition L ΦA ΦB hK hKA hKB
  refine ⟨R, hR, hRc, hC, fun p hp => ⟨(heq p hp).2.1, fun z w => ?_⟩⟩
  rw [(heq p hp).2.2]
  exact pullbackMetricCoefficients_chart_transition L g ΦA ΦB (hKA hp) (hKB hp) z w

end DifferentialGeometry.Geometry

end

end
