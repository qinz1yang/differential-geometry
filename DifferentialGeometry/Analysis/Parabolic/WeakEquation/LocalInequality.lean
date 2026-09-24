import DifferentialGeometry.Topology.PartitionOfUnity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const


noncomputable section

namespace DifferentialGeometry.Analysis

open Filter Set MeasureTheory
open scoped ContDiff Manifold Topology BigOperators

private theorem integrable_mul_of_locallyIntegrableOn
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X]
    {μ : Measure X} {Ω : Set X} {f g : X → ℝ}
    (hf : LocallyIntegrableOn f Ω μ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω) :
    Integrable (fun x => f x * g x) μ := by
  have hi : IntegrableOn (fun x => f x * g x) (tsupport g) μ :=
    (hf.integrableOn_compact_subset hgΩ hgc).mul_continuousOn hg.continuousOn hgc
  exact hi.integrable_of_forall_notMem_eq_zero fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} {Ω : Set X}
  {ι : Type*} [Fintype ι]

theorem integrable_mul_add_sum_mul_fderiv
    (B : X → ℝ) (A : ι → X → ℝ) (v : ι → X)
    (hB : LocallyIntegrableOn B Ω μ) (hA : ∀ i, LocallyIntegrableOn (A i) Ω μ)
    {φ : X → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) :
    Integrable (fun x => B x * φ x + ∑ i, A i x * fderiv ℝ φ x (v i)) μ := by
  apply (integrable_mul_of_locallyIntegrableOn hB hφ.continuous hφc hφΩ).add
  apply integrable_finsetSum
  intro i _
  exact integrable_mul_of_locallyIntegrableOn (hA i)
    ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (hφc.fderiv_apply ℝ (v i)) ((tsupport_fderiv_apply_subset ℝ (v i)).trans hφΩ)

theorem integral_mul_add_sum_mul_fderiv_nonneg_of_local
    [FiniteDimensional ℝ X]
    (B : X → ℝ) (A : ι → X → ℝ) (v : ι → X)
    (hB : LocallyIntegrableOn B Ω μ) (hA : ∀ i, LocallyIntegrableOn (A i) Ω μ)
    (hlocal : ∀ x ∈ Ω, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∀ ψ : X → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ V → (∀ y, 0 ≤ ψ y) →
        0 ≤ ∫ y, B y * ψ y + ∑ i, A i y * fderiv ℝ ψ y (v i) ∂μ)
    {φ : X → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) (hφn : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, B x * φ x + ∑ i, A i x * fderiv ℝ φ x (v i) ∂μ := by
  classical
  choose V hVo hxV hVΩ hV using fun x : Ω => hlocal x x.property
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, X)
    (isClosed_tsupport φ) V hVo (fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hφΩ hx⟩, hxV ⟨x, hφΩ hx⟩⟩)
  obtain ⟨s, hsum⟩ := ρ.toPartitionOfUnity.exists_finset_sum_smul_eq hφc
    (subset_tsupport φ)
  let ψ : Ω → X → ℝ := fun i x => ρ i x * φ x
  have hψ (i : Ω) : ContDiff ℝ 2 (ψ i) := by
    have hi : ContDiff ℝ 2 (ρ i) := by
      exact contMDiff_iff_contDiff.mp
        ((ρ i).contMDiff.of_le (by decide))
    exact hi.mul hφ
  have hψc (i : Ω) : HasCompactSupport (ψ i) := hφc.mul_left
  have hψV (i : Ω) : tsupport (ψ i) ⊆ V i :=
    tsupport_mul_subset_left.trans (hρ i)
  have hψΩ (i : Ω) : tsupport (ψ i) ⊆ Ω := (hψV i).trans (hVΩ i)
  have hψn (i : Ω) (x : X) : 0 ≤ ψ i x := mul_nonneg (ρ.nonneg i x) (hφn x)
  have hψint (i : Ω) :
      Integrable (fun x => B x * ψ i x + ∑ j, A j x * fderiv ℝ (ψ i) x (v j)) μ :=
    integrable_mul_add_sum_mul_fderiv B A v hB hA
      ((hψ i).of_le (by norm_num)) (hψc i) (hψΩ i)
  have heq : φ = ∑ i ∈ s, ψ i := by
    funext x
    have h := (hsum x).symm
    change φ x = ∑ i ∈ s, ρ i x * φ x at h
    simpa only [Finset.sum_apply, ψ] using h
  have hder (x w : X) : fderiv ℝ φ x w = ∑ i ∈ s, fderiv ℝ (ψ i) x w := by
    conv_lhs => rw [heq]
    rw [fderiv_sum (fun i _ => (hψ i).differentiable (by norm_num) x)]
    simp only [_root_.sum_apply]
  have hfun : (fun x => B x * φ x + ∑ j, A j x * fderiv ℝ φ x (v j)) =
      fun x => ∑ i ∈ s, (B x * ψ i x + ∑ j, A j x * fderiv ℝ (ψ i) x (v j)) := by
    funext x
    have hval : φ x = ∑ i ∈ s, ψ i x := by
      simpa only [Finset.sum_apply] using congrFun heq x
    simp_rw [hval, hder, Finset.mul_sum]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
  rw [hfun, integral_finsetSum s (fun i _ => hψint i)]
  exact Finset.sum_nonneg fun i _ => hV i (ψ i) (hψ i) (hψc i) (hψV i) (hψn i)

end DifferentialGeometry.Analysis

end
