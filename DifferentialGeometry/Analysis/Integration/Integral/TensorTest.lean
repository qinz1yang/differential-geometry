import DifferentialGeometry.Analysis.Integration.Lp.Lipschitz
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Set
open scoped Manifold Topology
namespace DifferentialGeometry.Analysis

private theorem tsupport_tensor_mul_subset {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {τ : E → ℝ} {ψ : F → ℝ} :
    tsupport (fun p : E × F => τ p.1 * ψ p.2) ⊆ tsupport τ ×ˢ tsupport ψ := by
  apply closure_minimal
  · intro p hp
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hp
    exact ⟨subset_tsupport τ hp.1, subset_tsupport ψ hp.2⟩
  · exact (isClosed_tsupport τ).prod (isClosed_tsupport ψ)

private theorem hasCompactSupport_tensor_mul {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {τ : E → ℝ} {ψ : F → ℝ}
    (hτ : HasCompactSupport τ) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun p : E × F => τ p.1 * ψ p.2) :=
  (hτ.isCompact.prod hψ.isCompact).of_isClosed_subset (isClosed_tsupport _)
    tsupport_tensor_mul_subset

private theorem exists_contDiff_cutoff_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K Ω : Set E} (hK : IsCompact K) (hΩ : IsOpen Ω) (hs : K ⊆ Ω) :
    ∃ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ω ∧
      (∀ x ∈ K, f x = 1) ∧ ∀ x, f x ∈ Icc 0 1 := by
  obtain ⟨B, hB, hKB, hBΩ⟩ := exists_compact_between hK hΩ hs
  obtain ⟨f, hf1, hf0, hfr⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (n := (⊤ : ℕ∞)) (𝓘(ℝ, E)) hK.isClosed hKB
  have hfs : tsupport (f : E → ℝ) ⊆ B := by
    apply closure_minimal _ hB.isClosed
    intro x hx
    by_contra hxB
    exact hx (hf0 x hxB)
  exact ⟨f, f.contMDiff.contDiff, hB.of_isClosed_subset (isClosed_tsupport _) hfs,
    hfs.trans hBΩ, fun x hx => hf1.self_of_nhdsSet x hx, hfr⟩

private theorem exists_contDiff_tensor_majorant
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {φ : E × F → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U ×ˢ V) :
    ∃ (f : E → ℝ) (g : F → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ U ∧ (∀ x, 0 ≤ f x) ∧
      ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧ (∀ x, 0 ≤ g x) ∧
      ∀ z, ‖φ z‖ ≤ f z.1 * g z.2 := by
  obtain ⟨f, hf, hfc, hfs, hf1, hf01⟩ := exists_contDiff_cutoff_eq_one
    (hc.image continuous_fst) hU (by rintro x ⟨z, hz, rfl⟩; exact (hs hz).1)
  obtain ⟨g, hg, hgc, hgs, hg1, hg01⟩ := exists_contDiff_cutoff_eq_one
    (hc.image continuous_snd) hV (by rintro x ⟨z, hz, rfl⟩; exact (hs hz).2)
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn hφ.continuousOn
  refine ⟨fun x => max B 0 * f x, g, contDiff_const.mul hf, hfc.mul_left,
    tsupport_mul_subset_right.trans hfs, fun x => mul_nonneg (le_max_right B 0) (hf01 x).1,
    hg, hgc, hgs, fun x => (hg01 x).1, ?_⟩
  intro z
  dsimp only
  by_cases hz : z ∈ tsupport φ
  · rw [hf1 z.1 (mem_image_of_mem _ hz), hg1 z.2 (mem_image_of_mem _ hz), mul_one, mul_one]
    exact (hB z hz).trans (le_max_left B 0)
  · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
    exact mul_nonneg (mul_nonneg (le_max_right B 0) (hf01 z.1).1) (hg01 z.2).1

private theorem sum_integral_mul_fderiv_sub
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [Fintype ι]
    {μ : Measure E} {Ω : Set E} (hΩ : IsOpen Ω) {b : ι → E → ℝ}
    (hb : ∀ i, LocallyIntegrableOn (b i) Ω μ) (v : ι → E)
    {f g : E → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ω)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ω) :
    (∑ i, ∫ x, b i x * fderiv ℝ (fun y => f y - g y) x (v i) ∂μ) =
      (∑ i, ∫ x, b i x * fderiv ℝ f x (v i) ∂μ) -
        ∑ i, ∫ x, b i x * fderiv ℝ g x (v i) ∂μ := by
  simp_rw [fderiv_fun_sub (hf.differentiable one_ne_zero _) (hg.differentiable one_ne_zero _),
    sub_apply, mul_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_sub
    ((hb i).integrable_mul_fderiv_of_hasCompactSupport hΩ hf.locallyLipschitz.locallyLipschitzOn hfc hfs (v i))
    ((hb i).integrable_mul_fderiv_of_hasCompactSupport hΩ hg.locallyLipschitz.locallyLipschitzOn hgc hgs (v i))

theorem sum_integral_mul_fderiv_le_of_nonneg_test
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [Fintype ι]
    {μ : Measure E} {Ω : Set E} (hΩ : IsOpen Ω)
    {b : ι → E → ℝ} (hb : ∀ i, LocallyIntegrableOn (b i) Ω μ) (v : ι → E)
    (hpos : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∀ z, 0 ≤ φ z) →
      0 ≤ ∑ i, ∫ z, b i z * fderiv ℝ φ z (v i) ∂μ)
    {f g : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ Ω) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ Ω) (hfg : ∀ x, f x ≤ g x) :
    (∑ i, ∫ x, b i x * fderiv ℝ f x (v i) ∂μ) ≤
      ∑ i, ∫ x, b i x * fderiv ℝ g x (v i) ∂μ := by
  have h := hpos (fun x => g x - f x) (hg.sub hf) (hgc.sub hfc)
    ((tsupport_binop_subset (· - ·) (sub_self 0) g f).trans (union_subset hgs hfs))
    (fun x => sub_nonneg.mpr (hfg x))
  rw [sum_integral_mul_fderiv_sub hΩ hb v (hg.of_le (by simp)) hgc hgs
    (hf.of_le (by simp)) hfc hfs] at h
  exact sub_nonneg.mp h

theorem sum_integral_mul_fderiv_eq_zero_of_nonneg_and_tensor_test
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace (E × F)] [OpensMeasurableSpace (E × F)] [Fintype ι]
    {μ : Measure (E × F)} {J : Set E} {Ω : Set F} (hJ : IsOpen J) (hΩ : IsOpen Ω)
    {b : ι → E × F → ℝ} (hb : ∀ i, LocallyIntegrableOn (b i) (J ×ˢ Ω) μ) (v : ι → E × F)
    (hpos : ∀ φ : E × F → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ Ω → (∀ z, 0 ≤ φ z) →
      0 ≤ ∑ i, ∫ z, b i z * fderiv ℝ φ z (v i) ∂μ)
    (htensor : ∀ (f : E → ℝ) (g : F → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ J → (∀ t, 0 ≤ f t) →
      ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ Ω → (∀ x, 0 ≤ g x) →
      (∑ i, ∫ z, b i z * fderiv ℝ (fun y : E × F => f y.1 * g y.2) z (v i) ∂μ) = 0)
    {φ : E × F → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ J ×ˢ Ω) :
    (∑ i, ∫ z, b i z * fderiv ℝ φ z (v i) ∂μ) = 0 := by
  obtain ⟨f, g, hf, hfc, hfs, hf0, hg, hgc, hgs, hg0, hbound⟩ :=
    exists_contDiff_tensor_majorant hJ hΩ hφ.continuous hc hs
  let η : E × F → ℝ := fun z => f z.1 * g z.2
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := (hf.comp contDiff_fst).mul (hg.comp contDiff_snd)
  have hηc : HasCompactSupport η := hasCompactSupport_tensor_mul hfc hgc
  have hηs : tsupport η ⊆ J ×ˢ Ω := tsupport_tensor_mul_subset.trans (Set.prod_mono hfs hgs)
  have hzero := htensor f g hf hfc hfs hf0 hg hgc hgs hg0
  have hminus := sum_integral_mul_fderiv_le_of_nonneg_test (hJ.prod hΩ) hb v hpos
    hφ hc hs hη hηc hηs (fun z => (le_abs_self (φ z)).trans (hbound z))
  have hplus := sum_integral_mul_fderiv_le_of_nonneg_test (hJ.prod hΩ) hb v hpos
    hφ.neg hc.neg (by simpa only [tsupport_fun_neg] using hs) hη hηc hηs
    (fun z => (neg_le_abs (φ z)).trans (hbound z))
  have hneg : (∑ i, ∫ z, b i z * fderiv ℝ (fun y => -φ y) z (v i) ∂μ) =
      -(∑ i, ∫ z, b i z * fderiv ℝ φ z (v i) ∂μ) := by
    simp only [fderiv_fun_neg, neg_apply, mul_neg, integral_neg, Finset.sum_neg_distrib]
  change (∑ i, ∫ z, b i z * fderiv ℝ η z (v i) ∂μ) = 0 at hzero
  rw [hzero] at hminus hplus
  rw [hneg] at hplus
  linarith

end DifferentialGeometry.Analysis
