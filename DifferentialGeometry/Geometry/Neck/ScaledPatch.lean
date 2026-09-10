import DifferentialGeometry.Geometry.Neck.BufferedPatch
import DifferentialGeometry.Geometry.Neck.CompactBand
import DifferentialGeometry.Analysis.ODE.Flow.Planar.LineCoverScaleEstimate

noncomputable section
open Set Bundle Topology
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open Poincare.Geometry.Affine Poincare.Analysis

namespace Poincare.Geometry.Neck

theorem exists_regular_patch_of_scaled_neck_bands_on_intersections
    {E H W F H' M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M] (m : ℝ) (hm : 0 < m) (Cₒ : ℝ) (hCₒ : 0 < Cₒ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (n : ℕ) (ι : W → M), ContMDiff I J ∞ ι →
      (∀ w, Function.Surjective (mfderiv I J ι w)) →
      ∀ (g : SmoothRiemannianMetric J M) (C : Fin (n + 1) → cylindricalChart J (M := M))
        (U : ∀ i, Set (C i).domain), (∀ i, IsOpen (U i)) →
      ∀ (ε : ℝ), 0 ≤ ε → ε < ε₀ →
      (∀ i, (C i).metricCloseOn g ε (U i)) →
      ∀ (s c : Fin n → ℝ), (∀ j, s j = 1 ∨ s j = -1) →
      (∀ j : Fin n, |(C j.castSucc).scale / (C j.succ).scale - 1| ≤ Cₒ * ε) →
      let a := finiteLineAffineAlignment s c
      let v : Fin (n + 1) → W → ℝ := fun i w ↦ (a i).1 * (C i).axial (ι w) + (a i).2
      let V : Fin (n + 1) → Set W := fun i ↦ ι ⁻¹' (C i).region (U i)
      ∀ (l r η : Fin (n + 1) → ℝ),
      (∀ i, m * (Real.sqrt (C i).scale)⁻¹ ≤ η i) →
      (∀ i, (univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ×ˢ
        ((fun t : ℝ ↦ (a i).1 * (Real.sqrt (C i).scale)⁻¹ * t + (a i).2) ⁻¹' Icc (l i) (r i)) ⊆
          Subtype.val '' U i) →
      (∀ w : W, ∃ i, w ∈ V i ∧ v i w ∈ Icc (l i + 2 * η i) (r i - 2 * η i)) →
      let K := fun i ↦ closure (V i ∩ v i ⁻¹' Icc (l i) (r i))
      (∀ w i, w ∈ K i → ∀ j, w ∈ K j → i.val ≤ j.val + 1) →
      (∀ j : Fin n, ∀ w ∈ K j.castSucc, w ∈ K j.succ →
        |(C j.succ).axial (ι w) - (s j * (C j.castSucc).axial (ι w) + c j)| ≤ Cₒ * ε / Real.sqrt (C j.castSucc).scale) →
      (∀ j : Fin n, ∀ w ∈ K j.castSucc, w ∈ K j.succ →
        Real.sqrt (g.inner (ι w) (gradFun g (C j.succ).axial (ι w) - s j • gradFun g (C j.castSucc).axial (ι w))
          (gradFun g (C j.succ).axial (ι w) - s j • gradFun g (C j.castSucc).axial (ι w))) ≤ Cₒ * ε) →
      ∃ (f : BumpCovering (Fin (n + 1)) W) (hf : ∀ i, ContMDiff I 𝓘(ℝ) ∞ (f i)),
        (∀ i, tsupport (f i) ⊆ K i) ∧
        (∀ i, ∀ w ∈ V i, v i w ∈ Icc (l i + η i) (r i - η i) → f i w = 1) ∧
        let u := fun w ↦ ∑ i, f.toSmoothPartitionOfUnity hf i w * v i w
        ContMDiff I 𝓘(ℝ) ∞ u ∧ ∀ w, mvfderiv I u w ≠ 0 := by
  obtain ⟨A, hA, hpatch⟩ := exists_uniform_regular_patch_of_buffered_neck_coordinates_on_intersections
    (I := I) (J := J) (W := W) (M := M)
  let ε₀ := min (1 / 200000 : ℝ) (min (1 / (2 * Cₒ)) (m / (24 * A * Cₒ)))
  have hε₀ : 0 < ε₀ := lt_min (by norm_num)
    (lt_min (one_div_pos.mpr (mul_pos (by norm_num) hCₒ))
      (div_pos hm (mul_pos (mul_pos (by norm_num) hA) hCₒ)))
  refine ⟨ε₀, hε₀, ?_⟩
  intro n ι hι hιsurj g C U hU ε hεnonneg hε hmetric s c hs hratio a v V l r η hwidth hband hcover K hline hvalue hoverlap
  have heps : ε < 1 / 200000 := hε.trans_le (min_le_left _ _)
  have heps' : ε < 1 / (2 * Cₒ) := hε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heps'' : ε < m / (24 * A * Cₒ) := hε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hmain : 92354 * ε < 1 / 2 := by linarith only [heps]
  have herr : Cₒ * ε < 1 / 2 := by
    have h := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hCₒ)).mp heps'
    nlinarith only [h]
  have hsmall : 24 * A * (Cₒ * ε) < m := by
    have h := (lt_div_iff₀ (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 24) hA) hCₒ)).mp heps''
    nlinarith only [h]
  have hη (i) : 0 < η i :=
    (mul_pos hm (inv_pos.mpr (Real.sqrt_pos.mpr (C i).scale_pos))).trans_le (hwidth i)
  have hbuffer (i) : K i ⊆ V i := by
    have hτ : (a i).1 ≠ 0 := by
      rcases finiteLineAffineAlignment_sign s c hs i with h | h <;> rw [h] <;> norm_num
    exact (C i).closure_preimage_affine_axial_band_subset_region (U i)
      (a i).1 (a i).2 (l i) (r i) hτ (hband i) ι hι.continuous
  have hcover' (w : W) : ∃ i, w ∈ V i ∧ v i w ∈ Ioo (l i + η i) (r i - η i) := by
    obtain ⟨i, hi, hv⟩ := hcover w
    refine ⟨i, hi, ?_⟩
    constructor <;> linarith only [hv.1, hv.2, hη i]
  let e : Fin n → ℝ := fun j ↦ Cₒ * ε / Real.sqrt (C j.castSucc).scale
  obtain ⟨Δ, hΔ, he, hbound⟩ := exists_overlap_error_bound_of_line_cover_with_margin m hm K hline
    (fun i ↦ (C i).scale) η (fun i ↦ (C i).scale_pos) hwidth e A (Cₒ * ε) (92354 * ε)
    hA.le (mul_nonneg hCₒ.le hεnonneg) (mul_nonneg (by norm_num) hεnonneg)
    hmain.le hsmall (fun j ↦ (hratio j).trans herr.le) (fun _ _ _ _ ↦ le_rfl)
  exact hpatch n ι hι hιsurj g C U hU ε (Cₒ * ε) heps
    (by linarith only [hmain, herr]) hmetric s c e hs
    l r η hη hbuffer hcover' hline hvalue hoverlap Δ hΔ he hbound

theorem exists_regular_patch_of_scaled_neck_bands_with_margin
    {E H W F H' M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M] (m : ℝ) (hm : 0 < m) (Cₒ : ℝ) (hCₒ : 0 < Cₒ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (n : ℕ) (ι : W → M), ContMDiff I J ∞ ι →
      (∀ w, Function.Surjective (mfderiv I J ι w)) →
      ∀ (g : SmoothRiemannianMetric J M) (C : Fin (n + 1) → cylindricalChart J (M := M))
        (U : ∀ i, Set (C i).domain), (∀ i, IsOpen (U i)) →
      ∀ (ε : ℝ), 0 ≤ ε → ε < ε₀ →
      (∀ i, (C i).metricCloseOn g ε (U i)) →
      ∀ (s c : Fin n → ℝ), (∀ j, s j = 1 ∨ s j = -1) →
      (∀ j : Fin n, |(C j.castSucc).scale / (C j.succ).scale - 1| ≤ Cₒ * ε) →
      (∀ j : Fin n, ∀ x ∈ (C j.castSucc).region (U j.castSucc), x ∈ (C j.succ).region (U j.succ) →
        |(C j.succ).axial x - (s j * (C j.castSucc).axial x + c j)| ≤ Cₒ * ε / Real.sqrt (C j.castSucc).scale) →
      (∀ j : Fin n, ∀ x ∈ (C j.castSucc).region (U j.castSucc), x ∈ (C j.succ).region (U j.succ) →
        Real.sqrt (g.inner x (gradFun g (C j.succ).axial x - s j • gradFun g (C j.castSucc).axial x)
          (gradFun g (C j.succ).axial x - s j • gradFun g (C j.castSucc).axial x)) ≤ Cₒ * ε) →
      let a := finiteLineAffineAlignment s c
      let v : Fin (n + 1) → W → ℝ := fun i w ↦ (a i).1 * (C i).axial (ι w) + (a i).2
      let V : Fin (n + 1) → Set W := fun i ↦ ι ⁻¹' (C i).region (U i)
      ∀ (l r η : Fin (n + 1) → ℝ),
      (∀ i, m * (Real.sqrt (C i).scale)⁻¹ ≤ η i) →
      (∀ i, (univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ×ˢ
        ((fun t : ℝ ↦ (a i).1 * (Real.sqrt (C i).scale)⁻¹ * t + (a i).2) ⁻¹' Icc (l i) (r i)) ⊆
          Subtype.val '' U i) →
      (∀ w : W, ∃ i, w ∈ V i ∧ v i w ∈ Icc (l i + 2 * η i) (r i - 2 * η i)) →
      let K := fun i ↦ closure (V i ∩ v i ⁻¹' Icc (l i) (r i))
      (∀ w i, w ∈ K i → ∀ j, w ∈ K j → i.val ≤ j.val + 1) →
      ∃ (f : BumpCovering (Fin (n + 1)) W) (hf : ∀ i, ContMDiff I 𝓘(ℝ) ∞ (f i)),
        (∀ i, tsupport (f i) ⊆ K i) ∧
        (∀ i, ∀ w ∈ V i, v i w ∈ Icc (l i + η i) (r i - η i) → f i w = 1) ∧
        let u := fun w ↦ ∑ i, f.toSmoothPartitionOfUnity hf i w * v i w
        ContMDiff I 𝓘(ℝ) ∞ u ∧ ∀ w, mvfderiv I u w ≠ 0 := by
  obtain ⟨ε₀, hε₀, hpatch⟩ := exists_regular_patch_of_scaled_neck_bands_on_intersections
    (I := I) (J := J) (W := W) (M := M) m hm Cₒ hCₒ
  refine ⟨ε₀, hε₀, ?_⟩
  intro n ι hι hιsurj g C U hU ε hεnonneg hε hmetric s c hs hratio hvalue hoverlap a v V
    l r η hwidth hband hcover K hline
  have hbuffer (i) : K i ⊆ V i := by
    have hτ : (a i).1 ≠ 0 := by
      rcases finiteLineAffineAlignment_sign s c hs i with h | h <;> rw [h] <;> norm_num
    exact (C i).closure_preimage_affine_axial_band_subset_region (U i)
      (a i).1 (a i).2 (l i) (r i) hτ (hband i) ι hι.continuous
  exact hpatch n ι hι hιsurj g C U hU ε hεnonneg hε hmetric s c hs hratio
    l r η hwidth hband hcover hline
    (fun j w hi hj ↦ hvalue j (ι w) (hbuffer _ hi) (hbuffer _ hj))
    (fun j w hi hj ↦ hoverlap j (ι w) (hbuffer _ hi) (hbuffer _ hj))

theorem exists_regular_patch_of_scaled_neck_bands
    {E H W F H' M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M] (Cₒ : ℝ) (hCₒ : 0 < Cₒ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (n : ℕ) (ι : W → M), ContMDiff I J ∞ ι →
      (∀ w, Function.Surjective (mfderiv I J ι w)) →
      ∀ (g : SmoothRiemannianMetric J M) (C : Fin (n + 1) → cylindricalChart J (M := M))
        (U : ∀ i, Set (C i).domain), (∀ i, IsOpen (U i)) →
      ∀ (ε : ℝ), 0 ≤ ε → ε < ε₀ →
      (∀ i, (C i).metricCloseOn g ε (U i)) →
      ∀ (s c : Fin n → ℝ), (∀ j, s j = 1 ∨ s j = -1) →
      (∀ j : Fin n, |(C j.castSucc).scale / (C j.succ).scale - 1| ≤ Cₒ * ε) →
      (∀ j : Fin n, ∀ x ∈ (C j.castSucc).region (U j.castSucc), x ∈ (C j.succ).region (U j.succ) →
        |(C j.succ).axial x - (s j * (C j.castSucc).axial x + c j)| ≤ Cₒ * ε / Real.sqrt (C j.castSucc).scale) →
      (∀ j : Fin n, ∀ x ∈ (C j.castSucc).region (U j.castSucc), x ∈ (C j.succ).region (U j.succ) →
        Real.sqrt (g.inner x (gradFun g (C j.succ).axial x - s j • gradFun g (C j.castSucc).axial x)
          (gradFun g (C j.succ).axial x - s j • gradFun g (C j.castSucc).axial x)) ≤ Cₒ * ε) →
      let a := finiteLineAffineAlignment s c
      let v : Fin (n + 1) → W → ℝ := fun i w ↦ (a i).1 * (C i).axial (ι w) + (a i).2
      let V : Fin (n + 1) → Set W := fun i ↦ ι ⁻¹' (C i).region (U i)
      ∀ (l r η : Fin (n + 1) → ℝ),
      (∀ i, (Real.sqrt (C i).scale)⁻¹ ≤ η i) →
      (∀ i, (univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ×ˢ
        ((fun t : ℝ ↦ (a i).1 * (Real.sqrt (C i).scale)⁻¹ * t + (a i).2) ⁻¹' Icc (l i) (r i)) ⊆
          Subtype.val '' U i) →
      (∀ w : W, ∃ i, w ∈ V i ∧ v i w ∈ Icc (l i + 2 * η i) (r i - 2 * η i)) →
      let K := fun i ↦ closure (V i ∩ v i ⁻¹' Icc (l i) (r i))
      (∀ w i, w ∈ K i → ∀ j, w ∈ K j → i.val ≤ j.val + 1) →
      ∃ (f : BumpCovering (Fin (n + 1)) W) (hf : ∀ i, ContMDiff I 𝓘(ℝ) ∞ (f i)),
        (∀ i, tsupport (f i) ⊆ K i) ∧
        (∀ i, ∀ w ∈ V i, v i w ∈ Icc (l i + η i) (r i - η i) → f i w = 1) ∧
        let u := fun w ↦ ∑ i, f.toSmoothPartitionOfUnity hf i w * v i w
        ContMDiff I 𝓘(ℝ) ∞ u ∧ ∀ w, mvfderiv I u w ≠ 0 := by
  simpa only [one_mul] using
    exists_regular_patch_of_scaled_neck_bands_with_margin
      (I := I) (J := J) (W := W) (M := M) 1 zero_lt_one Cₒ hCₒ

end Poincare.Geometry.Neck
