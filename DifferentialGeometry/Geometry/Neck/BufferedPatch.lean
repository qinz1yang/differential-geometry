import DifferentialGeometry.Geometry.Neck.FiniteAlignment
import DifferentialGeometry.Topology.Manifold.LinePatch
import DifferentialGeometry.Topology.Manifold.BufferedBumpCovering

noncomputable section
open Set Bundle Filter Topology
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open Poincare.Geometry.Affine Poincare.Topology.Manifold

namespace Poincare.Geometry.Neck

theorem exists_uniform_regular_patch_of_buffered_neck_coordinates_on_intersections
    {E H W F H' M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M] :
    ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ) (ι : W → M), ContMDiff I J ∞ ι →
    (∀ w, Function.Surjective (mfderiv I J ι w)) →
    ∀ (g : SmoothRiemannianMetric J M) (C : Fin (n + 1) → cylindricalChart J (M := M))
      (U : ∀ i, Set (C i).domain), (∀ i, IsOpen (U i)) →
    ∀ (ε δ₁ : ℝ), ε < 1 / 200000 → 92354 * ε + δ₁ < 1 →
    (∀ i, (C i).metricCloseOn g ε (U i)) →
    ∀ (s c e₀ : Fin n → ℝ), (∀ j, s j = 1 ∨ s j = -1) →
    let a := finiteLineAffineAlignment s c
    let v : Fin (n + 1) → W → ℝ := fun i w ↦ (a i).1 * (C i).axial (ι w) + (a i).2
    let V : Fin (n + 1) → Set W := fun i ↦ ι ⁻¹' (C i).region (U i)
    ∀ (l r η : Fin (n + 1) → ℝ), (∀ i, 0 < η i) →
      let K := fun i ↦ closure (V i ∩ v i ⁻¹' Icc (l i) (r i))
      (∀ i, K i ⊆ V i) →
      (∀ w : W, ∃ i, w ∈ V i ∧ v i w ∈ Ioo (l i + η i) (r i - η i)) →
      (∀ w i, w ∈ K i → ∀ j, w ∈ K j → i.val ≤ j.val + 1) →
      (∀ j : Fin n, ∀ w ∈ K j.castSucc, w ∈ K j.succ →
        |(C j.succ).axial (ι w) - (s j * (C j.castSucc).axial (ι w) + c j)| ≤ e₀ j) →
      (∀ j : Fin n, ∀ w ∈ K j.castSucc, w ∈ K j.succ →
        Real.sqrt (g.inner (ι w) (gradFun g (C j.succ).axial (ι w) - s j • gradFun g (C j.castSucc).axial (ι w))
          (gradFun g (C j.succ).axial (ι w) - s j • gradFun g (C j.castSucc).axial (ι w))) ≤ δ₁) →
      ∀ Δ : W → ℝ, (∀ w, 0 ≤ Δ w) →
      (∀ j : Fin n, ∀ w ∈ K j.castSucc, w ∈ K j.succ → e₀ j ≤ Δ w) →
      (∀ w i, w ∈ K i → 4 * ((A / η i) * (1 + 92354 * ε)) * Δ w < 1 - 92354 * ε) →
      ∃ (f : BumpCovering (Fin (n + 1)) W) (hf : ∀ i, ContMDiff I 𝓘(ℝ) ∞ (f i)),
        (∀ i, tsupport (f i) ⊆ K i) ∧
        (∀ i, ∀ w ∈ V i, v i w ∈ Icc (l i + η i) (r i - η i) → f i w = 1) ∧
        let u := fun w ↦ ∑ i, f.toSmoothPartitionOfUnity hf i w * v i w
        ContMDiff I 𝓘(ℝ) ∞ u ∧ ∀ w, mvfderiv I u w ≠ 0 := by
  classical
  obtain ⟨A, hA, hcutAll⟩ := exists_uniform_controlled_bumpCovering_of_buffered_functions (I := I) (M := W)
  refine ⟨A, hA, ?_⟩
  intro n ι hι hιsurj g C U hU ε δ₁ hε hδ₁ hmetric s c e₀ hs _ _ _
  have hcut := hcutAll (Fin (n + 1))
  let a := finiteLineAffineAlignment s c
  let q : Fin (n + 1) → M → ℝ := fun i x ↦ (a i).1 * (C i).axial x + (a i).2
  let v : Fin (n + 1) → W → ℝ := fun i ↦ q i ∘ ι
  let V : Fin (n + 1) → Set W := fun i ↦ ι ⁻¹' (C i).region (U i)
  obtain ⟨ν, Y, hp, heq⟩ := exists_finitely_aligned_least_ricci_fields_of_metric_close
    g C U hU ε hε hmetric s c hs
  have hopen (i) : IsOpen (V i) := ((C i).isOpen_region (hU i)).preimage hι.continuous
  have htarget (i) {w : W} (hw : w ∈ V i) : ι w ∈ (C i).target := by
    obtain ⟨y, _, hy⟩ := hw
    rw [← hy]
    exact y.property
  have hqat (i) {w : W} (hw : w ∈ V i) : ContMDiffAt J 𝓘(ℝ) ∞ (q i) (ι w) :=
    ((hp i).1 (ι w) (htarget i hw)).contMDiffAt ((C i).target.isOpen.mem_nhds (htarget i hw))
  have hvat (i) {w : W} (hw : w ∈ V i) : ContMDiffAt I 𝓘(ℝ) ∞ (v i) w :=
    (hqat i hw).comp w hι.contMDiffAt
  have hv (i) : ContMDiffOn I 𝓘(ℝ) ∞ (v i) (V i) :=
    fun w hw ↦ (hvat i hw).contMDiffWithinAt
  let L (w : W) (y : TangentSpace J (ι w)) : TangentSpace I w := (hιsurj w y).choose
  have hL (w : W) (y : TangentSpace J (ι w)) : mfderiv I J ι w (L w y) = y :=
    (hιsurj w y).choose_spec
  let X : Fin (n + 1) → ∀ w : W, TangentSpace I w := fun i w ↦ L w (Y i (ι w))
  have hd (i) {w : W} (hw : w ∈ V i) :
      mvfderiv I (v i) w (X i w) = mvfderiv J (q i) (ι w) (Y i (ι w)) := by
    have h := mvfderiv_comp_apply w ((hqat i hw).mdifferentiableAt (by decide))
      (hι.mdifferentiable (by decide) w) (X i w)
    change mvfderiv I (v i) w (X i w) =
      mvfderiv J (q i) (ι w) (mfderiv I J ι w (L w (Y i (ι w)))) at h
    rwa [hL] at h
  have hder (i) {w : W} (hw : w ∈ V i) :
      |mvfderiv I (v i) w (X i w) - 1| ≤ 92354 * ε := by
    rw [hd i hw]
    exact ((hp i).2.2.2 (ι w) hw).2.2.2.2.2.2
  intro l r η hη K hbuffer hcover hline hvalue hoverlap Δ hΔ he₀ hsmall
  obtain ⟨f, hf, hsupp, hone, hbumps⟩ := hcut V hopen v hv l r η hη hbuffer hcover
  refine ⟨f, hf, hsupp, hone, ?_⟩
  have hmax (w : W) : ∃ i, w ∈ K i ∧ ∀ j, w ∈ K j →
      (A / η j) * (1 + 92354 * ε) ≤ (A / η i) * (1 + 92354 * ε) := by
    let S := Finset.univ.filter (fun i ↦ w ∈ K i)
    have hS : S.Nonempty := by
      obtain ⟨i, hi, hc⟩ := hcover w
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, subset_closure ⟨hi, ?_⟩⟩⟩
      exact ⟨(le_add_of_nonneg_right (hη i).le).trans hc.1.le,
        hc.2.le.trans (sub_le_self _ (hη i).le)⟩
    obtain ⟨i, hi, himax⟩ := S.exists_max_image (fun i ↦ (A / η i) * (1 + 92354 * ε)) hS
    exact ⟨i, (Finset.mem_filter.mp hi).2,
      fun j hj ↦ himax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩
  choose imax himax hle using hmax
  let D : W → ℝ := fun w ↦ (A / η (imax w)) * (1 + 92354 * ε)
  apply contMDiff_and_mvfderiv_ne_zero_line_bump_partition f hf v
    (fun i w hw ↦ hvat i (hbuffer i (hsupp i hw))) X D Δ (fun _ ↦ 1 - 92354 * ε) hΔ
  · exact fun w i hi j hj ↦ hline w i (hsupp i hi) j (hsupp j hj)
  · intro j w hi hj
    change L w (Y j.succ (ι w)) = L w (Y j.castSucc (ι w))
    rw [(heq j (ι w) (hbuffer j.castSucc (hsupp _ hi)) (hbuffer j.succ (hsupp _ hj))
      δ₁ hδ₁ (hoverlap j w (hsupp _ hi) (hsupp _ hj))).2]
  · intro i w hw
    have hwV := hbuffer i (hsupp i hw)
    have hcoord : |mvfderiv I (v i) w (X i w)| ≤ 1 + 92354 * ε := by
      have hd' := abs_le.mp (hder i hwV)
      apply abs_le.mpr
      constructor <;> linarith only [hd'.1, hd'.2]
    exact (hbumps i w hwV (X i w)).trans
      ((mul_le_mul_of_nonneg_left hcoord (div_nonneg hA.le (hη i).le)).trans (hle w i (hsupp i hw)))
  · intro i w hw
    have hd' := (abs_le.mp (hder i (hbuffer i (hsupp i hw)))).1
    linarith only [hd']
  · intro j w hi hj
    have hval : |v j.succ w - v j.castSucc w| ≤ e₀ j := by
      change |(a j.succ).1 * (C j.succ).axial (ι w) + (a j.succ).2 -
        ((a j.castSucc).1 * (C j.castSucc).axial (ι w) + (a j.castSucc).2)| ≤ e₀ j
      rw [abs_finiteLineAffineAlignment_transition_error s c hs]
      exact hvalue j w (hsupp _ hi) (hsupp _ hj)
    exact hval.trans (he₀ j w (hsupp _ hi) (hsupp _ hj))
  · exact fun w ↦ hsmall w (imax w) (himax w)

theorem exists_uniform_regular_patch_of_buffered_neck_coordinates
    {E H W F H' M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M] :
    ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ) (ι : W → M), ContMDiff I J ∞ ι →
    (∀ w, Function.Surjective (mfderiv I J ι w)) →
    ∀ (g : SmoothRiemannianMetric J M) (C : Fin (n + 1) → cylindricalChart J (M := M))
      (U : ∀ i, Set (C i).domain), (∀ i, IsOpen (U i)) →
    ∀ (ε δ₁ : ℝ), ε < 1 / 200000 → 92354 * ε + δ₁ < 1 →
    (∀ i, (C i).metricCloseOn g ε (U i)) →
    ∀ (s c e₀ : Fin n → ℝ), (∀ j, s j = 1 ∨ s j = -1) →
    (∀ j : Fin n, ∀ x ∈ (C j.castSucc).region (U j.castSucc), x ∈ (C j.succ).region (U j.succ) →
      |(C j.succ).axial x - (s j * (C j.castSucc).axial x + c j)| ≤ e₀ j) →
    (∀ j : Fin n, ∀ x ∈ (C j.castSucc).region (U j.castSucc), x ∈ (C j.succ).region (U j.succ) →
      Real.sqrt (g.inner x (gradFun g (C j.succ).axial x - s j • gradFun g (C j.castSucc).axial x)
        (gradFun g (C j.succ).axial x - s j • gradFun g (C j.castSucc).axial x)) ≤ δ₁) →
    let a := finiteLineAffineAlignment s c
    let v : Fin (n + 1) → W → ℝ := fun i w ↦ (a i).1 * (C i).axial (ι w) + (a i).2
    let V : Fin (n + 1) → Set W := fun i ↦ ι ⁻¹' (C i).region (U i)
    ∀ (l r η : Fin (n + 1) → ℝ), (∀ i, 0 < η i) →
      let K := fun i ↦ closure (V i ∩ v i ⁻¹' Icc (l i) (r i))
      (∀ i, K i ⊆ V i) →
      (∀ w : W, ∃ i, w ∈ V i ∧ v i w ∈ Ioo (l i + η i) (r i - η i)) →
      (∀ w i, w ∈ K i → ∀ j, w ∈ K j → i.val ≤ j.val + 1) →
      ∀ Δ : W → ℝ, (∀ w, 0 ≤ Δ w) →
      (∀ j : Fin n, ∀ w ∈ K j.castSucc, w ∈ K j.succ → e₀ j ≤ Δ w) →
      (∀ w i, w ∈ K i → 4 * ((A / η i) * (1 + 92354 * ε)) * Δ w < 1 - 92354 * ε) →
      ∃ (f : BumpCovering (Fin (n + 1)) W) (hf : ∀ i, ContMDiff I 𝓘(ℝ) ∞ (f i)),
        (∀ i, tsupport (f i) ⊆ K i) ∧
        (∀ i, ∀ w ∈ V i, v i w ∈ Icc (l i + η i) (r i - η i) → f i w = 1) ∧
        let u := fun w ↦ ∑ i, f.toSmoothPartitionOfUnity hf i w * v i w
        ContMDiff I 𝓘(ℝ) ∞ u ∧ ∀ w, mvfderiv I u w ≠ 0 := by
  obtain ⟨A, hA, hpatch⟩ := exists_uniform_regular_patch_of_buffered_neck_coordinates_on_intersections
    (I := I) (J := J) (W := W) (M := M)
  refine ⟨A, hA, ?_⟩
  intro n ι hι hιsurj g C U hU ε δ₁ hε hδ₁ hmetric s c e₀ hs hvalue hoverlap a v V
    l r η hη K hbuffer hcover hline
  exact hpatch n ι hι hιsurj g C U hU ε δ₁ hε hδ₁ hmetric s c e₀ hs
    l r η hη hbuffer hcover hline
    (fun j w hi hj ↦ hvalue j (ι w) (hbuffer _ hi) (hbuffer _ hj))
    (fun j w hi hj ↦ hoverlap j (ι w) (hbuffer _ hi) (hbuffer _ hj))

theorem exists_regular_patch_of_buffered_neck_coordinates
    {n : ℕ} {E H W F H' M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M]
    (ι : W → M) (hι : ContMDiff I J ∞ ι)
    (hιsurj : ∀ w, Function.Surjective (mfderiv I J ι w))
    (g : SmoothRiemannianMetric J M) (C : Fin (n + 1) → cylindricalChart J (M := M))
    (U : ∀ i, Set (C i).domain) (hU : ∀ i, IsOpen (U i))
    (ε δ₁ : ℝ) (hε : ε < 1 / 200000) (hδ₁ : 92354 * ε + δ₁ < 1)
    (hmetric : ∀ i, (C i).metricCloseOn g ε (U i))
    (s c e₀ : Fin n → ℝ) (hs : ∀ j, s j = 1 ∨ s j = -1)
    (hvalue : ∀ j : Fin n, ∀ x ∈ (C j.castSucc).region (U j.castSucc), x ∈ (C j.succ).region (U j.succ) →
      |(C j.succ).axial x - (s j * (C j.castSucc).axial x + c j)| ≤ e₀ j)
    (hoverlap : ∀ j : Fin n, ∀ x ∈ (C j.castSucc).region (U j.castSucc), x ∈ (C j.succ).region (U j.succ) →
      Real.sqrt (g.inner x (gradFun g (C j.succ).axial x - s j • gradFun g (C j.castSucc).axial x)
        (gradFun g (C j.succ).axial x - s j • gradFun g (C j.castSucc).axial x)) ≤ δ₁) :
    let a := finiteLineAffineAlignment s c
    let v : Fin (n + 1) → W → ℝ := fun i w ↦ (a i).1 * (C i).axial (ι w) + (a i).2
    let V : Fin (n + 1) → Set W := fun i ↦ ι ⁻¹' (C i).region (U i)
    ∃ A : ℝ, 0 < A ∧ ∀ (l r η : Fin (n + 1) → ℝ), (∀ i, 0 < η i) →
      let K := fun i ↦ closure (V i ∩ v i ⁻¹' Icc (l i) (r i))
      (∀ i, K i ⊆ V i) →
      (∀ w : W, ∃ i, w ∈ V i ∧ v i w ∈ Ioo (l i + η i) (r i - η i)) →
      (∀ w i, w ∈ K i → ∀ j, w ∈ K j → i.val ≤ j.val + 1) →
      ∀ Δ : W → ℝ, (∀ w, 0 ≤ Δ w) →
      (∀ j : Fin n, ∀ w ∈ K j.castSucc, w ∈ K j.succ → e₀ j ≤ Δ w) →
      (∀ w i, w ∈ K i → 4 * ((A / η i) * (1 + 92354 * ε)) * Δ w < 1 - 92354 * ε) →
      ∃ (f : BumpCovering (Fin (n + 1)) W) (hf : ∀ i, ContMDiff I 𝓘(ℝ) ∞ (f i)),
        (∀ i, tsupport (f i) ⊆ K i) ∧
        (∀ i, ∀ w ∈ V i, v i w ∈ Icc (l i + η i) (r i - η i) → f i w = 1) ∧
        let u := fun w ↦ ∑ i, f.toSmoothPartitionOfUnity hf i w * v i w
        ContMDiff I 𝓘(ℝ) ∞ u ∧ ∀ w, mvfderiv I u w ≠ 0 := by
  obtain ⟨A, hA, h⟩ := exists_uniform_regular_patch_of_buffered_neck_coordinates
    (I := I) (J := J) (W := W) (M := M)
  exact ⟨A, hA, h n ι hι hιsurj g C U hU ε δ₁ hε hδ₁ hmetric s c e₀ hs hvalue hoverlap⟩

end Poincare.Geometry.Neck
