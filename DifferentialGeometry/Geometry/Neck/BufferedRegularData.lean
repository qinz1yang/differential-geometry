import DifferentialGeometry.Geometry.Neck.ScaledPatch
import DifferentialGeometry.Geometry.Neck.RegularEndpoints
import DifferentialGeometry.Topology.PartitionOfUnity.Locality

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open Poincare.Geometry.Affine Poincare.Geometry.Boundary Poincare.Topology.Ehresmann

namespace Poincare.Geometry.Neck

theorem exists_regular_data_of_buffered_neck_bands_on_intersections
    {E H W : Type} {F H' M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W]
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ W] [CompactSpace W] [PreconnectedSpace W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M] (m : ℝ) (hm : 0 < m) (Cₒ : ℝ) (hCₒ : 0 < Cₒ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (n : ℕ) (ι : W → M), ContMDiff I J ∞ ι →
      IsEmbedding ι → (∀ w, Function.Injective (mfderiv I J ι w)) →
      Module.finrank ℝ E = Module.finrank ℝ F →
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
      ∀ (S₀ S₁ : Set W), I.boundary W = S₀ ∪ S₁ →
      (∀ j, j ≠ 0 → Disjoint S₀ (K j)) →
      (∀ j, j ≠ Fin.last n → Disjoint S₁ (K j)) →
      ∀ (t₀ t₁ : ℝ)
        (hsection₀ : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, (p, t₀) ∈ (C 0).domain)
        (hsection₁ : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, (p, t₁) ∈ (C (Fin.last n)).domain),
      (ι '' S₀ = range (fun p ↦ ((C 0).chart ⟨(p, t₀), hsection₀ p⟩ : M))) →
      (ι '' S₁ = range (fun p ↦ ((C (Fin.last n)).chart ⟨(p, t₁), hsection₁ p⟩ : M))) →
      ∀ (d : ℝ), 0 < d →
      ∀ (hcollar : ∀ (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) t,
        t ∈ Icc 0 d → (p, t₀ + (a 0).1 * t) ∈ (C 0).domain),
      (∀ (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) t (ht : t ∈ Icc 0 d),
        ((C 0).chart ⟨(p, t₀ + (a 0).1 * t), hcollar p t ht⟩ : M) ∈ range ι) →
      ∃ (f : BumpCovering (Fin (n + 1)) W) (hf : ∀ i, ContMDiff I 𝓘(ℝ) ∞ (f i)),
        (∀ i, tsupport (f i) ⊆ K i) ∧
        let u := fun w ↦ ∑ i, f.toSmoothPartitionOfUnity hf i w * v i w
        let b₀ := (a 0).1 * (Real.sqrt (C 0).scale)⁻¹ * t₀ + (a 0).2
        let b₁ := (a (Fin.last n)).1 * (Real.sqrt (C (Fin.last n)).scale)⁻¹ * t₁ + (a (Fin.last n)).2
        ∃ (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hb : b₀ < b₁)
          (hbdy : ∀ w, I.IsBoundaryPoint w → u w = b₀ ∨ u w = b₁),
          RegularIntervalDatum I u b₀ b₁ ∧
          u ⁻¹' ({b₀} : Set ℝ) = S₀ ∧ u ⁻¹' ({b₁} : Set ℝ) = S₁ ∧
          (∀ᶠ w in 𝓝ˢ S₀, u w = v 0 w) ∧
          (∀ᶠ w in 𝓝ˢ S₁, u w = v (Fin.last n) w) ∧
          ∃ η₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, hI.boundaryI⟯
              boundaryLevel u b₀ b₁ hb.ne hu.continuous hbdy,
            ∀ p, ι (η₀ p).1.1 = ((C 0).chart ⟨(p, t₀), hsection₀ p⟩ : M) := by
  obtain ⟨ε₀, hε₀, hpatch⟩ := exists_regular_patch_of_scaled_neck_bands_on_intersections
    (I := I) (J := J) (W := W) (M := M) m hm Cₒ hCₒ
  refine ⟨ε₀, hε₀, ?_⟩
  intro n ι hι hemb hinj hdim g C U hU ε hεnonneg hε hmetric s c hs hratio a v V l r η hwidth hband hcover K hline hvalue hoverlap S₀ S₁ hboundary hdisj₀ hdisj₁ t₀ t₁ hsection₀ hsection₁ himage₀ himage₁ d hd hcollar hinward
  have hsurj (w : W) : Function.Surjective (mfderiv I J ι w) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (mfderiv I J ι w).toLinearMap)).mp (hinj w)
  obtain ⟨f, hf, hsupp, _, hu, hreg⟩ := hpatch n ι hι hsurj g C U hU ε hεnonneg hε
    hmetric s c hs hratio l r η hwidth hband hcover hline hvalue hoverlap
  let u := fun w ↦ ∑ i, f.toSmoothPartitionOfUnity hf i w * v i w
  have hρsupp (i) : tsupport (f.toPartitionOfUnity i) ⊆ K i :=
    (closure_mono (f.support_toPartitionOfUnity_subset i)).trans (hsupp i)
  have hcoe (i) (w : W) : f.toPartitionOfUnity i w = f.toSmoothPartitionOfUnity hf i w := rfl
  have hlocal₀ : ∀ᶠ w in 𝓝ˢ S₀, u w = v 0 w := by
    simpa only [finsum_eq_sum_of_fintype, smul_eq_mul, hcoe] using
      Poincare.Topology.partition_patch_eq_near_of_disjoint_tsupport f.toPartitionOfUnity v S₀ 0
        (fun j hj ↦ (hdisj₀ j hj).mono_right (hρsupp j))
  have hlocal₁ : ∀ᶠ w in 𝓝ˢ S₁, u w = v (Fin.last n) w := by
    simpa only [finsum_eq_sum_of_fintype, smul_eq_mul, hcoe] using
      Poincare.Topology.partition_patch_eq_near_of_disjoint_tsupport f.toPartitionOfUnity v S₁ (Fin.last n)
        (fun j hj ↦ (hdisj₁ j hj).mono_right (hρsupp j))
  obtain ⟨hb, hbdy, hdata, hfiber₀, hfiber₁, hη₀⟩ := exists_regular_endpoints_of_extreme_neck_sections
    ι hι hemb hinj hdim (C 0) (C (Fin.last n)) t₀ t₁ (a 0).1 (a (Fin.last n)).1
    (a 0).2 (a (Fin.last n)).2 (finiteLineAffineAlignment_sign s c hs 0)
    S₀ S₁ hboundary hsection₀ hsection₁ himage₀ himage₁ u hu hreg hlocal₀ hlocal₁ d hd hcollar hinward
  exact ⟨f, hf, hsupp, hu, hb, hbdy, hdata, hfiber₀, hfiber₁, hlocal₀, hlocal₁, hη₀⟩

theorem exists_regular_data_of_buffered_neck_bands
    {E H W : Type} {F H' M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W]
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ W] [CompactSpace W] [PreconnectedSpace W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M] (m : ℝ) (hm : 0 < m) (Cₒ : ℝ) (hCₒ : 0 < Cₒ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (n : ℕ) (ι : W → M), ContMDiff I J ∞ ι →
      IsEmbedding ι → (∀ w, Function.Injective (mfderiv I J ι w)) →
      Module.finrank ℝ E = Module.finrank ℝ F →
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
      ∀ (S₀ S₁ : Set W), I.boundary W = S₀ ∪ S₁ →
      (∀ j, j ≠ 0 → Disjoint S₀ (K j)) →
      (∀ j, j ≠ Fin.last n → Disjoint S₁ (K j)) →
      ∀ (t₀ t₁ : ℝ)
        (hsection₀ : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, (p, t₀) ∈ (C 0).domain)
        (hsection₁ : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, (p, t₁) ∈ (C (Fin.last n)).domain),
      (ι '' S₀ = range (fun p ↦ ((C 0).chart ⟨(p, t₀), hsection₀ p⟩ : M))) →
      (ι '' S₁ = range (fun p ↦ ((C (Fin.last n)).chart ⟨(p, t₁), hsection₁ p⟩ : M))) →
      ∀ (d : ℝ), 0 < d →
      ∀ (hcollar : ∀ (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) t,
        t ∈ Icc 0 d → (p, t₀ + (a 0).1 * t) ∈ (C 0).domain),
      (∀ (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) t (ht : t ∈ Icc 0 d),
        ((C 0).chart ⟨(p, t₀ + (a 0).1 * t), hcollar p t ht⟩ : M) ∈ range ι) →
      ∃ (f : BumpCovering (Fin (n + 1)) W) (hf : ∀ i, ContMDiff I 𝓘(ℝ) ∞ (f i)),
        (∀ i, tsupport (f i) ⊆ K i) ∧
        let u := fun w ↦ ∑ i, f.toSmoothPartitionOfUnity hf i w * v i w
        let b₀ := (a 0).1 * (Real.sqrt (C 0).scale)⁻¹ * t₀ + (a 0).2
        let b₁ := (a (Fin.last n)).1 * (Real.sqrt (C (Fin.last n)).scale)⁻¹ * t₁ + (a (Fin.last n)).2
        ∃ (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hb : b₀ < b₁)
          (hbdy : ∀ w, I.IsBoundaryPoint w → u w = b₀ ∨ u w = b₁),
          RegularIntervalDatum I u b₀ b₁ ∧
          u ⁻¹' ({b₀} : Set ℝ) = S₀ ∧ u ⁻¹' ({b₁} : Set ℝ) = S₁ ∧
          (∀ᶠ w in 𝓝ˢ S₀, u w = v 0 w) ∧
          (∀ᶠ w in 𝓝ˢ S₁, u w = v (Fin.last n) w) ∧
          ∃ η₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, hI.boundaryI⟯
              boundaryLevel u b₀ b₁ hb.ne hu.continuous hbdy,
            ∀ p, ι (η₀ p).1.1 = ((C 0).chart ⟨(p, t₀), hsection₀ p⟩ : M) := by
  obtain ⟨ε₀, hε₀, hpatch⟩ := exists_regular_data_of_buffered_neck_bands_on_intersections
    (I := I) (J := J) (W := W) (M := M) m hm Cₒ hCₒ
  refine ⟨ε₀, hε₀, ?_⟩
  intro n ι hι hemb hinj hdim g C U hU ε hεnonneg hε hmetric s c hs hratio hvalue hoverlap a v V
    l r η hwidth hband hcover K hline
  have hbuffer (i) : K i ⊆ V i := by
    have hτ : (a i).1 ≠ 0 := by
      rcases finiteLineAffineAlignment_sign s c hs i with h | h <;> rw [h] <;> norm_num
    exact (C i).closure_preimage_affine_axial_band_subset_region (U i)
      (a i).1 (a i).2 (l i) (r i) hτ (hband i) ι hι.continuous
  exact hpatch n ι hι hemb hinj hdim g C U hU ε hεnonneg hε hmetric s c hs hratio
    l r η hwidth hband hcover hline
    (fun j w hi hj ↦ hvalue j (ι w) (hbuffer _ hi) (hbuffer _ hj))
    (fun j w hi hj ↦ hoverlap j (ι w) (hbuffer _ hi) (hbuffer _ hj))

end Poincare.Geometry.Neck
