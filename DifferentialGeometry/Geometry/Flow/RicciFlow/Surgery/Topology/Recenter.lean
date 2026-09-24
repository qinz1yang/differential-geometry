import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition



noncomputable section

open Set Bundle Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_universal_neck_recenter_constants :
    ∃ c : ℝ, 4 ≤ c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M],
      ∀ (g : SmoothRiemannianMetric ThreeModel M) (k : ℕ), 2 ≤ k →
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ N : NormalizedNeck g δ k,
      ∀ side : Bool,
      let s : ℝ := if side then 1 else -1
      ∃ hbuffer : ∀ x : neckBuffer (c * δ),
          (x.1.1, s * (1 + x.1.2)) ∈ neckBuffer δ,
      ∃ N' : NormalizedNeck g (c * δ) k,
        N'.sphereMark = N.sphereMark ∧
        (∀ x : neckBuffer (c * δ), N'.chart x =
          N.chart ⟨(x.1.1, s * (1 + x.1.2)), hbuffer x⟩) ∧
        (∃ hcenter : (N.sphereMark, s) ∈ neckBuffer δ,
          N'.center = N.chart ⟨(N.sphereMark, s), hcenter⟩) ∧
        |N'.scale / N.scale - 1| ≤ c * δ := by
  refine ⟨20000, by norm_num, 1 / 40000, by norm_num, ?_⟩
  intro M _ _ _ _ _ g k hk δ hδ hδle N side
  have hcpos : (0 : ℝ) < 20000 := by norm_num
  have hεpos : 0 < 20000 * δ := mul_pos hcpos hδ
  have hδhalf : δ ≤ 1 / 2 := by linarith
  have hδinv : 40000 ≤ δ⁻¹ :=
    (le_inv_comm₀ (by norm_num : (0 : ℝ) < 40000) hδ).mpr (by norm_num; linarith)
  have hfit : ((20000 : ℝ) * δ)⁻¹ + 1 ≤ δ⁻¹ := by
    rw [mul_inv_rev]
    nlinarith [hδinv, inv_pos.mpr hδ]
  set s : ℝ := if side then 1 else -1 with hs_def
  have hs : s ^ 2 = 1 := by rcases side <;> simp [hs_def]
  let hbuffer : ∀ x : neckBuffer (20000 * δ), (x.1.1, s * (1 + x.1.2)) ∈ neckBuffer δ :=
    fun x => neckShift_mem_neckBuffer hfit hs x
  refine ⟨hbuffer, ?_⟩
  have hcenterMem : (N.sphereMark, s) ∈ neckBuffer δ := by
    change -δ⁻¹ - 1 < s ∧ s < δ⁻¹ + 1
    have hi : 1 ≤ δ⁻¹ := by linarith
    obtain h | h := sq_eq_one_iff.mp hs <;> rw [h] <;> constructor <;> linarith
  let xc : neckBuffer δ := ⟨(N.sphereMark, s), hcenterMem⟩
  let center' : M := N.chart xc
  let lam : ℝ := metricScalarAt g center' / N.scale
  have hcltest : xc ∈ neckClosedTest δ := by
    change -δ⁻¹ ≤ s ∧ s ≤ δ⁻¹
    have hi : 1 ≤ δ⁻¹ := by linarith
    obtain h | h := sq_eq_one_iff.mp hs <;> rw [h] <;> constructor <;> linarith
  have hlam_bound : |lam - 1| ≤ 4323 * δ := by
    have h := NormalizedNeck.abs_scalar_ratio_sub_one_le N hk hδhalf xc hcltest
    simpa only [lam, center', xc] using h
  have hsmall : 4323 * δ < 11353 := by nlinarith [hδle]
  have hlam_pos : 0 < lam := by
    have h1 : 1 - 4323 * δ ≤ lam := by linarith [abs_le.mp hlam_bound]
    have h2 : 4323 * δ < 1 := by nlinarith [hsmall]
    linarith
  let gε : SmoothRiemannianMetric NeckCylinderModel ↥(neckBuffer (20000 * δ)) :=
    Geometry.Neck.recenteringMetric hs hfit N.normalizedMetric
  let nmetric : SmoothRiemannianMetric NeckCylinderModel (neckBuffer (20000 * δ)) :=
    scaleMetric lam hlam_pos gε
  have hlamscale : lam * N.scale = metricScalarAt g center' := by
    change metricScalarAt g center' / N.scale * N.scale = metricScalarAt g center'
    exact div_mul_cancel₀ _ (ne_of_gt N.scale_pos)
  have hscale_pos : 0 < metricScalarAt g center' := by
    rw [← hlamscale]
    exact mul_pos hlam_pos N.scale_pos
  let ψ : C(neckBuffer (20000 * δ), neckBuffer δ) :=
    ⟨Geometry.Neck.recenteringCylinderMap hs hfit,
      (Geometry.Neck.contMDiff_recenteringCylinderMap hs hfit).continuous⟩
  have hψ_smooth : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞
      (Geometry.Neck.recenteringCylinderMap hs hfit) :=
    Geometry.Neck.isSmoothEmbedding_recenteringCylinderMap hs hfit
  refine ⟨{ delta_pos := hεpos
            delta_lt_one := by linarith
            sphereMark := N.sphereMark
            center := center'
            chart := N.chart.comp ψ
            chart_smooth := ?_
            marked := ?_
            scale := metricScalarAt g center'
            scale_pos := hscale_pos
            scale_scalar := rfl
            normalizedMetric := nmetric
            normalized_inner := ?_
            closeness := ?_ }, ?_, ?_, ?_, ?_⟩
  · exact IsSmoothEmbedding.comp (f := Geometry.Neck.recenteringCylinderMap hs hfit)
      (g := (N.chart : neckBuffer δ → M)) N.chart_smooth hψ_smooth (by simp)
  · change (N.chart : neckBuffer δ → M)
        (Geometry.Neck.recenteringCylinderMap hs hfit ⟨(N.sphereMark, 0), _⟩) =
      (N.chart : neckBuffer δ → M) ⟨(N.sphereMark, s), hcenterMem⟩
    congr 1
    apply Subtype.ext
    rw [Geometry.Neck.recenteringCylinderMap_val hs hfit]
    simp
  · intro x V W
    let rcF : ↥(neckBuffer (20000 * δ)) → ↥(neckBuffer δ) :=
      Geometry.Neck.recenteringCylinderMap hs hfit
    let chF : ↥(neckBuffer δ) → M := N.chart
    have hψ_md_x : MDifferentiableAt NeckCylinderModel NeckCylinderModel rcF x :=
      (Geometry.Neck.contMDiff_recenteringCylinderMap hs hfit).mdifferentiableAt (by simp)
    have hchart_md : MDifferentiableAt NeckCylinderModel ThreeModel chF (rcF x) :=
      N.chart_smooth.contMDiff.mdifferentiableAt (by simp)
    have hV : mfderiv NeckCylinderModel ThreeModel (fun y => chF (rcF y)) x V =
        mfderiv NeckCylinderModel ThreeModel chF (rcF x)
          (mfderiv NeckCylinderModel NeckCylinderModel rcF x V) :=
      mfderiv_comp_apply x (f := rcF) (g := chF) hchart_md hψ_md_x V
    have hW : mfderiv NeckCylinderModel ThreeModel (fun y => chF (rcF y)) x W =
        mfderiv NeckCylinderModel ThreeModel chF (rcF x)
          (mfderiv NeckCylinderModel NeckCylinderModel rcF x W) :=
      mfderiv_comp_apply x (f := rcF) (g := chF) hchart_md hψ_md_x W
    change nmetric.inner x V W = metricScalarAt g center' *
      g.inner (chF (rcF x))
        (mfderiv NeckCylinderModel ThreeModel (fun y => chF (rcF y)) x V)
        (mfderiv NeckCylinderModel ThreeModel (fun y => chF (rcF y)) x W)
    calc nmetric.inner x V W
        = lam * gε.inner x V W := scaleMetric_inner lam hlam_pos gε x V W
      _ = lam * N.normalizedMetric.inner (rcF x)
            (mfderiv NeckCylinderModel NeckCylinderModel rcF x V)
            (mfderiv NeckCylinderModel NeckCylinderModel rcF x W) := by
          exact congrArg (fun t : ℝ => lam * t)
            (Geometry.Neck.recenteringMetric_inner hs hfit N.normalizedMetric x V W)
      _ = lam * (N.scale * g.inner (chF (rcF x))
            (mfderiv NeckCylinderModel ThreeModel chF (rcF x)
              (mfderiv NeckCylinderModel NeckCylinderModel rcF x V))
            (mfderiv NeckCylinderModel ThreeModel chF (rcF x)
              (mfderiv NeckCylinderModel NeckCylinderModel rcF x W))) := by
          exact congrArg (fun t : ℝ => lam * t)
            (N.normalized_inner (rcF x)
              (mfderiv NeckCylinderModel NeckCylinderModel rcF x V)
              (mfderiv NeckCylinderModel NeckCylinderModel rcF x W))
      _ = metricScalarAt g center' * g.inner (chF (rcF x))
            (mfderiv NeckCylinderModel ThreeModel (fun y => chF (rcF y)) x V)
            (mfderiv NeckCylinderModel ThreeModel (fun y => chF (rcF y)) x W) := by
          rw [hV, hW, ← mul_assoc, hlamscale]
  · let gRefδ : SmoothRiemannianMetric NeckCylinderModel ↥(neckBuffer δ) :=
      Geometry.Neck.referenceMetric δ
    let gRefε : SmoothRiemannianMetric NeckCylinderModel ↥(neckBuffer (20000 * δ)) :=
      Geometry.Neck.referenceMetric (20000 * δ)
    have hsubset : Geometry.Neck.recenteringCylinderMap hs hfit '' neckClosedTest (20000 * δ) ⊆
        neckClosedTest δ := by
      rintro y ⟨x, hx, rfl⟩
      have hxy : Geometry.Neck.recenteringCylinderMap hs hfit x =
          (⟨(x.1.1, s * (1 + x.1.2)), neckShift_mem_neckBuffer hfit hs x⟩ : neckBuffer δ) := by
        apply Subtype.ext
        rw [Geometry.Neck.recenteringCylinderMap_val hs hfit]
      rw [hxy]
      exact neckShift_mem_neckClosedTest hfit hs x hx
    have hrec := metricDerivNormSupOn_recenteringMetric (ε := 20000 * δ) (δ := δ) (σ := s)
      hs hfit N.normalizedMetric gRefδ (neckClosedTest (20000 * δ)) k
    have hRefε : Geometry.Neck.referenceMetric (20000 * δ) = gRefε := rfl
    have hGε : Geometry.Neck.recenteringMetric hs hfit N.normalizedMetric = gε := rfl
    have hGRef : Geometry.Neck.recenteringMetric hs hfit gRefδ = gRefε :=
      Geometry.Neck.recenteringMetric_reference hs hfit
    rw [hRefε, hGε, hGRef] at hrec
    let Kδ : Set ↥(neckBuffer δ) :=
      Geometry.Neck.recenteringCylinderMap hs hfit '' neckClosedTest (20000 * δ)
    have hbnd : CheegerGromovCompactness.metricDerivNormSupOn (I := NeckCylinderModel)
        Kδ k N.normalizedMetric gRefδ gRefδ < δ := by
      have hclos := N.closeness
      rw [roundCylinderMetric_eq_geometry] at hclos
      refine lt_of_le_of_lt ?_ hclos
      refine CheegerGromovCompactness.metricDerivNormSupOn_le_of_forall (I := NeckCylinderModel)
        (K := Kδ) (p := k) (gk := N.normalizedMetric) (gInf := gRefδ) (gRef := gRefδ)
        (c := CheegerGromovCompactness.metricDerivNormSupOn (I := NeckCylinderModel)
          (neckClosedTest δ) k N.normalizedMetric gRefδ gRefδ)
        (metricDerivNormSupOn_nonneg _ _ _ _ _) ?_
      intro a ha x hx
      exact CheegerGromovCompactness.derivNorm_le_sup (I := NeckCylinderModel)
        (isCompact_neckClosedTest δ) ha _ _ _
        (hsubset hx)
    have hbound : CheegerGromovCompactness.metricDerivNormSupOn (I := NeckCylinderModel)
        (neckClosedTest (20000 * δ)) k gε gRefε gRefε < δ :=
      hrec.trans_lt hbnd
    have hscaled := metricDerivNormSupOn_scaleMetric_left_lt (I := NeckCylinderModel)
      (M := ↥(neckBuffer (20000 * δ))) (K := neckClosedTest (20000 * δ)) (ε := δ)
      (isCompact_neckClosedTest (20000 * δ)) k lam hlam_pos gε gRefε hbound
    have hroot : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) : ℝ) = 3 := by simp
    rw [hroot] at hscaled
    rw [roundCylinderMetric_eq_geometry]
    exact hscaled.trans (recenter_scaled_error_bound hδ hlam_bound hsmall)
  · rfl
  · intro x
    change (N.chart : neckBuffer δ → M)
        (Geometry.Neck.recenteringCylinderMap hs hfit
          (⟨(x.1.1, x.1.2), x.2⟩ : ↥(Geometry.Neck.bufferedCylinder (20000 * δ)))) =
      (N.chart : neckBuffer δ → M) ⟨(x.1.1, s * (1 + x.1.2)), hbuffer x⟩
    congr 1
    apply Subtype.ext
    rw [Geometry.Neck.recenteringCylinderMap_val hs hfit]
  · exact ⟨hcenterMem, rfl⟩
  · change |lam - 1| ≤ 20000 * δ
    nlinarith [hlam_bound, hδ.le]


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
