import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.CorayGradient

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Topology

private theorem positive_ray_isometry {X : Type*} [MetricSpace X]
    {γ : ℝ → X} (hγ : Isometry γ) : Isometry (fun t : ℝ≥0 => γ t) := by
  apply Isometry.of_dist_eq
  intro s t
  exact hγ.dist_eq s t

private theorem negative_ray_isometry {X : Type*} [MetricSpace X]
    {γ : ℝ → X} (hγ : Isometry γ) : Isometry (fun t : ℝ≥0 => γ (-(t : ℝ))) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [hγ.dist_eq, dist_neg_neg]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem existsUnique_calibrated_intrinsic_ray
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (c : ℝ≥0 → M) (hc : Isometry c) (p : M)
    (hb : MDifferentiableAt I 𝓘(ℝ, ℝ) (busemann c) p) :
    ∃! u : TangentSpace I p, g.inner p u u = 1 ∧
      Isometry (fun t : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm p u (t : ℝ)) ∧
      ∀ t : ℝ, 0 ≤ t → busemann c (intrinsicGeodesic (I := I) g hEnorm p u t) =
        busemann c p + t := by
  obtain ⟨u, hu, hi, hcal⟩ := exists_calibrated_intrinsic_ray (I := I) g hEnorm c hc p
  refine ⟨u, ⟨hu, hi, hcal⟩, ?_⟩
  intro v hv
  have hgu := gradient_busemann_eq_of_calibrated_intrinsic_ray (I := I) g hEnorm
    c hc p hb u hu hi hcal
  have hgv := gradient_busemann_eq_of_calibrated_intrinsic_ray (I := I) g hEnorm
    c hc p hb v hv.1 hv.2.1 hv.2.2
  exact hgv.symm.trans hgu

variable [PreconnectedSpace M]

theorem opposite_busemann_unique_corays
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {γ : ℝ → M} (hγ : Isometry γ) (p : M) :
    (∃! u : TangentSpace I p, g.inner p u u = 1 ∧
      Isometry (fun t : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm p u (t : ℝ)) ∧
      ∀ t : ℝ, 0 ≤ t → busemann (fun s : ℝ≥0 => γ s)
        (intrinsicGeodesic (I := I) g hEnorm p u t) =
          busemann (fun s : ℝ≥0 => γ s) p + t) ∧
    (∃! u : TangentSpace I p, g.inner p u u = 1 ∧
      Isometry (fun t : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm p u (t : ℝ)) ∧
      ∀ t : ℝ, 0 ≤ t → busemann (fun s : ℝ≥0 => γ (-(s : ℝ)))
        (intrinsicGeodesic (I := I) g hEnorm p u t) =
          busemann (fun s : ℝ≥0 => γ (-(s : ℝ))) p + t) := by
  have hd := opposite_busemann_mdifferentiable (I := I) g hEnorm hRic hγ
  exact ⟨existsUnique_calibrated_intrinsic_ray (I := I) g hEnorm
      (fun t : ℝ≥0 => γ t) (positive_ray_isometry hγ) p (hd.1 p),
    existsUnique_calibrated_intrinsic_ray (I := I) g hEnorm
      (fun t : ℝ≥0 => γ (-(t : ℝ))) (negative_ray_isometry hγ) p (hd.2 p)⟩

theorem opposite_busemann_gradient_line
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {γ : ℝ → M} (hγ : Isometry γ) (p : M) :
    let b := busemann (fun t : ℝ≥0 => γ t)
    let eta := intrinsicGeodesic (I := I) g hEnorm p (gradientFun (I := I) g b p)
    Isometry eta ∧ ContMDiff 𝓘(ℝ, ℝ) I ∞ eta ∧ IsGeodesic (I := I) g eta ∧
      eta 0 = p ∧ ∀ t : ℝ, b (eta t) = b p + t := by
  let cp : ℝ≥0 → M := fun t => γ t
  let cn : ℝ≥0 → M := fun t => γ (-(t : ℝ))
  have hp : Isometry cp := positive_ray_isometry hγ
  have hn : Isometry cn := negative_ray_isometry hγ
  let u : TangentSpace I p := gradientFun (I := I) g (busemann cp) p
  let eta : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  have hd := opposite_busemann_mdifferentiable (I := I) g hEnorm hRic hγ
  obtain ⟨vp, hvp, hip, hcap⟩ := exists_calibrated_intrinsic_ray (I := I) g hEnorm cp hp p
  obtain ⟨vn, hvn, hin, hcan⟩ := exists_calibrated_intrinsic_ray (I := I) g hEnorm cn hn p
  have hgp : u = vp := gradient_busemann_eq_of_calibrated_intrinsic_ray (I := I)
    g hEnorm cp hp p (hd.1 p) vp hvp hip hcap
  have hgn : vn = -u := by
    have h := gradient_busemann_eq_of_calibrated_intrinsic_ray (I := I)
      g hEnorm cn hn p (hd.2 p) vn hvn hin hcan
    exact h.symm.trans (opposite_busemann_gradient_neg (I := I) g hEnorm hRic hγ p)
  have hu : g.inner p u u = 1 := by rw [hgp, hvp]
  have hcal (t : ℝ) : busemann cp (eta t) = busemann cp p + t := by
    by_cases ht : 0 ≤ t
    · change busemann cp (intrinsicGeodesic (I := I) g hEnorm p u t) = busemann cp p + t
      rw [hgp]
      exact hcap t ht
    · have hnt : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
      have hreverse : intrinsicGeodesic (I := I) g hEnorm p vn (-t) = eta t := by
        rw [hgn]
        have h := intrinsicGeo_smul_apply (I := I) g hEnorm p u (-1) (-t)
        simpa only [neg_one_smul, neg_mul, one_mul, neg_neg] using h
      have hminus := hcan (-t) hnt
      rw [hreverse] at hminus
      have hsumt := opposite_busemann_sum_eq_zero (I := I) g hEnorm hRic hγ (eta t)
      have hsump := opposite_busemann_sum_eq_zero (I := I) g hEnorm hRic hγ p
      change busemann cp (eta t) + busemann cn (eta t) = 0 at hsumt
      change busemann cp p + busemann cn p = 0 at hsump
      linarith
  have hiso : Isometry eta := by
    have hetaLip := lipschitzWith_one_intrinsicGeodesic (I := I) g hEnorm p u hu
    apply Isometry.of_dist_eq
    intro s t
    apply le_antisymm
    · simpa only [NNReal.coe_one, one_mul] using hetaLip.dist_le_mul s t
    · have h := (lipschitzWith_busemann hp).dist_le_mul (eta s) (eta t)
      rw [NNReal.coe_one, one_mul, hcal, hcal, Real.dist_eq] at h
      have hsub : busemann cp p + s - (busemann cp p + t) = s - t := by ring
      rw [hsub] at h
      exact h
  exact ⟨hiso, intrinsicGeodesic_contMDiff (I := I) g hEnorm p u,
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u,
    intrinsicGeodesic_zero (I := I) g hEnorm p u, hcal⟩

end DifferentialGeometry.Geometry.Topology

end
