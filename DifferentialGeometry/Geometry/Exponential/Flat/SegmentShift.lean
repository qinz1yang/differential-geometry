import DifferentialGeometry.Geometry.Exponential.Flat.TranslationIsometry

/-!
# SF4(b): a translation shifting a metric segment (producer for LFR23's torus exclusion)

On a complete flat orientable surface, for a metric segment `γ` of length `2s` there is an isometry
`τ` with `τ (γ 0) = γ s` and `τ (γ s) = γ (2s)` (`flat_exists_isometryEquiv_shift_segment`, and the
`dist` form `flat_exists_isometryEquiv_shift_segment_dist` for a metric space carrier). This is the
hypothesis of W4-F7c's `false_of_translation_of_lt` (`Collapse/FiniteSurface/TranslationExclusion.lean`).

Proof: lift `γ s` to `a` with `‖a‖ = s` (Hopf–Rinow at `p = γ 0`), let `τ` be the translation by `a`;
lift `τ⁻¹ (γ 2s)` to `b` with `‖b‖ = s`. Then `exp_p (a + b) = γ (2s)` and `exp_p` is `1`-Lipschitz,
so `2s ≤ ‖a + b‖ ≤ ‖a‖ + ‖b‖ = 2s`; strict convexity forces `b = a`, so `τ (γ s) = exp_p (2a) = γ (2s)`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open Connection Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section EMetric

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- SF4(b), producer: on a complete flat orientable surface a metric segment of length `2s` is
shifted by `s` by an isometry. -/
theorem flat_exists_isometryEquiv_shift_segment (hdim : Module.finrank ℝ E = 2) [ConnectedSpace M]
    (o : DifferentialGeometry.ManifoldOrientation I M 2)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    {γ : ℝ → M} {s : ℝ} (hs : 0 ≤ s)
    (hγ : ∀ t ∈ Icc 0 (2 * s), ∀ t' ∈ Icc 0 (2 * s), edist (γ t) (γ t') = ENNReal.ofReal |t - t'|) :
    ∃ τ : M ≃ᵢ M, τ (γ 0) = γ s ∧ τ (γ s) = γ (2 * s) := by
  set p := γ 0 with hp
  let F : TangentSpace I p → M := fun v => expMapIntrinsic (I := I) g hEnorm p v
  have hF0 : F 0 = p := expMapIntrinsic_zero (I := I) g hEnorm p
  have hHR : ∀ q : M, ∃ v : TangentSpace I p, F v = q ∧ ‖v‖ = (edist p q).toReal := by
    intro q
    obtain ⟨v, hv, hlen⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm p q
    refine ⟨v, hv, ?_⟩
    have h := hEnorm p v
    rw [hlen, ← ofReal_norm] at h
    rw [IsRiemannianManifold.out (I := I)]
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) ENNReal.toReal_nonneg).mp h
  have hmem0 : (0 : ℝ) ∈ Icc 0 (2 * s) := ⟨le_rfl, by linarith⟩
  have hmems : s ∈ Icc 0 (2 * s) := ⟨hs, by linarith⟩
  have hmem2 : 2 * s ∈ Icc 0 (2 * s) := ⟨by linarith, le_rfl⟩
  have d1 : edist p (γ s) = ENNReal.ofReal s := by
    rw [hp, hγ 0 hmem0 s hmems, zero_sub, abs_neg, abs_of_nonneg hs]
  have d2 : edist (γ s) (γ (2 * s)) = ENNReal.ofReal s := by
    rw [hγ s hmems (2 * s) hmem2, abs_sub_comm, show 2 * s - s = s by ring, abs_of_nonneg hs]
  have d3 : edist p (γ (2 * s)) = ENNReal.ofReal (2 * s) := by
    rw [hp, hγ 0 hmem0 (2 * s) hmem2, zero_sub, abs_neg, abs_of_nonneg (by linarith)]
  obtain ⟨a, ha, hna⟩ := hHR (γ s)
  rw [d1, ENNReal.toReal_ofReal hs] at hna
  obtain ⟨τ, hτ⟩ := flat_exists_translation_isometryEquiv (I := I) hdim o g hEnorm hR p a
  have hτF : ∀ w : TangentSpace I p, τ (F w) = F (w + a) := fun w => hτ w
  have hτp : τ p = γ s := by rw [← hF0, hτF, zero_add, ha]
  obtain ⟨b, hb, hnb⟩ := hHR (τ.symm (γ (2 * s)))
  have hdb : edist p (τ.symm (γ (2 * s))) = ENNReal.ofReal s := by
    rw [← τ.edist_eq, τ.apply_symm_apply, hτp, d2]
  rw [hdb, ENNReal.toReal_ofReal hs] at hnb
  have hFba : F (b + a) = γ (2 * s) := by rw [← hτF, hb, τ.apply_symm_apply]
  have hlip := edist_expMapIntrinsic_le_of_flat (I := I) g hEnorm hR p 0 (b + a)
  change edist (F 0) (F (b + a)) ≤ _ at hlip
  rw [hF0, hFba, d3, zero_sub, enorm_neg, ← ofReal_norm,
    ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)] at hlip
  have hsum : ‖b + a‖ = ‖b‖ + ‖a‖ := by
    have := norm_add_le b a
    linarith
  have hba : b = a := (sameRay_iff_norm_add.mpr hsum).eq_of_norm_eq (by rw [hna, hnb])
  refine ⟨τ, hτp, ?_⟩
  rw [← ha, hτF, ← hFba, hba]

end EMetric

section Metric

variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- SF4(b), producer, `dist` form (the shape of `false_of_translation_of_lt`). -/
theorem flat_exists_isometryEquiv_shift_segment_dist (hdim : Module.finrank ℝ E = 2)
    [ConnectedSpace M] (o : DifferentialGeometry.ManifoldOrientation I M 2)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    {γ : ℝ → M} {s : ℝ} (hs : 0 ≤ s)
    (hγ : ∀ t ∈ Icc 0 (2 * s), ∀ t' ∈ Icc 0 (2 * s), dist (γ t) (γ t') = |t - t'|) :
    ∃ τ : M ≃ᵢ M, τ (γ 0) = γ s ∧ τ (γ s) = γ (2 * s) :=
  flat_exists_isometryEquiv_shift_segment (I := I) hdim o g hEnorm hR hs
    (fun t ht t' ht' => by rw [edist_dist, hγ t ht t' ht'])

end Metric

end DifferentialGeometry.Geometry.Riemannian.Exponential
