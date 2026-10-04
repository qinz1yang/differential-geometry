import DifferentialGeometry.Geometry.Exponential.RadialFlat

/-!
# SF4(a): the exponential map of a complete flat metric (clause (FC), smooth metrics)

For a complete smooth Riemannian metric with vanishing curvature, `exp_p : T_pM → M` is a local
diffeomorphism whose differential is a linear isometry from `(T_pM, g_p)` at every point, a covering
map, and onto (`flat_expMapIntrinsic_isLocalIsometry_isCoveringMap`). These are the tree's
`RadialFlat` results, collected in the form of W4-F7c's clause (FC). We add the metric form:
`exp_p` is `1`-Lipschitz from `(T_pM, g_p)` (`edist_expMapIntrinsic_le_of_flat`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open Connection Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- SF4(a) = clause (FC) for a smooth complete flat metric: `exp_p` is a local diffeomorphism, its
differential is an isometry from `g_p` at every point, and it is a surjective covering map. -/
theorem flat_expMapIntrinsic_isLocalIsometry_isCoveringMap [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) :
    IsLocalDiffeomorph 𝓘(ℝ, E) I ∞
        (fun z : E => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)) ∧
      (∀ u v w : E,
        g.inner (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from u))
          (mfderiv 𝓘(ℝ, E) I
            (fun z : E => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)) u v)
          (mfderiv 𝓘(ℝ, E) I
            (fun z : E => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)) u w) =
          inner ℝ (show TangentSpace I p from v) (show TangentSpace I p from w)) ∧
      IsCoveringMap
        (fun z : E => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)) ∧
      Surjective
        (fun z : E => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)) := by
  refine ⟨expMapIntrinsic_isLocalDiffeomorph_of_riemannOp_eq_zero (I := I) g hEnorm hR p,
    fun u v w => (expMapIntrinsic_mfderiv_inner_of_riemannOp_eq_zero (I := I) g hEnorm hR p
      u v w).symm,
    expMapIntrinsic_isCoveringMap_of_riemannOp_eq_zero (I := I) g hEnorm hR p, fun q => ?_⟩
  obtain ⟨v, hv, -⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm p q
  exact ⟨v, hv⟩

/-- The differential of a flat `exp_p` preserves the extended norm of `g`. -/
theorem enorm_mfderiv_expMapIntrinsic_of_flat
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) (u w : E) :
    ‖(mfderiv 𝓘(ℝ, E) I
        (fun z : E => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)) u w :
          TangentSpace I (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from u)))‖ₑ =
      ‖(show TangentSpace I p from w)‖ₑ := by
  rw [hEnorm, ← expMapIntrinsic_mfderiv_inner_of_riemannOp_eq_zero (I := I) g hEnorm hR p u w w,
    real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _), ofReal_norm]

/-- SF4(a), metric form: a flat `exp_p` is `1`-Lipschitz from `(T_pM, g_p)`. -/
theorem edist_expMapIntrinsic_le_of_flat
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) (u v : TangentSpace I p) :
    edist (expMapIntrinsic (I := I) g hEnorm p u) (expMapIntrinsic (I := I) g hEnorm p v) ≤
      ‖u - v‖ₑ := by
  let F : E → M := fun z => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)
  have hF : ContMDiff 𝓘(ℝ, E) I ∞ F :=
    (expMapIntrinsic_isLocalDiffeomorph_of_riemannOp_eq_zero (I := I) g hEnorm hR p).contMDiff
  let ℓ : ℝ → E := fun t => (u : E) + t • ((v : E) - u)
  have hℓ : ContDiff ℝ ∞ ℓ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hℓd : ∀ t, HasDerivAt ℓ ((v : E) - u) t := by
    intro t
    have h := ((hasDerivAt_id' t).smul_const ((v : E) - u)).const_add (u : E)
    rwa [one_smul] at h
  let c : ℝ → M := F ∘ ℓ
  have hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c := hF.comp hℓ.contMDiff
  have hderiv : ∀ t, mfderiv 𝓘(ℝ, ℝ) I c t 1 = mfderiv 𝓘(ℝ, E) I F (ℓ t) ((v : E) - u) := by
    intro t
    have hcomp := mfderiv_comp (I' := 𝓘(ℝ, E)) t ((hF (ℓ t)).mdifferentiableAt (by simp))
      (hℓ.contMDiff.mdifferentiableAt (n := ∞) (by simp) (x := t))
    rw [hcomp]
    change mfderiv 𝓘(ℝ, E) I F (ℓ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ℓ t 1) = _
    rw [mfderiv_eq_fderiv, (hℓd t).hasFDerivAt.fderiv]
    exact congrArg (mfderiv 𝓘(ℝ, E) I F (ℓ t)) (one_smul ℝ ((v : E) - u))
  have hlen : Manifold.pathELength I c 0 1 = ‖v - u‖ₑ := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have hconst : ∀ t, ‖mfderiv 𝓘(ℝ, ℝ) I c t 1‖ₑ = ‖v - u‖ₑ := by
      intro t
      rw [hderiv t]
      exact enorm_mfderiv_expMapIntrinsic_of_flat (I := I) g hEnorm hR p (ℓ t) ((v : E) - u)
    simp only [hconst, lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
      Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
  have hc0 : c 0 = expMapIntrinsic (I := I) g hEnorm p u := by
    change F ((u : E) + (0 : ℝ) • ((v : E) - u)) = _
    rw [zero_smul, add_zero]
  have hc1 : c 1 = expMapIntrinsic (I := I) g hEnorm p v := by
    change F ((u : E) + (1 : ℝ) • ((v : E) - u)) = _
    rw [one_smul, add_sub_cancel]
  rw [IsRiemannianManifold.out (I := I), enorm_sub_rev, ← hlen]
  exact Manifold.riemannianEDist_le_pathELength ((hc.of_le (by simp)).contMDiffOn) hc0 hc1
    zero_le_one

end DifferentialGeometry.Geometry.Riemannian.Exponential
