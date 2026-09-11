import DifferentialGeometry.Geometry.Metric.RicciSoliton.PotentialCompleteness
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Operations
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.Product.Completeness
import DifferentialGeometry.Geometry.Operator.NormGradSqScaling
import DifferentialGeometry.Geometry.Operator.Product

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

def normalizedGradientRicciSoliton
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) : Prop :=
  RiemannianMetricComplete (I := I) g ∧
    gradientRicciSoliton (I := I) g f 1 ∧
      ∀ x : M, metricScalarAt (I := I) g x +
        normGradSqFun (I := I) g f x = f x

section Product

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G} [J.Boundaryless]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [SigmaCompactSpace N] [T2Space N]

theorem normalizedGradientRicciSoliton_prod
    [CompleteSpace E] [CompleteSpace F]
    [BoundarylessManifold I M] [BoundarylessManifold J N]
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    {f : C^∞⟮I, M; Real⟯} {k : C^∞⟮J, N; Real⟯}
    (hg : normalizedGradientRicciSoliton (I := I) g f)
    (hh : normalizedGradientRicciSoliton (I := J) h k) :
    normalizedGradientRicciSoliton (I := I.prod J) (g.prod h)
      (f.comp ContMDiffMap.fst + k.comp ContMDiffMap.snd) := by
  refine ⟨RiemannianMetricComplete.prod hg.1 hh.1,
    gradientRicciSoliton_prod hg.2.1 hh.2.1, ?_⟩
  intro x
  change metricScalarAt (I := I.prod J) (g.prod h) x +
      normGradSqFun (I := I.prod J) (g.prod h)
        (fun q : M × N => f q.1 + k q.2) x = f x.1 + k x.2
  rw [Curvature.metricScalarAt_productMetric,
    Operator.normGradSqFun_prod]
  calc
    metricScalarAt (I := I) g x.1 + metricScalarAt (I := J) h x.2 +
          (normGradSqFun (I := I) g f x.1 +
            normGradSqFun (I := J) h k x.2) =
        (metricScalarAt (I := I) g x.1 +
            normGradSqFun (I := I) g f x.1) +
          (metricScalarAt (I := J) h x.2 +
            normGradSqFun (I := J) h k x.2) := by ring
    _ = f x.1 + k x.2 := by rw [hg.2.2 x.1, hh.2.2 x.2]

end Product

section LocalPull

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G} [J.Boundaryless]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [SigmaCompactSpace N] [T2Space N]

theorem normalizedGradientRicciSoliton_localPullMetric
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯}
    {Phi : M → N}
    (hsol : normalizedGradientRicciSoliton (I := J) g f)
    (hPhi : IsLocalDiffeomorph I J ∞ Phi)
    (hcomplete : RiemannianMetricComplete (I := I) (localPullMetric g Phi hPhi)) :
    normalizedGradientRicciSoliton (I := I) (localPullMetric g Phi hPhi)
      (f.comp ⟨Phi, hPhi.contMDiff⟩) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let _ : CompleteSpace F := FiniteDimensional.complete Real F
  refine ⟨hcomplete, gradientRicciSoliton_localPullMetric hsol.2.1 hPhi, ?_⟩
  intro x
  change metricScalarAt (localPullMetric g Phi hPhi) x +
      normGradSqFun (localPullMetric g Phi hPhi) (f ∘ Phi) x = f (Phi x)
  rw [metricScalarAt_localPull, normGradSqFun_localPull g Phi hPhi f x
    (f.contMDiff.mdifferentiableAt (by simp))]
  exact hsol.2.2 (Phi x)

theorem normalizedGradientRicciSoliton_of_surjective_localPullMetric
    {h : SmoothRiemannianMetric I M} {Fpot : C^∞⟮I, M; Real⟯}
    {g : SmoothRiemannianMetric J N} {f : C^∞⟮J, N; Real⟯}
    {Phi : M → N}
    (hsol : normalizedGradientRicciSoliton (I := I) h Fpot)
    (hcomplete : RiemannianMetricComplete (I := J) g)
    (hPhi : IsLocalDiffeomorph I J ∞ Phi)
    (hsurj : Function.Surjective Phi)
    (hpull : localPullMetric (I := I) (J := J) g Phi hPhi = h)
    (hpotential : ∀ x : M, Fpot x = f (Phi x)) :
    normalizedGradientRicciSoliton (I := J) g f := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let _ : CompleteSpace F := FiniteDimensional.complete Real F
  refine ⟨hcomplete,
    gradientRicciSoliton_of_surjective_localPullMetric hsol.2.1
      hPhi hsurj hpull hpotential, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  have hsource := hsol.2.2 x
  have hpotentialEq : (Fpot : M → Real) = f ∘ Phi :=
    funext hpotential
  rw [← hpull, hpotentialEq,
    Curvature.metricScalarAt_localPull (I := I) (J := J) g Phi hPhi,
    Operator.normGradSqFun_localPull (I := I) (J := J) g Phi hPhi f x
      (f.contMDiff.mdifferentiableAt (by simp))] at hsource
  exact hsource

end LocalPull

theorem normalizedGradientRicciSoliton_complete
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) :
    RiemannianMetricComplete (I := I) g :=
  h.1

theorem normalizedGradientRicciSoliton_equation
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) :
    gradientRicciSoliton (I := I) g f 1 :=
  h.2.1

theorem normalizedGradientRicciSoliton_potential_equation
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) (x : M) :
    metricScalarAt (I := I) g x +
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) = f x := by
  simpa only [normGradSqFun_def] using h.2.2 x

theorem normalizedGradientRicciSoliton_potential_eq_metricScalarAt_of_gradient_eq_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) (x : M)
    (hgrad : gradFun (I := I) g f x = 0) :
    f x = metricScalarAt (I := I) g x := by
  have hpotential := normalizedGradientRicciSoliton_potential_equation (I := I) h x
  rw [hgrad] at hpotential
  simpa using hpotential.symm

theorem normalizedGradientRicciSoliton_scalar_nonneg
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) (x : M) :
    0 ≤ metricScalarAt (I := I) g x := by
  have hR := gradientRicciSoliton_scalar_lower_bound
    (I := I) g f 1 h.1 h.2.1 x
  have hhalf : 0 ≤ (Module.finrank Real E : Real) * 1 / 2 := by positivity
  rw [min_eq_left hhalf] at hR
  exact hR

theorem normalizedGradientRicciSoliton_potential_nonneg
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) (x : M) :
    0 ≤ f x := by
  have hR := normalizedGradientRicciSoliton_scalar_nonneg (I := I) h x
  have hgrad := normGradSqFun_nonneg (I := I) g (f : M → Real) x
  linarith [h.2.2 x]

theorem normalizedGradientRicciSoliton_isCompact_sublevel_of_isProperMap
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hproper : IsProperMap (f : M → ℝ)) (a : ℝ) :
    IsCompact {x : M | f x ≤ a} := by
  have heq : {x : M | f x ≤ a} = (f : M → ℝ) ⁻¹' Set.Icc 0 a := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc]
    exact (and_iff_right (normalizedGradientRicciSoliton_potential_nonneg h x)).symm
  rw [heq]
  exact hproper.isCompact_preimage isCompact_Icc

theorem normalizedGradientRicciSoliton_hamilton_normalized
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) :
    hamiltonNormalized (I := I) g f 1 := by
  intro x
  simpa only [one_mul] using
    normalizedGradientRicciSoliton_potential_equation (I := I) h x

theorem normalizedGradientRicciSoliton_weightedLaplacian_potential
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) (x : M) :
    weightedLaplacian (I := I) g f f x =
      (Module.finrank Real E : Real) / 2 - f x := by
  have hC : ∀ y : M,
      metricScalarAt (I := I) g y +
          g.inner y (gradFun (I := I) g f y) (gradFun (I := I) g f y) - 1 * f y = 0 := by
    intro y
    rw [normalizedGradientRicciSoliton_potential_equation (I := I) h y]
    ring
  have hw := gradientRicciSoliton_weightedLaplacian_potential
    (I := I) h.2.1 hC x
  rw [one_mul, sub_zero] at hw
  simpa only [mul_one] using hw

theorem normalizedGradientRicciSoliton_add_const_unique
    [Nonempty M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {c : Real}
    (hf : normalizedGradientRicciSoliton (I := I) g f)
    (hc : normalizedGradientRicciSoliton (I := I) g
      (f + ContMDiffMap.const (I := I)
        (I' := modelWithCornersSelf Real Real) (M := M) (n := ∞) c)) :
    c = 0 := by
  let x : M := Classical.choice (inferInstance : Nonempty M)
  have hgrad :
      gradFun (I := I) g ((f : M → Real) + (fun _ : M => c)) x =
        gradFun (I := I) g f x := by
    rw [Operator.gradFun_add (I := I) g
      ((f.contMDiff x).mdifferentiableAt (by simp))
      (mdifferentiableAt_const (c := c)), Operator.gradFun_const]
    simp
  have hf' := normalizedGradientRicciSoliton_potential_equation (I := I) hf x
  have hc' := normalizedGradientRicciSoliton_potential_equation (I := I) hc x
  change metricScalarAt (I := I) g x +
      g.inner x (gradFun (I := I) g
        ((f : M → Real) + (fun _ : M => c)) x)
        (gradFun (I := I) g ((f : M → Real) + (fun _ : M => c)) x) =
    f x + c at hc'
  rw [hgrad] at hc'
  linarith

theorem gradientRicciSoliton_exists_normalized
    [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {sigma : Real}
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hsigma : 0 < sigma) :
    ∃ C : Real,
      normalizedGradientRicciSoliton (I := I)
        (scaleMetric (I := I) sigma hsigma g)
        (f + ContMDiffMap.const (I := I)
          (I' := modelWithCornersSelf Real Real) (M := M) (n := ∞) (C / sigma)) := by
  obtain ⟨C, hC⟩ := gradientRicciSoliton_hamilton_constant hsol
  refine ⟨C, DifferentialGeometry.RiemannianMetricComplete.scaleMetric
    hcomplete sigma hsigma, ?_, ?_⟩
  · have hscaled := gradientRicciSoliton_scaleMetric hsol sigma hsigma
    have hparam : sigma / sigma = 1 := div_self (ne_of_gt hsigma)
    rw [hparam] at hscaled
    exact gradientRicciSoliton_add_const hscaled (C / sigma)
  · intro x
    rw [metricScalarAt_scaleMetric,
      normGradSqFun_scaleMetric]
    have hgradshift : normGradSqFun (I := I) g
        ((f : M → Real) + (fun _ : M => C / sigma)) x =
        normGradSqFun (I := I) g f x := by
      simp only [normGradSqFun_def]
      have hgrad : gradFun (I := I) g
          ((f : M → Real) + (fun _ : M => C / sigma)) x =
          gradFun (I := I) g f x := by
        rw [Operator.gradFun_add (I := I) g
          ((f.contMDiff x).mdifferentiableAt (by simp))
          (mdifferentiableAt_const (c := C / sigma)), Operator.gradFun_const]
        simp
      rw [hgrad]
    change sigma⁻¹ * metricScalarAt (I := I) g x +
        sigma⁻¹ * normGradSqFun (I := I) g
          ((f : M → Real) + (fun _ : M => C / sigma)) x =
      f x + C / sigma
    rw [hgradshift]
    have hCx := hC x
    change metricScalarAt (I := I) g x +
        normGradSqFun (I := I) g f x - sigma * f x = C at hCx
    have hsum : metricScalarAt (I := I) g x +
        normGradSqFun (I := I) g f x = sigma * f x + C := by
      linarith
    calc
      sigma⁻¹ * metricScalarAt (I := I) g x +
          sigma⁻¹ * normGradSqFun (I := I) g f x =
        sigma⁻¹ * (metricScalarAt (I := I) g x +
          normGradSqFun (I := I) g f x) := by ring
      _ = sigma⁻¹ * (sigma * f x + C) := by rw [hsum]
      _ = f x + C / sigma := by
        field_simp

theorem gradientRicciSoliton_existsUnique_normalized
    [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {sigma : ℝ}
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hsigma : 0 < sigma) :
    ∃! C : ℝ,
      (∀ x : M, metricScalarAt (I := I) g x +
        normGradSqFun (I := I) g f x - sigma * f x = C) ∧
      normalizedGradientRicciSoliton (I := I)
        (scaleMetric (I := I) sigma hsigma g)
        (f + ContMDiffMap.const (I := I)
          (I' := modelWithCornersSelf ℝ ℝ) (M := M) (n := ∞) (C / sigma)) := by
  obtain ⟨C, hn⟩ := gradientRicciSoliton_exists_normalized hcomplete hsol hsigma
  have hC (x : M) : metricScalarAt (I := I) g x +
      normGradSqFun (I := I) g f x - sigma * f x = C := by
    have hnormal := hn.2.2 x
    rw [metricScalarAt_scaleMetric, normGradSqFun_scaleMetric] at hnormal
    have hgradshift : normGradSqFun (I := I) g
        ((f : M → ℝ) + (fun _ : M => C / sigma)) x =
        normGradSqFun (I := I) g f x := by
      simp only [normGradSqFun_def]
      have hgrad : gradFun (I := I) g
          ((f : M → ℝ) + (fun _ : M => C / sigma)) x =
          gradFun (I := I) g f x := by
        rw [Operator.gradFun_add (I := I) g
          ((f.contMDiff x).mdifferentiableAt (by simp))
          (mdifferentiableAt_const (c := C / sigma)), Operator.gradFun_const]
        simp
      rw [hgrad]
    change sigma⁻¹ * metricScalarAt (I := I) g x +
        sigma⁻¹ * normGradSqFun (I := I) g
          ((f : M → ℝ) + (fun _ : M => C / sigma)) x =
      f x + C / sigma at hnormal
    rw [hgradshift] at hnormal
    field_simp [ne_of_gt hsigma] at hnormal
    linarith
  refine ⟨C, ⟨hC, hn⟩, ?_⟩
  intro D hD
  let x : M := Classical.choice (inferInstance : Nonempty M)
  exact (hD.1 x).symm.trans (hC x)

end DifferentialGeometry.Geometry
