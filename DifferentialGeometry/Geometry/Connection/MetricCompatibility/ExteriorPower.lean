import DifferentialGeometry.Geometry.Connection.TensorNabla.ExteriorPower
import DifferentialGeometry.Geometry.Metric.ExteriorPowerMusicalBundle
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Alternating

noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff RealInnerProductSpace

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

private instance alternatingFiniteDimensional (k : ℕ) :
    FiniteDimensional ℝ (F [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
    (Module.finBasis ℝ F)).finiteDimensional_of_finite

theorem IsMetricCompatible.exteriorPower_musicalEquiv
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible) (k : ℕ)
    (u : ∀ x, ⋀[ℝ]^k (V x)) (x : M) (X : TangentSpace I x) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    MDifferentiableAt I (I.prod 𝓘(ℝ, ⋀[ℝ]^k F))
      (fun y => (⟨y, u y⟩ : TotalSpace (⋀[ℝ]^k F) (fun z => ⋀[ℝ]^k (V z)))) x →
      _root_.exteriorPower.musicalEquiv k (cov.exteriorPower k u x X) =
        CovariantDerivative.alternating cov k
          (fun y => _root_.exteriorPower.musicalEquiv k (u y)) x X := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  intro hu
  classical
  have hmus := Bundle.ExteriorPower.contMDiff_musicalEquiv_map (IB := I) (n := 1) F V k
  have hmu := (hmus.mdifferentiableAt one_ne_zero).comp x hu
  have heval := Bundle.ExteriorPower.contMDiff_alternatingDualEquiv_map (IB := I) F V k 1
  have heu := (heval.mdifferentiableAt one_ne_zero).comp x hu
  have hc : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  apply (_root_.exteriorPower.musicalEquiv k).symm.injective
  apply ext_inner_right ℝ
  intro w
  apply mul_left_cancel₀ hc
  let a := _root_.exteriorPower.musicalEquiv k w
  obtain ⟨A, hA⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := F [⋀^Fin k]→L[ℝ] ℝ)
    (V := Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ))
    (n := (⊤ : ℕ∞)) x a
  have hg := hcov.alternating_mvfderiv_inner k hmu A.mdifferentiableAt X
  have hfun : (fun y => (alternatingRiemannianMetric (F := F) V k).inner y
      (_root_.exteriorPower.musicalEquiv k (u y)) (A y)) =
      (fun y => (k.factorial : ℝ) * _root_.exteriorPower.alternatingDualEquiv k (u y) (A y)) := by
    funext y
    exact alternatingRiemannianMetric_musicalEquiv_left V k y (u y) (A y)
  have hderiv := congrArg (fun f : M → ℝ => mfderiv I 𝓘(ℝ, ℝ) f x X) hfun
  have hg := hderiv.symm.trans hg
  have hgterm := alternatingRiemannianMetric_musicalEquiv_left (F := F) V k x (u x)
    (CovariantDerivative.alternating cov k A x X)
  have hg := hg.trans (congrArg (fun z : ℝ =>
    (alternatingRiemannianMetric (F := F) V k).inner x
      (CovariantDerivative.alternating cov k
        (fun y => _root_.exteriorPower.musicalEquiv k (u y)) x X) (A x) + z) hgterm)
  have heua : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => _root_.exteriorPower.alternatingDualEquiv k (u y) (A y)) x := by
    have h := heu.clm_bundle_apply A.mdifferentiableAt
    simp only [mdifferentiableAt_totalSpace] at h
    exact h.2
  have hd := mvfderiv_smul (I := I) (a := fun _ : M => (k.factorial : ℝ))
    (mdifferentiableAt_const (c := (k.factorial : ℝ))) heua
  simp only [mvfderiv_const, ContinuousLinearMap.zero_smulRight, add_zero] at hd
  change mvfderiv (I := I)
      (fun y => (k.factorial : ℝ) * _root_.exteriorPower.alternatingDualEquiv k (u y) (A y)) x =
    (k.factorial : ℝ) • mvfderiv (I := I)
      (fun y => _root_.exteriorPower.alternatingDualEquiv k (u y) (A y)) x at hd
  change mvfderiv (I := I)
      (fun y => (k.factorial : ℝ) * _root_.exteriorPower.alternatingDualEquiv k (u y) (A y)) x X =
    (alternatingRiemannianMetric (F := F) V k).inner x
      (CovariantDerivative.alternating cov k
        (fun y => _root_.exteriorPower.musicalEquiv k (u y)) x X) (A x) +
      (k.factorial : ℝ) * _root_.exteriorPower.alternatingDualEquiv k (u x)
        (CovariantDerivative.alternating cov k A x X) at hg
  rw [hd, smul_apply, smul_eq_mul] at hg
  have hp := alternatingRiemannianMetric_musicalEquiv_left (F := F) V k x
    (cov.exteriorPower k u x X) (A x)
  rw [exteriorPower_alternatingDualEquiv_apply cov k u A x X A.mdifferentiableAt hu] at hp
  have hpair : (alternatingRiemannianMetric (F := F) V k).inner x
      (_root_.exteriorPower.musicalEquiv k (cov.exteriorPower k u x X)) (A x) =
    (alternatingRiemannianMetric (F := F) V k).inner x
      (CovariantDerivative.alternating cov k
        (fun y => _root_.exteriorPower.musicalEquiv k (u y)) x X) (A x) := by
    linear_combination hp + hg
  rw [alternatingRiemannianMetric_inner_eq_factorial_mul_exterior_inner,
    alternatingRiemannianMetric_inner_eq_factorial_mul_exterior_inner, hA] at hpair
  simpa only [a, ContinuousLinearEquiv.symm_apply_apply] using hpair

theorem IsMetricCompatible.exteriorPower_musicalEquiv_symm
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible) (k : ℕ)
    (a : ∀ x, V x [⋀^Fin k]→L[ℝ] ℝ) (x : M) (X : TangentSpace I x)
    (ha : MDifferentiableAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, a y⟩ : TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)))) x) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    cov.exteriorPower k (fun y => (_root_.exteriorPower.musicalEquiv k).symm (a y)) x X =
      (_root_.exteriorPower.musicalEquiv k).symm (CovariantDerivative.alternating cov k a x X) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  have hm := Bundle.ExteriorPower.contMDiff_musicalEquiv_symm_map (IB := I) (n := 1) F V k
  have hu := (hm.mdifferentiableAt one_ne_zero).comp x ha
  have h := hcov.exteriorPower_musicalEquiv k
    (fun y => (_root_.exteriorPower.musicalEquiv k).symm (a y)) x X hu
  apply (_root_.exteriorPower.musicalEquiv k).injective
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

theorem IsMetricCompatible.exteriorPower
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible) (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := 1) F V k
    letI := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := 1) F V k
    (cov.exteriorPower k).IsMetricCompatible := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := 1) F V k
  let := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := 1) F V k
  apply (isMetricCompatible_iff _).mpr
  intro x X σ τ _ hσ hτ
  have hm := Bundle.ExteriorPower.contMDiff_musicalEquiv_map (IB := I) (n := 1) F V k
  have hmσ := (hm.mdifferentiableAt one_ne_zero).comp x hσ
  have hmτ := (hm.mdifferentiableAt one_ne_zero).comp x hτ
  have hg := hcov.alternating_mvfderiv_inner k hmσ hmτ (X x)
  have hinner (y : M) (v w : ⋀[ℝ]^k (V y)) :
      (alternatingRiemannianMetric (F := F) V k).inner y
        (_root_.exteriorPower.musicalEquiv k v) (_root_.exteriorPower.musicalEquiv k w) =
          (k.factorial : ℝ) * inner ℝ v w := by
    rw [alternatingRiemannianMetric_inner_eq_factorial_mul_exterior_inner,
      ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
  have hfun : (fun y => (alternatingRiemannianMetric (F := F) V k).inner y
      (_root_.exteriorPower.musicalEquiv k (σ y)) (_root_.exteriorPower.musicalEquiv k (τ y))) =
      (fun y => (k.factorial : ℝ) * inner ℝ (σ y) (τ y)) := by
    funext y
    exact hinner y (σ y) (τ y)
  have hderiv := congrArg (fun f : M → ℝ => mfderiv I 𝓘(ℝ, ℝ) f x (X x)) hfun
  have hg := hderiv.symm.trans hg
  have hDσ := hcov.exteriorPower_musicalEquiv k σ x (X x) hσ
  have hDτ := hcov.exteriorPower_musicalEquiv k τ x (X x) hτ
  have hterms : (alternatingRiemannianMetric (F := F) V k).inner x
      (CovariantDerivative.alternating cov k
        (fun y => _root_.exteriorPower.musicalEquiv k (σ y)) x (X x))
      (_root_.exteriorPower.musicalEquiv k (τ x)) +
      (alternatingRiemannianMetric (F := F) V k).inner x
        (_root_.exteriorPower.musicalEquiv k (σ x))
        (CovariantDerivative.alternating cov k
          (fun y => _root_.exteriorPower.musicalEquiv k (τ y)) x (X x)) =
      (k.factorial : ℝ) * inner ℝ (cov.exteriorPower k σ x (X x)) (τ x) +
        (k.factorial : ℝ) * inner ℝ (σ x) (cov.exteriorPower k τ x (X x)) := by
    exact congrArg₂ (fun v w =>
      (alternatingRiemannianMetric (F := F) V k).inner x v
        (_root_.exteriorPower.musicalEquiv k (τ x)) +
      (alternatingRiemannianMetric (F := F) V k).inner x
        (_root_.exteriorPower.musicalEquiv k (σ x)) w) hDσ.symm hDτ.symm |>.trans
      (congrArg₂ (· + ·) (hinner x (cov.exteriorPower k σ x (X x)) (τ x))
        (hinner x (σ x) (cov.exteriorPower k τ x (X x))))
  have hg := hg.trans hterms
  have hd := mvfderiv_smul (I := I) (a := fun _ : M => (k.factorial : ℝ))
    (mdifferentiableAt_const (c := (k.factorial : ℝ))) (hσ.inner_bundle hτ)
  simp only [mvfderiv_const, ContinuousLinearMap.zero_smulRight, add_zero] at hd
  change mvfderiv (I := I) (fun y => (k.factorial : ℝ) * inner ℝ (σ y) (τ y)) x =
    (k.factorial : ℝ) • mvfderiv (I := I) (fun y => inner ℝ (σ y) (τ y)) x at hd
  change mvfderiv (I := I) (fun y => (k.factorial : ℝ) * inner ℝ (σ y) (τ y)) x (X x) =
    (k.factorial : ℝ) * inner ℝ (cov.exteriorPower k σ x (X x)) (τ x) +
      (k.factorial : ℝ) * inner ℝ (σ x) (cov.exteriorPower k τ x (X x)) at hg
  rw [hd, smul_apply, smul_eq_mul, ← mul_add] at hg
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr k.factorial_ne_zero) hg

end CovariantDerivative
