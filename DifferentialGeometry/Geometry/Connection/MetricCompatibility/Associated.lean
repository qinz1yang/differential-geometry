import DifferentialGeometry.Geometry.Connection.Associated
import DifferentialGeometry.Geometry.Metric.Associated
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

noncomputable section

open Set Bundle
open scoped Manifold ContDiff Bundle


namespace ContRepresentation

variable {G B W : Type*} [Group G]
  [TopologicalSpace G] [TopologicalSpace B] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {P : B → Type*} [∀ x, Torsor G (P x)] [∀ x, TopologicalSpace (P x)]
  [TopologicalSpace (TotalSpace G P)] [FiberBundle G P] [IsPrincipalBundle P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [ChartedSpace H B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG] (IG : ModelWithCorners ℝ EG HG) [ChartedSpace HG G]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners ℝ EP HP)
  [ChartedSpace HP (TotalSpace G P)]

theorem associatedCovariantDerivativeOfLocalSections_metric
    (ρ : ContRepresentation ℝ G W) (hρc : Continuous (fun g => ρ g))
    (hρ : MDifferentiableAt IG 𝓘(ℝ, W →L[ℝ] W) (fun g => ρ g) 1)
    (horth : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w)
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (form : ∀ p : TotalSpace G P, TangentSpace IP p →L[ℝ] GroupLieAlgebra IG G)
    (σ τ : ∀ x, P x →ₑ[ρ.toRepresentation] W) {x : B} (X : TangentSpace I x) :
    let := (ρ.associatedVectorPrebundle (P := P) hρc).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρc A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρc A hA e₀ he₀ hx₀
    let cov := ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρc A hA e₀ he₀ hx₀ form
    let metric := ρ.toRepresentation.associatedRiemannianMetric horth P
    MDifferentiableAt I (I.prod 𝓘(ℝ, W))
      (fun y => (⟨y, σ y⟩ : TotalSpace W (fun z => P z →ₑ[ρ.toRepresentation] W))) x →
    MDifferentiableAt I (I.prod 𝓘(ℝ, W))
      (fun y => (⟨y, τ y⟩ : TotalSpace W (fun z => P z →ₑ[ρ.toRepresentation] W))) x →
    mvfderiv I (fun y => metric.inner y (σ y) (τ y)) x X =
      metric.inner x (cov σ x X) (τ x) + metric.inner x (σ x) (cov τ x X) := by
  let := (ρ.associatedVectorPrebundle (P := P) hρc).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρc A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρc A hA e₀ he₀ hx₀
  dsimp only
  intro hσ hτ
  let e := e₀ x
  let u : B → W := fun y => σ y (e.principalSection y)
  let v : B → W := fun y => τ y (e.principalSection y)
  have hu : MDifferentiableAt I 𝓘(ℝ, W) u x := (mdifferentiableAt_section I σ).mp hσ
  have hv : MDifferentiableAt I 𝓘(ℝ, W) v x := (mdifferentiableAt_section I τ).mp hτ
  let L : W →L[ℝ] W →L[ℝ] ℝ := innerSL ℝ
  have hA := (mdifferentiableAt_const (c := L)).clm_apply hu
  have hd := congrArg (fun L => L X) (hA.mvfderiv_clm_apply hv)
  have hD := congrArg (fun L => L X) ((mdifferentiableAt_const (c := L)).mvfderiv_clm_apply hu)
  simp only [mvfderiv_const, ContinuousLinearMap.comp_zero, add_zero,
    ContinuousLinearMap.comp_apply] at hD
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, hD] at hd
  have hfun : (fun y => (ρ.toRepresentation.associatedRiemannianMetric horth P).inner y (σ y) (τ y)) =
      fun y => L (u y) (v y) := by
    funext y
    exact ρ.toRepresentation.associatedRiemannianMetric_inner horth P y (e.principalSection y) _ _
  rw [hfun, hd,
    ρ.toRepresentation.associatedRiemannianMetric_inner horth P x (e.principalSection x),
    ρ.toRepresentation.associatedRiemannianMetric_inner horth P x (e.principalSection x),
    ρ.associatedCovariantDerivativeOfLocalSections_apply,
    ρ.associatedCovariantDerivativeOfLocalSections_apply]
  simp only [e, sdiv_self, map_one, one_apply_eq_self]
  let U : GroupLieAlgebra IG G := form ⟨x, e.principalSection x⟩
    (mfderiv I IP (fun y => (⟨y, e.principalSection y⟩ : TotalSpace G P)) x X)
  have hz := ρ.inner_mvfderiv_one hρ horth U (u x) (v x)
  change inner ℝ (u x) (mvfderiv I v x X) + inner ℝ (mvfderiv I u x X) (v x) =
    inner ℝ (mvfderiv I u x X - mvfderiv IG (fun g => ρ g) 1 U (u x)) (v x) +
    inner ℝ (u x) (mvfderiv I v x X - mvfderiv IG (fun g => ρ g) 1 U (v x))
  rw [inner_sub_left, inner_sub_right]
  linarith

theorem isMetricCompatible_associatedCovariantDerivativeOfLocalSections
    [FiniteDimensional ℝ W] [IsManifold I 1 B]
    (ρ : ContRepresentation ℝ G W)
    (hρ : ContMDiff IG 𝓘(ℝ, W →L[ℝ] W) 1 (fun g => ρ g))
    (horth : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w)
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ∀ e' ∈ A,
      ContMDiffOn I IG 1 (fun x => e'.principalSection x /ₛ e.principalSection x)
        (e.baseSet ∩ e'.baseSet))
    (form : ∀ p : TotalSpace G P, TangentSpace IP p →L[ℝ] GroupLieAlgebra IG G) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_contMDiffVectorBundle_of_atlas I IG 1 hρ A hA e₀ he₀ hx₀ hP
    let metric := ρ.associatedContMDiffRiemannianMetric I 1 hρ.continuous horth A hA e₀ he₀ hx₀
    letI : RiemannianBundle (fun x => P x →ₑ[ρ.toRepresentation] W) := ⟨metric.toRiemannianMetric⟩
    letI : ∀ x, NormedAddCommGroup (P x →ₑ[ρ.toRepresentation] W) := fun x =>
      (metric.toRiemannianMetric.toCore x).toNormedAddCommGroupOfTopology
        (metric.toRiemannianMetric.continuousAt x) (metric.toRiemannianMetric.isVonNBounded x)
    letI : ∀ x, InnerProductSpace ℝ (P x →ₑ[ρ.toRepresentation] W) := fun x =>
      InnerProductSpace.ofCoreOfTopology (metric.toRiemannianMetric.toCore x)
        (metric.toRiemannianMetric.continuousAt x) (metric.toRiemannianMetric.isVonNBounded x)
    CovariantDerivative.IsMetricCompatible (I := I) (F := W)
      (V := fun x => P x →ₑ[ρ.toRepresentation] W)
      (ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₀ he₀ hx₀ form) := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_contMDiffVectorBundle_of_atlas I IG 1 hρ A hA e₀ he₀ hx₀ hP
  let metric := ρ.associatedContMDiffRiemannianMetric I 1 hρ.continuous horth A hA e₀ he₀ hx₀
  let : RiemannianBundle (fun x => P x →ₑ[ρ.toRepresentation] W) := ⟨metric.toRiemannianMetric⟩
  let : ∀ x, NormedAddCommGroup (P x →ₑ[ρ.toRepresentation] W) := fun x =>
      (metric.toRiemannianMetric.toCore x).toNormedAddCommGroupOfTopology
        (metric.toRiemannianMetric.continuousAt x) (metric.toRiemannianMetric.isVonNBounded x)
  let : ∀ x, InnerProductSpace ℝ (P x →ₑ[ρ.toRepresentation] W) := fun x =>
      InnerProductSpace.ofCoreOfTopology (metric.toRiemannianMetric.toCore x)
        (metric.toRiemannianMetric.continuousAt x) (metric.toRiemannianMetric.isVonNBounded x)
  let : IsContMDiffRiemannianBundle I 1 W (fun x => P x →ₑ[ρ.toRepresentation] W) := inferInstance
  apply (CovariantDerivative.isMetricCompatible_iff _).mpr
  intro x X σ τ _hX hσ hτ
  exact ρ.associatedCovariantDerivativeOfLocalSections_metric I IG IP hρ.continuous
    (hρ.contMDiffAt.mdifferentiableAt (by simp)) horth A hA e₀ he₀ hx₀ form σ τ (X x) hσ hτ

theorem isMetricCompatible_associatedCovariantDerivative [IsManifold IP 1 (TotalSpace G P)]
    {n : ℕ∞ω}
    [FiniteDimensional ℝ W] [IsManifold I 1 B]
    (ρ : ContRepresentation ℝ G W)
    (hρ : ContMDiff IG 𝓘(ℝ, W →L[ℝ] W) 1 (fun g => ρ g))
    (horth : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w)
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ∀ e' ∈ A,
      ContMDiffOn I IG 1 (fun x => e'.principalSection x /ₛ e.principalSection x)
        (e.baseSet ∩ e'.baseSet))
    (form : PrincipalConnectionForm IG G IP P n) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_contMDiffVectorBundle_of_atlas I IG 1 hρ A hA e₀ he₀ hx₀ hP
    let metric := ρ.associatedContMDiffRiemannianMetric I 1 hρ.continuous horth A hA e₀ he₀ hx₀
    letI : RiemannianBundle (fun x => P x →ₑ[ρ.toRepresentation] W) := ⟨metric.toRiemannianMetric⟩
    letI : ∀ x, NormedAddCommGroup (P x →ₑ[ρ.toRepresentation] W) := fun x =>
      (metric.toRiemannianMetric.toCore x).toNormedAddCommGroupOfTopology
        (metric.toRiemannianMetric.continuousAt x) (metric.toRiemannianMetric.isVonNBounded x)
    letI : ∀ x, InnerProductSpace ℝ (P x →ₑ[ρ.toRepresentation] W) := fun x =>
      InnerProductSpace.ofCoreOfTopology (metric.toRiemannianMetric.toCore x)
        (metric.toRiemannianMetric.continuousAt x) (metric.toRiemannianMetric.isVonNBounded x)
    CovariantDerivative.IsMetricCompatible (I := I) (F := W)
      (V := fun x => P x →ₑ[ρ.toRepresentation] W)
      (ρ.associatedCovariantDerivative I IG IP hρ.continuous A hA e₀ he₀ hx₀ form) :=
  ρ.isMetricCompatible_associatedCovariantDerivativeOfLocalSections I IG IP hρ horth A hA e₀ he₀ hx₀ hP
    form.toFun

end ContRepresentation
