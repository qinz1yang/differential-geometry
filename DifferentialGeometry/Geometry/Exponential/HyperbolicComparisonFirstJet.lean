/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Exponential.HyperbolicComparison
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Exponential
import DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero.IntrinsicDerivative

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem hyperboloid_expMapIntrinsicOriginDiffeomorph_symm_origin :
    (Hyperboloid.expMapIntrinsicOriginDiffeomorph (E := E)).symm Hyperboloid.origin = 0 := by
  rw [Hyperboloid.expMapIntrinsicOriginDiffeomorph_symm_apply, Hyperboloid.origin_space,
    smul_zero]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hyperbolicComparison_origin (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (p : M) :
    letI -zeta : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    letI -zeta : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI -zeta : T3Space M := inferInstance
    letI -zeta : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI -zeta : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI -zeta : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI -zeta : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI -zeta : CompleteSpace M := hg.complete
    ∀ (i : E ≃ₗᵢ[ℝ] TangentSpace I p),
      hyperbolicComparison g hg p i Hyperboloid.origin = p := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let _ : CompleteSpace M := hg.complete
  let hEnorm : IsMetricNorm (I := I) g :=
    fun x w => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x w
  dsimp only
  intro i
  rw [hyperbolicComparison_apply, hyperboloid_expMapIntrinsicOriginDiffeomorph_symm_origin,
    map_zero]
  exact expMapIntrinsic_zero (I := I) g hEnorm p

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hyperbolicComparison_mfderiv_origin (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (p : M) :
    letI -zeta : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    letI -zeta : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI -zeta : T3Space M := inferInstance
    letI -zeta : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI -zeta : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI -zeta : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI -zeta : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI -zeta : CompleteSpace M := hg.complete
    ∀ (i : E ≃ₗᵢ[ℝ] TangentSpace I p) (v : E),
      mfderiv 𝓘(ℝ, E) I (hyperbolicComparison g hg p i) Hyperboloid.origin v = i v := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let _ : CompleteSpace M := hg.complete
  let hEnorm : IsMetricNorm (I := I) g :=
    fun x w => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x w
  let _ : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) :=
    ⟨(Hyperboloid.riemannianMetric (E := E)).toContinuousRiemannianMetric.toRiemannianMetric⟩
  let hHNorm := isMetricNorm_of_riemannianBundle (Hyperboloid.riemannianMetric (E := E))
  let _ : IsRiemannianManifold 𝓘(ℝ, E) (Hyperboloid E) :=
    ⟨fun a b => (Hyperboloid.riemannianEDistOf_eq_edist a b).symm⟩
  let _ : IsContinuousRiemannianBundle E
      (TangentSpace 𝓘(ℝ, E) : Hyperboloid E → Type _) := hHNorm.isContinuousRiemannianBundle
  dsimp only
  intro i v
  let j : E ≃L[ℝ] E := (show E ≃ₗ[ℝ] E from i.toLinearEquiv).toContinuousLinearEquiv
  have hsymm0 := hyperboloid_expMapIntrinsicOriginDiffeomorph_symm_origin (E := E)
  have hmodel : (fun a : E => expMapIntrinsic (I := 𝓘(ℝ, E))
      (Hyperboloid.riemannianMetric (E := E)) hHNorm Hyperboloid.origin
      (show TangentSpace 𝓘(ℝ, E) (Hyperboloid.origin : Hyperboloid E) from a)) =
        (Hyperboloid.expMapIntrinsicOriginDiffeomorph (E := E) : E → Hyperboloid E) := by
    funext a
    rfl
  have hΦ0 := mfderiv_expMapIntrinsic_at_zero (I := 𝓘(ℝ, E))
    (Hyperboloid.riemannianMetric (E := E)) hHNorm Hyperboloid.origin
  rw [hmodel] at hΦ0
  have hid : ((Hyperboloid.expMapIntrinsicOriginDiffeomorph (E := E) : E → Hyperboloid E) ∘
      ((Hyperboloid.expMapIntrinsicOriginDiffeomorph (E := E)).symm : Hyperboloid E → E)) =
        id :=
    funext (Hyperboloid.expMapIntrinsicOriginDiffeomorph (E := E)).apply_symm_apply
  have hΦd :=
    (Hyperboloid.expMapIntrinsicOriginDiffeomorph (E := E)).contMDiff.mdifferentiableAt
      (by simp) (x := (0 : E))
  have hsd :=
    (Hyperboloid.expMapIntrinsicOriginDiffeomorph (E := E)).symm.contMDiff.mdifferentiableAt
      (by simp) (x := (Hyperboloid.origin : Hyperboloid E))
  have hsymm : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      ((Hyperboloid.expMapIntrinsicOriginDiffeomorph (E := E)).symm : Hyperboloid E → E)
      Hyperboloid.origin v = v := by
    have hc := mfderiv_comp_apply_of_eq Hyperboloid.origin hΦd hsd hsymm0 v
    rw [hid, mfderiv_id, hΦ0] at hc
    exact hc.symm
  have hjd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (j : E → E)
      ((Hyperboloid.expMapIntrinsicOriginDiffeomorph (E := E)).symm Hyperboloid.origin) :=
    j.mdifferentiableAt
  have hjsd := hjd.comp Hyperboloid.origin hsd
  have hy : ((j : E → E) ∘
      ((Hyperboloid.expMapIntrinsicOriginDiffeomorph (E := E)).symm : Hyperboloid E → E))
        Hyperboloid.origin = 0 :=
    (DFunLike.congr_arg j hsymm0).trans (map_zero j)
  have hexpd := (intrinsicFiber_smooth g hEnorm p).mdifferentiableAt (by simp) (x := (0 : E))
  have hstep := mfderiv_comp_apply_of_eq Hyperboloid.origin hexpd hjsd hy v
  rw [mfderiv_expMapIntrinsic_at_zero (I := I) g hEnorm p,
    mfderiv_comp_apply Hyperboloid.origin hjd hsd v, ContinuousLinearEquiv.mfderiv_eq,
    hsymm] at hstep
  have hF : (hyperbolicComparison g hg p i : Hyperboloid E → M) =
      (fun u : E => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from u)) ∘
        ((j : E → E) ∘
          ((Hyperboloid.expMapIntrinsicOriginDiffeomorph (E := E)).symm :
            Hyperboloid E → E)) := by
    funext x
    exact hyperbolicComparison_apply g hg p i x
  rw [hF]
  exact hstep

end DifferentialGeometry.Geometry.Riemannian.Exponential
