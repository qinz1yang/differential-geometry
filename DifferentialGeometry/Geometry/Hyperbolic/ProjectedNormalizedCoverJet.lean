/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.UniversalCover
import DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph
import DifferentialGeometry.Geometry.Exponential.HyperbolicComparisonFirstJet

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isLocalDiffeomorph_proj_normalizedUniversalCoverIsometryEquiv
    (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (κ : ℝ) (hκ : κ < 0) (x₀ : M)
    (hsec : ∀ (x : M) (X Y : TangentSpace I x),
      Curvature.metricRm04StandardAt g x X Y Y X =
        κ * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)) :
    letI -zeta : Inhabited M := ⟨x₀⟩
    letI -zeta : LocallyPathConnectedSpace H :=
      I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI -zeta : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI -zeta : SemilocallySimplyConnectedSpace M :=
      manifold_semilocallySimplyConnectedSpace (I := I)
    letI -zeta : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI -zeta : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ :=
      UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
    letI -zeta : IsManifold I 1 (UniversalCover M) :=
      IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
    letI -zeta : TopologicalSpace.MetrizableSpace (UniversalCover M) :=
      Manifold.metrizableSpace I (UniversalCover M)
    letI -zeta : T3Space (UniversalCover M) := inferInstance
    letI -zeta : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) :=
      ⟨ĝ.toRiemannianMetric⟩
    letI -zeta : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI -zeta : EMetricSpace (UniversalCover M) :=
      EMetricSpace.ofRiemannianMetric I (UniversalCover M)
    letI -zeta : PseudoEMetricSpace (UniversalCover M) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
    letI -zeta : CompleteSpace (UniversalCover M) := hĝ.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))),
      IsLocalDiffeomorph 𝓘(ℝ, E₃) I ∞ (fun z => UniversalCover.proj
        (normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i z)) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ :=
    UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) :=
    Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) :=
    ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  dsimp only
  intro i
  let _ : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩
  let e := normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i
  have heq : (e : Hyperboloid E₃ → UniversalCover M) =
      Riemannian.Exponential.hyperbolicComparison ĝ hĝ UniversalCover.basePoint i :=
    funext (normalizedUniversalCoverIsometryEquiv_apply g hg κ hκ x₀ hsec i)
  have he : IsLocalDiffeomorph 𝓘(ℝ, E₃) I ∞ (e : Hyperboloid E₃ → UniversalCover M) := by
    rw [heq]
    exact Riemannian.Exponential.isLocalDiffeomorph_hyperbolicComparison ĝ hĝ
      UniversalCover.basePoint (normalized_lifted_riemannOp g κ hκ hsec) i
  intro x
  exact (he x).comp I M (UniversalCover.proj_localDiffeo (I := I) (e x))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem proj_normalizedUniversalCoverIsometryEquiv_inner
    (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (κ : ℝ) (hκ : κ < 0) (x₀ : M)
    (hsec : ∀ (x : M) (X Y : TangentSpace I x),
      Curvature.metricRm04StandardAt g x X Y Y X =
        κ * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)) :
    letI -zeta : Inhabited M := ⟨x₀⟩
    letI -zeta : LocallyPathConnectedSpace H :=
      I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI -zeta : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI -zeta : SemilocallySimplyConnectedSpace M :=
      manifold_semilocallySimplyConnectedSpace (I := I)
    letI -zeta : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI -zeta : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ :=
      UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
    letI -zeta : IsManifold I 1 (UniversalCover M) :=
      IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
    letI -zeta : TopologicalSpace.MetrizableSpace (UniversalCover M) :=
      Manifold.metrizableSpace I (UniversalCover M)
    letI -zeta : T3Space (UniversalCover M) := inferInstance
    letI -zeta : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) :=
      ⟨ĝ.toRiemannianMetric⟩
    letI -zeta : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI -zeta : EMetricSpace (UniversalCover M) :=
      EMetricSpace.ofRiemannianMetric I (UniversalCover M)
    letI -zeta : PseudoEMetricSpace (UniversalCover M) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
    letI -zeta : CompleteSpace (UniversalCover M) := hĝ.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M)))
      (y : Hyperboloid E₃) (v w : TangentSpace 𝓘(ℝ, E₃) y),
      Hyperboloid.riemannianMetric.inner y v w =
        (scaleMetric (-κ) (neg_pos.mpr hκ) g).inner
          (UniversalCover.proj (normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i y))
          (mfderiv 𝓘(ℝ, E₃) I (fun z => UniversalCover.proj
            (normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i z)) y v)
          (mfderiv 𝓘(ℝ, E₃) I (fun z => UniversalCover.proj
            (normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i z)) y w) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ :=
    UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) :=
    Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) :=
    ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  dsimp only
  intro i y v w
  let _ : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩
  let e := normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i
  have heq : (e : Hyperboloid E₃ → UniversalCover M) =
      Riemannian.Exponential.hyperbolicComparison ĝ hĝ UniversalCover.basePoint i :=
    funext (normalizedUniversalCoverIsometryEquiv_apply g hg κ hκ x₀ hsec i)
  have hed : MDifferentiableAt 𝓘(ℝ, E₃) I (e : Hyperboloid E₃ → UniversalCover M) y := by
    rw [heq]
    exact (Riemannian.Exponential.contMDiff_hyperbolicComparison ĝ hĝ
      UniversalCover.basePoint i).mdifferentiableAt (by simp)
  have hpd := UniversalCover.hasMFDerivAt_proj (I := I) (M := M) (e y)
  have hd (u : E₃) : mfderiv 𝓘(ℝ, E₃) I (fun z => UniversalCover.proj (e z)) y u =
      mfderiv 𝓘(ℝ, E₃) I (e : Hyperboloid E₃ → UniversalCover M) y u := by
    have hc := (hpd.comp y hed.hasMFDerivAt).mfderiv
    exact congrArg (fun L : E₃ →L[ℝ] E₃ => L u) hc
  have hin := Riemannian.Exponential.hyperbolicComparison_inner ĝ hĝ
    UniversalCover.basePoint (normalized_lifted_riemannOp g κ hκ hsec) i y v w
  have hfin : Hyperboloid.riemannianMetric.inner y v w =
      gN.inner (UniversalCover.proj (e y))
        (mfderiv 𝓘(ℝ, E₃) I (fun z => UniversalCover.proj (e z)) y v)
        (mfderiv 𝓘(ℝ, E₃) I (fun z => UniversalCover.proj (e z)) y w) := by
    have hinner := congrArg
      (fun f : Hyperboloid E₃ → UniversalCover M =>
        gN.inner (UniversalCover.proj (f y))
          (mfderiv 𝓘(ℝ, E₃) I f y v) (mfderiv 𝓘(ℝ, E₃) I f y w)) heq
    have hderiv := congrArg₂
      (fun a b : E₃ => gN.inner (UniversalCover.proj (e y)) a b) (hd v) (hd w)
    exact (hderiv.trans (hinner.trans hin)).symm
  exact hfin

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mfderiv_proj_normalizedUniversalCoverIsometryEquiv_origin
    (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (κ : ℝ) (hκ : κ < 0) (x₀ : M)
    (hsec : ∀ (x : M) (X Y : TangentSpace I x),
      Curvature.metricRm04StandardAt g x X Y Y X =
        κ * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)) :
    letI -zeta : Inhabited M := ⟨x₀⟩
    letI -zeta : LocallyPathConnectedSpace H :=
      I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI -zeta : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI -zeta : SemilocallySimplyConnectedSpace M :=
      manifold_semilocallySimplyConnectedSpace (I := I)
    letI -zeta : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI -zeta : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ :=
      UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
    letI -zeta : IsManifold I 1 (UniversalCover M) :=
      IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
    letI -zeta : TopologicalSpace.MetrizableSpace (UniversalCover M) :=
      Manifold.metrizableSpace I (UniversalCover M)
    letI -zeta : T3Space (UniversalCover M) := inferInstance
    letI -zeta : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) :=
      ⟨ĝ.toRiemannianMetric⟩
    letI -zeta : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI -zeta : EMetricSpace (UniversalCover M) :=
      EMetricSpace.ofRiemannianMetric I (UniversalCover M)
    letI -zeta : PseudoEMetricSpace (UniversalCover M) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
    letI -zeta : CompleteSpace (UniversalCover M) := hĝ.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))) (v : E₃),
      mfderiv 𝓘(ℝ, E₃) I (fun z => UniversalCover.proj
        (normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i z)) Hyperboloid.origin v =
          i v := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ :=
    UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) :=
    Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) :=
    ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  dsimp only
  intro i v
  let _ : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩
  let e := normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i
  have heq : (e : Hyperboloid E₃ → UniversalCover M) =
      Riemannian.Exponential.hyperbolicComparison ĝ hĝ UniversalCover.basePoint i :=
    funext (normalizedUniversalCoverIsometryEquiv_apply g hg κ hκ x₀ hsec i)
  have hed : MDifferentiableAt 𝓘(ℝ, E₃) I (e : Hyperboloid E₃ → UniversalCover M)
      Hyperboloid.origin := by
    rw [heq]
    exact (Riemannian.Exponential.contMDiff_hyperbolicComparison ĝ hĝ
      UniversalCover.basePoint i).mdifferentiableAt (by simp)
  have hpd := UniversalCover.hasMFDerivAt_proj (I := I) (M := M) (e Hyperboloid.origin)
  have hd : mfderiv 𝓘(ℝ, E₃) I (fun z => UniversalCover.proj (e z)) Hyperboloid.origin v =
      mfderiv 𝓘(ℝ, E₃) I (e : Hyperboloid E₃ → UniversalCover M) Hyperboloid.origin v := by
    have hc := (hpd.comp Hyperboloid.origin hed.hasMFDerivAt).mfderiv
    exact congrArg (fun L : E₃ →L[ℝ] E₃ => L v) hc
  have hfin :
      mfderiv 𝓘(ℝ, E₃) I (fun z => UniversalCover.proj (e z)) Hyperboloid.origin v = i v := by
    have hderiv := congrArg
      (fun f : Hyperboloid E₃ → UniversalCover M =>
        (mfderiv 𝓘(ℝ, E₃) I f Hyperboloid.origin v : E₃)) heq
    exact hd.trans (hderiv.trans
      (Riemannian.Exponential.hyperbolicComparison_mfderiv_origin ĝ hĝ
        UniversalCover.basePoint i v))
  exact hfin

end DifferentialGeometry.Geometry.Hyperbolic
