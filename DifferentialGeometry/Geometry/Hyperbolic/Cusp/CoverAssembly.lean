/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.NormalizedCoverFrame
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.CoverCommutation
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.SliceLift
import DifferentialGeometry.Geometry.Hyperbolic.UniversalCoverMetric
import DifferentialGeometry.Geometry.Hyperbolic.ProjectedNormalizedCoverJet

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Bundle

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

local notation "V₂" => Fin 2 → ℝ
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {H : FiniteVolumeHyperbolicModel}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_native_cover_square_of_curvature_identity
    (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    (hsec : ∀ (x : H.Carrier) (X Y : TangentSpace (𝓡 3) x),
      Geometry.Curvature.metricRm04StandardAt H.metric x X Y Y X =
        -(1 / 4 : ℝ) * (H.metric.inner x X X * H.metric.inner x Y Y -
          H.metric.inner x X Y * H.metric.inner x X Y))
    (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ q : C(V₂, Torus), ∃ P : C(Hyperboloid E₃, H.Carrier),
      IsCoveringMap q ∧ Function.Surjective q ∧ IsCoveringMap P ∧
      ∀ (r : ℝ) (_ : 0 < r) (z : V₂),
        P (modelSlice r₀ r z) = Tr.cuspMap i (q z, halfSpaceOneLift r) := by
  obtain ⟨q, hq, hqs, hql, hqmetric⟩ := (Tr.cusp i).exists_orthonormal_cover_projection
  have hqSmooth := hql.contMDiff
  let x₀ := positiveMap Tr i q (basePoint r₀ hr₀)
  let κ : ℝ := -(1 / 4)
  have hκ : κ < 0 := by norm_num [κ]
  let _ : Inhabited H.Carrier := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace E₃ :=
    (𝓡 3).toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace H.Carrier :=
    ChartedSpace.locallyPathConnectedSpace E₃ H.Carrier
  let _ : SemilocallySimplyConnectedSpace H.Carrier :=
    manifold_semilocallySimplyConnectedSpace (I := 𝓡 3)
  let _ : SecondCountableTopology E₃ := ModelWithCorners.secondCountableTopology (𝓡 3)
  let _ : SecondCountableTopology H.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact E₃ H.Carrier
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) H.metric
  let ĝ := UniversalCover.liftedMetric (I := 𝓡 3) gN
  let hĝ : RiemannianMetricComplete ĝ :=
    UniversalCover.liftedMetric_complete gN (H.complete.scaleMetric _ _)
  let _ : IsManifold (𝓡 3) 1 (UniversalCover H.Carrier) :=
    IsManifold.of_le (I := 𝓡 3) (M := UniversalCover H.Carrier) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover H.Carrier) :=
    Manifold.metrizableSpace (𝓡 3) (UniversalCover H.Carrier)
  let _ : T3Space (UniversalCover H.Carrier) := inferInstance
  let _ : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : UniversalCover H.Carrier → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃
      (TangentSpace (𝓡 3) : UniversalCover H.Carrier → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover H.Carrier) :=
    EMetricSpace.ofRiemannianMetric (𝓡 3) (UniversalCover H.Carrier)
  let _ : PseudoEMetricSpace (UniversalCover H.Carrier) :=
    (EMetricSpace.ofRiemannianMetric (𝓡 3) (UniversalCover H.Carrier)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover H.Carrier) := hĝ.complete
  let _ : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩
  obtain ⟨frame, hframe⟩ :=
    exists_normalized_cover_frame Tr i hqSmooth hqmetric r₀ hr₀
  let e := normalizedUniversalCoverIsometryEquiv H.metric H.complete κ hκ x₀ hsec frame
  let P : Hyperboloid E₃ → H.Carrier := fun y => UniversalCover.proj (e y)
  have hP : IsLocalDiffeomorph 𝓘(ℝ, E₃) (𝓡 3) ∞ P :=
    isLocalDiffeomorph_proj_normalizedUniversalCoverIsometryEquiv
      H.metric H.complete κ hκ x₀ hsec frame
  have hPcover : IsCoveringMap P :=
    isCoveringMap_proj_normalizedUniversalCoverIsometryEquiv
      H.metric H.complete κ hκ x₀ hsec frame
  have hPmetric (y : Hyperboloid E₃) (v w : E₃) :
      Hyperboloid.riemannianMetric.inner y v w = gN.inner (P y)
        (mfderiv 𝓘(ℝ, E₃) (𝓡 3) P y v) (mfderiv 𝓘(ℝ, E₃) (𝓡 3) P y w) :=
    proj_normalizedUniversalCoverIsometryEquiv_inner
      H.metric H.complete κ hκ x₀ hsec frame y v w
  have hPbase : P Hyperboloid.origin = positiveMap Tr i q (basePoint r₀ hr₀) :=
    proj_normalizedUniversalCoverIsometryEquiv_origin
      H.metric H.complete κ hκ x₀ hsec frame
  have hPjet (v : E₃) : mfderiv 𝓘(ℝ, E₃) (𝓡 3) P Hyperboloid.origin v =
      comparisonFrame Tr i hqSmooth hqmetric r₀ (basePoint r₀ hr₀) v :=
    (mfderiv_proj_normalizedUniversalCoverIsometryEquiv_origin
      H.metric H.complete κ hκ x₀ hsec frame v).trans (hframe v)
  have hcomm := positiveMap_eq_cover_comp_of_first_jet Tr i hqSmooth hqmetric
    r₀ hr₀ P hP hPmetric hPbase hPjet
  refine ⟨⟨q, hqSmooth.continuous⟩, ⟨P, hP.contMDiff.continuous⟩, hq, hqs, hPcover, ?_⟩
  intro r hr z
  exact modelSlice_cover_square Tr i q r₀ r hr P hcomm z

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
