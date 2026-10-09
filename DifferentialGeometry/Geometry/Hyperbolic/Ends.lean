import DifferentialGeometry.Geometry.Hyperbolic.HaarCovolume
import DifferentialGeometry.Geometry.Hyperbolic.Quotient
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.ProjectiveQuotient
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Ends
import Mathlib.Topology.DiscreteSubset

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)
open DifferentialGeometry.ProjectiveOrthogonalGroup (PO)

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open DifferentialGeometry.Geometry.Topology (endCount endCount_homeomorph)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private instance : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem endCount_eq_cuspCount_normalized_universal_cover (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (κ : ℝ) (hκ : κ < 0) (x₀ : M)
    (hsec : ∀ (x : M) (X Y : TangentSpace I x),
      Curvature.metricRm04StandardAt g x X Y Y X =
        κ * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y))
    (hvol : riemannianVolumeMeasure I M g Set.univ < ⊤) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
    letI : IsManifold I 1 (UniversalCover M) :=
      IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
    letI : T3Space (UniversalCover M) := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
    letI : PseudoEMetricSpace (UniversalCover M) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
    letI : CompleteSpace (UniversalCover M) := hĝ.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))),
      let ρ := (Hyperboloid.projectiveOrthogonalGroupEquiv 2).toMulEquiv.toMonoidHom.comp
        (normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i)
      endCount M = CuspCorrespondence.cuspCount (by decide : 1 ≤ 3) ρ.range := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  dsimp only
  intro i
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let Φ := Hyperboloid.projectiveOrthogonalGroupEquiv 2
  let σ := Φ.toMulEquiv.toMonoidHom.comp ρ
  let p := normalizedUniversalCoverQuotientHomeomorph g hg κ hκ x₀ hsec i
  let q := Hyperboloid.projectiveQuotientHomeomorph 2 ρ
  let _ : DiscreteTopology ρ.range :=
    discreteTopology_range_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  have hdisc : IsDiscrete (SetLike.coe σ.range) := by
    change IsDiscrete (SetLike.coe (Φ.toMulEquiv.toMonoidHom.comp ρ).range)
    rw [MonoidHom.range_comp]
    exact (SetLike.isDiscrete_iff_discreteTopology.mpr
      (inferInstance : DiscreteTopology ρ.range)).image Φ.toHomeomorph.isInducing
  obtain ⟨hfd, hcv⟩ :=
    hasFundamentalDomain_and_covolume_ne_top_normalized_universal_cover g hg κ hκ x₀ hsec hvol i
  let _ := hfd
  exact (endCount_homeomorph (q.trans p)).symm.trans
    (CuspCorrespondence.endCount_quotient_eq_cuspCount (by decide) (by decide)
      σ.range hdisc hcv)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem endCount_lt_top_of_finite_volume (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (κ : ℝ) (hκ : κ < 0)
    (hsec : ∀ (x : M) (X Y : TangentSpace I x),
      Curvature.metricRm04StandardAt g x X Y Y X =
        κ * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y))
    (hvol : riemannianVolumeMeasure I M g Set.univ < ⊤) : endCount M < ⊤ := by
  let x₀ : M := Classical.choice (inferInstance : Nonempty M)
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  let b : OrthonormalBasis (Fin 3) ℝ
      (TangentSpace I (UniversalCover.basePoint (X := M))) :=
    (stdOrthonormalBasis ℝ (TangentSpace I (UniversalCover.basePoint (X := M)))).reindex
      (finCongr (show Module.finrank ℝ
        (TangentSpace I (UniversalCover.basePoint (X := M))) = 3 from finrank_euclideanSpace_fin))
  let i := b.repr.symm
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let Φ := Hyperboloid.projectiveOrthogonalGroupEquiv 2
  let σ := Φ.toMulEquiv.toMonoidHom.comp ρ
  let _ : DiscreteTopology ρ.range :=
    discreteTopology_range_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  have hdisc : IsDiscrete (SetLike.coe σ.range) := by
    change IsDiscrete (SetLike.coe (Φ.toMulEquiv.toMonoidHom.comp ρ).range)
    rw [MonoidHom.range_comp]
    exact (SetLike.isDiscrete_iff_discreteTopology.mpr
      (inferInstance : DiscreteTopology ρ.range)).image Φ.toHomeomorph.isInducing
  obtain ⟨hfd, hcv⟩ :=
    hasFundamentalDomain_and_covolume_ne_top_normalized_universal_cover g hg κ hκ x₀ hsec hvol i
  let _ := hfd
  rw [endCount_eq_cuspCount_normalized_universal_cover g hg κ hκ x₀ hsec hvol i]
  exact CuspCorrespondence.cuspCount_lt_top (by decide) (by decide) σ.range hdisc hcv

end DifferentialGeometry.Geometry.Hyperbolic
