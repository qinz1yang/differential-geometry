import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Haar
import DifferentialGeometry.Geometry.Hyperbolic.NormalizedFundamentalDomain
import DifferentialGeometry.Geometry.Hyperbolic.DeckGroup
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.ProjectiveOrthogonalGroup

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)
open DifferentialGeometry.ProjectiveOrthogonalGroup (PO)

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private instance : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace (Hyperboloid E₃) := borel (Hyperboloid E₃)
private local instance : BorelSpace (Hyperboloid E₃) := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hasFundamentalDomain_and_covolume_ne_top_normalized_universal_cover (g : SmoothRiemannianMetric I M)
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
      MeasureTheory.HasFundamentalDomain ρ.range (PO 3 1) ∧
        MeasureTheory.covolume ρ.range (PO 3 1) ≠ ⊤ := by
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
  let Φ := Hyperboloid.projectiveOrthogonalGroupEquiv 2
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let _ : DiscreteTopology ρ.range :=
    discreteTopology_range_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let _ : SecondCountableTopology (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) :=
    Φ.toHomeomorph.secondCountableTopology
  let _ : Countable ρ.range := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  obtain ⟨D, hD, hrep, _, hvolume⟩ :=
    exists_normalized_universal_cover_fundamental_domain_volume_eq g hg κ hκ x₀ hsec i
  have hfin : riemannianVolumeMeasure 𝓘(ℝ, E₃) (Hyperboloid E₃)
      Hyperboloid.riemannianMetric D ≠ ⊤ := by
    rw [hvolume]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hvol.ne
  have h := Hyperboloid.hasFundamentalDomain_and_covolume_ne_top_map_of_fundamental_domain
    Φ (MeasureTheory.volume : MeasureTheory.Measure (PO 3 1)) ρ.range hD hrep hfin
  change MeasureTheory.HasFundamentalDomain (Φ.toMulEquiv.toMonoidHom.comp ρ).range (PO 3 1) ∧
    MeasureTheory.covolume (Φ.toMulEquiv.toMonoidHom.comp ρ).range (PO 3 1) ≠ ⊤
  rw [MonoidHom.range_comp]
  exact h

end DifferentialGeometry.Geometry.Hyperbolic
