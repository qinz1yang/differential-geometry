import DifferentialGeometry.Geometry.Measure.LocalIsometrySection
import DifferentialGeometry.Geometry.Hyperbolic.DeckRepresentation
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Proper
import DifferentialGeometry.Geometry.Metric.Isometry.Topology
import DifferentialGeometry.Geometry.Measure.UniversalCover
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

noncomputable section

open scoped Manifold ContDiff Bundle
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

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

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem lifted_inner_proj [Inhabited M] [LocallyPathConnectedSpace M]
    [SemilocallySimplyConnectedSpace M] (g : SmoothRiemannianMetric I M)
    (x : UniversalCover M) (v w : TangentSpace I x) :
    (UniversalCover.liftedMetric (I := I) g).inner x v w =
      g.inner (UniversalCover.proj x) (mfderiv I I UniversalCover.proj x v)
        (mfderiv I I UniversalCover.proj x w) := by
  rw [(UniversalCover.hasMFDerivAt_proj (I := I) x).mfderiv]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_normalized_universal_cover_fundamental_domain_volume_eq (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (κ : ℝ) (hκ : κ < 0) (x₀ : M)
    (hsec : ∀ (x : M) (X Y : TangentSpace I x),
      Curvature.metricRm04StandardAt g x X Y Y X =
        κ * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)) :
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
      ∃ D : Set (Hyperboloid E₃), MeasurableSet D ∧
        (∀ z : Hyperboloid E₃, ∃! a :
          (normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i).range, a • z ∈ D) ∧
        MeasureTheory.IsFundamentalDomain
          (normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i).range D
          (riemannianVolumeMeasure 𝓘(ℝ, E₃) (Hyperboloid E₃) Hyperboloid.riemannianMetric) ∧
        riemannianVolumeMeasure 𝓘(ℝ, E₃) (Hyperboloid E₃) Hyperboloid.riemannianMetric D =
          ENNReal.ofReal (Real.sqrt (-κ)) ^ 3 * riemannianVolumeMeasure I M g Set.univ := by
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
  let e := normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let pH : Hyperboloid E₃ → M := fun z => UniversalCover.proj (e z)
  have heq : (e : Hyperboloid E₃ → UniversalCover M) =
      Riemannian.Exponential.hyperbolicComparison ĝ hĝ UniversalCover.basePoint i := by
    funext z
    exact normalizedUniversalCoverIsometryEquiv_apply g hg κ hκ x₀ hsec i z
  have helocal : IsLocalDiffeomorph 𝓘(ℝ, E₃) I ∞ e := by
    rw [heq]
    exact Riemannian.Exponential.isLocalDiffeomorph_hyperbolicComparison ĝ hĝ
      UniversalCover.basePoint (normalized_lifted_riemannOp g κ hκ hsec) i
  have hplocal : IsLocalDiffeomorph 𝓘(ℝ, E₃) I ∞ pH :=
    isLocalDiffeomorph_comp UniversalCover.proj_localDiffeo helocal
  have honto : Function.Surjective pH := by
    let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
    intro y
    let q : UniversalCover M :=
      ⟨y, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ y)⟩
    refine ⟨e.symm q, ?_⟩
    change UniversalCover.proj (e (e.symm q)) = y
    rw [e.apply_symm_apply]
    rfl
  have hmetric (z : Hyperboloid E₃) (v w : TangentSpace 𝓘(ℝ, E₃) z) :
      Hyperboloid.riemannianMetric.inner z v w =
        gN.inner (pH z) (mfderiv 𝓘(ℝ, E₃) I pH z v) (mfderiv 𝓘(ℝ, E₃) I pH z w) := by
    have heinner : ĝ.inner (e z) (mfderiv 𝓘(ℝ, E₃) I e z v)
        (mfderiv 𝓘(ℝ, E₃) I e z w) = Hyperboloid.riemannianMetric.inner z v w := by
      rw [heq]
      exact Riemannian.Exponential.hyperbolicComparison_inner ĝ hĝ UniversalCover.basePoint
        (normalized_lifted_riemannOp g κ hκ hsec) i z v w
    have hd (u : TangentSpace 𝓘(ℝ, E₃) z) :
        mfderiv 𝓘(ℝ, E₃) I pH z u =
          mfderiv I I UniversalCover.proj (e z) (mfderiv 𝓘(ℝ, E₃) I e z u) :=
      mfderiv_comp_apply z
        ((UniversalCover.proj_localDiffeo (I := I) (M := M)).contMDiff.mdifferentiableAt (by simp))
        (helocal.contMDiff.mdifferentiableAt (by simp)) u
    calc
      Hyperboloid.riemannianMetric.inner z v w =
          ĝ.inner (e z) (mfderiv 𝓘(ℝ, E₃) I e z v) (mfderiv 𝓘(ℝ, E₃) I e z w) :=
        heinner.symm
      _ = gN.inner (pH z)
          (mfderiv I I UniversalCover.proj (e z) (mfderiv 𝓘(ℝ, E₃) I e z v))
          (mfderiv I I UniversalCover.proj (e z) (mfderiv 𝓘(ℝ, E₃) I e z w)) :=
        lifted_inner_proj gN (e z) _ _
      _ = gN.inner (pH z) (mfderiv 𝓘(ℝ, E₃) I pH z v)
          (mfderiv 𝓘(ℝ, E₃) I pH z w) :=
        congrArg₂ (fun a b : TangentSpace I (pH z) => gN.inner (pH z) a b)
          (hd v).symm (hd w).symm
  have hfiber (x y : Hyperboloid E₃) : pH x = pH y ↔ ∃ a : ρ.range, a • x = y := by
    constructor
    · intro hxy
      obtain ⟨γ, hγ⟩ := (UniversalCover.proj_eq_iff_smul (e x) (e y)).mp hxy
      refine ⟨⟨ρ γ, ⟨γ, rfl⟩⟩, e.injective ?_⟩
      exact (normalizedUniversalCoverIsometryEquiv_deckRepresentation
        g hg κ hκ x₀ hsec i γ x).trans hγ
    · rintro ⟨a, ha⟩
      obtain ⟨γ, hγ⟩ := a.property
      have hpres : pH (a • x) = pH x := by
        change pH ((a : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) x) = pH x
        rw [← hγ]
        exact proj_normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i γ x
      exact hpres.symm.trans (congrArg pH ha)
  have hfree (a : ρ.range) (ha : a ≠ 1) (z : Hyperboloid E₃) : a • z ≠ z := by
    intro hz
    obtain ⟨γ, hγ⟩ := a.property
    change (a : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) z = z at hz
    rw [← hγ] at hz
    have hfix : @UniversalCover.deckAct M _ ⟨x₀⟩ γ (e z) = e z :=
      (normalizedUniversalCoverIsometryEquiv_deckRepresentation
        g hg κ hκ x₀ hsec i γ z).symm.trans (congrArg e hz)
    have hγone : γ = 1 :=
      (@UniversalCover.deckAct_eq_self_iff M _ ⟨x₀⟩ γ (e z)).mp hfix
    apply ha
    apply Subtype.ext
    rw [← hγ, hγone, map_one]
    rfl
  obtain ⟨D, hD, hrep, hfund, hvol⟩ :=
    Geometry.Measure.exists_fundamental_domain_volume_eq_of_surjective_local_isometry
      Hyperboloid.riemannianMetric gN pH hplocal honto hmetric hfiber hfree
  refine ⟨D, hD, hrep, hfund, hvol.trans ?_⟩
  simpa [gN, finrank_euclideanSpace] using
    Integral.Measure.volume_scale_apply (-κ) (neg_pos.mpr hκ) g Set.univ

end DifferentialGeometry.Geometry.Hyperbolic
