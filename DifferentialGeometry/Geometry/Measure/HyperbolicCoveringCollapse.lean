import DifferentialGeometry.Geometry.Hyperbolic.DeckGroup
import DifferentialGeometry.Geometry.Measure.HyperbolicComparison
import DifferentialGeometry.Geometry.Measure.UniversalCoverCollapse
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Proper

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open Riemannian.Exponential (hyperbolicComparison hyperbolicComparisonIsometryEquiv
  hyperbolicComparisonIsometryEquiv_apply hyperbolicComparisonIsometryEquiv_origin
  riemannianVolumeMeasure_ball_hyperbolicComparison)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private instance : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem nat_mul_volume_normalized_ball_le_of_short_deck_displacement
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (κ : ℝ) (hκ : κ < 0) (x₀ : M)
    (hsec : ∀ (p : M) (X Y : TangentSpace I p),
      Curvature.metricRm04StandardAt g p X Y Y X =
        κ * (g.inner p X X * g.inner p Y Y - g.inner p X Y * g.inner p X Y)) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    ∀ (γ : FundamentalGroup M (default : M)), γ ≠ 1 →
    ∀ (x : UniversalCover M) (R δ : ℝ), 0 < R → 0 ≤ δ →
      riemannianEDistOf ĝ x (γ • x) ≤ ENNReal.ofReal δ → ∀ N : ℕ,
      (N : ℝ≥0∞) * riemannianVolumeMeasure I M gN (riemannianBallOf gN (UniversalCover.proj x) R) ≤
        riemannianVolumeMeasure 𝓘(ℝ, E₃) (Hyperboloid E₃) Hyperboloid.riemannianMetric
          (Metric.ball Hyperboloid.origin (R + ((N - 1 : ℕ) : ℝ) * δ)) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  have hĝ : RiemannianMetricComplete ĝ :=
    UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  dsimp only
  intro γ hγ x R δ hRpos hδ hshort N
  have hR := normalized_lifted_riemannOp g κ hκ hsec
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro q v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  let i₀ : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M)) :=
    (stdOrthonormalBasis ℝ E₃).equiv
      (stdOrthonormalBasis ℝ (TangentSpace I (UniversalCover.basePoint (X := M)))) (finCongr rfl)
  let ρ := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i₀
  have hγinf : ¬ IsOfFinOrder γ := by
    intro hfin
    have hρfin := ρ.rangeRestrict.isOfFinOrder hfin
    have hρone := (normalizedUniversalCoverDeckRepresentation_range_isOfFinOrder_iff_eq_one
      g hg κ hκ x₀ hsec i₀ (ρ.rangeRestrict γ)).mp hρfin
    apply hγ
    apply normalizedUniversalCoverDeckRepresentation_injective g hg κ hκ x₀ hsec i₀
    exact (congrArg Subtype.val hρone).trans (map_one ρ).symm
  have hdeck := UniversalCover.nat_mul_volume_ball_le_of_short_deck_displacement
    gN γ hγinf x R δ hRpos hδ hshort N
  let i : E₃ ≃ₗᵢ[ℝ] TangentSpace I x := (stdOrthonormalBasis ℝ E₃).equiv
    (stdOrthonormalBasis ℝ (TangentSpace I x)) (finCongr rfl)
  have horigin : hyperbolicComparison ĝ hĝ x i Hyperboloid.origin = x := by
    rw [← hyperbolicComparisonIsometryEquiv_apply ĝ hĝ x hR i,
      hyperbolicComparisonIsometryEquiv_origin]
  have hvolume := riemannianVolumeMeasure_ball_hyperbolicComparison
    ĝ hĝ x hR i Hyperboloid.origin (R + ((N - 1 : ℕ) : ℝ) * δ)
  rw [horigin] at hvolume
  exact hdeck.trans_eq hvolume

private local instance : MeasurableSpace (Hyperboloid E₃) := borel (Hyperboloid E₃)
private local instance : BorelSpace (Hyperboloid E₃) := ⟨rfl⟩

theorem exists_pos_volume_normalized_ball_lt_of_short_deck_displacement
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (κ : ℝ) (hκ : κ < 0) (x₀ : M)
    (hsec : ∀ (p : M) (X Y : TangentSpace I p),
      Curvature.metricRm04StandardAt g p X Y Y X =
        κ * (g.inner p X X * g.inner p Y Y - g.inner p X Y * g.inner p X Y)) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ (x : UniversalCover M) (γ : FundamentalGroup M (default : M)),
        γ ≠ 1 → riemannianEDistOf ĝ x (γ • x) ≤ ENNReal.ofReal δ →
        riemannianVolumeMeasure I M gN (riemannianBallOf gN (UniversalCover.proj x) R) <
          ENNReal.ofReal η := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ := Integral.Measure.riemannianVolumeMeasure_isFiniteMeasureOnCompacts
    (Hyperboloid.riemannianMetric (E := E₃))
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  dsimp only
  intro R hR η hη
  let V := riemannianVolumeMeasure 𝓘(ℝ, E₃) (Hyperboloid E₃) Hyperboloid.riemannianMetric
    (Metric.ball Hyperboloid.origin (2 * R))
  have hV : V ≠ ⊤ := MeasureTheory.measure_ball_ne_top
  obtain ⟨N, hN⟩ := exists_nat_gt (V.toReal / η)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg ENNReal.toReal_nonneg hη.le) hN
  have hlarge : V < (N : ℝ≥0∞) * ENNReal.ofReal η := by
    apply (ENNReal.toReal_lt_toReal hV (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top).ne).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hη.le]
    exact (div_lt_iff₀ hη).mp hN
  refine ⟨R / N, div_pos hR hNpos, ?_⟩
  intro x γ hγ hshort
  have hbound := nat_mul_volume_normalized_ball_le_of_short_deck_displacement
    g hg κ hκ x₀ hsec γ hγ x R (R / N) hR (div_pos hR hNpos).le hshort N
  have hradius : R + ((N - 1 : ℕ) : ℝ) * (R / N) ≤ 2 * R := by
    have hn : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    have hm := mul_le_mul_of_nonneg_right hn (div_pos hR hNpos).le
    have he : (N : ℝ) * (R / N) = R := by field_simp
    rw [he] at hm
    linarith
  have hfinal : (N : ℝ≥0∞) * riemannianVolumeMeasure I M gN
      (riemannianBallOf gN (UniversalCover.proj x) R) ≤ V :=
    hbound.trans (MeasureTheory.measure_mono (Metric.ball_subset_ball hradius))
  by_contra hnot
  have hle := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) (show 0 ≤ (N : ℝ≥0∞) from zero_le)
  exact (not_lt_of_ge (hle.trans hfinal)) hlarge

end DifferentialGeometry.Geometry.Hyperbolic
