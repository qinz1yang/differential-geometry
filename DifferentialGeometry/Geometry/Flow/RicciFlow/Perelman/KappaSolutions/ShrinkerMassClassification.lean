import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic
import DifferentialGeometry.Geometry.Curvature.ModelChange
import DifferentialGeometry.Geometry.Operator.ModelChange
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Operations
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciNaturalityCross
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CompactRankReduction
import DifferentialGeometry.Geometry.Metric.RicciSoliton.PositiveRoundness
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorPositiveSectional
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients
import DifferentialGeometry.Geometry.Metric.ProjectiveSpace
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator (normGradSqFun gradientFun normGradSqFun_def
  normGradSqFun_transContinuousLinearEquiv)
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (L : PointedRiemannianManifold.{u, uE, uH} (I := I))

local instance massLimitTopology : TopologicalSpace L.M := L.topology
local instance massLimitCharted : ChartedSpace H L.M := L.charted
local instance massLimitSmooth : IsManifold I ∞ L.M := L.smooth
local instance massLimitT2 : T2Space L.M := L.t2
local instance massLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact


private theorem round_three_shrinker_scalar_of_innerProductSpace
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (hdim : Module.finrank ℝ E = 3)
    (hnonflat : ∃ x : M, metricScalarAt (I := I) g x ≠ 0)
    (hnco : ∀ x : M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
      0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt (I := I) g x (v i) (w i) (w j) (v j))
    (hsoliton : gradientRicciSoliton (I := I) g f 1)
    (hnormal : IsHamiltonNormalizedPotential (I := I) g f) :
    (∀ x : M, metricScalarAt (I := I) g x = (3 : ℝ) / 2) ∧
      ∀ x : M, ∀ v : TangentSpace I x,
        ricciTensor (I := I) g x v v = ((3 / 2 : ℝ) / 3) * g.inner x v v := by
  have hnorm : normalizedGradientRicciSoliton (I := I) g f :=
    ⟨RiemannianMetricComplete.of_compact (I := I) g, hsoliton, hnormal⟩
  have hcone : ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :=
    fun x => (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (M := M) g x).mpr (hnco x)
  have hnot : ¬ isGaussianGradientRicciSoliton (E := E) g f 1 := by
    intro hgaussian
    obtain ⟨x, hx⟩ := hnonflat
    exact hx (isGaussianGradientRicciSoliton_scalarCurvature_eq_zero (I := I) hgaussian x)
  have hrank :=
    normalizedGradientRicciSoliton_metricCurvatureOperatorRankAt_eq_three_of_compact_of_finrank_eq_three_of_nonnegative_of_not_isGaussian
      (I := I) (M := M) hnorm hdim hnot hcone
  have hdimAt : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = 3 := by
    intro x
    have hfin : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
    rw [hfin]
    exact hdim
  have hsec : ∀ (x : M) (v w : TangentSpace I x),
      LinearIndependent ℝ (vec2 (I := I) v w) →
        0 < metricRm04StandardAt (I := I) (M := M) g x v w w v := by
    intro x v w hvw
    exact metricRm04StdAt_pos_of_metricCurvatureOperatorRankAt_eq_three_of_nonnegative
      (I := I) (M := M) g x (hdimAt x) (hrank x) (hcone x) v w hvw
  have hscalar : ∀ x : M, 0 < metricScalarAt (I := I) (M := M) g x :=
    fun x => metricScalarAt_pos_of_sectional_pos_of_finrank_eq_three
      (I := I) (M := M) g x (hdimAt x) (hsec x)
  have hdefect : ∀ x : M, ricciReactionDefectAt (I := I) g x = 0 :=
    gradientRicciSoliton_ricciReactionDefectAt_eq_zero_of_compact_of_finrank_eq_three
      (I := I) (M := M) hsoliton hscalar hdim
  have heinstein : ∀ (x : M) (v w : TangentSpace I x),
      metricRicciAt (I := I) (M := M) g x (vec2 (I := I) v w) =
        (metricScalarAt (I := I) (M := M) g x / 3) * g.inner x v w :=
    fun x => metricRicciAt_eq_scalar_div_three_of_ricciReactionDefectAt_eq_zero_of_sectional_pos
      (I := I) (M := M) g x (hdimAt x) (hdefect x) (hsec x)
  have hscalarEq : ∀ x : M, metricScalarAt (I := I) (M := M) g x = 3 * (1 : ℝ) / 2 :=
    gradientRicciSoliton_metricScalarAt_eq_three_mul_sigma_div_two_of_compact_of_finrank_eq_three_of_sectional_pos
      (I := I) (M := M) hsoliton hdim hsec
  refine ⟨?_, ?_⟩
  · intro x
    rw [hscalarEq x]
    norm_num
  · intro x v
    rw [← metricRicciAt_apply_eq_ricciTensor (I := I) g x v v]
    rw [heinstein x v v, hscalarEq x]
    norm_num

theorem normalized_nonflat_three_shrinker_round
    (hdim : Module.finrank ℝ E = 3) (hconnected : ConnectedSpace L.M)
    (hnonflat : ∃ x : L.M, metricScalarAt L.metric x ≠ 0)
    (hnco : ∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
      0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j))
    (f : C^∞⟮I, L.M; ℝ⟯) (hsoliton : gradientRicciSoliton L.metric f 1)
    (hnormal : IsHamiltonNormalizedPotential L.metric f)
    (hcompact : CompactSpace L.M) :
    (∀ x : L.M, metricScalarAt L.metric x = (3 : ℝ) / 2) ∧
      ∀ x : L.M, ∀ v : TangentSpace I x,
        ricciTensor L.metric x v v = ((3 / 2 : ℝ) / 3) * L.metric.inner x v v := by
  classical
  let LL : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := E)
      (F := EuclideanSpace ℝ (Fin 3)) (by
        rw [finrank_euclideanSpace_fin]
        exact hdim)
  let J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H := I.transContinuousLinearEquiv LL
  let g : SmoothRiemannianMetric I L.M := L.metric
  let k : SmoothRiemannianMetric J L.M := g.transContinuousLinearEquiv LL
  let Φ : L.M ≃ₘ⟮I, J⟯ L.M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I L.M LL
  let u : C^∞⟮J, L.M; ℝ⟯ := f.comp Φ.symm.toContMDiffMap
  have hΦ : (Φ : L.M → L.M) = id := rfl
  have hΦsymm : ((Φ.symm : L.M → L.M)) = id := rfl
  have hu : (u : L.M → ℝ) = f := by
    funext y
    rw [show u y = f ((Φ.symm : L.M → L.M) y) from rfl, hΦsymm]
    rfl
  have hpull : Diffeomorph.pullbackMetricCross (I := J) (J := I) g Φ.symm = k :=
    Diffeomorph.pullbackMetricCross_symm_eq_iff.mpr
      (SmoothRiemannianMetric.pullback_transContinuousLinearEquiv g LL)
  have hpullk : Diffeomorph.pullbackMetricCross (I := I) (J := J) k Φ = g :=
    SmoothRiemannianMetric.pullback_transContinuousLinearEquiv g LL
  let _ : CompactSpace L.M := hcompact
  have hdimJ : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 :=
    finrank_euclideanSpace_fin
  have hnonflatJ : ∃ x : L.M, metricScalarAt (I := J) k x ≠ 0 := by
    obtain ⟨x, hx⟩ := hnonflat
    refine ⟨x, ?_⟩
    rw [metricScalarAt_transContinuousLinearEquiv (I := I) g LL x]
    exact hx
  have hncoJ : ∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ)
      (v w : Fin n → TangentSpace J x),
      0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt (I := J) k x (v i) (w i) (w j) (v j) := by
    intro x n c v w
    let B : TangentSpace I x ≃L[ℝ] TangentSpace J x :=
      Φ.mfderivToContinuousLinearEquiv (by simp : (∞ : ℕ∞ω) ≠ 0) x
    have hkey : ∀ X Y Z W : TangentSpace I x,
        metricRm04StandardAt (I := I) g x X Y Z W =
          metricRm04StandardAt (I := J) k x (B X) (B Y) (B Z) (B W) := by
      intro X Y Z W
      have h := metricRm04Standard_pullbackCross (g := k) (Phi := Φ) x X Y Z W
      rwa [hpullk] at h
    refine (hnco x n c (fun i => B.symm (v i)) (fun i => B.symm (w i))).trans_eq ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hkey (B.symm (v i)) (B.symm (w i)) (B.symm (w j)) (B.symm (v j)),
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hsolitonJ : gradientRicciSoliton (I := J) k u 1 := by
    have h := gradientRicciSoliton_pullbackCross (I := J) (J := I) hsoliton Φ.symm
    rw [hpull] at h
    exact h
  have hnormalJ : IsHamiltonNormalizedPotential (I := J) k u := by
    intro x
    have hsc : metricScalarAt (I := J) k x = metricScalarAt L.metric x :=
      metricScalarAt_transContinuousLinearEquiv (I := I) g LL x
    have hgrad : normGradSqFun (I := J) k (u : L.M → ℝ) x =
        normGradSqFun (I := I) g (f : L.M → ℝ) x := by
      rw [hu]
      exact normGradSqFun_transContinuousLinearEquiv (I := I) g LL (f : L.M → ℝ) x
        (f.contMDiff.mdifferentiableAt (by simp))
    have hval : u x = f x := by
      rw [show u x = f ((Φ.symm : L.M → L.M) x) from rfl, hΦsymm]
      rfl
    have htarget : metricScalarAt (I := I) g x + normGradSqFun (I := I) g (f : L.M → ℝ) x = f x := by
      rw [normGradSqFun_def]
      exact hnormal x
    calc metricScalarAt (I := J) k x +
          k.inner x (gradientFun (I := J) k (u : L.M → ℝ) x)
            (gradientFun (I := J) k (u : L.M → ℝ) x)
        = metricScalarAt (I := J) k x + normGradSqFun (I := J) k (u : L.M → ℝ) x := by
          rw [normGradSqFun_def]
          rfl
      _ = metricScalarAt (I := I) g x + normGradSqFun (I := I) g (f : L.M → ℝ) x := by
          rw [hsc, hgrad]
      _ = f x := htarget
      _ = u x := hval.symm
  obtain ⟨hscalarJ, hricciJ⟩ :=
    round_three_shrinker_scalar_of_innerProductSpace (I := J) (M := L.M)
      k u hdimJ hnonflatJ hncoJ hsolitonJ hnormalJ
  refine ⟨fun x => ?_, fun x v => ?_⟩
  · rw [← metricScalarAt_transContinuousLinearEquiv (I := I) g LL x]
    exact hscalarJ x
  · have hric : ricciTensor (I := I) g x v v =
        ricciTensor (I := J) k (Φ x) ((mfderiv I J (Φ : L.M → L.M) x) v)
          ((mfderiv I J (Φ : L.M → L.M) x) v) := by
      have h := ricciTensor_pullbackCross (I := I) (J := J) (g := k) (Φ := Φ) x v v
      rw [hpullk] at h
      exact h
    have hinner : g.inner x v v = k.inner (Φ x)
        ((mfderiv I J (Φ : L.M → L.M) x) v)
        ((mfderiv I J (Φ : L.M → L.M) x) v) := by
      have h := Diffeomorph.pullbackMetricCross_inner (I := I) (J := J) k Φ x v v
      rw [hpullk] at h
      exact h
    rw [hric, hinner]
    exact hricciJ (Φ x) ((mfderiv I J (Φ : L.M → L.M) x) v)

theorem normalized_nonflat_three_shrinker_round_or_mass_of_noncompact_mass
    (hdim : Module.finrank ℝ E = 3)
    (hconnected : ConnectedSpace L.M)
    (hnonflat : ∃ x : L.M, metricScalarAt L.metric x ≠ 0)
    (hnco : ∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
      0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j))
    (f : C^∞⟮I, L.M; ℝ⟯) (hsoliton : gradientRicciSoliton L.metric f 1)
    (hnormal : IsHamiltonNormalizedPotential L.metric f)
    (hnoncompactMass : ¬ CompactSpace L.M →
      normalizedShrinkerMass L.metric f = ENNReal.ofReal (2 * Real.exp (-1)) ∨
      normalizedShrinkerMass L.metric f = ENNReal.ofReal (Real.exp (-1))) :
    (CompactSpace L.M ∧ (∀ x : L.M, metricScalarAt L.metric x = (3 : ℝ) / 2) ∧
      ∀ x : L.M, ∀ v : TangentSpace I x,
        ricciTensor L.metric x v v = ((3 / 2 : ℝ) / 3) * L.metric.inner x v v) ∨
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (2 * Real.exp (-1)) ∨
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (Real.exp (-1)) := by
  by_cases hcompact : CompactSpace L.M
  · have hround := normalized_nonflat_three_shrinker_round L hdim hconnected hnonflat
      hnco f hsoliton hnormal hcompact
    exact Or.inl ⟨hcompact, hround.1, hround.2⟩
  · exact Or.inr (hnoncompactMass hcompact)

private instance euclideanThreeFinrankFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

omit [CompleteSpace E] [I.Boundaryless] in
theorem normalizedShrinkerMass_pullbackMetricCross
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    [T2Space N] [SigmaCompactSpace N]
    (hfin : Module.finrank ℝ E = Module.finrank ℝ E')
    (g : SmoothRiemannianMetric I L.M) (f : C^∞⟮I, L.M; ℝ⟯)
    (e : N ≃ₘ⟮J, I⟯ L.M) :
    normalizedShrinkerMass (I := I) (M := L.M) g f =
      normalizedShrinkerMass (I := J) (M := N) (Diffeomorph.pullbackMetricCross g e)
        (fun y => f (e y)) := by
  let _ : MeasurableSpace L.M := borel L.M
  let _ : BorelSpace L.M := ⟨rfl⟩
  let _ : MeasurableSpace N := borel N
  let _ : BorelSpace N := ⟨rfl⟩
  unfold normalizedShrinkerMass
  rw [hfin]
  rw [DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_pullback_cross
    (I := J) (J := I) (M := N) (N := L.M) g e]
  have hmeas : Measurable (fun y : N => ENNReal.ofReal (Real.exp
      (-(f (e y)) - ((Module.finrank ℝ E' : ℝ) / 2) * Real.log (4 * Real.pi)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((f.contMDiff.continuous.measurable.comp e.contMDiff.continuous.measurable).neg).sub
        measurable_const))
  rw [MeasureTheory.lintegral_map
    (μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := L.M) g)
    (g := (e.symm : L.M → N)) hmeas e.symm.contMDiff.continuous.measurable]
  refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Diffeomorph.apply_symm_apply]

def NoncompactShrinkerIsometryModels
    (g : SmoothRiemannianMetric I L.M) (f : C^∞⟮I, L.M; ℝ⟯) : Prop :=
  (∃ e : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) ≃ₘ⟮
        (𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ L.M,
      Diffeomorph.pullbackMetricCross g e = roundThreeCylinderShrinkerMetric ∧
        ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ,
          f (e x) = 1 + x.2 ^ 2 / 4) ∨
    (∃ e : (RealProjectivePlane × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ L.M,
      Diffeomorph.pullbackMetricCross g e =
          ((DifferentialGeometry.scaleMetric 2 (by norm_num)
              (roundProjectiveMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))).prod
            (euclideanMetric (E := ℝ))) ∧
        ∀ x : RealProjectivePlane × ℝ, f (e x) = 1 + x.2 ^ 2 / 4) ∨
    (∃ e : (CylinderDiagonalQuotient) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ L.M,
      Diffeomorph.pullbackMetricCross g e = cylinderDiagonalQuotientMetric ∧
        ∀ x : CylinderDiagonalQuotient, f (e x) = cylinderDiagonalQuotientPotential x)

def NoncompactShrinkerModelMasses : Prop :=
  (normalizedShrinkerMass (I := (𝓡 2).prod 𝓘(ℝ, ℝ))
      (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
      roundThreeCylinderShrinkerMetric
      (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ =>
        roundThreeCylinderShrinkerPotential x) =
    ENNReal.ofReal (2 * Real.exp (-1))) ∧
  (normalizedShrinkerMass (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (M := RealProjectivePlane × ℝ)
      ((DifferentialGeometry.scaleMetric 2 (by norm_num)
          (roundProjectiveMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))).prod
        (euclideanMetric (E := ℝ)))
      (fun x : RealProjectivePlane × ℝ => 1 + x.2 ^ 2 / 4) =
    ENNReal.ofReal (Real.exp (-1))) ∧
  (normalizedShrinkerMass (I := (𝓡 2).prod 𝓘(ℝ, ℝ))
      (M := CylinderDiagonalQuotient) cylinderDiagonalQuotientMetric
      (fun x : CylinderDiagonalQuotient => cylinderDiagonalQuotientPotential x) =
    ENNReal.ofReal (Real.exp (-1)))

theorem normalized_nonflat_three_shrinker_round_or_mass_of_noncompactModels
    (hdim : Module.finrank ℝ E = 3) (f : C^∞⟮I, L.M; ℝ⟯)
    (hmodels : NoncompactShrinkerIsometryModels (I := I) L L.metric f)
    (hmasses : NoncompactShrinkerModelMasses) :
    (CompactSpace L.M ∧ (∀ x : L.M, metricScalarAt L.metric x = (3 : ℝ) / 2) ∧
      ∀ x : L.M, ∀ v : TangentSpace I x,
        ricciTensor L.metric x v v = ((3 / 2 : ℝ) / 3) * L.metric.inner x v v) ∨
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (2 * Real.exp (-1)) ∨
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (Real.exp (-1)) := by
  have hfin : Module.finrank ℝ E = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    hdim.trans (by simp)
  rcases hmodels with ⟨e, hmetric, hpot⟩ | ⟨e, hmetric, hpot⟩ | ⟨e, hmetric, hpot⟩
  · refine Or.inr (Or.inl ?_)
    calc normalizedShrinkerMass L.metric f
        = normalizedShrinkerMass (Diffeomorph.pullbackMetricCross L.metric e)
            (fun y => f (e y)) :=
          normalizedShrinkerMass_pullbackMetricCross (I := I) (L := L)
            (J := (𝓡 2).prod 𝓘(ℝ, ℝ))
            (N := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
            hfin L.metric f e
      _ = normalizedShrinkerMass roundThreeCylinderShrinkerMetric
            (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ =>
              roundThreeCylinderShrinkerPotential x) := by
          rw [hmetric]
          congr 1 with x
          simpa only [roundThreeCylinderShrinkerPotential_apply] using hpot x
      _ = ENNReal.ofReal (2 * Real.exp (-1)) := hmasses.1
  · refine Or.inr (Or.inr ?_)
    calc normalizedShrinkerMass L.metric f
        = normalizedShrinkerMass (Diffeomorph.pullbackMetricCross L.metric e)
            (fun y => f (e y)) :=
          normalizedShrinkerMass_pullbackMetricCross (I := I) (L := L)
            (J := (𝓡 2).prod 𝓘(ℝ, ℝ)) (N := RealProjectivePlane × ℝ)
            hfin L.metric f e
      _ = normalizedShrinkerMass
            ((DifferentialGeometry.scaleMetric 2 (by norm_num)
                (roundProjectiveMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))).prod
              (euclideanMetric (E := ℝ)))
            (fun x : RealProjectivePlane × ℝ => 1 + x.2 ^ 2 / 4) := by
          rw [hmetric]
          congr 1 with x
          exact hpot x
      _ = ENNReal.ofReal (Real.exp (-1)) := hmasses.2.1
  · refine Or.inr (Or.inr ?_)
    calc normalizedShrinkerMass L.metric f
        = normalizedShrinkerMass (Diffeomorph.pullbackMetricCross L.metric e)
            (fun y => f (e y)) :=
          normalizedShrinkerMass_pullbackMetricCross (I := I) (L := L)
            (J := (𝓡 2).prod 𝓘(ℝ, ℝ)) (N := CylinderDiagonalQuotient)
            hfin L.metric f e
      _ = normalizedShrinkerMass cylinderDiagonalQuotientMetric
            (fun x : CylinderDiagonalQuotient => cylinderDiagonalQuotientPotential x) := by
          rw [hmetric]
          congr 1 with x
          exact hpot x
      _ = ENNReal.ofReal (Real.exp (-1)) := hmasses.2.2

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
