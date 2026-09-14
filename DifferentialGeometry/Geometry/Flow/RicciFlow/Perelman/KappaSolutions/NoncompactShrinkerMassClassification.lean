import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerMassClassification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerModelMasses
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.ClassificationNonnegative

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (L : PointedRiemannianManifold.{u, uE, uH} (I := I))

local instance noncompactMassClassificationTopology : TopologicalSpace L.M := L.topology
local instance noncompactMassClassificationCharted : ChartedSpace H L.M := L.charted
local instance noncompactMassClassificationSmooth : IsManifold I ∞ L.M := L.smooth
local instance noncompactMassClassificationT2 : T2Space L.M := L.t2
local instance noncompactMassClassificationSigma : SigmaCompactSpace L.M := L.sigmaCompact

theorem noncompactShrinkerIsometryModels_of_noncompact_of_nonflat_three_shrinker
    (hdim : Module.finrank ℝ E = 3) (hcomplete : MetricComplete (I := I) L)
    (hconnected : ConnectedSpace L.M)
    (hnonflat : ∃ x : L.M, metricScalarAt L.metric x ≠ 0)
    (hnco : ∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
      0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j))
    (f : C^∞⟮I, L.M; ℝ⟯) (hsoliton : gradientRicciSoliton L.metric f 1)
    (hnormal : IsHamiltonNormalizedPotential L.metric f)
    (hnoncompact : ¬ CompactSpace L.M) :
    NoncompactShrinkerIsometryModels (I := I) L L.metric f := by
  let _ : ConnectedSpace L.M := hconnected
  have hmetricComplete : RiemannianMetricComplete (I := I) L.metric := ⟨hcomplete⟩
  have hnorm : normalizedGradientRicciSoliton (I := I) L.metric f :=
    ⟨hmetricComplete, hsoliton, hnormal⟩
  have hcone : ∀ x : L.M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := L.M) L.metric x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := L.M) :=
    fun x => (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (M := L.M) L.metric x).mpr (hnco x)
  have hnonflatRm : ∃ x : L.M, metricRm04At (I := I) (M := L.M) L.metric x ≠ 0 := by
    obtain ⟨x, hx⟩ := hnonflat
    exact ⟨x, fun hzero => hx (metricScalarAt_eq_zero_of_metricRm04At_eq_zero
      (I := I) (M := L.M) L.metric x hzero)⟩
  have hclass :=
    normalizedGradientRicciSoliton_isometry_classification_of_nonnegative_of_nonflat
      (I := I) (M := L.M) hnorm hdim hcone hnonflatRm
  rcases hclass.2 with hsphere | hcylinder
  · exfalso
    obtain ⟨G, hfin, hcancel, hsync, hcmdiff, hmetric, e, hpull, hconst⟩ := hsphere.1
    have hQc : CompactSpace (MulAction.orbitRel.Quotient G
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) := Quotient.compactSpace
    have hsurj : Function.Surjective (e : MulAction.orbitRel.Quotient G
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) → L.M) := e.surjective
    have hcompactM : CompactSpace L.M := by
      refine ⟨?_⟩
      have h := hQc.isCompact_univ.image e.contMDiff.continuous
      rwa [Set.image_univ_of_surjective hsurj] at h
    exact hnoncompact hcompactM
  · obtain ⟨cover, -, hdisj⟩ := hcylinder.1
    rcases hdisj with ⟨-, e, -, hmetric, hpot⟩ | ⟨-, e, -, hmetric, hpot⟩
      | ⟨-, e, -, hmetric, hpot⟩
    · exact Or.inl ⟨e, hmetric, hpot⟩
    · exact Or.inr (Or.inl ⟨e, hmetric, hpot⟩)
    · exact Or.inr (Or.inr ⟨cylinderDiagonalQuotientDiffeomorph.trans e, hmetric, hpot⟩)

theorem normalized_nonflat_three_shrinker_classification
    (hdim : Module.finrank ℝ E = 3) (hcomplete : MetricComplete (I := I) L)
    (hconnected : ConnectedSpace L.M)
    (hnonflat : ∃ x : L.M, metricScalarAt L.metric x ≠ 0)
    (hnco : ∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
      0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j))
    (f : C^∞⟮I, L.M; ℝ⟯) (hsoliton : gradientRicciSoliton L.metric f 1)
    (hnormal : IsHamiltonNormalizedPotential L.metric f) :
    (CompactSpace L.M ∧ (∀ x : L.M, metricScalarAt L.metric x = (3 : ℝ) / 2) ∧
      ∀ x : L.M, ∀ v : TangentSpace I x,
        ricciTensor L.metric x v v = ((3 / 2 : ℝ) / 3) * L.metric.inner x v v) ∨
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (2 * Real.exp (-1)) ∨
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (Real.exp (-1)) := by
  by_cases hcompact : CompactSpace L.M
  · exact Or.inl ⟨hcompact, normalized_nonflat_three_shrinker_round L hdim hconnected
      hnonflat hnco f hsoliton hnormal hcompact⟩
  · exact normalized_nonflat_three_shrinker_round_or_mass_of_noncompactModels L hdim f
      (noncompactShrinkerIsometryModels_of_noncompact_of_nonflat_three_shrinker L hdim
        hcomplete hconnected hnonflat hnco f hsoliton hnormal hcompact)
      noncompactShrinkerModelMasses

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
