import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerMassClassification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerModelMasses

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal _root_.Topology

universe u uE uH

local notation "CylI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private def shrinkerSpherePoint : S2 :=
  ⟨PiLp.single 2 (0 : Fin 3) (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm, PiLp.norm_single, norm_one]⟩

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (L : PointedRiemannianManifold.{u, uE, uH} (I := I))

local instance reductionTopology : TopologicalSpace L.M := L.topology
local instance reductionCharted : ChartedSpace H L.M := L.charted
local instance reductionSmooth : IsManifold I ∞ L.M := L.smooth
local instance reductionT2 : T2Space L.M := L.t2
local instance reductionSigma : SigmaCompactSpace L.M := L.sigmaCompact

theorem normalized_nonflat_three_shrinker_round_or_mass_of_noncompactShrinkerIsometryModels
    (hdim : Module.finrank ℝ E = 3) (hcomplete : MetricComplete (I := I) L)
    (hconnected : ConnectedSpace L.M)
    (hnonflat : ∃ x : L.M, metricScalarAt L.metric x ≠ 0)
    (hnco : ∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
      0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j))
    (f : C^∞⟮I, L.M; ℝ⟯) (hsoliton : gradientRicciSoliton L.metric f 1)
    (hnormal : IsHamiltonNormalizedPotential L.metric f)
    (hmodels : ¬ CompactSpace L.M → MetricComplete (I := I) L →
      NoncompactShrinkerIsometryModels (I := I) L L.metric f) :
    (CompactSpace L.M ∧ (∀ x : L.M, metricScalarAt L.metric x = (3 : ℝ) / 2) ∧
      ∀ x : L.M, ∀ v : TangentSpace I x,
        ricciTensor L.metric x v v = ((3 / 2 : ℝ) / 3) * L.metric.inner x v v) ∨
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (2 * Real.exp (-1)) ∨
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (Real.exp (-1)) := by
  by_cases hcompact : CompactSpace L.M
  · exact Or.inl ⟨hcompact, normalized_nonflat_three_shrinker_round L hdim hconnected hnonflat
      hnco f hsoliton hnormal hcompact⟩
  · exact normalized_nonflat_three_shrinker_round_or_mass_of_noncompactModels L hdim f
      (hmodels hcompact hcomplete) noncompactShrinkerModelMasses

theorem exists_pointed_normalizedShrinkerMass_two_exp_neg_one :
    ∃ (L : PointedRiemannianManifold.{0, 0, 0} (I := CylI)) (f : L.M → ℝ),
      normalizedShrinkerMass (I := CylI) (M := L.M) L.metric f =
        ENNReal.ofReal (2 * Real.exp (-1)) := by
  let L₀ : PointedRiemannianManifold.{0, 0, 0} (I := CylI) :=
    { M := S2 × ℝ
      basepoint := (shrinkerSpherePoint, 0)
      metric := roundThreeCylinderShrinkerMetric }
  refine ⟨L₀, fun x : S2 × ℝ => roundThreeCylinderShrinkerPotential x, ?_⟩
  simpa only [L₀] using normalizedShrinkerMass_roundThreeCylinderShrinker

theorem exists_pointed_normalizedShrinkerMass_exp_neg_one :
    ∃ (L : PointedRiemannianManifold.{0, 0, 0} (I := CylI)) (f : L.M → ℝ),
      normalizedShrinkerMass (I := CylI) (M := L.M) L.metric f =
        ENNReal.ofReal (Real.exp (-1)) := by
  let L₀ : PointedRiemannianManifold.{0, 0, 0} (I := CylI) :=
    { M := RealProjectivePlane × ℝ
      basepoint := (realProjectivePlaneQuotientMap shrinkerSpherePoint, 0)
      metric := (scaleMetric 2 (by norm_num)
        (roundProjectiveMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))).prod
          (euclideanMetric (E := ℝ)) }
  refine ⟨L₀, fun x : RealProjectivePlane × ℝ => 1 + x.2 ^ 2 / 4, ?_⟩
  simpa only [L₀] using normalizedShrinkerMass_realProjectivePlaneProduct

theorem normalizedShrinkerMass_alternative_values_ne :
    ENNReal.ofReal (Real.exp (-1)) ≠ ENNReal.ofReal (2 * Real.exp (-1)) := by
  intro h
  have hreal := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal (Real.exp_pos (-1)).le,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * Real.exp (-1))] at hreal
  have hpos : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
