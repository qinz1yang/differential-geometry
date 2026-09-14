import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerModelMasses

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (L : PointedRiemannianManifold.{u, uE, uH} (I := I))

local instance massDichotomyTopology : TopologicalSpace L.M := L.topology
local instance massDichotomyCharted : ChartedSpace H L.M := L.charted
local instance massDichotomySmooth : IsManifold I ∞ L.M := L.smooth
local instance massDichotomyT2 : T2Space L.M := L.t2
local instance massDichotomySigma : SigmaCompactSpace L.M := L.sigmaCompact

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
private theorem finrank_eq_three_of_isometryModels
    (f : C^∞⟮I, L.M; ℝ⟯)
    (hmodels : NoncompactShrinkerIsometryModels (I := I) L L.metric f) :
    Module.finrank ℝ E = 3 := by
  have hcylinder : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
      Module.finrank ℝ E := by
    rcases hmodels with ⟨e, -, -⟩ | ⟨e, -, -⟩ | ⟨e, -, -⟩
    · exact (e.symm.mfderivToContinuousLinearEquiv (n := ∞) (by decide)
        L.basepoint).toLinearEquiv.finrank_eq.symm
    · exact (e.symm.mfderivToContinuousLinearEquiv (n := ∞) (by decide)
        L.basepoint).toLinearEquiv.finrank_eq.symm
    · exact (e.symm.mfderivToContinuousLinearEquiv (n := ∞) (by decide)
        L.basepoint).toLinearEquiv.finrank_eq.symm
  rw [← hcylinder]
  simp

theorem noncompactShrinkerMass_dichotomy_of_isometryModels
    (f : C^∞⟮I, L.M; ℝ⟯)
    (hmodels : NoncompactShrinkerIsometryModels (I := I) L L.metric f)
    (hnoncompact : ¬ CompactSpace L.M) :
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (2 * Real.exp (-1)) ∨
      normalizedShrinkerMass L.metric f = ENNReal.ofReal (Real.exp (-1)) := by
  rcases normalized_nonflat_three_shrinker_round_or_mass_of_noncompactModels
      (I := I) L (finrank_eq_three_of_isometryModels (I := I) L f hmodels) f hmodels
      noncompactShrinkerModelMasses with hcompact | hmass | hmass
  · exact absurd hcompact.1 hnoncompact
  · exact Or.inl hmass
  · exact Or.inr hmass

theorem normalized_nonflat_three_shrinker_round_or_mass_of_isometryModels
    (hdim : Module.finrank ℝ E = 3) (hcomplete : MetricComplete (I := I) L)
    (hconnected : ConnectedSpace L.M)
    (hnonflat : ∃ x : L.M, metricScalarAt L.metric x ≠ 0)
    (hnco : ∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
      0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j))
    (f : C^∞⟮I, L.M; ℝ⟯) (hsoliton : gradientRicciSoliton L.metric f 1)
    (hnormal : IsHamiltonNormalizedPotential L.metric f)
    (hmodels : NoncompactShrinkerIsometryModels (I := I) L L.metric f) :
    (CompactSpace L.M ∧ (∀ x : L.M, metricScalarAt L.metric x = (3 : ℝ) / 2) ∧
      ∀ x : L.M, ∀ v : TangentSpace I x,
        ricciTensor L.metric x v v = ((3 / 2 : ℝ) / 3) * L.metric.inner x v v) ∨
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (2 * Real.exp (-1)) ∨
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (Real.exp (-1)) := by
  let _ := hcomplete
  exact normalized_nonflat_three_shrinker_round_or_mass_of_noncompact_mass (I := I) L hdim
    hconnected hnonflat hnco f hsoliton hnormal fun hnoncompact =>
      noncompactShrinkerMass_dichotomy_of_isometryModels (I := I) L f hmodels hnoncompact

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
