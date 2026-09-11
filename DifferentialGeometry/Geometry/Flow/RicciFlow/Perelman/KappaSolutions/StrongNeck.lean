import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossModelTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

universe u uE uH

private local instance strongNeckSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩


def strongNeckBackgroundMetric (epsilon s : ℝ) :
    SmoothRiemannianMetric SpatialNeckCylinderModel (spatialNeckBuffer epsilon) :=
  (scalarOneShrinkingCylinderMetric (min s 0)
    ((min_le_right s 0).trans_lt (by norm_num))).restrictOpen (spatialNeckBuffer epsilon)


theorem strongNeckBackgroundMetric_of_nonpos (epsilon s : ℝ) (hs : s ≤ 0) :
    strongNeckBackgroundMetric epsilon s =
      (scalarOneShrinkingCylinderMetric s (hs.trans_lt (by norm_num))).restrictOpen
        (spatialNeckBuffer epsilon) := by
  simp only [strongNeckBackgroundMetric, min_eq_left hs]


def StrongNeckJetControl (epsilon : ℝ)
    (jet : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2) : Prop :=
  ∃ delta : ℝ, 0 ≤ delta ∧ delta < epsilon ∧
    ∀ a b : ℕ, a + 2 * b ≤ Nat.ceil epsilon⁻¹ →
      ∀ s ∈ Icc (-1 : ℝ) 0, ∀ x ∈ spatialNeckClosedCore epsilon,
        tensor02CovDerivNormWith a (jet b s)
          (strongNeckBackgroundMetric epsilon s) (strongNeckBackgroundMetric epsilon s) x ≤ delta

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

private local instance strongNeckC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)


def strongNeckNormalizedMetric (S : SolutionOn (I := I) (M := M) D)
    (p : M) (t : ℝ) (hQ : 0 < S.scalar t p) {epsilon : ℝ}
    {Phi : C(spatialNeckBuffer epsilon, M)}
    (hPhi : IsSmoothEmbedding SpatialNeckCylinderModel I ∞ Phi) (s : ℝ) :
    SmoothRiemannianMetric SpatialNeckCylinderModel (spatialNeckBuffer epsilon) :=
  scaleMetric (S.scalar t p) hQ
    (immersionInducedMetric (S.base.metric (parabolicTime t (S.scalar t p) s)) hPhi.isImmersion)

omit [T2Space M] in
theorem strongNeckNormalizedMetric_inner (S : SolutionOn (I := I) (M := M) D)
    (p : M) (t : ℝ) (hQ : 0 < S.scalar t p) {epsilon : ℝ}
    {Phi : C(spatialNeckBuffer epsilon, M)}
    (hPhi : IsSmoothEmbedding SpatialNeckCylinderModel I ∞ Phi) (s : ℝ)
    (x : spatialNeckBuffer epsilon) (v w : TangentSpace SpatialNeckCylinderModel x) :
    (strongNeckNormalizedMetric S p t hQ hPhi s).inner x v w =
      S.scalar t p * (S.base.metric (t + s / S.scalar t p)).inner (Phi x)
        (mfderiv SpatialNeckCylinderModel I Phi x v)
        (mfderiv SpatialNeckCylinderModel I Phi x w) := by
  rw [strongNeckNormalizedMetric, scaleMetric_inner, immersionInducedMetric_inner]
  rfl


structure StrongNeckWitness (S : SolutionOn (I := I) (M := M) D)
    (yStar : SpatialNeckSphere) (p : M) (t epsilon : ℝ) where
  dimension_three : Module.finrank ℝ E = 3
  isSolution : IsSolutionOn S
  epsilon_pos : 0 < epsilon
  epsilon_lt_one : epsilon < 1
  scalar_pos : 0 < S.scalar t p
  time_window : Icc (t - (S.scalar t p)⁻¹) t ⊆ D.carrier
  embedding : C(spatialNeckBuffer epsilon, M)
  smooth_embedding : IsSmoothEmbedding SpatialNeckCylinderModel I ∞ embedding
  marked : embedding (spatialNeckCentralPoint epsilon epsilon_pos yStar) = p
  jet : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
    (M := spatialNeckBuffer epsilon) (n := ∞) 2
  jet_zero : ∀ s ∈ Icc (-1 : ℝ) 0, ∀ x v,
    jet 0 s x v =
      (strongNeckNormalizedMetric S p t scalar_pos smooth_embedding s).inner x (v 0) (v 1) -
        (strongNeckBackgroundMetric epsilon s).inner x (v 0) (v 1)
  jet_succ : ∀ b s, s ∈ Icc (-1 : ℝ) 0 → ∀ (x : spatialNeckBuffer epsilon)
      (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x),
    HasDerivWithinAt (fun r => jet b r x v) (jet (b + 1) s x v) (Icc (-1 : ℝ) 0) s
  closeness : StrongNeckJetControl epsilon jet


def IsStrongNeckCenter (S : SolutionOn (I := I) (M := M) D)
    (yStar : SpatialNeckSphere) (p : M) (t epsilon : ℝ) : Prop :=
  Nonempty (StrongNeckWitness S yStar p t epsilon)

namespace StrongNeckWitness

variable {S : SolutionOn (I := I) (M := M) D} {yStar : SpatialNeckSphere}
  {p : M} {t epsilon : ℝ} (W : StrongNeckWitness S yStar p t epsilon)

include W in
theorem normalized_time_mem {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 0) :
    parabolicTime t (S.scalar t p) s ∈ D.carrier := by
  have hlo : -(S.scalar t p)⁻¹ ≤ s / S.scalar t p := by
    simpa only [neg_div, one_div] using
      (div_le_div_of_nonneg_right hs.1 W.scalar_pos.le)
  have hhi : s / S.scalar t p ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hs.2 W.scalar_pos.le
  apply W.time_window
  change t - (S.scalar t p)⁻¹ ≤ t + s / S.scalar t p ∧ t + s / S.scalar t p ≤ t
  constructor <;> linarith


theorem jet_eq_iteratedDerivWithin (q : ℕ) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 0)
    (x : spatialNeckBuffer epsilon) (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x) :
    W.jet q s x v = iteratedDerivWithin q
      (fun r =>
        (strongNeckNormalizedMetric S p t W.scalar_pos W.smooth_embedding r).inner x (v 0) (v 1) -
          (strongNeckBackgroundMetric epsilon r).inner x (v 0) (v 1)) (Icc (-1 : ℝ) 0) s := by
  induction q generalizing s with
  | zero => simpa only [iteratedDerivWithin_zero] using W.jet_zero s hs x v
  | succ q ih =>
    have hd := W.jet_succ q s hs x v
    rw [iteratedDerivWithin_succ]
    exact (hd.derivWithin (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0) s hs)).symm.trans
      (derivWithin_congr (fun r hr => ih hr) (ih hs))

end StrongNeckWitness
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
