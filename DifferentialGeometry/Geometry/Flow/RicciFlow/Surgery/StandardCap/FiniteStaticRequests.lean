import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticRequests

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticRequest

def baseline : StaticRequest := ⟨1, 0, 1, by norm_num, by norm_num⟩

def join (P P' : StaticRequest) : StaticRequest where
  radius := 1 + max P.radius P'.radius
  order := max P.order P'.order
  error := min P.error P'.error
  radius_pos := add_pos zero_lt_one (P.radius_pos.trans_le (le_max_left _ _))
  error_pos := lt_min P.error_pos P'.error_pos

theorem dominatedBy_join_left (P P' : StaticRequest) : P.DominatedBy (join P P') :=
  ⟨(le_max_left _ _).trans (by dsimp [join]; linarith), le_max_left _ _, min_le_left _ _⟩

theorem dominatedBy_join_right (P P' : StaticRequest) : P'.DominatedBy (join P P') :=
  ⟨(le_max_right _ _).trans (by dsimp [join]; linarith), le_max_right _ _, min_le_right _ _⟩

def combine : List StaticRequest → StaticRequest
  | [] => baseline
  | [P] => P
  | P :: P' :: ps => join P (combine (P' :: ps))

theorem dominatedBy_combine {ps : List StaticRequest} {P : StaticRequest} (hP : P ∈ ps) :
    P.DominatedBy (combine ps) := by
  induction ps with
  | nil => simp at hP
  | cons Q qs ih =>
    cases qs with
    | nil =>
      have he : P = Q := by simpa only [List.mem_singleton] using hP
      subst P
      exact dominatedBy_refl Q
    | cons Q' qs =>
      rcases List.mem_cons.mp hP with rfl | hp
      · exact dominatedBy_join_left _ _
      · exact (ih hp).trans (dominatedBy_join_right _ _)

def withLoss (P : StaticRequest) (A : ℝ) : StaticRequest where
  radius := P.radius
  order := P.order
  error := P.error / max 1 A
  radius_pos := P.radius_pos
  error_pos := div_pos P.error_pos (zero_lt_one.trans_le (le_max_left _ _))

theorem dominatedBy_withLoss (P : StaticRequest) (A : ℝ) : P.DominatedBy (withLoss P A) := by
  refine ⟨le_rfl, le_rfl, ?_⟩
  exact div_le_self P.error_pos.le (le_max_left _ _)

theorem withLoss_mul_error_le (P : StaticRequest) (A : ℝ) : A * (withLoss P A).error ≤ P.error := by
  have hd : 0 < max 1 A := zero_lt_one.trans_le (le_max_left _ _)
  calc
    A * (P.error / max 1 A) ≤ max 1 A * (P.error / max 1 A) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (div_nonneg P.error_pos.le hd.le)
    _ = P.error := by field_simp

def combineWithLoss (ps : List (StaticRequest × ℝ)) : StaticRequest :=
  combine (ps.map (fun q => withLoss q.1 q.2))

theorem withLoss_dominatedBy_combineWithLoss {ps : List (StaticRequest × ℝ)}
    {P : StaticRequest} {A : ℝ} (hP : (P, A) ∈ ps) :
    (withLoss P A).DominatedBy (combineWithLoss ps) :=
  dominatedBy_combine (List.mem_map.mpr ⟨(P, A), hP, rfl⟩)

theorem consumerNorm_lt (P : StaticRequest) (A : ℝ) (hA : 0 < A)
    {fixedNorm consumerNorm : ℝ≥0∞}
    (hsmall : fixedNorm < ENNReal.ofReal (withLoss P A).error)
    (hcomparison : consumerNorm ≤ ENNReal.ofReal A * fixedNorm) :
    consumerNorm < ENNReal.ofReal P.error := by
  have hs := ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hA))
    ENNReal.ofReal_ne_top hsmall
  rw [← ENNReal.ofReal_mul hA.le] at hs
  exact (hcomparison.trans_lt hs).trans_le (ENNReal.ofReal_le_ofReal (withLoss_mul_error_le P A))

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  (g : SmoothRiemannianMetric I M) (Q : ℝ) (hQ : 0 < Q)
  (U : Opens E3) (J : U → M) (hJ : IsLocalDiffeomorph (𝓡 3) I ∞ J)
  (hinj : Injective J) (p : M)

theorem IsSatisfied.of_mem_combine {ps : List StaticRequest}
    (h : (combine ps).IsSatisfied g Q hQ U J hJ hinj p)
    {P : StaticRequest} (hP : P ∈ ps) : P.IsSatisfied g Q hQ U J hJ hinj p :=
  h.mono g Q hQ U J hJ hinj p (dominatedBy_combine hP)

theorem IsSatisfied.of_mem_combineWithLoss {ps : List (StaticRequest × ℝ)}
    (h : (combineWithLoss ps).IsSatisfied g Q hQ U J hJ hinj p)
    {P : StaticRequest} {A : ℝ} (hP : (P, A) ∈ ps) (hA : 0 < A)
    (consumerNorm : ℝ≥0∞)
    (hcomparison : consumerNorm ≤ ENNReal.ofReal A * metricDerivENormSupOn
      {x : U | x.val ∈ closedModelBall P.radius} P.order
      (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric Q hQ g) J hJ hinj)
      (metric.restrictOpen U) (metric.restrictOpen U)) :
    P.IsSatisfied g Q hQ U J hJ hinj p ∧ consumerNorm < ENNReal.ofReal P.error := by
  have hweak := h.mono g Q hQ U J hJ hinj p (withLoss_dominatedBy_combineWithLoss hP)
  exact ⟨hweak.mono g Q hQ U J hJ hinj p (dominatedBy_withLoss P A),
    consumerNorm_lt P A hA hweak.2.2 hcomparison⟩
end DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticRequest
