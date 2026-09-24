import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Coercivity
import DifferentialGeometry.Geometry.Metric.CurveEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.QuadraticForm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.UniformEquivalence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.Range

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ENNReal Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private def lRmFactor (E : Type uE) [NormedAddCommGroup E]
    [NormedSpace Real E] (K : Real) : Real :=
  (Module.finrank Real E : Real) ^ 2 * Real.sqrt K

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
theorem lRegularizedPot_lower_rm
    (S : SolutionOn (I := I) (M := M) D)
    (K T b : Real) (hb : 0 ≤ b)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (s : Real) (hs : s ∈ Icc 0 b) (x : M) :
    -2 * b ^ 2 * lRmFactor E K ≤
      2 * s ^ 2 * S.scalar (T - s ^ 2) x := by
  have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb).2 hs.2
  have ht : T - s ^ 2 ∈ Icc (T - b ^ 2) T := by
    constructor <;> linarith [sq_nonneg s]
  have hscalar := scalar_abs_le_rm (I := I) (S.base.metric (T - s ^ 2)) x
  have hscalar' : |S.scalar (T - s ^ 2) x| ≤ lRmFactor E K := by
    simpa only [SolutionOn.scalar, SolutionFamily.scalar, SolutionFamily.rm04,
      metricRm04_apply, lRmFactor,
      show Module.finrank Real (TangentSpace I x) = Module.finrank Real E by rfl] using hscalar.trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hRm _ ht x)) (sq_nonneg _))
  have hA : 0 ≤ lRmFactor E K :=
    mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg K)
  have hlow : -lRmFactor E K ≤ S.scalar (T - s ^ 2) x :=
    neg_le_of_abs_le hscalar'
  have hmul : 2 * s ^ 2 * (-lRmFactor E K) ≤
      2 * s ^ 2 * S.scalar (T - s ^ 2) x :=
    mul_le_mul_of_nonneg_left hlow (mul_nonneg (by norm_num) (sq_nonneg s))
  have hsqmul : 2 * s ^ 2 * lRmFactor E K ≤
      2 * b ^ 2 * lRmFactor E K :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs2 (by norm_num)) hA
  linarith

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
theorem lRegularizedPot_upper_rm
    (S : SolutionOn (I := I) (M := M) D)
    (K T b : Real) (hb : 0 ≤ b)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (s : Real) (hs : s ∈ Icc 0 b) (x : M) :
    2 * s ^ 2 * S.scalar (T - s ^ 2) x ≤
      2 * b ^ 2 * lRmFactor E K := by
  have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb).2 hs.2
  have ht : T - s ^ 2 ∈ Icc (T - b ^ 2) T := by
    constructor <;> linarith [sq_nonneg s]
  have hscalar := scalar_abs_le_rm (I := I) (S.base.metric (T - s ^ 2)) x
  have hscalar' : |S.scalar (T - s ^ 2) x| ≤ lRmFactor E K := by
    simpa only [SolutionOn.scalar, SolutionFamily.scalar, SolutionFamily.rm04,
      metricRm04_apply, lRmFactor,
      show Module.finrank Real (TangentSpace I x) = Module.finrank Real E by rfl] using hscalar.trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hRm _ ht x)) (sq_nonneg _))
  have hA : 0 ≤ lRmFactor E K :=
    mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg K)
  have hupp : S.scalar (T - s ^ 2) x ≤ lRmFactor E K :=
    le_of_abs_le hscalar'
  have hmul : 2 * s ^ 2 * S.scalar (T - s ^ 2) x ≤
      2 * s ^ 2 * lRmFactor E K :=
    mul_le_mul_of_nonneg_left hupp (mul_nonneg (by norm_num) (sq_nonneg s))
  exact hmul.trans <| mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs2 (by norm_num)) hA

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] in
theorem lRegularizedMetric_le_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T b : Real) (hb : 0 ≤ b)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (s : Real) (hs : s ∈ Icc 0 b) (x : M)
    (v : TangentSpace I x) :
    (S.base.metric T).inner x v v ≤
      Real.exp (2 * lRmFactor E K * b ^ 2) *
        (S.base.metric (T - s ^ 2)).inner x v v := by
  let : CompleteSpace E := FiniteDimensional.complete Real E
  let A : Real := lRmFactor E K
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg K)
  have ht0 : T ∈ Icc (T - b ^ 2) T := by
    constructor <;> linarith [sq_nonneg b]
  have hquad : ∀ i : Nat, ∀ t : Real, t ∈ Icc (T - b ^ 2) T →
      ∀ y : M, y ∈ (Set.univ : Set M) → ∀ w : TangentSpace I y,
        |S.ricciAt t y (vec2 (I := I) w w)| ≤
          A * (S.base.metric t).inner y w w := by
    have hbound := twoTensorQuadBound_of_solutions (I := I)
      (fun _ : Nat ↦ S) Set.univ (T - b ^ 2) T K
      (fun _ t ht y _ ↦ hRm t ht y)
    intro i t ht y hy w
    exact hbound.2 i t ht y hy w
  have hequiv := metric_uniform_equivalent_on_window_of_solutions (I := I)
    (fun _ : Nat ↦ S) (fun _ ↦ hS) Set.univ (T - b ^ 2) T T 1 A
    (S.base.metric T) hreg ht0 (by norm_num) hA
    (fun _ ↦ by
      refine ⟨by norm_num, ?_⟩
      intro y _hy w
      simp)
    hquad
  have ht : T - s ^ 2 ∈ Icc (T - b ^ 2) T := by
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb).2 hs.2
    constructor <;> linarith [sq_nonneg s]
  have hlow := (hequiv 0 (T - s ^ 2) ht).2 x (Set.mem_univ x) v |>.1
  let F : Real := metricEquivalenceFactor 1 A (T - s ^ 2) T
  have hF : F = Real.exp (2 * A * s ^ 2) := by
    dsimp only [F]
    rw [metricEquivalenceFactor]
    simp only [one_mul]
    rw [show T - s ^ 2 - T = -(s ^ 2) by ring, abs_neg,
      abs_of_nonneg (sq_nonneg s)]
  have hFpos : 0 < F := by rw [hF]; exact Real.exp_pos _
  have hFB : F ≤ Real.exp (2 * A * b ^ 2) := by
    rw [hF]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ hs.1 hb).2 hs.2)
      (mul_nonneg (by norm_num) hA)
  have hmov : 0 ≤ (S.base.metric (T - s ^ 2)).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact ((S.base.metric (T - s ^ 2)).pos x v hv).le
  calc
    (S.base.metric T).inner x v v =
        F * (F⁻¹ * (S.base.metric T).inner x v v) := by
      field_simp [ne_of_gt hFpos]
    _ ≤ F * (S.base.metric (T - s ^ 2)).inner x v v :=
      mul_le_mul_of_nonneg_left hlow hFpos.le
    _ ≤ Real.exp (2 * A * b ^ 2) *
        (S.base.metric (T - s ^ 2)).inner x v v :=
      mul_le_mul_of_nonneg_right hFB hmov

theorem lRegularizedRange_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (alpha : Real → M) (a b A : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1 alpha (Icc a b))
    (hE : IntegrableOn (fun s ↦
      (S.base.metric T).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) (Icc a b))
    (hkin : IntervalIntegrable (lRegularizedSpeedSq S T alpha) volume a b)
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume a b)
    (hact : lRegularizedAction S T alpha a b ≤ A) :
    ∃ Cpt : Set M, IsCompact Cpt ∧ alpha '' Icc a b ⊆ Cpt := by
  have hb : 0 ≤ b := ha.trans hab
  apply lRegularizedRange_compact (I := I) S (S.base.metric T) hg T alpha a b A
    (-2 * b ^ 2 * lRmFactor E K)
    (Real.exp (2 * lRmFactor E K * b ^ 2)) hab (Real.exp_pos _).le
  · intro s hs v
    exact lRegularizedMetric_le_rm (I := I) S hS K T b hb hreg hRm s
      ⟨ha.trans hs.1, hs.2⟩ (alpha s) v
  · intro s hs
    exact lRegularizedPot_lower_rm (I := I) S K T b hb hRm s
      ⟨ha.trans hs.1, hs.2⟩ (alpha s)
  · exact halpha
  · exact hE
  · exact hkin
  · exact hLag
  · exact hact

theorem lRegularizedRanges_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (alpha : Nat → Real → M) (x : M) (a b A : Real)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    (hstart : ∀ n, alpha n a = x)
    (halpha : ∀ n,
      ContMDiffOn (modelWithCornersSelf Real Real) I 1 (alpha n) (Icc a b))
    (hE : ∀ n, IntegrableOn (fun s ↦
      (S.base.metric T).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s))
      (Icc a b))
    (hkin : ∀ n, IntervalIntegrable (lRegularizedSpeedSq S T (alpha n)) volume a b)
    (hLag : ∀ n, IntervalIntegrable (lRegularizedLagrangian S T (alpha n)) volume a b)
    (hact : ∀ n, lRegularizedAction S T (alpha n) a b ≤ A) :
    ∃ Cpt : Set M, IsCompact Cpt ∧ ∀ n, alpha n '' Icc a b ⊆ Cpt := by
  have hb : 0 ≤ b := ha.trans hab
  apply lRegularizedRanges_compact (I := I) S (S.base.metric T) hg T alpha x a b A
    (-2 * b ^ 2 * lRmFactor E K)
    (Real.exp (2 * lRmFactor E K * b ^ 2)) hab (Real.exp_pos _).le hstart
  · intro n s hs v
    exact lRegularizedMetric_le_rm (I := I) S hS K T b hb hreg hRm s
      ⟨ha.trans hs.1, hs.2⟩ (alpha n s) v
  · intro n s hs
    exact lRegularizedPot_lower_rm (I := I) S K T b hb hRm s
      ⟨ha.trans hs.1, hs.2⟩ (alpha n s)
  · exact halpha
  · exact hE
  · exact hkin
  · exact hLag
  · exact hact

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegularizedAction_ge_riemannianEDistOf_sq_div_add_constant
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (α : ℝ → M)
    {a b c C : ℝ} (hab : a < b) (hc : 0 ≤ c)
    (g : SmoothRiemannianMetric I M)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) I 1 α (Icc a b))
    (hmetric : ∀ s ∈ Icc a b,
      c * g.inner (α s) (lVelocity (I := I) α s) (lVelocity (I := I) α s) ≤
        (S.base.metric (T - s ^ 2)).inner (α s)
          (lVelocity (I := I) α s) (lVelocity (I := I) α s))
    (hpotential : ∀ s ∈ Icc a b, C ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (α s))
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T α) volume a b) :
    c * (riemannianEDistOf g (α a) (α b)).toReal ^ 2 / (2 * (b - a)) + C * (b - a) ≤
      lRegularizedAction S T α a b := by
  have hE := integrableOn_inner_mfderiv_self_of_contMDiffOn g hα
  have href : IntervalIntegrable
      (fun s => g.inner (α s) (lVelocity (I := I) α s) (lVelocity (I := I) α s)) volume a b := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hab.le, lVelocity] using hE
  have hcoerc := lRegularizedAction_ge_reference_energy_add_constant S T α g a b c C hab.le
    hmetric hpotential href hLag
  rw [intervalIntegral.integral_const_mul] at hcoerc
  change c / 2 * curveEnergy g α a b + C * (b - a) ≤ _ at hcoerc
  have hd := riemannianEDistOf_toReal_sq_le_curveEnergy g hab.le hα hE
  have hdist : c * (riemannianEDistOf g (α a) (α b)).toReal ^ 2 / (2 * (b - a)) ≤
      c / 2 * curveEnergy g α a b := by
    apply (div_le_iff₀ (by linarith : 0 < 2 * (b - a))).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd hc]
  exact (add_le_add hdist le_rfl).trans hcoerc


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegularizedAction_ge_riemannianEDistOf_sq_div_sub_scalar_bound [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (α : ℝ → M)
    {a b c K : ℝ} (ha : 0 ≤ a) (hab : a < b) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (g : SmoothRiemannianMetric I M) (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.carrier)
    (hmetric : ∀ s ∈ Icc a b,
      c * g.inner (α s) (lVelocity (I := I) α s) (lVelocity (I := I) α s) ≤
        (S.base.metric (T - s ^ 2)).inner (α s)
          (lVelocity (I := I) α s) (lVelocity (I := I) α s))
    (hscalar : ∀ s ∈ Icc a b, -K ≤ S.scalar (T - s ^ 2) (α s)) :
    c * (riemannianEDistOf g (α a) (α b)).toReal ^ 2 / (2 * (b - a)) -
        2 * K * b ^ 2 * (b - a) ≤ lRegularizedAction S T α a b := by
  have hLag : IntervalIntegrable (lRegularizedLagrangian S T α) volume a b := by
    have hcont := lRegularizedLagrangian_continuousOn_carrier S hS α hα
    have hcurve := hcont.comp (s := Icc a b)
      (continuous_const.prodMk continuous_id).continuousOn (fun s hs => htime s hs)
    exact hcurve.intervalIntegrable_of_Icc hab.le
  have hpotential : ∀ s ∈ Icc a b, -(2 * K * b ^ 2) ≤
      2 * s ^ 2 * S.scalar (T - s ^ 2) (α s) := by
    intro s hs
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ (ha.trans hs.1) (ha.trans hab.le)).mpr hs.2
    have hmul := mul_le_mul_of_nonneg_left (hscalar s hs) (by positivity : 0 ≤ 2 * s ^ 2)
    have hsK := mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ 2 * K)
    nlinarith
  have hh := lRegularizedAction_ge_riemannianEDistOf_sq_div_add_constant
    S T α hab hc g hα.contMDiffOn hmetric hpotential hLag
  simpa only [neg_mul, sub_eq_add_neg] using hh


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegularizedAction_ge_of_endpoint_separation [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (α : ℝ → M)
    {a b c K d : ℝ} (ha : 0 ≤ a) (hab : a < b) (hc : 0 ≤ c) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (g : SmoothRiemannianMetric I M) (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.carrier)
    (hmetric : ∀ s ∈ Icc a b,
      c * g.inner (α s) (lVelocity (I := I) α s) (lVelocity (I := I) α s) ≤
        (S.base.metric (T - s ^ 2)).inner (α s)
          (lVelocity (I := I) α s) (lVelocity (I := I) α s))
    (hscalar : ∀ s ∈ Icc a b, -K ≤ S.scalar (T - s ^ 2) (α s))
    (hseparation : ENNReal.ofReal d ≤ riemannianEDistOf g (α a) (α b)) :
    c * d ^ 2 / (2 * (b - a)) - 2 * K * b ^ 2 * (b - a) ≤
      lRegularizedAction S T α a b := by
  have hE := integrableOn_inner_mfderiv_self_of_contMDiffOn g (a := a) (b := b) hα.contMDiffOn
  have hfinite : riemannianEDistOf g (α a) (α b) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (edistOf_le_energy g hab.le hα.contMDiffOn hE)
  have hdist : d ≤ (riemannianEDistOf g (α a) (α b)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hseparation
  have hsq : d ^ 2 ≤ (riemannianEDistOf g (α a) (α b)).toReal ^ 2 :=
    pow_le_pow_left₀ hd hdist 2
  have hratio := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hc)
    (by linarith : 0 ≤ 2 * (b - a))
  exact (sub_le_sub_right hratio _).trans
    (lRegularizedAction_ge_riemannianEDistOf_sq_div_sub_scalar_bound S hS T α ha hab hc hK g hα
      htime hmetric hscalar)

end DifferentialGeometry.PDE.RicciFlow.Perelman


namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegularizedAction_ge_of_initial_segment_separation [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (α : ℝ → M)
    {b τ c K d : ℝ} (hτ : 0 < τ) (hτb : τ ≤ b) (hc : 0 ≤ c) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (g : SmoothRiemannianMetric I M) (hα : ContMDiff 𝓘(ℝ, ℝ) I 1 α)
    (htime : ∀ s ∈ Icc 0 b, T - s ^ 2 ∈ D.carrier)
    (hmetric : ∀ s ∈ Icc 0 τ,
      c * g.inner (α s) (lVelocity (I := I) α s) (lVelocity (I := I) α s) ≤
        (S.base.metric (T - s ^ 2)).inner (α s)
          (lVelocity (I := I) α s) (lVelocity (I := I) α s))
    (hscalar : ∀ s ∈ Icc 0 b, -K ≤ S.scalar (T - s ^ 2) (α s))
    (hseparation : ENNReal.ofReal d ≤ riemannianEDistOf g (α 0) (α τ)) :
    c * d ^ 2 / (2 * b) - 2 * K * b ^ 3 ≤ lRegularizedAction S T α 0 b := by
  have hb : 0 < b := hτ.trans_le hτb
  let C := -(2 * K * b ^ 2)
  have hpot : ∀ s ∈ Icc 0 b, C ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (α s) := by
    intro s hs
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).mpr hs.2
    have hmul := mul_le_mul_of_nonneg_left (hscalar s hs) (by positivity : 0 ≤ 2 * s ^ 2)
    have hKb := mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ 2 * K)
    dsimp only [C]
    nlinarith
  have hint (a' b' : ℝ) (ha' : 0 ≤ a') (hab' : a' ≤ b') (hb' : b' ≤ b) :
      IntervalIntegrable (lRegularizedLagrangian S T α) volume a' b' := by
    have hcont := lRegularizedLagrangian_continuousOn_carrier S hS α hα
    have hcurve := hcont.comp (s := Icc a' b')
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => htime s ⟨ha'.trans hs.1, hs.2.trans hb'⟩)
    exact hcurve.intervalIntegrable_of_Icc hab'
  have hE := integrableOn_inner_mfderiv_self_of_contMDiffOn g (a := 0) (b := τ) hα.contMDiffOn
  have hfinite : riemannianEDistOf g (α 0) (α τ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (edistOf_le_energy g hτ.le hα.contMDiffOn hE)
  have hdist : d ≤ (riemannianEDistOf g (α 0) (α τ)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hseparation
  have hsq := pow_le_pow_left₀ hd hdist 2
  have hpref := lRegularizedAction_ge_riemannianEDistOf_sq_div_add_constant S T α hτ hc g hα.contMDiffOn
    hmetric (fun s hs => hpot s ⟨hs.1, hs.2.trans hτb⟩) (hint 0 τ le_rfl hτ.le hτb)
  simp only [sub_zero] at hpref
  have hsmall := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hc) (by positivity : 0 ≤ 2 * τ)
  have hsmall' : c * d ^ 2 / (2 * τ) + C * τ ≤ lRegularizedAction S T α 0 τ :=
    (add_le_add hsmall le_rfl).trans hpref
  have href : IntervalIntegrable
      (fun s => g.inner (α s) (lVelocity (I := I) α s) (lVelocity (I := I) α s)) volume τ b := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hτb, lVelocity] using
      integrableOn_inner_mfderiv_self_of_contMDiffOn g (a := τ) (b := b) hα.contMDiffOn
  have htail := lRegularizedAction_ge_reference_energy_add_constant S T α g τ b 0 C hτb
    (fun s hs => by simp only [zero_mul]; exact metric_inner_self_nonneg _ _ _)
    (fun s hs => hpot s ⟨hτ.le.trans hs.1, hs.2⟩) href (hint τ b hτ.le hτb le_rfl)
  simp only [zero_div, zero_mul, intervalIntegral.integral_zero, zero_add] at htail
  have hsum := add_le_add hsmall' htail
  rw [lRegularizedAction_add S T α 0 τ b (hint 0 τ le_rfl hτ.le hτb) (hint τ b hτ.le hτb le_rfl)] at hsum
  have hratio : c * d ^ 2 / (2 * b) ≤ c * d ^ 2 / (2 * τ) :=
    div_le_div_of_nonneg_left (mul_nonneg hc (sq_nonneg d)) (by positivity) (by linarith)
  dsimp only [C] at hsum
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman
