import DifferentialGeometry.Geometry.Curvature.ScalarNormBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.RicciOperator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.FlowUniformEquivalence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.RangeCompactness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ENNReal Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.HCGCompactness
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
theorem lRegPot_lower_rm
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
theorem lRegPot_upper_rm
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
theorem lRegMetric_le_rm
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

theorem lRegRange_of_rm
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
    (hkin : IntervalIntegrable (lRegSpeedSq S T alpha) volume a b)
    (hLag : IntervalIntegrable (lRegLagrangian S T alpha) volume a b)
    (hact : lRegAction S T alpha a b ≤ A) :
    ∃ Cpt : Set M, IsCompact Cpt ∧ alpha '' Icc a b ⊆ Cpt := by
  have hb : 0 ≤ b := ha.trans hab
  apply lRegRange_compact (I := I) S (S.base.metric T) hg T alpha a b A
    (-2 * b ^ 2 * lRmFactor E K)
    (Real.exp (2 * lRmFactor E K * b ^ 2)) hab (Real.exp_pos _).le
  · intro s hs v
    exact lRegMetric_le_rm (I := I) S hS K T b hb hreg hRm s
      ⟨ha.trans hs.1, hs.2⟩ (alpha s) v
  · intro s hs
    exact lRegPot_lower_rm (I := I) S K T b hb hRm s
      ⟨ha.trans hs.1, hs.2⟩ (alpha s)
  · exact halpha
  · exact hE
  · exact hkin
  · exact hLag
  · exact hact

theorem lRegRanges_of_rm
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
    (hkin : ∀ n, IntervalIntegrable (lRegSpeedSq S T (alpha n)) volume a b)
    (hLag : ∀ n, IntervalIntegrable (lRegLagrangian S T (alpha n)) volume a b)
    (hact : ∀ n, lRegAction S T (alpha n) a b ≤ A) :
    ∃ Cpt : Set M, IsCompact Cpt ∧ ∀ n, alpha n '' Icc a b ⊆ Cpt := by
  have hb : 0 ≤ b := ha.trans hab
  apply lRegRanges_compact (I := I) S (S.base.metric T) hg T alpha x a b A
    (-2 * b ^ 2 * lRmFactor E K)
    (Real.exp (2 * lRmFactor E K * b ^ 2)) hab (Real.exp_pos _).le hstart
  · intro n s hs v
    exact lRegMetric_le_rm (I := I) S hS K T b hb hreg hRm s
      ⟨ha.trans hs.1, hs.2⟩ (alpha n s) v
  · intro n s hs
    exact lRegPot_lower_rm (I := I) S K T b hb hRm s
      ⟨ha.trans hs.1, hs.2⟩ (alpha n s)
  · exact halpha
  · exact hE
  · exact hkin
  · exact hLag
  · exact hact

end DifferentialGeometry.PDE.RicciFlow.Perelman
