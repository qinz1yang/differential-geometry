import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.LowerBound.FiniteCoverLengthBound

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

theorem sqrt_gap_low
    {a₀ a₁ a omega T : Real} (ha₀a₁ : a₀ < a₁) (ha₁a : a₁ < a)
    (haomega : a < omega) (haT : a ≤ T) (hTomega : T ≤ omega) :
    0 < (a₁ - a₀) / (2 * Real.sqrt (omega - a₀)) ∧
      (a₁ - a₀) / (2 * Real.sqrt (omega - a₀)) ≤
        Real.sqrt (T - a₀) - Real.sqrt (T - a₁) := by
  have hTa₀ : 0 < T - a₀ := by linarith
  have hTa₁ : 0 < T - a₁ := by linarith
  have homegaa₀ : 0 < omega - a₀ := by linarith
  have hbpos : 0 < Real.sqrt (T - a₀) := Real.sqrt_pos.2 hTa₀
  have hcpos : 0 < Real.sqrt (T - a₁) := Real.sqrt_pos.2 hTa₁
  have hBpos : 0 < Real.sqrt (omega - a₀) :=
    Real.sqrt_pos.2 homegaa₀
  have hcsq : (Real.sqrt (T - a₁)) ^ 2 = T - a₁ :=
    Real.sq_sqrt hTa₁.le
  have hbsq : (Real.sqrt (T - a₀)) ^ 2 = T - a₀ :=
    Real.sq_sqrt hTa₀.le
  have hcb : Real.sqrt (T - a₁) ≤ Real.sqrt (T - a₀) :=
    Real.sqrt_le_sqrt (by linarith)
  have hbB : Real.sqrt (T - a₀) ≤ Real.sqrt (omega - a₀) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsum : Real.sqrt (T - a₀) + Real.sqrt (T - a₁) ≤
      2 * Real.sqrt (omega - a₀) := by
    linarith
  have hgap : 0 ≤ Real.sqrt (T - a₀) - Real.sqrt (T - a₁) :=
    sub_nonneg.mpr hcb
  have hid :
      (Real.sqrt (T - a₀) - Real.sqrt (T - a₁)) *
          (Real.sqrt (T - a₀) + Real.sqrt (T - a₁)) =
        a₁ - a₀ := by
    nlinarith
  refine ⟨div_pos (sub_pos.mpr ha₀a₁) (mul_pos (by norm_num) hBpos), ?_⟩
  apply (div_le_iff₀ (mul_pos (by norm_num) hBpos)).2
  rw [← hid]
  exact mul_le_mul_of_nonneg_left hsum hgap

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem redLen_slice_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {a₀ a₁ a omega l₀ : Real} (ha₀a₁ : a₀ < a₁) (ha₁a : a₁ < a)
    (haomega : a < omega) (hregFwd : Icc a₀ a₁ ⊆ D.regular)
    (x₀ : M) :
    ∃ K : Real, ∃ v : ENNReal, 0 ≤ K ∧ 0 < v ∧
      ∀ {T : Real}, a ≤ T → T < omega →
        ∀ {x : M} {W : TangentSpace I x},
          Icc a₀ T ⊆ D.regular →
          Real.sqrt (T - a₀) ∈ lRegDomain S T x W →
          (W, T - a₁) ∈ lMinDomain S T x →
          redLength S T x
              (lRegCurve S T x W (Real.sqrt (T - a₁))) (T - a₁) ≤ l₀ →
          ∃ A : Set M,
            MeasurableSet A ∧
              v ≤ riemannianVolumeMeasure (I := I) (M := M)
                (S.base.metric a₀) A ∧
              ∀ y ∈ A, redLength S T x y (T - a₀) ≤ K := by
  classical
  have ha₀omega : a₀ ≤ omega := by linarith
  obtain ⟨Cg, Cs, R, v, hCg, hCs, hR, hv, hcover⟩ :=
    redLen_cover_bound (I := I) S hS (t₀ := a₀) (t₁ := a₁)
      (omega := omega) ha₀omega hregFwd a₀ x₀
  let beta : Real := Real.sqrt (a - a₀)
  let B : Real := Real.sqrt (omega - a₀)
  let delta : Real := (a₁ - a₀) / (2 * B)
  let N : Real := 2 * B * |l₀| +
    (Cg / 2) * ((2 * R) ^ 2 / delta) + Cs * B
  let K : Real := N / (2 * beta)
  have hbeta : 0 < beta := by
    exact Real.sqrt_pos.2 (by linarith)
  have hB : 0 < B := by
    exact Real.sqrt_pos.2 (by linarith)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact div_pos (sub_pos.mpr ha₀a₁) (mul_pos (by norm_num) hB)
  have hN : 0 ≤ N := by
    dsimp only [N]
    positivity
  have hK : 0 ≤ K := by
    exact div_nonneg hN (mul_nonneg (by norm_num) hbeta.le)
  refine ⟨K, v, hK, hv, ?_⟩
  intro T haT hTomega x W hslab hbdom hmin hred
  let b : Real := Real.sqrt (T - a₀)
  let c : Real := Real.sqrt (T - a₁)
  have hTa₀ : 0 < T - a₀ := by linarith
  have hTa₁ : 0 < T - a₁ := by linarith
  have hb : 0 < b := Real.sqrt_pos.2 hTa₀
  have hc : 0 < c := Real.sqrt_pos.2 hTa₁
  have hbsq : b ^ 2 = T - a₀ := Real.sq_sqrt hTa₀.le
  have hcsq : c ^ 2 = T - a₁ := Real.sq_sqrt hTa₁.le
  have hcb : c < b := by
    exact Real.sqrt_lt_sqrt hTa₁.le (by linarith)
  have hEarly : T - b ^ 2 = a₀ := by rw [hbsq]; ring
  have hslab' : Icc (T - b ^ 2) T ⊆ D.regular := by
    rw [hEarly]
    exact hslab
  have hforward : ∀ r ∈ Icc (0 : Real) (b - c),
      T - (c + r) ^ 2 ∈ Icc a₀ a₁ := by
    intro r hr
    have hcr0 : 0 ≤ c + r := add_nonneg hc.le hr.1
    have hcrle : c + r ≤ b := by linarith [hr.2]
    have hcSqLe : c ^ 2 ≤ (c + r) ^ 2 :=
      (sq_le_sq₀ hc.le hcr0).2 (by linarith [hr.1])
    have hSqLe : (c + r) ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hcr0 hb.le).2 hcrle
    constructor <;> linarith
  have hmin' : (W, c ^ 2) ∈ lMinDomain S T x := by
    rw [hcsq]
    exact hmin
  have hred' : redLength S T x (lRegCurve S T x W c) (c ^ 2) ≤ l₀ := by
    rw [hcsq]
    exact hred
  obtain ⟨A, hAmeas, hAvol, hAlen⟩ :=
    hcover hTomega.le hc hcb hslab' hforward hEarly hbdom hmin' hred'
  refine ⟨A, hAmeas, ?_, ?_⟩
  · rw [← hEarly]
    exact hAvol
  · intro y hy
    have hyLen := hAlen y hy
    rw [hbsq] at hyLen
    have hgap := (sqrt_gap_low ha₀a₁ ha₁a haomega haT hTomega.le).2
    change delta ≤ b - c at hgap
    have hbB : b ≤ B := by
      exact Real.sqrt_le_sqrt (by linarith)
    have hbetaB : beta ≤ b := by
      exact Real.sqrt_le_sqrt (by linarith)
    have hgapB : b - c ≤ B := by linarith
    have hcl₀ : c * l₀ ≤ B * |l₀| := by
      calc
        c * l₀ ≤ c * |l₀| :=
          mul_le_mul_of_nonneg_left (le_abs_self l₀) hc.le
        _ ≤ B * |l₀| :=
          mul_le_mul_of_nonneg_right (hcb.le.trans hbB) (abs_nonneg l₀)
    have hfirst : 2 * c * l₀ ≤ 2 * B * |l₀| := by
      nlinarith
    have hdiv : (2 * R) ^ 2 / (b - c) ≤ (2 * R) ^ 2 / delta :=
      div_le_div_of_nonneg_left (sq_nonneg _) hdelta hgap
    have hgram :
        (Cg / 2) * ((2 * R) ^ 2 / (b - c)) ≤
          (Cg / 2) * ((2 * R) ^ 2 / delta) :=
      mul_le_mul_of_nonneg_left hdiv (div_nonneg hCg (by norm_num))
    have hscalar : Cs * (b - c) ≤ Cs * B :=
      mul_le_mul_of_nonneg_left hgapB hCs
    have hnum :
        2 * c * l₀ + (Cg / 2) * ((2 * R) ^ 2 / (b - c)) +
            Cs * (b - c) ≤ N := by
      dsimp only [N]
      linarith
    have hfrac :
        (2 * c * l₀ + (Cg / 2) * ((2 * R) ^ 2 / (b - c)) +
              Cs * (b - c)) /
            (2 * b) ≤ N / (2 * b) :=
      (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hb)).2 hnum
    have hden : 2 * beta ≤ 2 * b :=
      mul_le_mul_of_nonneg_left hbetaB (by norm_num)
    have hNK : N / (2 * b) ≤ K := by
      dsimp only [K]
      exact div_le_div_of_nonneg_left hN (mul_pos (by norm_num) hbeta) hden
    exact hyLen.trans (hfrac.trans hNK)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
