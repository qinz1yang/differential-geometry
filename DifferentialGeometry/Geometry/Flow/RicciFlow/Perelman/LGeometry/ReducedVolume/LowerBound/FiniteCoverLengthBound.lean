import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.LowerBound.FiniteChartBallCover

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

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
theorem redLen_cover_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {t₀ t₁ omega : Real} (ht₀omega : t₀ ≤ omega)
    (hregFwd : Icc t₀ t₁ ⊆ D.regular) (tEarly : Real) (x₀ : M) :
    ∃ Cg Cs R : Real, ∃ v : ENNReal,
      0 ≤ Cg ∧ 0 ≤ Cs ∧ 0 < R ∧ 0 < v ∧
        ∀ {T b c l₀ : Real} {x : M} {W : TangentSpace I x},
          T ≤ omega → 0 < c → c < b →
          Icc (T - b ^ 2) T ⊆ D.regular →
          (∀ r ∈ Icc (0 : Real) (b - c),
            T - (c + r) ^ 2 ∈ Icc t₀ t₁) →
          T - b ^ 2 = tEarly →
          b ∈ lRegDomain S T x W → (W, c ^ 2) ∈ lMinDomain S T x →
          redLength S T x (lRegCurve S T x W c) (c ^ 2) ≤ l₀ →
          ∃ A : Set M,
            MeasurableSet A ∧
              v ≤ riemannianVolumeMeasure (I := I) (M := M)
                (S.base.metric (T - b ^ 2)) A ∧
              ∀ y ∈ A,
                redLength S T x y (b ^ 2) ≤
                  (2 * c * l₀ +
                      (Cg / 2) * ((2 * R) ^ 2 / (b - c)) +
                        Cs * (b - c)) /
                    (2 * b) := by
  classical
  obtain ⟨s, Rloc, v, hsne, hvpos, hchart, hcover⟩ :=
    finite_chart_balls (I := I) (M := M) (S.base.metric tEarly) x₀
  have hattach : s.attach.Nonempty := hsne.attach
  have hlocal : ∀ p : {q : M // q ∈ s},
      ∃ Cg Cs : Real, 0 ≤ Cg ∧ 0 ≤ Cs ∧
        ∀ {T b c l₀ : Real} {x : M} {W : TangentSpace I x},
          T ≤ omega → 0 < c → c < b →
          Icc (T - b ^ 2) T ⊆ D.regular →
          (∀ r ∈ Icc (0 : Real) (b - c),
            T - (c + r) ^ 2 ∈ Icc t₀ t₁) →
          b ∈ lRegDomain S T x W → (W, c ^ 2) ∈ lMinDomain S T x →
          lRegCurve S T x W c ∈ (chartAt H p.1).source →
          (extChartAt I p.1) (lRegCurve S T x W c) ∈
            Metric.closedBall ((extChartAt I p.1) p.1) (Rloc p.1) →
          redLength S T x (lRegCurve S T x W c) (c ^ 2) ≤ l₀ →
          let A := (extChartAt I p.1).symm ''
            Metric.ball ((extChartAt I p.1) p.1) (Rloc p.1)
          MeasurableSet A ∧
            0 < riemannianVolumeMeasure (I := I) (M := M)
              (S.base.metric (T - b ^ 2)) A ∧
            ∀ y ∈ A,
              redLength S T x y (b ^ 2) ≤
                (2 * c * l₀ +
                    (Cg / 2) * ((2 * Rloc p.1) ^ 2 / (b - c)) +
                      Cs * (b - c)) /
                  (2 * b) := by
    intro p
    exact redLen_ball_bound (I := I) S hS ht₀omega hregFwd p.1
      ((extChartAt I p.1) p.1) (hchart p.1 p.2).1
      (hchart p.1 p.2).2.1
  choose CgLoc CsLoc hCgLoc hCsLoc hbound using hlocal
  let Cg : Real := s.attach.sup' hattach CgLoc
  let Cs : Real := s.attach.sup' hattach CsLoc
  let R : Real := s.attach.sup' hattach (fun p ↦ Rloc p.1)
  obtain ⟨p₀, hp₀⟩ := hattach
  have hCg : 0 ≤ Cg :=
    (hCgLoc p₀).trans (Finset.le_sup' CgLoc hp₀)
  have hCs : 0 ≤ Cs :=
    (hCsLoc p₀).trans (Finset.le_sup' CsLoc hp₀)
  have hR : 0 < R :=
    (hchart p₀.1 p₀.2).1.trans_le
      (Finset.le_sup' (fun p : {q : M // q ∈ s} ↦ Rloc p.1) hp₀)
  refine ⟨Cg, Cs, R, v, hCg, hCs, hR, hvpos, ?_⟩
  intro T b c l₀ x W hT hc hcb hslab hforward hEarly hbdom hmin hred
  obtain ⟨p, hp, hraySource, hrayBall⟩ :=
    hcover (lRegCurve S T x W c)
  let p' : {q : M // q ∈ s} := ⟨p, hp⟩
  have hpAttach : p' ∈ s.attach := by
    simp only [p', Finset.mem_attach]
  have hCgLe : CgLoc p' ≤ Cg := Finset.le_sup' CgLoc hpAttach
  have hCsLe : CsLoc p' ≤ Cs := Finset.le_sup' CsLoc hpAttach
  have hRLe : Rloc p ≤ R :=
    Finset.le_sup' (fun q : {z : M // z ∈ s} ↦ Rloc q.1) hpAttach
  have hresult := hbound p' hT hc hcb hslab hforward hbdom hmin
    hraySource (Metric.ball_subset_closedBall hrayBall) hred
  let A : Set M := (extChartAt I p).symm ''
    Metric.ball ((extChartAt I p) p) (Rloc p)
  change MeasurableSet A ∧
      0 < riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric (T - b ^ 2)) A ∧
      ∀ y ∈ A,
        redLength S T x y (b ^ 2) ≤
          (2 * c * l₀ +
              (CgLoc p' / 2) * ((2 * Rloc p) ^ 2 / (b - c)) +
                CsLoc p' * (b - c)) /
            (2 * b) at hresult
  refine ⟨A, hresult.1, ?_, ?_⟩
  · rw [hEarly]
    exact (hchart p hp).2.2
  · intro y hy
    have hlocalBound := hresult.2.2 y hy
    have hrad : (2 * Rloc p) ^ 2 ≤ (2 * R) ^ 2 := by
      apply (sq_le_sq₀ (mul_nonneg (by norm_num) (hchart p hp).1.le)
        (mul_nonneg (by norm_num) hR.le)).2
      exact mul_le_mul_of_nonneg_left hRLe (by norm_num)
    have hfrac : (2 * Rloc p) ^ 2 / (b - c) ≤
        (2 * R) ^ 2 / (b - c) :=
      (div_le_div_iff_of_pos_right (sub_pos.mpr hcb)).2 hrad
    have hqnonneg : 0 ≤ (2 * Rloc p) ^ 2 / (b - c) :=
      div_nonneg (sq_nonneg _) (sub_nonneg.mpr hcb.le)
    have hCgTerm :
        (CgLoc p' / 2) * ((2 * Rloc p) ^ 2 / (b - c)) ≤
          (Cg / 2) * ((2 * R) ^ 2 / (b - c)) := by
      calc
        (CgLoc p' / 2) * ((2 * Rloc p) ^ 2 / (b - c)) ≤
            (Cg / 2) * ((2 * Rloc p) ^ 2 / (b - c)) :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hCgLe (by norm_num)) hqnonneg
        _ ≤ (Cg / 2) * ((2 * R) ^ 2 / (b - c)) :=
          mul_le_mul_of_nonneg_left hfrac (div_nonneg hCg (by norm_num))
    have hCsTerm : CsLoc p' * (b - c) ≤ Cs * (b - c) :=
      mul_le_mul_of_nonneg_right hCsLe (sub_nonneg.mpr hcb.le)
    have hb : 0 < b := hc.trans hcb
    exact hlocalBound.trans <| by
      apply (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hb)).2
      linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
