import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.HarmonicMassRegularity
import DifferentialGeometry.Analysis.ODE.StateCoerciveMass

/-!
# One-radius finite harmonic-map mass families

On a compact initial time window, joint chart-Gram continuity gives one
two-sided comparison constant for all moving volume measures.  This file
converts that comparison into the real total-volume bound used by the finite
state-mass Lipschitz estimate, and then chooses one coefficient radius on
which all moving masses are Lipschitz, uniformly coercive, and continuous in
time.

The radius is selected only after all time-uniform constants have been fixed.
There is no metric-dependent or time-dependent shrinking.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped ENNReal Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M] [ConnectedSpace M]

/-! ## The real total-volume consequence -/

/-- The common two-sided measure comparison on a compact initial window also
gives one real upper bound for every moving total volume.  The same comparison
constant is retained so that its reverse inequality can subsequently provide
the zero-state mass coercivity bound. -/
theorem hmfVolumeReal
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M) {a b c : ℝ} (hcb : c < b)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M ↦
        chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
      (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      (∀ t ∈ Icc a c,
        riemannianVolumeMeasure (I := I) (M := M) (g t) ≤
            C • riemannianVolumeMeasure (I := I) (M := M) q ∧
          riemannianVolumeMeasure (I := I) (M := M) q ≤
            C • riemannianVolumeMeasure (I := I) (M := M) (g t)) ∧
      ∀ t ∈ Icc a c,
        (riemannianVolumeMeasure (I := I) (M := M) (g t)).real Set.univ ≤
          C.toReal *
            (riemannianVolumeMeasure (I := I) (M := M) q).real Set.univ := by
  obtain ⟨C, hC0, hCtop, hvol⟩ :=
    hmfVolumeEquiv (I := I) (M := M) q g hcb hgram
  refine ⟨C, hC0, hCtop, hvol, ?_⟩
  intro t ht
  let μq := riemannianVolumeMeasure (I := I) (M := M) q
  let μt := riemannianVolumeMeasure (I := I) (M := M) (g t)
  haveI : IsFiniteMeasure μq :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) q
  have hle : μt Set.univ ≤ C * μq Set.univ := by
    have h := (hvol t ht).1 Set.univ
    simpa only [μt, μq, Measure.smul_apply, smul_eq_mul] using h
  have htop : C * μq Set.univ ≠ ⊤ :=
    ENNReal.mul_ne_top hCtop (measure_ne_top μq Set.univ)
  have hreal := ENNReal.toReal_mono htop hle
  simpa only [μt, μq, Measure.real, ENNReal.toReal_mul] using hreal

/-! ## Operator-valued time continuity -/

/-- On one state ball chosen before the metric family and compact time set,
the faithful finite mass is continuous in time in operator norm.  The scalar
moving-integral continuity from `hmfStateTime_cont` is promoted through the
two continuous-linear-map arguments, while `hmfSpecMass_state` identifies the
operator integral with the genuine local-addition state mass. -/
theorem hmfSpecTime_cont
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    ∃ R : ℝ, 0 < R ∧
      ∀ (g : ℝ → SmoothRiemannianMetric I M) {K : Set ℝ}, IsCompact K →
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)), ContinuousOn
        (fun p : ℝ × M ↦ chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (K ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      ∀ u : EuclideanSpace ℝ {i // i ∈ S}, u ∈ Metric.ball 0 R →
        ContinuousOn
          (fun t ↦ hmfSpecMassOp (I := I) (M := M) q (g t) S u) K := by
  obtain ⟨Rt, hRt, htime⟩ :=
    hmfStateTime_cont (I := I) (M := M) q S
  obtain ⟨Rm, hRm, hmass⟩ :=
    hmfSpecMassPt_cd (I := I) (M := M) q S
  obtain ⟨Ra, hRa, hmap⟩ :=
    hmfSpecMap_cd (I := I) (M := M) q S 1 (by norm_num)
  let R := min Rt (min Rm Ra)
  have hR : 0 < R := lt_min hRt (lt_min hRm hRa)
  refine ⟨R, hR, ?_⟩
  intro g K hK hgram u hu
  have hu_t : u ∈ Metric.ball
      (0 : EuclideanSpace ℝ {i // i ∈ S}) Rt :=
    Metric.ball_subset_ball (min_le_left Rt (min Rm Ra)) hu
  have hu_m : u ∈ Metric.ball
      (0 : EuclideanSpace ℝ {i // i ∈ S}) Rm :=
    Metric.ball_subset_ball
      ((min_le_right Rt (min Rm Ra)).trans (min_le_left Rm Ra)) hu
  have hu_a : u ∈ Metric.ball
      (0 : EuclideanSpace ℝ {i // i ∈ S}) Ra :=
    Metric.ball_subset_ball
      ((min_le_right Rt (min Rm Ra)).trans (min_le_right Rm Ra)) hu
  have hpt : Continuous
      (fun x : M ↦ hmfSpecMassPt (I := I) (M := M) q S u x) := by
    rw [← continuousOn_univ]
    exact hmass.continuousOn.comp
      (continuousOn_const.prodMk continuousOn_id)
      (fun x _ ↦ ⟨hu_m, Set.mem_univ x⟩)
  have hmd : ∀ x : M,
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
        (fun z : EuclideanSpace ℝ {i // i ∈ S} ↦
          hmfAdd (I := I) (M := M) q
            (hmfSpecIncl (I := I) (M := M) q S z) x) u := by
    intro x
    have hp : (u, x) ∈
        Metric.ball (0 : EuclideanSpace ℝ {i // i ∈ S}) Ra ×ˢ
          (Set.univ : Set M) := ⟨hu_a, Set.mem_univ _⟩
    have hopen : IsOpen
        (Metric.ball (0 : EuclideanSpace ℝ {i // i ∈ S}) Ra ×ˢ
          (Set.univ : Set M)) := Metric.isOpen_ball.prod isOpen_univ
    have hjoint := (hmap (u, x) hp).contMDiffAt (hopen.mem_nhds hp)
    have hincl : ContMDiffAt
        𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S})
        (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) (1 : ℕ∞)
        (fun z : EuclideanSpace ℝ {i // i ∈ S} ↦ (z, x)) u :=
      contMDiffAt_id.prodMk contMDiffAt_const
    exact (hjoint.comp u hincl).mdifferentiableAt (by norm_num)
  rw [continuousOn_clm_apply]
  intro v
  rw [continuousOn_clm_apply]
  intro w
  refine (htime g hK hgram u hu_t v w).congr (fun t ht ↦ ?_)
  have hint : Integrable
      (fun x : M ↦ hmfSpecMassPt (I := I) (M := M) q S u x)
      (riemannianVolumeMeasure (I := I) (M := M) (g t)) :=
    integrableOn_univ.mp
      (hpt.continuousOn.integrableOn_compact isCompact_univ)
  exact (hmfSpecMass_state (I := I) (M := M) q (g t) S u v w hmd hint).symm

/-! ## The compact-window package -/

/-- Joint chart-Gram continuity on an initial window supplies one radius for
the entire finite faithful mass family.  On that radius the family is
uniformly state-Lipschitz, retains half of its common zero-state coercivity,
and is continuous in time in operator norm. -/
theorem hmfMassFamily
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (g : ℝ → SmoothRiemannianMetric I M) {a b c : ℝ} (hcb : c < b)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M ↦
        chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
      (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      (∀ t ∈ Icc a c,
        riemannianVolumeMeasure (I := I) (M := M) (g t) ≤
            C • riemannianVolumeMeasure (I := I) (M := M) q ∧
          riemannianVolumeMeasure (I := I) (M := M) q ≤
            C • riemannianVolumeMeasure (I := I) (M := M) (g t)) ∧
      (∀ t ∈ Icc a c,
        (riemannianVolumeMeasure (I := I) (M := M) (g t)).real Set.univ ≤
          C.toReal *
            (riemannianVolumeMeasure (I := I) (M := M) q).real Set.univ) ∧
      ∃ R : ℝ, 0 < R ∧ ∃ L : ℝ≥0,
        (∀ t ∈ Icc a c, LipschitzOnWith L
          (hmfSpecMassOp (I := I) (M := M) q (g t) S)
          (Metric.closedBall 0 R)) ∧
        (∀ t ∈ Icc a c,
          ∀ u ∈ Metric.closedBall
            (0 : EuclideanSpace ℝ {i // i ∈ S}) R,
          ∀ v : EuclideanSpace ℝ {i // i ∈ S},
            (C.toReal⁻¹ / 2) * ‖v‖ * ‖v‖ ≤
              hmfSpecMassOp (I := I) (M := M) q (g t) S u v v) ∧
        ∀ u ∈ Metric.closedBall
            (0 : EuclideanSpace ℝ {i // i ∈ S}) R,
          ContinuousOn
            (fun t ↦ hmfSpecMassOp (I := I) (M := M) q (g t) S u)
            (Icc a c) := by
  obtain ⟨C, hC0, hCtop, hvol, hvolReal⟩ :=
    hmfVolumeReal (I := I) (M := M) q g hcb hgram
  let B : ℝ≥0 := ⟨C.toReal *
    (riemannianVolumeMeasure (I := I) (M := M) q).real Set.univ,
    mul_nonneg ENNReal.toReal_nonneg measureReal_nonneg⟩
  have hB : ∀ t ∈ Icc a c,
      (riemannianVolumeMeasure (I := I) (M := M) (g t)).real Set.univ ≤ B := by
    intro t ht
    simpa only [B, NNReal.coe_mk] using hvolReal t ht
  obtain ⟨Rl, hRl, L, hlip⟩ :=
    hmfMassFam_lip (I := I) (M := M) q S g B hB
  obtain ⟨Rt, hRt, htime⟩ :=
    hmfSpecTime_cont (I := I) (M := M) q S
  have hCpos : 0 < C.toReal := ENNReal.toReal_pos hC0 hCtop
  have hc0 : 0 < C.toReal⁻¹ := inv_pos.mpr hCpos
  let Rc : ℝ := C.toReal⁻¹ / (2 * ((L : ℝ) + 1))
  have hRc : 0 < Rc := by
    exact div_pos hc0 (mul_pos (by norm_num) (by positivity))
  let R : ℝ := min Rl (min (Rt / 2) Rc)
  have hR : 0 < R := lt_min hRl (lt_min (half_pos hRt) hRc)
  have hR_Rl : R ≤ Rl := min_le_left Rl (min (Rt / 2) Rc)
  have hR_Rt2 : R ≤ Rt / 2 :=
    (min_le_right Rl (min (Rt / 2) Rc)).trans (min_le_left (Rt / 2) Rc)
  have hR_Rc : R ≤ Rc :=
    (min_le_right Rl (min (Rt / 2) Rc)).trans (min_le_right (Rt / 2) Rc)
  have hLR : (L : ℝ) * R ≤ C.toReal⁻¹ / 2 := by
    calc
      (L : ℝ) * R ≤ (L : ℝ) * Rc :=
        mul_le_mul_of_nonneg_left hR_Rc L.coe_nonneg
      _ ≤ ((L : ℝ) + 1) * Rc := by
        exact mul_le_mul_of_nonneg_right (by linarith) hRc.le
      _ = C.toReal⁻¹ / 2 := by
        dsimp only [Rc]
        field_simp [ne_of_gt (show 0 < (L : ℝ) + 1 by positivity)]
  have hgramI : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M ↦ chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
      (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    exact (hgram x₀ i j).mono fun p hp ↦
      ⟨⟨hp.1.1, hp.1.2.trans_lt hcb⟩, hp.2⟩
  have hclosed_lip : Metric.closedBall
      (0 : EuclideanSpace ℝ {i // i ∈ S}) R ⊆
      Metric.closedBall 0 Rl := Metric.closedBall_subset_closedBall hR_Rl
  have hR_Rt : R < Rt := hR_Rt2.trans_lt (half_lt_self hRt)
  have hclosed_time : Metric.closedBall
      (0 : EuclideanSpace ℝ {i // i ∈ S}) R ⊆
      Metric.ball 0 Rt := Metric.closedBall_subset_ball hR_Rt
  refine ⟨C, hC0, hCtop, hvol, hvolReal, R, hR, L, ?_, ?_, ?_⟩
  · intro t ht
    exact (hlip t ht).mono hclosed_lip
  · intro t ht u hu
    exact (DifferentialGeometry.Analysis.ODE.coerOn_of_lip
      (B := hmfSpecMassOp (I := I) (M := M) q (g t) S)
      (c := C.toReal⁻¹) (R := R) (K := L) hR.le
      ((hlip t ht).mono hclosed_lip)
      (hmfSpecMass_lower (I := I) (M := M) q (g t) S C hC0 hCtop
        (hvol t ht).2) hLR) u hu
  · intro u hu
    exact htime g isCompact_Icc hgramI u (hclosed_time hu)

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
