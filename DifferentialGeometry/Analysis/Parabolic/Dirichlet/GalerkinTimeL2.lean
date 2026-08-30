import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GalerkinSequence
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MetricComparison
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2
import DifferentialGeometry.Geometry.Metric.Family.UniformEquivalence

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal
  RealInnerProductSpace InnerProductSpace BigOperators

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private lemma norm_smoothToH1ComplDirichlet_sq
    {q : SmoothRiemannianMetric (I_half n) M}
    (u : SmoothScalarDirichlet q) :
    ‖smoothToH1ComplDirichlet q u‖ ^ 2 =
      dirichletMass q u u + dirichletEnergy q u u := by
  rw [show ‖smoothToH1ComplDirichlet q u‖ = ‖u‖ by
    exact UniformSpace.Completion.norm_coe u]
  rw [u.norm_sq_eq_inner_self]
  rfl

private lemma trajectory_continuousOn
    {q : SmoothRiemannianMetric (I_half n) M}
    {T : ℝ} {s : Finset (SmoothDirichletBasisIndex q)}
    {γ : ℝ → EuclideanSpace ℝ s}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) T)) :
    ContinuousOn (fun t => smoothToH1ComplDirichlet q
      (smoothDirichletBasisFinIncl s (γ t))) (Icc (0 : ℝ) T) := by
  have hJ : Continuous (smoothDirichletBasisFinIncl s) :=
    LinearMap.continuous_of_finiteDimensional _
  exact (smoothToH1ComplDirichlet q).continuous.comp_continuousOn
    (hJ.comp_continuousOn hγ)

private lemma exists_timeL2_trajectory_of_bounds
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    {s : Finset (SmoothDirichletBasisIndex q)}
    {γ : ℝ → EuclideanSpace ℝ s}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) T))
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    {Cv : ℝ≥0∞} (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
          Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q ∧
        riemannianVolumeMeasure (I := I_half n) (M := M) q ≤
          Cv • riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t))
    {A B : ℝ}
    (hmass : ∀ t ∈ Icc (0 : ℝ) T,
      dirichletMass (G.metric t)
          (smoothDirichletBasisFinIncl s (γ t))
          (smoothDirichletBasisFinIncl s (γ t)) ≤ A)
    (henergy : (∫ t in (0 : ℝ)..T,
      dirichletEnergy (G.metric t)
          (smoothDirichletBasisFinIncl s (γ t))
          (smoothDirichletBasisFinIncl s (γ t))) ≤ B) :
    ∃ U : DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeL2
        (H1ComplDirichlet q) T,
      U =ᵐ[DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeMeasure T]
          (fun t => smoothToH1ComplDirichlet q
            (smoothDirichletBasisFinIncl s (γ t))) ∧
        ‖U‖ ^ 2 ≤ Cv.toReal * (T * A + Cg * B) := by
  let J := smoothDirichletBasisFinIncl s
  let u : ℝ → SmoothScalarDirichlet q := fun t => J (γ t)
  have hucont : ContinuousOn
      (fun t => smoothToH1ComplDirichlet q (u t)) (Icc (0 : ℝ) T) := by
    simpa only [u, J] using trajectory_continuousOn hγ
  let U : DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeL2
      (H1ComplDirichlet q) T :=
    DifferentialGeometry.Analysis.Parabolic.TimeSobolev.ofContinuousOn hucont
  have hU : U =ᵐ[
      DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeMeasure T]
      (fun t => smoothToH1ComplDirichlet q (u t)) :=
    DifferentialGeometry.Analysis.Parabolic.TimeSobolev.coeFn_ofContinuousOn hucont
  have hmasscont : ContinuousOn
      (fun t => dirichletMass (G.metric t) (u t) (u t)) (Icc (0 : ℝ) T) := by
    have hform := dirichletFinMass_cont G.metric isCompact_Icc
      (fun x₀ i j => hG.chartGramMatrix_continuousOn hreg x₀ i j) J
    have hfirst := hform.clm_apply hγ
    have hsecond := hfirst.clm_apply hγ
    simpa only [u, J, dirichletFinMass_apply] using hsecond
  have henergycont : ContinuousOn
      (fun t => dirichletEnergy (G.metric t) (u t) (u t)) (Icc (0 : ℝ) T) := by
    have hform := dirichletFinEnergy_cont hG isCompact_Icc hreg J
    have hfirst := hform.clm_apply hγ
    have hsecond := hfirst.clm_apply hγ
    simpa only [u, J, dirichletFinEnergy_apply] using hsecond
  have hpoint : ∀ t ∈ Icc (0 : ℝ) T,
      ‖smoothToH1ComplDirichlet q (u t)‖ ^ 2 ≤
        Cv.toReal * dirichletMass (G.metric t) (u t) (u t) +
          Cv.toReal * Cg * dirichletEnergy (G.metric t) (u t) (u t) := by
    intro t ht
    have hm := dirichletMass_self_rev (G.metric t) Cv hCv0 hCvtop
      (hvol t ht).2 (u t)
    have he := dirichletEnergy_self_le_of_metric_and_volume
      (G.metric t) hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht).2 (u t)
    rw [norm_smoothToH1ComplDirichlet_sq]
    linarith
  have hleftcont : ContinuousOn
      (fun t => ‖smoothToH1ComplDirichlet q (u t)‖ ^ 2) (Icc (0 : ℝ) T) :=
    hucont.norm.pow 2
  have hrightcont : ContinuousOn
      (fun t => Cv.toReal * dirichletMass (G.metric t) (u t) (u t) +
        Cv.toReal * Cg * dirichletEnergy (G.metric t) (u t) (u t))
      (Icc (0 : ℝ) T) :=
    (continuousOn_const.mul hmasscont).add (continuousOn_const.mul henergycont)
  have hmono : (∫ t in (0 : ℝ)..T,
      ‖smoothToH1ComplDirichlet q (u t)‖ ^ 2) ≤
      ∫ t in (0 : ℝ)..T,
        Cv.toReal * dirichletMass (G.metric t) (u t) (u t) +
          Cv.toReal * Cg * dirichletEnergy (G.metric t) (u t) (u t) :=
    intervalIntegral.integral_mono_on hT
      (hleftcont.intervalIntegrable_of_Icc hT)
      (hrightcont.intervalIntegrable_of_Icc hT) hpoint
  have hmassint : (∫ t in (0 : ℝ)..T,
      dirichletMass (G.metric t) (u t) (u t)) ≤ T * A := by
    have h := intervalIntegral.integral_mono_on hT
      (hmasscont.intervalIntegrable_of_Icc hT)
      (_root_.intervalIntegrable_const (μ := volume))
      (fun t ht => by simpa only [u, J] using hmass t ht)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] using h
  have hbound : (∫ t in (0 : ℝ)..T,
      ‖smoothToH1ComplDirichlet q (u t)‖ ^ 2) ≤
      Cv.toReal * (T * A + Cg * B) := by
    calc
      (∫ t in (0 : ℝ)..T, ‖smoothToH1ComplDirichlet q (u t)‖ ^ 2) ≤
          ∫ t in (0 : ℝ)..T,
            Cv.toReal * dirichletMass (G.metric t) (u t) (u t) +
              Cv.toReal * Cg * dirichletEnergy (G.metric t) (u t) (u t) := hmono
      _ = Cv.toReal * (∫ t in (0 : ℝ)..T,
            dirichletMass (G.metric t) (u t) (u t)) +
          Cv.toReal * Cg * (∫ t in (0 : ℝ)..T,
            dirichletEnergy (G.metric t) (u t) (u t)) := by
        rw [intervalIntegral.integral_add
          ((hmasscont.intervalIntegrable_of_Icc hT).const_mul Cv.toReal)
          ((henergycont.intervalIntegrable_of_Icc hT).const_mul
            (Cv.toReal * Cg)),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
      _ ≤ Cv.toReal * (T * A + Cg * B) := by
        have hCv : 0 ≤ Cv.toReal := ENNReal.toReal_nonneg
        have hCg0 : 0 ≤ Cg := le_trans (by norm_num) hCg
        calc
          Cv.toReal * (∫ t in (0 : ℝ)..T,
                dirichletMass (G.metric t) (u t) (u t)) +
              Cv.toReal * Cg * (∫ t in (0 : ℝ)..T,
                dirichletEnergy (G.metric t) (u t) (u t)) ≤
              Cv.toReal * (T * A) + Cv.toReal * Cg * B :=
            add_le_add (mul_le_mul_of_nonneg_left hmassint hCv)
              (mul_le_mul_of_nonneg_left henergy (mul_nonneg hCv hCg0))
          _ = Cv.toReal * (T * A + Cg * B) := by ring
  refine ⟨U, ?_, ?_⟩
  · simpa only [u, J] using hU
  rw [DifferentialGeometry.Analysis.Parabolic.TimeSobolev.norm_sq_eq_integral]
  have hUintegral :
      (∫ t in Icc (0 : ℝ) T, ‖U t‖ ^ 2) =
        ∫ t in Icc (0 : ℝ) T,
          ‖smoothToH1ComplDirichlet q (u t)‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hU] with t ht
    rw [ht]
  rw [hUintegral, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hT]
  exact hbound

theorem exists_dirichletGalerkin_timeL2_sequence
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 < T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hXcont : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (a : ℝ → ℝ) (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    (Bx Bv : ℝ)
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv)
    (ha : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ a t)
    (f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    ∃ γ : (m : ℕ) → ℝ →
        EuclideanSpace ℝ (smoothDirichletBasisFinset q m),
      ∃ U : ℕ → DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeL2
          (H1ComplDirichlet q) T,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ m,
          γ m 0 = smoothDirichletBasisCoordinates
              (smoothDirichletBasisFinset q m) f₀ ∧
          ContinuousOn (γ m) (Icc (0 : ℝ) T) ∧
          (∀ t, (ht : t ∈ Ico (0 : ℝ) T) →
            ∃ v : EuclideanSpace ℝ (smoothDirichletBasisFinset q m),
              HasDerivWithinAt (γ m) v (Ici (0 : ℝ)) t ∧
              dirichletFinMass (G.metric t)
                  (smoothDirichletBasisFinIncl
                    (smoothDirichletBasisFinset q m)) v =
                dirichletFinWeakForm (G.metric t) (X t) (a t)
                  (smoothDirichletBasisFinIncl
                    (smoothDirichletBasisFinset q m)) (γ m t)) ∧
          U m =ᵐ[DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeMeasure T]
            (fun t => smoothToH1ComplDirichlet q
              (smoothDirichletBasisFinIncl
                (smoothDirichletBasisFinset q m) (γ m t))) ∧
          ‖U m‖ ^ 2 ≤ C * ‖f₀‖ ^ 2 := by
  classical
  obtain ⟨γ, hγ⟩ := exists_dirichletGalerkin_sequence hG hT hreg X hXcont
    a hacont Bx Bv hX htrace ha f₀
  obtain ⟨Cg, hCg, hequiv⟩ :=
    exists_metric_equivalence_bound_on_icc_of_metricFamilySmoothOn
      G.metric hG (fun _ ht => D.regular_subset (hreg ht)) q
  obtain ⟨Cv, hCv0, hCvtop, hvol⟩ := volume_uniform_equiv
    (I := I_half n) (M := M) q G.metric isCompact_Icc
    (fun x₀ i j => hG.chartGramMatrix_continuousOn hreg x₀ i j)
  let K := max (Bx + (1 / 2) * Bv) 0
  let F := 1 + K * T * Real.exp (K * T)
  let C := Cv.toReal ^ 2 * (T * Real.exp (K * T) + Cg * F)
  have hK : 0 ≤ K := le_max_right _ _
  have hF : 0 ≤ F := by
    dsimp only [F]
    positivity
  have hCv : 0 ≤ Cv.toReal := ENNReal.toReal_nonneg
  have hCg0 : 0 ≤ Cg := le_trans (by norm_num) hCg
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hU : ∀ m : ℕ,
      ∃ U : DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeL2
          (H1ComplDirichlet q) T,
        U =ᵐ[DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeMeasure T]
          (fun t => smoothToH1ComplDirichlet q
            (smoothDirichletBasisFinIncl
              (smoothDirichletBasisFinset q m) (γ m t))) ∧
        ‖U‖ ^ 2 ≤ C * ‖f₀‖ ^ 2 := by
    intro m
    let s := smoothDirichletBasisFinset q m
    let J := smoothDirichletBasisFinIncl s
    let u₀ := smoothDirichletBasisApproximation q m f₀
    have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    have hnorm : ‖smoothToLpDirichlet q u₀‖ ^ 2 ≤ ‖f₀‖ ^ 2 := by
      have hle := norm_smoothToLpDirichlet_smoothDirichletBasisApproximation_le
        q m f₀
      nlinarith [norm_nonneg (smoothToLpDirichlet q u₀), norm_nonneg f₀]
    have hinit :
        dirichletMass (G.metric 0) u₀ u₀ ≤ Cv.toReal * ‖f₀‖ ^ 2 := by
      calc
        dirichletMass (G.metric 0) u₀ u₀ ≤
            Cv.toReal * dirichletMass q u₀ u₀ :=
          dirichletMass_self_le_of_volume (G.metric 0) Cv hCv0 hCvtop
            (hvol 0 hzero).1 u₀
        _ = Cv.toReal * ‖smoothToLpDirichlet q u₀‖ ^ 2 := by
          rw [show dirichletMass q u₀ u₀ =
              ‖smoothToLpDirichlet q u₀‖ ^ 2 from
            u₀.norm_smoothToLp_sq.symm]
        _ ≤ Cv.toReal * ‖f₀‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hnorm hCv
    have hmass : ∀ t ∈ Icc (0 : ℝ) T,
        dirichletMass (G.metric t) (J (γ m t)) (J (γ m t)) ≤
          Cv.toReal * ‖f₀‖ ^ 2 * Real.exp (K * T) := by
      intro t ht
      have hraw := (hγ m).2.2.2.1 t ht
      have hmul := mul_le_mul_of_nonneg_right hinit (Real.exp_pos (K * T)).le
      simpa only [K, s, J, u₀] using hraw.trans hmul
    have henergy : (∫ t in (0 : ℝ)..T,
        dirichletEnergy (G.metric t) (J (γ m t)) (J (γ m t))) ≤
          Cv.toReal * ‖f₀‖ ^ 2 * F := by
      have hraw := (hγ m).2.2.2.2 T ⟨hT.le, le_rfl⟩
      have hmul := mul_le_mul_of_nonneg_right hinit hF
      simpa only [K, F, s, J, u₀] using hraw.trans hmul
    obtain ⟨U, hUtie, hUbound⟩ := exists_timeL2_trajectory_of_bounds
      hG hT.le hreg (hγ m).2.1 hCg hequiv hCv0 hCvtop hvol hmass henergy
    refine ⟨U, ?_, ?_⟩
    · simpa only [s, J] using hUtie
    calc
      ‖U‖ ^ 2 ≤ Cv.toReal *
          (T * (Cv.toReal * ‖f₀‖ ^ 2 * Real.exp (K * T)) +
            Cg * (Cv.toReal * ‖f₀‖ ^ 2 * F)) := hUbound
      _ = C * ‖f₀‖ ^ 2 := by
        dsimp only [C]
        ring
  choose U hU using hU
  refine ⟨γ, U, C, hC, ?_⟩
  intro m
  exact ⟨(hγ m).1, (hγ m).2.1, (hγ m).2.2.1, (hU m).1, (hU m).2⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
