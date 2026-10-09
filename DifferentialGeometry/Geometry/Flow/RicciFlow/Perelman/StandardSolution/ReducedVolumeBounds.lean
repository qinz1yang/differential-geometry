import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.SourceGaussian
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.PositiveDefinite.GaussianTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.SmallReducedComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CutTime

set_option autoImplicit false
noncomputable section

open Bundle Filter Set MeasureTheory
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] in
theorem lSourceGaussian_tail_eq_spd
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (R : ℝ) :
    (∫⁻ Z : E in {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
      ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E)) =
      ∫⁻ y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) in
        {y | R < Real.sqrt (inner ℝ y
          (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E))
            (𝕜 := ℝ) (lSourceGram S T x) y))},
        ENNReal.ofReal
          (((Real.pi : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
            Real.sqrt (lSourceGram S T x).det *
            Real.exp (-inner ℝ y
              (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E))
                (𝕜 := ℝ) (lSourceGram S T x) y))) ∂volume := by
  classical
  let A := lSourceGram S T x
  let e := toEuclidean (E := E)
  let sE : Set E := {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)}
  let sU : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    {y | R < Real.sqrt (inner ℝ y
      (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E)) (𝕜 := ℝ) A y))}
  let G : E → ℝ≥0∞ := sE.indicator (fun Z ↦ ENNReal.ofReal (lSourceGaussian S T x Z))
  have hsE : MeasurableSet sE := by
    dsimp only [sE]
    apply measurableSet_lt measurable_const
    fun_prop
  have hsU : MeasurableSet sU := by
    dsimp only [sU]
    apply measurableSet_lt measurable_const
    fun_prop
  have hmem : ∀ y, e.symm y ∈ sE ↔ y ∈ sU := by
    intro y
    simp only [sE, sU, Set.mem_ofPred_eq]
    have hquad := lSourceGram_quadraticForm S T x (e.symm y)
    simp only [e, ContinuousLinearEquiv.apply_symm_apply] at hquad
    rw [← hquad]
  have hpoint : ∀ y,
      G (e.symm y) =
        sU.indicator
          (fun z ↦ ENNReal.ofReal
            (((Real.pi : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
              Real.sqrt A.det * Real.exp (-inner ℝ z
                (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E))
                  (𝕜 := ℝ) A z)))) y := by
    intro y
    by_cases hy : y ∈ sU
    · have hEy : e.symm y ∈ sE := (hmem y).mpr hy
      simp only [G, Set.indicator_of_mem hEy, Set.indicator_of_mem hy]
      rw [lSourceGaussian_eq_metric_norm]
      have hquad := lSourceGram_quadraticForm S T x (e.symm y)
      simp only [e, ContinuousLinearEquiv.apply_symm_apply] at hquad
      rw [← hquad]
      rfl
    · have hEy : e.symm y ∉ sE := fun h ↦ hy ((hmem y).mp h)
      simp only [G, Set.indicator_of_notMem hEy,
        Set.indicator_of_notMem hy]
  calc
    (∫⁻ Z : E in sE, ENNReal.ofReal (lSourceGaussian S T x Z)
        ∂modelHaar (E := E)) =
        ∫⁻ Z : E, G Z ∂modelHaar (E := E) := by
      rw [← lintegral_indicator hsE]
    _ = ∫⁻ y, G ((toEuclidean (E := E)).symm y)
        ∂Measure.map (toEuclidean (E := E)) (modelHaar (E := E)) := by
      symm
      calc
        (∫⁻ y, G ((toEuclidean (E := E)).symm y)
            ∂Measure.map (toEuclidean (E := E)) (modelHaar (E := E))) =
            ∫⁻ Z, G ((toEuclidean (E := E)).symm (toEuclidean Z))
              ∂modelHaar (E := E) :=
          (toEuclidean (E := E)).toHomeomorph.measurableEmbedding.lintegral_map _
        _ = ∫⁻ Z, G Z ∂modelHaar (E := E) := by
          refine lintegral_congr fun Z ↦ ?_
          rw [ContinuousLinearEquiv.symm_apply_apply]
    _ = ∫⁻ y, G ((toEuclidean (E := E)).symm y)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
      rw [map_toEuclidean_modelHaar_eq_volume (E := E)]
    _ = ∫⁻ y in sU, ENNReal.ofReal
        (((Real.pi : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
          Real.sqrt A.det * Real.exp (-inner ℝ y
            (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E))
              (𝕜 := ℝ) A y))) ∂volume := by
      rw [← lintegral_indicator hsU]
      exact lintegral_congr fun y ↦ by
        simpa only [e] using hpoint y

theorem lRedJac_src_le_of_rm
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    (tau : ℝ) (htau : 0 < tau) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x) ≤
      ENNReal.ofReal (lSourceGaussian S T x Z) := by
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  have hsigmapos : 0 < sigma := htau.trans hsigma
  have hdom : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).mp hmin).1
  have hregSigma : Icc (T - sigma) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hback : T - t ≤ sigma := by linarith only [ht.1]
    have hsqrt : Real.sqrt (T - t) ∈ Icc (0 : ℝ) (Real.sqrt sigma) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
    have hclock := lExpPosDom_regularity S T x Z hdom hsqrt
    have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
      rw [Real.sq_sqrt hnonneg]
      ring
    simpa only [heq] using hclock
  obtain ⟨K, hK⟩ := hRm sigma hsigmapos hregSigma
  apply ENNReal.ofReal_le_ofReal
  rw [lSourceGaussian_eq_metric_norm]
  calc
    lReducedJacobian S T x Z tau * lSourceDensity S T x ≤
        (((Real.pi : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
          Real.exp (-(S.base.metric T).inner x Z Z)) * lSourceDensity S T x :=
      mul_le_mul_of_nonneg_right
        (lRedJac_le_gauss_of_rm S hS K T x hmin htau hsigma hK)
        (lSourceDensity_pos S T x).le
    _ = ((Real.pi : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
        lSourceDensity S T x * Real.exp (-(S.base.metric T).inner x Z Z) := by
      ring

theorem lRedJac_tail_le_of_rm
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    (tau R : ℝ) (htau : 0 < tau) :
    (∫⁻ Z : E in lInjDomain S T x tau ∩
        {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
      ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E)) ≤
      ∫⁻ Z : E in {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
        ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E) := by
  have hgauss : Measurable (fun Z : E ↦ ENNReal.ofReal (lSourceGaussian S T x Z)) := by
    unfold lSourceGaussian
    fun_prop
  calc
    (∫⁻ Z : E in lInjDomain S T x tau ∩
        {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
      ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E)) ≤
        ∫⁻ Z : E in lInjDomain S T x tau ∩
          {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
          ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E) :=
      setLIntegral_mono hgauss fun Z hZ ↦
        lRedJac_src_le_of_rm S hS T x hRm tau htau hZ.1
    _ ≤ ∫⁻ Z : E in {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
        ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E) :=
      lintegral_mono_set inter_subset_right

theorem lRedJac_tail_unif_of_rm (eps : ℝ≥0∞) (heps : 0 < eps) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ (D : RealTimeInterval) (S : SolutionOn (I := I) (M := M) D),
        IsSolutionOn (I := I) S → ∀ (T : ℝ) (x : M),
        (∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
          ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : M,
            normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K) →
        ∀ tau : ℝ, 0 < tau →
        (∫⁻ Z : E in lInjDomain S T x tau ∩
            {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
          ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
            ∂modelHaar (E := E)) ≤ eps := by
  let : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  obtain ⟨R, hR, htail⟩ :=
    gaussianPosDef_uniform_tail (n := Fin (Module.finrank ℝ E)) eps heps
  refine ⟨R, hR, ?_⟩
  intro D S hS T x hRm tau htau
  refine (lRedJac_tail_le_of_rm S hS T x hRm tau R htau).trans ?_
  rw [lSourceGaussian_tail_eq_spd S T x R]
  simpa only [Fintype.card_fin] using htail (lSourceGram S T x) (lSourceGram_posDef S T x)

variable [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]

theorem redVolume_le_one_of_rm
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (hg : RiemannianMetricComplete (I := I) (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    (tau : ℝ) (htau : 0 < tau) (hslab : Icc (T - tau) T ⊆ D.regular) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau ≤ 1 := by
  rw [redVolume_lint_of_rm S hS T hg x hRm tau htau hslab]
  calc
    (∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E)) ≤
        ∫⁻ Z in lInjDomain S T x tau,
          ENNReal.ofReal (lSourceGaussian S T x Z) ∂modelHaar (E := E) := by
      refine setLIntegral_mono'
        (measurableSet_lInjDomain_of_rm S hS T x hRm tau) ?_
      intro Z hZ
      exact lRedJac_src_le_of_rm S hS T x hRm tau htau hZ
    _ ≤ ∫⁻ Z : E, ENNReal.ofReal (lSourceGaussian S T x Z)
        ∂modelHaar (E := E) := setLIntegral_le_lintegral _ _
    _ = 1 := lSourceGaussian_mass S T x

end DifferentialGeometry.PDE.RicciFlow

end
