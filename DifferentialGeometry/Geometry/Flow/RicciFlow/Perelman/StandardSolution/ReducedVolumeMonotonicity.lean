import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InjGeometryComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RedJacobian

set_option autoImplicit false

noncomputable section

open Bundle Set MeasureTheory
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M]
  {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem redVolume_lint_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4
          (S.base.rm04 t z) ≤ K)
    (tau : ℝ) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau =
      ∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E) := by
  obtain ⟨Φ, hsource, _himage, hmap, _hcut, hnull⟩ :=
    exists_lExpPartial_full_of_rm S hS T hg x hRm tau htau hslab
  exact redVolume_lint_of_param S hS T x hRm tau htau
    Φ hsource hmap hnull

theorem redVolume_anti_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4
          (S.base.rm04 t z) ≤ K)
    {tau₁ tau₂ : ℝ} (htau₁ : 0 < tau₁) (h12 : tau₁ ≤ tau₂)
    (hslab : Icc (T - tau₂) T ⊆ D.regular) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau₂ ≤
      DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau₁ := by
  have htau₂ : 0 < tau₂ := htau₁.trans_le h12
  have hslab₁ : Icc (T - tau₁) T ⊆ D.regular := by
    intro t ht
    exact hslab ⟨(sub_le_sub_left h12 T).trans ht.1, ht.2⟩
  have hdomain : lInjDomain S T x tau₂ ⊆ lInjDomain S T x tau₁ := by
    rintro Z ⟨sigma, hsigma, hmin⟩
    exact ⟨sigma, lt_of_le_of_lt h12 hsigma, hmin⟩
  have hpoint : ∀ Z ∈ lInjDomain S T x tau₂,
      lReducedJacobian S T x Z tau₂ ≤ lReducedJacobian S T x Z tau₁ := by
    rintro Z ⟨sigma, hsigma, hmin⟩
    have hsigmapos : 0 < sigma := htau₂.trans hsigma
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
    exact (lRedJac_antitoneOn_of_rm S hS K T x hmin hK)
      ⟨htau₁, lt_of_le_of_lt h12 hsigma⟩ ⟨htau₂, hsigma⟩ h12
  rw [redVolume_lint_of_rm S hS T hg x hRm tau₂ htau₂ hslab,
    redVolume_lint_of_rm S hS T hg x hRm tau₁ htau₁ hslab₁]
  calc
    (∫⁻ Z in lInjDomain S T x tau₂,
        ENNReal.ofReal (lReducedJacobian S T x Z tau₂ * lSourceDensity S T x)
        ∂modelHaar (E := E)) ≤
        ∫⁻ Z in lInjDomain S T x tau₂,
          ENNReal.ofReal (lReducedJacobian S T x Z tau₁ * lSourceDensity S T x)
          ∂modelHaar (E := E) := by
      refine MeasureTheory.setLIntegral_mono'
        (lInj_isOpen_of_rm S hS T hg x hRm tau₂).measurableSet ?_
      intro Z hZ
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hpoint Z hZ)
          (lSourceDensity_pos S T x).le)
    _ ≤ ∫⁻ Z in lInjDomain S T x tau₁,
        ENNReal.ofReal (lReducedJacobian S T x Z tau₁ * lSourceDensity S T x)
        ∂modelHaar (E := E) :=
      MeasureTheory.lintegral_mono_set hdomain

end DifferentialGeometry.PDE.RicciFlow

end
