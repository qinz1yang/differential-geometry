import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.SmallVolumeComplete
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.OpenPos


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open scoped ContDiff ENNReal Manifold _root_.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem ae_lReducedJacobian_indicator_eq_gaussian_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau : ℝ} (htau : 0 < tau) (hslab : Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) :
    (lInjDomain S T x tau).indicator
        (fun Z : E => ENNReal.ofReal
          (lReducedJacobian S T x Z tau * lSourceDensity S T x)) =ᵐ[modelHaar]
      fun Z : E => ENNReal.ofReal (lSourceGaussian S T x Z) := by
  let J : E → ℝ≥0∞ := (lInjDomain S T x tau).indicator
    (fun Z => ENNReal.ofReal
      (lReducedJacobian S T x Z tau * lSourceDensity S T x))
  let G : E → ℝ≥0∞ := fun Z => ENNReal.ofReal (lSourceGaussian S T x Z)
  have hU := (lInj_isOpen_of_rm S hS T hg x hRm tau).measurableSet
  have hmass : (∫⁻ Z, J Z ∂modelHaar) = 1 := by
    rw [show (∫⁻ Z, J Z ∂modelHaar) =
      ∫⁻ Z in lInjDomain S T x tau, ENNReal.ofReal
        (lReducedJacobian S T x Z tau * lSourceDensity S T x) ∂modelHaar from
      lintegral_indicator hU _]
    exact (redVolume_lint_of_rm S hS T hg x hRm tau htau hslab).symm.trans hvol
  have hJG : J ≤ᵐ[modelHaar] G := by
    apply ae_of_all
    intro Z
    by_cases hZ : Z ∈ lInjDomain S T x tau
    · simpa only [J, G, Set.indicator_of_mem hZ] using
        lRedJac_src_le_of_rm S hS T x hRm tau htau hZ
    · simp only [J, Set.indicator_of_notMem hZ, zero_le]
  have hG : Measurable G := by
    dsimp only [G]
    unfold lSourceGaussian
    fun_prop
  exact ae_eq_of_ae_le_of_lintegral_le hJG (by rw [hmass]; exact ENNReal.one_ne_top)
    hG.aemeasurable (by rw [hmass]; exact (lSourceGaussian_mass S T x).le)

theorem ae_mem_lInjDomain_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau : ℝ} (htau : 0 < tau) (hslab : Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) :
    ∀ᵐ Z : E ∂modelHaar, Z ∈ lInjDomain S T x tau := by
  filter_upwards [ae_lReducedJacobian_indicator_eq_gaussian_of_redVolume_eq_one
    S hS T hg x hRm htau hslab hvol] with Z hZ
  by_contra hnot
  have hpos : 0 < lSourceGaussian S T x Z := by
    rw [lSourceGaussian_eq_metric_norm]
    exact mul_pos (mul_pos (inv_pos.mpr (Real.rpow_pos_of_pos Real.pi_pos _))
      (lSourceDensity_pos S T x)) (Real.exp_pos _)
  rw [Set.indicator_of_notMem hnot] at hZ
  exact (ENNReal.ofReal_pos.mpr hpos).ne' hZ.symm

theorem lReducedJacobian_mul_source_eq_gaussian_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau : ℝ} (htau : 0 < tau) (hslab : Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    lReducedJacobian S T x Z tau * lSourceDensity S T x =
      lSourceGaussian S T x Z := by
  have hU := lInj_isOpen_of_rm S hS T hg x hRm tau
  have hae : (fun W : E => lReducedJacobian S T x W tau * lSourceDensity S T x)
      =ᵐ[(modelHaar (E := E)).restrict (lInjDomain S T x tau)]
      lSourceGaussian S T x := by
    filter_upwards [ae_restrict_of_ae
      (ae_lReducedJacobian_indicator_eq_gaussian_of_redVolume_eq_one
        S hS T hg x hRm htau hslab hvol), ae_restrict_mem hU.measurableSet]
      with W hW hWU
    rw [Set.indicator_of_mem hWU] at hW
    have hnonneg : 0 ≤ lReducedJacobian S T x W tau * lSourceDensity S T x :=
      mul_nonneg (Real.exp_pos _).le (lSourceDensity_pos S T x).le
    have hgauss : 0 ≤ lSourceGaussian S T x W := by
      rw [lSourceGaussian_eq_metric_norm]
      exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Real.rpow_pos_of_pos Real.pi_pos _).le)
        (lSourceDensity_pos S T x).le) (Real.exp_pos _).le
    exact (ENNReal.ofReal_eq_ofReal_iff hnonneg hgauss).mp hW
  have hcont : Continuous (lSourceGaussian S T x) := by
    unfold lSourceGaussian
    fun_prop
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae hU
    (lRedJac_mul_src_contOn_of_rm S hS T hg x hRm tau htau)
    hcont.continuousOn hZ

theorem hasDerivAt_lReducedJacobian_zero_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau s : ℝ} (hs : 0 < s) (hstau : s < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    HasDerivAt (lReducedJacobian S T x Z) 0 s := by
  have hlocal : lReducedJacobian S T x Z =ᶠ[𝓝 s]
      fun _ => lSourceGaussian S T x Z / lSourceDensity S T x := by
    filter_upwards [isOpen_Ioo.mem_nhds (show s ∈ Ioo (0 : ℝ) tau from ⟨hs, hstau⟩)]
      with r hr
    have hslabr : Icc (T - r) T ⊆ D.regular :=
      (Icc_subset_Icc (sub_le_sub_left hr.2.le T) le_rfl).trans hslab
    have hvolr : redVolume S T x r = 1 := by
      apply le_antisymm
      · exact DifferentialGeometry.PDE.RicciFlow.redVolume_le_one_of_rm
          S hS T hg x hRm r hr.1 hslabr
      · have hmono := DifferentialGeometry.PDE.RicciFlow.redVolume_anti_of_rm
          S hS T hg x hRm hr.1 hr.2.le hslab
        change redVolume S T x tau ≤ redVolume S T x r at hmono
        rwa [hvol] at hmono
    have hZr : Z ∈ lInjDomain S T x r := by
      obtain ⟨sigma, hsigma, hmin⟩ := hZ
      exact ⟨sigma, hr.2.trans hsigma, hmin⟩
    exact (eq_div_iff (lSourceDensity_pos S T x).ne').mpr
      (lReducedJacobian_mul_source_eq_gaussian_of_redVolume_eq_one
        S hS T hg x hRm hr.1 hslabr hvolr hZr)
  exact (hasDerivAt_const s (lSourceGaussian S T x Z / lSourceDensity S T x)).congr_of_eventuallyEq
    hlocal

end DifferentialGeometry.PDE.RicciFlow.Perelman
