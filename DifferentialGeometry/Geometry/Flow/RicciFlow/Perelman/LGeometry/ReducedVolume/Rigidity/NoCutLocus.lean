import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.ClosedMinimizingSlice
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Rigidity.GaussianJacobian


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem lMinDomain_slice_eq_univ_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : M,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    {tau : ℝ} (htau : 0 < tau) (hslab : Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) :
    {Z : E | (Z, tau) ∈ lMinDomain S T x} = univ := by
  have hclosed := lMinSlice_closed_of_rm S hS T hg x hRm htau hslab
  apply (hclosed.ae_eq_univ_iff_eq (μ := modelHaar)).mp
  filter_upwards [ae_mem_lInjDomain_of_redVolume_eq_one S hS T hg x hRm htau hslab hvol]
    with Z hZ
  have hmin : (Z, tau) ∈ lMinDomain S T x := by
    obtain ⟨sigma, hsigma, hmin⟩ := hZ
    have hdom := ((mem_lMinDomain S T x Z sigma).mp hmin).1
    have hreg : Icc (T - sigma) T ⊆ D.regular := by
      intro t ht
      have ht0 : 0 ≤ T - t := sub_nonneg.mpr ht.2
      have htS : T - t ≤ sigma := by linarith only [ht.1]
      have hsqrt : Real.sqrt (T - t) ∈ Icc (0 : ℝ) (Real.sqrt sigma) :=
        ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt htS⟩
      have h := lExpPosDom_regularity S T x Z hdom hsqrt
      have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
        rw [Real.sq_sqrt ht0]
        ring
      simpa only [heq] using h
    obtain ⟨K, hK⟩ := hRm sigma (htau.trans hsigma) hreg
    exact lMinDomain_down_of_rm S hS K T x Z hmin htau hsigma.le hK
  exact propext (iff_of_true hmin (mem_univ Z))

theorem lInjDomain_eq_univ_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : M,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    {tau s : ℝ} (htau : 0 < tau) (hstau : s < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) :
    lInjDomain S T x s = univ := by
  have hmin := lMinDomain_slice_eq_univ_of_redVolume_eq_one S hS T hg x hRm
    htau hslab hvol
  apply Set.eq_univ_of_forall
  intro Z
  refine ⟨tau, hstau, ?_⟩
  have hZ : Z ∈ {W : E | (W, tau) ∈ lMinDomain S T x} := by
    rw [hmin]
    exact mem_univ Z
  exact hZ

end DifferentialGeometry.PDE.RicciFlow.Perelman
