import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.CompleteDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarGradientSlab
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinVector
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem lMinSlice_closed_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : M,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    {tau : ℝ} (htau : 0 < tau) (hslab : Icc (T - tau) T ⊆ D.regular) :
    IsClosed {Z : E | (Z, tau) ∈ lMinDomain S T x} := by
  have hleft : T - tau ∈ D.regular := hslab ⟨le_rfl, sub_le_self T htau.le⟩
  obtain ⟨a, ha, hareg⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp
    (nhdsWithin_le_nhds (D.regular_isOpen.mem_nhds hleft))
  have hwide : Icc a T ⊆ D.regular := by
    intro t ht
    rcases le_total t (T - tau) with htl | hlt
    · exact hareg ⟨ht.1, htl⟩
    · exact hslab ⟨hlt, ht.2⟩
  have hsig : 0 < T - a := by linarith
  have hwide' : Icc (T - (T - a)) T ⊆ D.regular := by
    simpa only [sub_sub_cancel] using hwide
  obtain ⟨K, hK'⟩ := hRm (T - a) hsig hwide'
  have hK : ∀ t ∈ Icc a T, ∀ y : M,
      normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K := by
    simpa only [sub_sub_cancel] using hK'
  have hcomplete : ∀ t ∈ Icc a T, RiemannianMetricComplete (S.base.metric t) := by
    intro t ht
    exact complete_of_curvature_bound S hS
      (fun r hr => D.regular_subset (hwide hr))
      (fun r hr => hwide ⟨hr.1.le, hr.2.le⟩) hK ht
      ⟨by linarith, le_rfl⟩ hg
  obtain ⟨G, hG, hgrad⟩ := exists_uniform_scalar_gradient_bound_on_Icc hS ha hwide
    hcomplete hK
  have hKsmall : ∀ t ∈ Icc (T - tau) T, ∀ y : M,
      normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K :=
    fun t ht y => hK t ⟨ha.le.trans ht.1, ht.2⟩ y
  rw [← isSeqClosed_iff_isClosed]
  intro Z Z₀ hmin hZ
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hb2 : (Real.sqrt tau) ^ 2 = tau := Real.sq_sqrt htau.le
  have hregSq : Icc (T - (Real.sqrt tau) ^ 2) T ⊆ D.regular := by
    simpa only [hb2] using hslab
  have hKsq : ∀ t ∈ Icc (T - (Real.sqrt tau) ^ 2) T, ∀ y : M,
      normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K := by
    simpa only [hb2] using hKsmall
  have hgradsq : ∀ t ∈ Icc (T - (Real.sqrt tau) ^ 2) T,
      ∀ y : M, ∀ v : TangentSpace I y,
        |(S.base.metric t).inner y (gradientFun (S.base.metric t) (S.scalar t) y) v| ≤
          G * Real.sqrt ((S.base.metric t).inner y v v) := by
    simpa only [hb2] using hgrad
  have hdom : (Z₀, tau) ∈ lExpPosDom S T x := by
    apply (mem_lExpPosDom S T x Z₀ tau).mpr
    refine ⟨htau, htau.le, ?_⟩
    exact mem_lRegularizedDomain_of_complete_of_scalar_gradient_bound S hS T x Z₀ hg
      hb.le hG hregSq hKsq hgradsq
  apply lMinVec_lim_of_bdd S hS T x hmin hZ hdom
  intro y
  exact lRegularizedCosts_bdd_rm S hS K T 0 (Real.sqrt tau) le_rfl hb.le
    hregSq hKsq x y

end DifferentialGeometry.PDE.RicciFlow.Perelman
