import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientLocalCoefficientBounds
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.InnerProductSpace.PiL2


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff _root_.Topology BigOperators Matrix

private theorem exists_uniform_quadratic_lower_bound
    {Y V : Type*} [TopologicalSpace Y] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [ProperSpace V] (K : Set Y) (hK : IsCompact K) (Q : Y → V → ℝ)
    (hcont : ContinuousOn (fun p : Y × V => Q p.1 p.2) (K ×ˢ univ))
    (hpos : ∀ y ∈ K, ∀ v : V, v ≠ 0 → 0 < Q y v)
    (hscale : ∀ y v c, Q y (c • v) = c ^ 2 * Q y v) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ y ∈ K, ∀ v : V, ℓ * ‖v‖ ^ 2 ≤ Q y v := by
  let B := K ×ˢ Metric.sphere (0 : V) 1
  have hB : IsCompact B := hK.prod (isCompact_sphere (0 : V) 1)
  have hnorm {v : V} (hv : v ∈ Metric.sphere (0 : V) 1) : ‖v‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hv
  have hunit {v : V} (hv : v ∈ Metric.sphere (0 : V) 1) : v ≠ 0 := by
    intro hv0
    simpa [hv0] using hnorm hv
  by_cases hne : B.Nonempty
  · obtain ⟨p, hp, hmin⟩ := hB.exists_isMinOn hne
      (hcont.mono (fun q hq => ⟨hq.1, mem_univ _⟩))
    refine ⟨Q p.1 p.2, hpos p.1 hp.1 p.2 (hunit hp.2), ?_⟩
    intro y hy v
    by_cases hv : v = 0
    · have hz : Q y (0 : V) = 0 := by simpa using hscale y (0 : V) 0
      simp [hv, hz]
    · have hnormalize : NormedSpace.normalize v ∈ Metric.sphere (0 : V) 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hv
      have hb := hmin (a := (y, NormedSpace.normalize v)) ⟨hy, hnormalize⟩
      have hscaled := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖v‖)
      have heq := hscale y (NormedSpace.normalize v) ‖v‖
      rw [NormedSpace.norm_smul_normalize] at heq
      calc
        _ = ‖v‖ ^ 2 * Q p.1 p.2 := mul_comm _ _
        _ ≤ ‖v‖ ^ 2 * Q y (NormedSpace.normalize v) := hscaled
        _ = Q y v := heq.symm
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y hy v
    by_cases hv : v = 0
    · have hz : Q y (0 : V) = 0 := by simpa using hscale y (0 : V) 0
      simp [hv, hz]
    · have hnormalize : NormedSpace.normalize v ∈ Metric.sphere (0 : V) 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hv
      exact (hne ⟨(y, NormedSpace.normalize v), hy, hnormalize⟩).elim

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]


theorem exists_uniform_ancient_chart_ellipticity
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (p : M) (K : Set E) (hK : IsCompact K) (hKW : K ⊆ (extChartAt I p).target) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ t ∈ Icc a b, ∀ y ∈ K,
      ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
        ℓ * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j,
          chartInvGramOnE (I := I) (S.base.metric t) p i j y * ξ i * ξ j := by
  classical
  let N := Fin (Module.finrank ℝ E)
  let Q := fun q : ℝ × E => fun ξ : EuclideanSpace ℝ N =>
    ∑ i : N, ∑ j : N, chartInvGramOnE (I := I) (S.base.metric q.1) p i j q.2 * ξ i * ξ j
  have hentry (i j : N) : ContinuousOn
      (fun q : ℝ × E => chartInvGramOnE (I := I) (S.base.metric q.1) p i j q.2)
      (Icc a b ×ˢ K) := by
    have h := (continuous_eval_const (fun z : Fin 0 => Fin.elim0 z)).comp_continuousOn
      (solution_chartInvGram_jets_continuousOn_carrier S hS hcarrier hregular p i j 0)
    have hsubset : Icc a b ×ˢ K ⊆ Iic b ×ˢ (extChartAt I p).target :=
      fun q hq => ⟨hq.1.2, hKW hq.2⟩
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using h.mono hsubset
  have hcont : ContinuousOn (fun q : (ℝ × E) × EuclideanSpace ℝ N => Q q.1 q.2)
      ((Icc a b ×ˢ K) ×ˢ univ) := by
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact (((hentry i j).comp continuous_fst.continuousOn (fun q hq => hq.1)).mul
      ((PiLp.continuous_apply (p := 2) (β := fun _ : N => ℝ) i).comp
        continuous_snd).continuousOn).mul
        ((PiLp.continuous_apply (p := 2) (β := fun _ : N => ℝ) j).comp
          continuous_snd).continuousOn
  have hpos : ∀ q ∈ Icc a b ×ˢ K, ∀ ξ : EuclideanSpace ℝ N, ξ ≠ 0 → 0 < Q q ξ := by
    intro q hq ξ hξ
    have hξfun : (fun i : N => ξ i) ≠ 0 := by
      intro heq
      apply hξ
      ext i
      exact congrFun heq i
    have hpd := chartInvGramOnE_posDef (I := I) (S.base.metric q.1) p (hKW hq.2)
    have hdot := hpd.dotProduct_mulVec_pos hξfun
    have heq : star (fun i : N => ξ i) ⬝ᵥ
        (Matrix.of fun i j : N => chartInvGramOnE (I := I) (S.base.metric q.1) p i j q.2)
          *ᵥ (fun i : N => ξ i) = Q q ξ := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Matrix.of_apply, Q]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    exact heq ▸ hdot
  have hscale : ∀ q ξ c, Q q (c • ξ) = c ^ 2 * Q q ξ := by
    intro q ξ c
    dsimp [Q]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ * (c * ξ i) * (c * ξ j) = _
    ring
  obtain ⟨ℓ, hℓ, hbound⟩ := exists_uniform_quadratic_lower_bound
    (Icc a b ×ˢ K) (isCompact_Icc.prod hK) Q hcont hpos hscale
  refine ⟨ℓ, hℓ, ?_⟩
  intro t ht y hy ξ
  have hh := hbound (t, y) ⟨ht, hy⟩ (WithLp.toLp 2 ξ)
  simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply, Q] using hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
