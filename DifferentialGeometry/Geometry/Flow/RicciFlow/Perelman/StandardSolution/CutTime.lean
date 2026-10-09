import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinVector
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinPrefix

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem lInjDomain_eq_iUnion_rat_of_down
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ)
    (hdown : ∀ {Z : E} {sigma rho : ℝ},
      (Z, sigma) ∈ lMinDomain S T x →
      0 < rho → rho ≤ sigma →
      (Z, rho) ∈ lMinDomain S T x) :
    lInjDomain S T x tau =
      ⋃ q : {q : ℚ // max tau 0 < (q : ℝ)},
        {Z : E | (Z, (q.1 : ℝ)) ∈ lMinDomain S T x} := by
  ext Z
  change (∃ sigma > tau, (Z, sigma) ∈ lMinDomain S T x) ↔ _
  constructor
  · rintro ⟨sigma, hsigma, hmin⟩
    have hsigmaPos : 0 < sigma :=
      lMinDomain_pos S T x Z sigma hmin
    obtain ⟨q, hqlo, hqhi⟩ :=
      exists_rat_btwn (max_lt hsigma hsigmaPos)
    refine mem_iUnion.mpr ⟨⟨q, hqlo⟩, ?_⟩
    exact hdown hmin ((le_max_right tau 0).trans_lt hqlo) hqhi.le
  · intro hZ
    rcases mem_iUnion.mp hZ with ⟨q, hq⟩
    exact ⟨(q.1 : ℝ), (le_max_left tau 0).trans_lt q.2, hq⟩

private theorem lCutDomain_eq_diff
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ) :
    lCutDomain S T x tau =
      {Z : E | (Z, tau) ∈ lMinDomain S T x} \
        lInjDomain S T x tau := by
  ext Z
  exact mem_lCutDomain S T x tau Z

noncomputable def lCutTime
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (Z : E) : ℝ≥0∞ :=
  ⨆ sigma : {sigma : ℝ // (Z, sigma) ∈ lMinDomain S T x},
    ENNReal.ofReal sigma.1

theorem ofReal_lt_lCutTime_iff
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ) (Z : E) :
    ENNReal.ofReal tau < lCutTime S T x Z ↔
      Z ∈ lInjDomain S T x tau := by
  unfold lCutTime
  rw [lt_iSup_iff]
  constructor
  · rintro ⟨sigma, hsigma⟩
    refine ⟨sigma.1, ?_, sigma.2⟩
    exact (ENNReal.ofReal_lt_ofReal_iff
      (lMinDomain_pos S T x Z sigma.1 sigma.2)).1 hsigma
  · rintro ⟨sigma, hsigma, hmin⟩
    refine ⟨⟨sigma, hmin⟩, ?_⟩
    exact (ENNReal.ofReal_lt_ofReal_iff
      (lMinDomain_pos S T x Z sigma hmin)).2 hsigma

theorem mem_lCutDomain_iff_lCutTime_eq
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ) (Z : E) :
    Z ∈ lCutDomain S T x tau ↔
      (Z, tau) ∈ lMinDomain S T x ∧ lCutTime S T x Z = ENNReal.ofReal tau := by
  rw [mem_lCutDomain S T x tau Z]
  constructor
  · rintro ⟨hmin, hnot⟩
    refine ⟨hmin, le_antisymm ?_ ?_⟩
    · exact le_of_not_gt (fun h => hnot ((ofReal_lt_lCutTime_iff S T x tau Z).mp h))
    · exact le_iSup_of_le (⟨tau, hmin⟩ : {sigma : ℝ // (Z, sigma) ∈ lMinDomain S T x}) le_rfl
  · rintro ⟨hmin, heq⟩
    refine ⟨hmin, ?_⟩
    intro hinj
    have hlt := (ofReal_lt_lCutTime_iff S T x tau Z).mpr hinj
    rw [heq] at hlt
    exact (lt_irrefl _) hlt

section Measurable

variable [MeasurableSpace E]

private theorem lInjDomain_meas_of_down
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ)
    (hdown : ∀ {Z : E} {sigma rho : ℝ},
      (Z, sigma) ∈ lMinDomain S T x →
      0 < rho → rho ≤ sigma →
      (Z, rho) ∈ lMinDomain S T x)
    (hslice : ∀ rho : ℝ, 0 < rho →
      MeasurableSet {Z : E | (Z, rho) ∈ lMinDomain S T x}) :
    MeasurableSet (lInjDomain S T x tau) := by
  rw [lInjDomain_eq_iUnion_rat_of_down S T x tau hdown]
  apply MeasurableSet.iUnion
  intro q
  exact hslice (q.1 : ℝ) ((le_max_right tau 0).trans_lt q.2)

private theorem lCutTime_measurable_of_inj
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M)
    (hinj : ∀ tau : ℝ,
      MeasurableSet (lInjDomain S T x tau)) :
    Measurable (lCutTime S T x) := by
  apply measurable_of_Ioi (f := lCutTime S T x)
  intro a
  by_cases ha : a = (∞ : ℝ≥0∞)
  · subst a
    simpa only [Ioi_top, preimage_empty] using
      (MeasurableSet.empty : MeasurableSet (∅ : Set E))
  · have heq :
        (lCutTime S T x) ⁻¹' Ioi a =
          lInjDomain S T x a.toReal := by
      ext Z
      change a < lCutTime S T x Z ↔ _
      simpa only [ENNReal.ofReal_toReal ha] using
        (ofReal_lt_lCutTime_iff S T x a.toReal Z)
    rw [heq]
    exact hinj a.toReal

end Measurable

private theorem downward_minimality_of_regular_slab_bounds
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K) :
    ∀ {Z : E} {sigma rho : ℝ}, (Z, sigma) ∈ lMinDomain S T x →
      0 < rho → rho ≤ sigma → (Z, rho) ∈ lMinDomain S T x := by
  intro Z sigma rho hmin hrho hle
  have hdom := ((mem_lMinDomain S T x Z sigma).mp hmin).1
  have hsigma := lMinDomain_pos S T x Z sigma hmin
  have hreg : Icc (T - sigma) T ⊆ D.regular := by
    intro t ht
    have ht0 : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have htS : T - t ≤ sigma := by linarith only [ht.1]
    have hsqrt : Real.sqrt (T - t) ∈ Icc (0 : ℝ) (Real.sqrt sigma) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt htS⟩
    have h := lExpPosDom_regularity S T x Z hdom hsqrt
    have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by rw [Real.sq_sqrt ht0]; ring
    simpa only [heq] using h
  obtain ⟨K, hK⟩ := hRm sigma hsigma hreg
  exact lMinDomain_down_of_rm S hS K T x Z hmin hrho hle hK

theorem measurableSet_lInjDomain_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    (tau : ℝ) : @MeasurableSet E (borel E) (lInjDomain S T x tau) := by
  let : MeasurableSpace E := borel E
  exact lInjDomain_meas_of_down S T x tau
    (downward_minimality_of_regular_slab_bounds S hS T x hRm)
    (fun rho _hrho => measurableSet_lMinDomain_slice_of_rm S hS T x hRm rho)

theorem measurableSet_lCutDomain_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    (tau : ℝ) : @MeasurableSet E (borel E) (lCutDomain S T x tau) := by
  let : MeasurableSpace E := borel E
  rw [lCutDomain_eq_diff S T x tau]
  exact (measurableSet_lMinDomain_slice_of_rm S hS T x hRm tau).diff
    (measurableSet_lInjDomain_of_rm S hS T x hRm tau)

theorem measurable_lCutTime_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K) :
    @Measurable E ℝ≥0∞ (borel E) (borel ℝ≥0∞) (lCutTime S T x) := by
  let : MeasurableSpace E := borel E
  exact lCutTime_measurable_of_inj S T x
    (measurableSet_lInjDomain_of_rm S hS T x hRm)
end DifferentialGeometry.PDE.RicciFlow
