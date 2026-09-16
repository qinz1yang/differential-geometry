import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.MaximalPointSlabReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalFromJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.JetPolynomialBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.MixedJetPolynomials

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]

theorem high_curvature_interval_eventually_contains_closed_window
    {T theta : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (htheta : 0 < theta) (htlower : ∀ᶠ i in atTop, theta ≤ t i)
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop) (A : ℝ) :
    ∀ᶠ i in atTop,
      Icc (-A) 0 ⊆ (highCurvatureInterval hT S x t htpos hpos i).carrier ∧
      Ioo (-A) 0 ⊆ (highCurvatureInterval hT S x t htpos hpos i).regular := by
  filter_upwards [hscalar.eventually_ge_atTop (A / theta), htlower] with i hi hti
  have hA : A ≤ S.scalar (t i) (x i) * theta := (div_le_iff₀ htheta).mp hi
  have hdeep : A ≤ t i * S.scalar (t i) (x i) := by
    simpa only [mul_comm] using hA.trans (mul_le_mul_of_nonneg_left hti (hpos i).le)
  constructor
  · intro s hs
    exact ⟨(neg_le_neg hdeep).trans hs.1, hs.2⟩
  · intro s hs
    exact ⟨(neg_le_neg hdeep).trans_lt hs.1, hs.2⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section

open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M]

theorem highCurvatureFlowSequence_curvDerivNorm_eventually_le_on_closed_window
    {T theta : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hmax : ∀ i s, s ∈ Icc 0 (t i) → ∀ y : M,
      S.scalar s y ≤ S.scalar (t i) (x i))
    (htheta : 0 < theta) (htlower : ∀ᶠ i in atTop, theta ≤ t i)
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop) (A : ℝ) :
    ∀ᶠ i in atTop, ∀ m : ℕ, ∀ s ∈ Icc (-A) 0,
      ∀ y : ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).M,
        curvDerivNorm (I := I3) m
          (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).S.base.metric s) y ≤
          shiLocalUniformBound 3 m 16 4 * 16 := by
  have hbound := highCurvatureFlowSequence_rmNormSq_eventually_le_of_past_scalar_maximum
    hT S hS x t htmem htpos hpos hmax hscalar
  have hwindow := high_curvature_interval_eventually_contains_closed_window
    hT S x t htpos hpos htheta htlower hscalar (A + 2)
  filter_upwards [hbound, hwindow] with i hi hwi m s hs y
  let F := (highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i
  let : CompactSpace F.M := ‹CompactSpace M›
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hcarrier : Icc (s - 1) s ⊆ (highCurvatureInterval hT S x t htpos hpos i).carrier := by
    intro r hr
    exact hwi.1 ⟨by linarith [hs.1, hr.1], hr.2.trans hs.2⟩
  have hregular : Ico (s - 1) s ⊆ (highCurvatureInterval hT S x t htpos hpos i).regular := by
    intro r hr
    exact hwi.2 ⟨by linarith [hs.1, hr.1], hr.2.trans_le hs.2⟩
  have hball : IsCompact {z : F.M |
      riemannianEDistOf (I := I3) (F.S.base.metric (s - 1)) y z ≤
        ENNReal.ofReal (4 / Real.sqrt 16)} := by
    exact RiemannianMetricComplete.closedEBall_isCompact
      (RiemannianMetricComplete.of_compact (F.S.base.metric (s - 1))) y _
  have hcurv : ∀ r ∈ Icc (s - 1) s, ∀ z : F.M,
      riemannianEDistOf (I := I3) (F.S.base.metric (s - 1)) y z ≤
        ENNReal.ofReal (4 / Real.sqrt 16) →
      curvDerivNormSq (I := I3) 0 (F.S.base.metric r) z ≤ (16 : ℝ) ^ 2 := by
    intro r hr z _
    change F.rmNormSq r z ≤ (16 : ℝ) ^ 2
    exact (hi r (hcarrier hr) z).trans (by norm_num)
  have hcenter : riemannianEDistOf (I := I3) (F.S.base.metric (s - 1)) y y ≤
      ENNReal.ofReal (4 / (2 * Real.sqrt 16)) := by
    rw [riemannianEDistOf_self]
    exact zero_le
  have hb := shi_local_curvDerivNorm_terminal_of_solution_jets F.S F.isSolution
    (by omega : 2 ≤ Module.finrank ℝ ThreeSpace)
    (a := s - 1) (b := s) (K := 16) (R := 4)
    (by linarith) (by norm_num) (by norm_num) hcarrier hregular y hball hcurv
    m s ⟨by linarith, le_rfl⟩ y hcenter
  have hspan : s - (s - 1) = 1 := by ring
  simpa only [hdim, hspan, mul_one, Real.sqrt_one, one_pow, div_one] using hb

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open KappaSolutions
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_highCurvatureFlowSequence_mixedCurvatureNorm_bound_on_closed_window (p q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M]
        {T theta : ℝ} (hT : 0 < T)
        (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
        (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
        (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
        (hpos : ∀ i, 0 < S.scalar (t i) (x i)),
        (∀ i s, s ∈ Icc 0 (t i) → ∀ y : M, S.scalar s y ≤ S.scalar (t i) (x i)) →
        0 < theta → (∀ᶠ i in atTop, theta ≤ t i) →
        Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop → ∀ A : ℝ,
        ∀ᶠ i in atTop, ∀ s ∈ Icc (-A) 0,
          ∀ y : ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).M,
            DifferentiableWithinAt ℝ (fun r => mixedCurvatureTensor
              ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).S p q r y)
              (highCurvatureInterval hT S x t htpos hpos i).carrier s ∧
            mixedCurvatureNorm
              ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).S p q s y ≤ C := by
  classical
  choose P hP using fun j : ℕ => exists_mixed_curvature_jet_polynomials.{u, 0, 0} 3 p j
  let B : ℕ → ℝ := fun j => shiLocalUniformBound 3 j 16 4 * 16
  refine ⟨1 + curvatureJetPolynomialNormBound (P q) B, ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg _)
  intro M _ _ _ _ _ T theta hT S hS x t htmem htpos hpos hmax htheta htlower hscalar A
  have hspatial := highCurvatureFlowSequence_curvDerivNorm_eventually_le_on_closed_window
    hT S hS x t htmem htpos hpos hmax htheta htlower hscalar A
  have hwindow := high_curvature_interval_eventually_contains_closed_window
    hT S x t htpos hpos htheta htlower hscalar (A + 2)
  filter_upwards [hspatial, hwindow] with i hi hwi s hs y
  let F := (highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i
  let : IsManifold I3 1 F.M := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I3 2 F.M := IsManifold.of_le (n := ∞) (by decide)
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hdim : Module.finrank ℝ (TangentSpace I3 y) = 3 := by
    change Module.finrank ℝ ThreeSpace = 3
    simp [ThreeSpace]
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I3) (F.S.base.metric s) y hdim
  have hON : ∀ j k, (F.S.base.metric s).inner y (basis j) (basis k) =
      if j = k then 1 else 0 := horth
  have hactual : DifferentiableWithinAt ℝ
      (fun r => mixedCurvatureTensor F.S p q r y)
        (highCurvatureInterval hT S x t htpos hpos i).carrier s ∧
      ∀ slots, component0S (I := I3) basis (mixedCurvatureTensor F.S p q s y) slots =
        MvPolynomial.eval (curvatureJetPolynomialValues F.S (p + 2 * q) s basis) (P q slots) := by
    rcases lt_or_eq_of_le hs.2 with hsneg | rfl
    · have hsr : s ∈ (highCurvatureInterval hT S x t htpos hpos i).regular :=
        hwi.2 ⟨by linarith [hs.1], hsneg⟩
      obtain ⟨hdiff, hcomp⟩ := hP q F.S F.isSolution s hsr y basis
      exact ⟨hdiff.differentiableWithinAt, hcomp⟩
    · have hA : 0 ≤ A := by linarith [hs.1]
      have hdeep : -(t i * S.scalar (t i) (x i)) ≤ -(A + 2) :=
        (hwi.1 ⟨le_rfl, by linarith⟩).1
      have hreg : Ioo (-1 : ℝ) 0 ⊆ (highCurvatureInterval hT S x t htpos hpos i).regular := by
        intro r hr
        exact hwi.2 ⟨by linarith [hr.1], hr.2⟩
      exact mixedCurvature_polynomial_terminal_of_regular_Icc F.S F.isSolution p
        (c := -(t i * S.scalar (t i) (x i))) (a := -1) (b := 0)
        (by linarith) (by norm_num) rfl hreg P y basis
        (fun j r hr => hP j F.S F.isSolution r (hreg hr) y basis) q
  refine ⟨hactual.1, ?_⟩
  have hb := norm_le_curvatureJetPolynomialNormBound F.S s basis hON (P q)
    (mixedCurvatureTensor F.S p q s y) hactual.2 B (fun j _ => hi j s hs y)
  exact hb.trans (le_add_of_nonneg_left zero_le_one)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open KappaSolutions
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_highCurvatureFlowSequence_mixedCurvatureNorm_bound_through_order_on_closed_window (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M]
        {T theta : ℝ} (hT : 0 < T)
        (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
        (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
        (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
        (hpos : ∀ i, 0 < S.scalar (t i) (x i)),
        (∀ i s, s ∈ Icc 0 (t i) → ∀ y : M, S.scalar s y ≤ S.scalar (t i) (x i)) →
        0 < theta → (∀ᶠ i in atTop, theta ≤ t i) →
        Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop → ∀ A : ℝ,
        ∀ᶠ i in atTop, ∀ p q : ℕ, p + 2 * q ≤ N → ∀ s ∈ Icc (-A) 0,
          ∀ y : ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).M,
            DifferentiableWithinAt ℝ (fun r => mixedCurvatureTensor
              ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).S p q r y)
              (highCurvatureInterval hT S x t htpos hpos i).carrier s ∧
            mixedCurvatureNorm
              ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).S p q s y ≤ C := by
  classical
  choose C hC hbound using fun p q : ℕ =>
    exists_highCurvatureFlowSequence_mixedCurvatureNorm_bound_on_closed_window.{u} p q
  let K : ℝ := 1 + ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1), C j k
  have hsum : 0 ≤ ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1), C j k :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => (hC j k).le
  have hCK (p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) : C p q ≤ K := by
    have hqmem : q ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hpmem : p ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hqsum : C p q ≤ ∑ k ∈ Finset.range (N + 1), C p k :=
      Finset.single_le_sum (fun k _ => (hC p k).le) hqmem
    have hpsum : (∑ k ∈ Finset.range (N + 1), C p k) ≤
        ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1), C j k :=
      Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun k _ => (hC j k).le) hpmem
    exact (hqsum.trans hpsum).trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨K, add_pos_of_pos_of_nonneg zero_lt_one hsum, ?_⟩
  intro M _ _ _ _ _ T theta hT S hS x t htmem htpos hpos hmax htheta htlower hscalar A
  have hall := Filter.eventually_all.2 (fun p : Fin (N + 1) =>
    Filter.eventually_all.2 (fun q : Fin (N + 1) =>
      hbound p.val q.val hT S hS x t htmem htpos hpos hmax htheta htlower hscalar A))
  filter_upwards [hall] with i hi p q hpq s hs y
  have hp : p ≤ N := by omega
  have hq : q ≤ N := by omega
  have hv := hi ⟨p, by omega⟩ ⟨q, by omega⟩ s hs y
  exact ⟨hv.1, hv.2.trans (hCK p q hp hq)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end
