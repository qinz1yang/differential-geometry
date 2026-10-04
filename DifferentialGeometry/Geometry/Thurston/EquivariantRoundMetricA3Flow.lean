import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA3Algebra
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.ScalarPositivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TraceCorollaries
import DifferentialGeometry.Geometry.Metric.Family.Comparison

/-!
# Flow wrappers for the U1 curvature bound

Chapter 7, packet P8, surface lemma U1, route (a), lane a3. For a Ricci flow `S` on `[0, T)` on a
compact connected surface whose initial scalar curvature is positive:

* `surfaceFlow_scalar_pos`: the scalar curvature stays positive
  (`scalar_curvature_positive_of_nonnegative_initial` through `smoothOfSolution`).
* `surfaceFlow_entropy_le_initial`: Hamilton's surface entropy at time `t` is at most its initial
  value (`surfaceEntropy_hasDerivAt_first`, `surfaceEntropy_deriv_nonpos` on the open interval,
  continuity at the endpoints).
* `surfaceFlow_edist_le`: if `0 ≤ R ≤ K` on `[a, t]` then `d_{g(a)} ≤ e^{K (t - a) / 2} d_{g(t)}`,
  because `∂ₜ g = -R g` in dimension two.
* `surfaceFlow_harnack`: Hamilton's trace Harnack inequality with an origin `o > 0`
  (`hamilton_trace_harnack_distance`; completeness from compactness, the curvature bound on compact
  regular intervals from `exists_curvature_bound_on_closed_interval_of_isSolutionOn`, the cone
  condition from `mem_curvatureOperatorNonnegativeCone_of_finrank_two`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]
  {T : ℝ} {hT : 0 < T}

theorem surfaceFlow_scalar_pos
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) {t : ℝ} (ht : t ∈ Ico 0 T) (x : M) : 0 < S.scalar t x := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  rcases ht.1.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact hscal x
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  exact scalar_curvature_positive_of_nonnegative_initial S (smoothOfSolution S hS) hpos
    (fun s hs => (⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩ : s ∈ Ico 0 T))
    (fun s hs => (⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩ : s ∈ Ioo 0 T))
    (fun y => (hscal y).le) (hscal x₀) x

theorem surfaceFlow_entropy_le_initial (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) {t : ℝ} (ht : t ∈ Ico 0 T) :
    surfaceEntropy (S.family.metric t) ≤ surfaceEntropy (S.family.metric 0) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; decide⟩
  have hpositive : ∀ s ∈ (RealTimeInterval.closedOpen 0 T hT).regular, ∀ x, 0 < S.scalar s x :=
    fun s hs x => surfaceFlow_scalar_pos S hS hscal ⟨hs.1.le, hs.2⟩ x
  have hcont : ContinuousOn (fun s => surfaceEntropy (S.family.metric s)) (Icc 0 t) :=
    (surfaceFlow_integrals_continuousOn_compact S hS isCompact_Icc
      (fun s hs => (⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩ : s ∈ Ico 0 T))).2.2
  have hreg : ∀ s ∈ interior (Icc 0 t), s ∈ (RealTimeInterval.closedOpen 0 T hT).regular := by
    intro s hs
    rw [interior_Icc] at hs
    exact (⟨hs.1, hs.2.trans ht.2⟩ : s ∈ Ioo 0 T)
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc 0 t) hcont
    (fun s hs => (surfaceEntropy_hasDerivAt_first S hS hdim hpositive (hreg s hs))
      |>.differentiableAt.differentiableWithinAt)
    (fun s hs => surfaceEntropy_deriv_nonpos S hS hdim hpositive (hreg s hs))
  exact hanti ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1

omit [CompactSpace M] [ConnectedSpace M] in
theorem surfaceFlow_edist_le (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    {a t K : ℝ} (ha : 0 < a) (hat : a ≤ t) (htT : t < T)
    (hK : ∀ u ∈ Icc a t, ∀ x, 0 ≤ S.scalar u x ∧ S.scalar u x ≤ K) (x y : M) :
    riemannianEDistOf (S.family.metric a) x y ≤
      ENNReal.ofReal (Real.exp (K / 2 * (t - a))) * riemannianEDistOf (S.family.metric t) x y := by
  have h := riemannianEDistOf_le_exp_mul_of_abs_deriv_le S.family.metric (a := a) (b := t) (K := K)
    (fun r hr z v => ?_) ⟨le_rfl, hat⟩ ⟨hat, le_rfl⟩ x y
  · rwa [abs_of_nonpos (sub_nonpos.mpr hat), neg_sub] at h
  have hr' : r ∈ (RealTimeInterval.closedOpen 0 T hT).regular :=
    (⟨ha.trans_le hr.1, hr.2.trans_lt htT⟩ : r ∈ Ioo 0 T)
  have hd := metricDerivAt S hS ⟨r, hr'⟩ z v v
  have hric : S.ricciAt r z (vec2 v v) = S.scalar r z / 2 * (S.family.metric r).inner z v v := by
    simp only [SolutionOn.ricciAt, SolutionFamily.ricciAt, metricRicciAt_apply_eq_ricciTensor,
      SolutionOn.family_metric]
    exact ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two _ hdim z v v
  refine ⟨_, hd.hasDerivWithinAt, ?_⟩
  change |(-2 : ℝ) * S.ricciAt r z (vec2 v v)| ≤ K * (S.family.metric r).inner z v v
  rw [hric]
  have hnn : 0 ≤ (S.family.metric r).inner z v v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact ((S.family.metric r).pos z v hv).le
  obtain ⟨h0, hK'⟩ := hK r hr z
  rw [show (-2 : ℝ) * (S.scalar r z / 2 * (S.family.metric r).inner z v v) =
    -(S.scalar r z * (S.family.metric r).inner z v v) by ring, abs_neg,
    abs_of_nonneg (mul_nonneg h0 hnn)]
  exact mul_le_mul_of_nonneg_right hK' hnn

theorem surfaceFlow_harnack (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) {o t₁ t₂ : ℝ} (ho : 0 < o) (h1 : o < t₁) (h2 : t₁ < t₂)
    (h2T : t₂ < T) (x y : M) :
    (t₁ - o) / (t₂ - o) *
        Real.exp (-((riemannianEDistOf (S.family.metric t₁) x y).toReal ^ 2 / (4 * (t₂ - t₁)))) *
      S.scalar t₁ x ≤ S.scalar t₂ y := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; decide⟩
  have hreg : Icc o t₂ ⊆ (RealTimeInterval.closedOpen 0 T hT).regular :=
    fun s hs => (⟨ho.trans_le hs.1, hs.2.trans_lt h2T⟩ : s ∈ Ioo 0 T)
  exact hamilton_trace_harnack_distance S hS
    (fun t _ => DifferentialGeometry.RiemannianMetricComplete.of_compact _)
    (fun a b hab => by
      obtain ⟨C, -, hC⟩ := exists_curvature_bound_on_closed_interval_of_isSolutionOn S hS hab
      exact ⟨C, fun t ht z => hC t ht z⟩)
    (fun t ht z => mem_curvatureOperatorNonnegativeCone_of_finrank_two hdim _ z
      (surfaceFlow_scalar_pos S hS hscal ⟨ht.1.le, ht.2⟩ z).le)
    h1 h2 hreg x y (by rw [PreconnectedSpace.connectedComponent_eq_univ]; trivial)

end GC.Geometry
