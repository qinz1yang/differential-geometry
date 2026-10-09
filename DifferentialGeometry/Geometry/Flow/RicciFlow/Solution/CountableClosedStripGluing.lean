import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Locality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Congruence
import DifferentialGeometry.Geometry.Metric.Completeness

/-!
# Ricci flow from coherent closed time strips

Successive agreement on an actual increasing, cofinal family of closed strips
constructs one solution on the closed backward half-line of the same carrier.
The original metrics, time restrictions and complete slices are retained.
-/

set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Successive agreement on whole old strips implies agreement with every
later piece. The actual monotone depths pay the time-domain inclusion at each
step; this is not an initial-data uniqueness argument. -/
private theorem metric_eq_on_earlier_strip
    (depth : ℕ → ℝ) (hdepth : ∀ n, 0 < depth n) (hmono : Monotone depth)
    (S : ∀ n, SolutionOn (I := I) (M := M)
      (RealTimeInterval.closed (-depth n) 0 (neg_nonpos.mpr (hdepth n).le)))
    (hnext : ∀ n, ∀ t ∈ Icc (-depth n) 0,
      (S (n + 1)).base.metric t = (S n).base.metric t)
    {n m : ℕ} (hnm : n ≤ m) {t : ℝ} (ht : t ∈ Icc (-depth n) 0) :
    (S m).base.metric t = (S n).base.metric t := by
  apply Nat.le_induction (P := fun j _ => (S j).base.metric t = (S n).base.metric t)
    rfl (fun j hnj ih => ?_) m hnm
  exact (hnext j t ⟨(neg_le_neg (hmono hnj)).trans ht.1,ht.2⟩).trans ih

/-- A genuinely coherent exhaustion of one carrier by closed time strips
constructs one Ricci flow on (-infinity,0], retaining each full original strip.
The countable family and its agreements are supplied; this theorem does not
choose coherent extensions from unrelated finite-horizon existential outputs.
The metric at positive times is only the all-real extension required by the
existing SolutionOn type. -/
theorem exists_solution_of_coherent_closed_strips
    (depth : ℕ → ℝ) (hdepth : ∀ n, 0 < depth n) (hmono : Monotone depth)
    (hcofinal : Tendsto depth atTop atTop)
    (S : ∀ n, SolutionOn (I := I) (M := M)
      (RealTimeInterval.closed (-depth n) 0 (neg_nonpos.mpr (hdepth n).le)))
    (hS : ∀ n, IsSolutionOn (S n))
    (hnext : ∀ n, ∀ t ∈ Icc (-depth n) 0,
      (S (n + 1)).base.metric t = (S n).base.metric t) :
    ∃ G : SolutionOn (I := I) (M := M) (RealTimeInterval.infiniteClosed 0 0 le_rfl),
      IsSolutionOn G ∧
      (∀ n, ∀ t ∈ Icc (-depth n) 0, G.base.metric t = (S n).base.metric t) ∧
      (∀ n, IsSolutionOn (G.timeRestrict
        (RealTimeInterval.closed (-depth n) 0 (neg_nonpos.mpr (hdepth n).le)))) ∧
      G.base.metric 0 = (S 0).base.metric 0 := by
  classical
  have hcover (t : ℝ) : ∃ n : ℕ, -depth n < t := by
    obtain ⟨n,hn⟩ := (hcofinal.eventually_gt_atTop (-t)).exists
    exact ⟨n,by linarith⟩
  choose index hindex using hcover
  let G : SolutionOn (I := I) (M := M) (RealTimeInterval.infiniteClosed 0 0 le_rfl) :=
    { base.metric := fun t => (S (index t)).base.metric t }
  have hmatch (n : ℕ) (t : ℝ) (ht : t ∈ Icc (-depth n) 0) :
      G.base.metric t = (S n).base.metric t := by
    change (S (index t)).base.metric t = (S n).base.metric t
    have hi : t ∈ Icc (-depth (index t)) 0 := ⟨(hindex t).le,ht.2⟩
    exact (metric_eq_on_earlier_strip depth hdepth hmono S hnext
      (le_max_left (index t) n) hi).symm.trans
        (metric_eq_on_earlier_strip depth hdepth hmono S hnext
          (le_max_right (index t) n) ht)
  have hrestr (n : ℕ) : IsSolutionOn (G.timeRestrict
      (RealTimeInterval.closed (-depth n) 0 (neg_nonpos.mpr (hdepth n).le))) :=
    IsSolutionOn.congr_metric (g := (S n).base.metric) (h := G.base.metric)
      (hS n) (fun t ht => (hmatch n t ht).symm)
  refine ⟨G,?_,hmatch,hrestr,hmatch 0 0 ⟨neg_nonpos.mpr (hdepth 0).le,le_rfl⟩⟩
  apply isSolutionOn_of_local_time_restrictions G
  intro t ht
  refine ⟨Ioi (-depth (index t)),isOpen_Ioi,hindex t,
    RealTimeInterval.closed (-depth (index t)) 0
      (neg_nonpos.mpr (hdepth (index t)).le),?_,?_,hrestr (index t)⟩
  · intro u hu
    exact ⟨hu.2.le,hu.1⟩
  · intro u hu
    exact ⟨hu.2,hu.1⟩

variable [SigmaCompactSpace M]

/-- Completeness is inherited from the actual containing strip at every
closed ancient time. No curvature bound, noncollapse, profile or convergence
hypothesis is manufactured by the gluing construction. -/
theorem exists_complete_solution_of_coherent_closed_strips
    (depth : ℕ → ℝ) (hdepth : ∀ n, 0 < depth n) (hmono : Monotone depth)
    (hcofinal : Tendsto depth atTop atTop)
    (S : ∀ n, SolutionOn (I := I) (M := M)
      (RealTimeInterval.closed (-depth n) 0 (neg_nonpos.mpr (hdepth n).le)))
    (hS : ∀ n, IsSolutionOn (S n))
    (hnext : ∀ n, ∀ t ∈ Icc (-depth n) 0,
      (S (n + 1)).base.metric t = (S n).base.metric t)
    (hcomplete : ∀ n, ∀ t ∈ Icc (-depth n) 0,
      RiemannianMetricComplete ((S n).base.metric t)) :
    ∃ G : SolutionOn (I := I) (M := M) (RealTimeInterval.infiniteClosed 0 0 le_rfl),
      IsSolutionOn G ∧
      (∀ n, ∀ t ∈ Icc (-depth n) 0, G.base.metric t = (S n).base.metric t) ∧
      (∀ n, IsSolutionOn (G.timeRestrict
        (RealTimeInterval.closed (-depth n) 0 (neg_nonpos.mpr (hdepth n).le)))) ∧
      G.base.metric 0 = (S 0).base.metric 0 ∧
      ∀ t ≤ 0, RiemannianMetricComplete (G.base.metric t) := by
  obtain ⟨G,hG,hmatch,hrestr,hzero⟩ :=
    exists_solution_of_coherent_closed_strips depth hdepth hmono hcofinal S hS hnext
  refine ⟨G,hG,hmatch,hrestr,hzero,?_⟩
  intro t ht
  obtain ⟨n,hn⟩ := (hcofinal.eventually_ge_atTop (-t)).exists
  have htn : t ∈ Icc (-depth n) 0 := ⟨by linarith,ht⟩
  rw [hmatch n t htn]
  exact hcomplete n t htn

end DifferentialGeometry.PDE.RicciFlow
