import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonCongruence
import DifferentialGeometry.Topology.Sequences.DiagonalSubsequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FlowConvergenceAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension.Classification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Locality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Congruence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive

set_option autoImplicit false
noncomputable section
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_isHalfLineExtension_of_compatible_slabs
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J)
    (D : ℕ → RealTimeInterval) (F : ∀ n, BackwardExtension L (D n))
    (htimes : ∀ n, (D n).carrier ⊆ Set.Iic 0)
    (hcover : ∀ a b : ℝ, a ≤ b → b ≤ 0 → ∃ n, Set.Icc a b ⊆ (D n).carrier)
    (hcompat : ∀ n m t, t ∈ (D n).carrier → t ∈ (D m).carrier →
      (F n).solution.base.metric t = (F m).solution.base.metric t)
    (hJ : J.carrier ⊆ Set.Iic 0)
    (hagree : ∀ n t, t ∈ J.carrier → t ∈ (D n).carrier →
      (F n).solution.base.metric t = B.solution.base.metric t)
    (diagonal : ℕ → ℕ) (hdiag : StrictMono diagonal)
    (hfactor : ∀ n, ∃ k : ℕ, ∃ r : ℕ → ℕ, StrictMono r ∧
      ∀ i, B.subseq (diagonal (k + i)) = (F n).subseq (r i)) :
    ∃ g : ℝ → SmoothRiemannianMetric I3 L.space.M,
      IsHalfLineExtension B g ∧
      ∀ n, Set.EqOn g (F n).solution.base.metric (D n).carrier := by
  classical
  have hc : ∀ t : ℝ, t ≤ 0 → ∃ n, t ∈ (D n).carrier := by
    intro t ht
    obtain ⟨n, hn⟩ := hcover t t le_rfl ht
    exact ⟨n, hn ⟨le_rfl, le_rfl⟩⟩
  let g : ℝ → SmoothRiemannianMetric I3 L.space.M := fun t =>
    if ht : t ≤ 0 then (F (hc t ht).choose).solution.base.metric t else L.space.metric
  have hgn : ∀ n, Set.EqOn g (F n).solution.base.metric (D n).carrier := by
    intro n t ht
    have ht0 : t ≤ 0 := htimes n ht
    dsimp [g]
    rw [dite_eq_left ht0]
    exact hcompat _ n t (hc t ht0).choose_spec ht
  have hg0 : g 0 = L.space.metric := by
    obtain ⟨n, hn⟩ := hc 0 le_rfl
    exact (hgn n hn).trans (F n).terminal
  refine ⟨g, ?_, hgn⟩
  apply isHalfLineExtension_of_eventually_metricComparisonOn B hdiag hg0
  · intro t ht
    obtain ⟨n, hn⟩ := hc t (hJ ht)
    exact (hgn n hn).trans (hagree n t ht hn)
  · intro K hK a b hab hb order tolerance htol
    obtain ⟨n, hn⟩ := hcover a b hab hb
    obtain ⟨k, r, hr, hfactor⟩ := hfactor n
    have htail : ∀ᶠ i in Filter.atTop,
        Nonempty (MetricComparisonOn g
          (fun s => (X.term (L.subseq (B.subseq (diagonal (k + i))))).S.base.metric s)
          (L.maps.partialDiffeomorph (B.subseq (diagonal (k + i))))
          K (Set.Icc a b) order tolerance) := by
      filter_upwards [hr.tendsto_atTop.eventually
        ((F n).convergence K hK a b hab hn order tolerance htol)] with i hi
      rw [hfactor i]
      obtain ⟨C⟩ := hi.2.2
      exact nonempty_metricComparisonOn_congr_reference C (fun t ht => hgn n (hn ht))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp htail
    refine Filter.eventually_atTop.mpr ⟨k + N, fun i hi => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show k ≤ i by omega)
    exact hN j (by omega)


theorem exists_isHalfLineExtension_of_nested_compatible_slabs
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J)
    (D : ℕ → RealTimeInterval) (F : ∀ n, BackwardExtension L (D n))
    (htimes : ∀ n, (D n).carrier ⊆ Set.Iic 0)
    (hcover : ∀ a b : ℝ, a ≤ b → b ≤ 0 → ∃ n, Set.Icc a b ⊆ (D n).carrier)
    (hcompat : ∀ n m t, t ∈ (D n).carrier → t ∈ (D m).carrier →
      (F n).solution.base.metric t = (F m).solution.base.metric t)
    (hJ : J.carrier ⊆ Set.Iic 0)
    (hagree : ∀ n t, t ∈ J.carrier → t ∈ (D n).carrier →
      (F n).solution.base.metric t = B.solution.base.metric t)
    (q : ℕ → ℕ → ℕ) (hq : ∀ n, StrictMono (q n))
    (hsubseq : ∀ n, (F n).subseq = B.subseq ∘ q n)
    (hnest : ∀ n, Set.range (q (n + 1)) ⊆ Set.range (q n)) :
    ∃ g : ℝ → SmoothRiemannianMetric I3 L.space.M,
      IsHalfLineExtension B g ∧
      ∀ n, Set.EqOn g (F n).solution.base.metric (D n).carrier := by
  obtain ⟨diagonal, hd, hr⟩ := exists_strictMono_diagonal_of_nested_ranges q hq hnest
  apply exists_isHalfLineExtension_of_compatible_slabs B D F htimes hcover hcompat
    hJ hagree diagonal hd
  intro n
  obtain ⟨r, hr, heq⟩ := hr n
  refine ⟨n, r, hr, fun i => ?_⟩
  rw [heq i, hsubseq n]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_ancientExtension_of_cofinal_backwardExtensions
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B₀ : BackwardExtension L J) (hkappa : 0 < kappa)
    (hJ : J.carrier ⊆ Iic 0)
    (a : ℕ → ℝ) (ha : ∀ n, a n < 0)
    (B : ∀ n, BackwardExtension L (RealTimeInterval.closed (a n) 0 (ha n).le))
    (hcofinal : Tendsto a atTop atBot)
    (hcompatible : ∀ n m t, t ∈ Icc (a n) 0 → t ∈ Icc (a m) 0 →
      (B n).solution.base.metric t = (B m).solution.base.metric t)
    (hagree : ∀ n t, t ∈ J.carrier → t ∈ Icc (a n) 0 →
      (B n).solution.base.metric t = B₀.solution.base.metric t)
    (q : ℕ → ℕ → ℕ) (hq : ∀ n, StrictMono (q n))
    (hsubseq : ∀ n, (B n).subseq = B₀.subseq ∘ q n)
    (hnest : ∀ n, range (q (n + 1)) ⊆ range (q n)) :
    Nonempty (AncientExtension B₀) := by
  have hcover : ∀ c d : ℝ, c ≤ d → d ≤ 0 → ∃ n, Icc c d ⊆ Icc (a n) 0 := by
    intro c d _ hd
    obtain ⟨n, hn⟩ := (hcofinal.eventually_le_atBot c).exists
    exact ⟨n, Icc_subset_Icc hn hd⟩
  obtain ⟨g, hlim, hgn⟩ := exists_isHalfLineExtension_of_nested_compatible_slabs
    B₀ (fun n => RealTimeInterval.closed (a n) 0 (ha n).le) B
    (fun _ => Icc_subset_Iic_self) hcover hcompatible hJ hagree q hq hsubseq hnest
  let S : SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval := { base.metric := g }
  have hsol : IsSolutionOn S := by
    apply isSolutionOn_of_local_time_restrictions S
    intro t ht
    obtain ⟨n, hn⟩ := (hcofinal.eventually_lt_atBot t).exists
    refine ⟨Ioi (a n), isOpen_Ioi, hn,
      RealTimeInterval.closed (a n) 0 (ha n).le, ?_, ?_, ?_⟩
    · exact fun r hr => ⟨hr.2.le, hr.1⟩
    · exact fun r hr => ⟨hr.2, hr.1⟩
    · exact (B n).isSolution.congr_metric (fun r hr => (hgn n hr).symm)
  obtain ⟨hg0, hB₀, diagonal, hdiagonal, hconv⟩ := hlim
  have hcomplete : ∀ t ∈ ancientTimeInterval.carrier,
      MetricComplete { L.space with metric := g t } := by
    intro t ht
    obtain ⟨n, hn⟩ := hcover t t le_rfl ht
    rw [hgn n (hn ⟨le_rfl, le_rfl⟩)]
    exact (B n).complete t (hn ⟨le_rfl, le_rfl⟩)
  have hnonnegative : ∀ t ∈ ancientTimeInterval.carrier, SecLower (g t) 0 univ := by
    intro t ht
    obtain ⟨n, hn⟩ := hcover t t le_rfl ht
    rw [hgn n (hn ⟨le_rfl, le_rfl⟩)]
    exact (B n).nonnegative t (hn ⟨le_rfl, le_rfl⟩)
  have hbound : ∀ c d : ℝ, c ≤ d → Icc c d ⊆ ancientTimeInterval.carrier →
      ∃ C : ℝ, ∀ t ∈ Icc c d, ∀ x : L.space.M, FlowMetricBall.rmNormSq S t x ≤ C := by
    intro c d hcd hsub
    obtain ⟨n, hn⟩ := hcover c d hcd (hsub (right_mem_Icc.mpr hcd))
    obtain ⟨C, hC⟩ := (B n).compact_time_bound c d hcd hn
    refine ⟨C, ?_⟩
    intro t ht x
    change Tensor0SBundle.normSq0S (g t) x 4 (metricRm04At (g t) x) ≤ C
    rw [hgn n (hn ht)]
    exact hC t ht x
  let E : BackwardExtension L ancientTimeInterval :=
    { solution := S
      isSolution := hsol
      terminal := hg0
      subseq := B₀.subseq ∘ diagonal
      strictMono := B₀.strictMono.comp hdiagonal
      convergence := hconv
      complete := hcomplete
      nonnegative := hnonnegative
      compact_time_bound := hbound }
  have hanc := E.isAncientKappaSolution hkappa
  obtain ⟨C, _hscalar, hRm⟩ := KappaSolutions.ancientKappa_rmNormSqBounded
    E.pointed (by simp [ThreeSpace]) hanc
  refine ⟨{ extension := E
            agrees := hB₀
            diagonal := diagonal
            strictMono := hdiagonal
            maps_agree := rfl
            ancient := hanc
            normalized := ?_
            global_rm := ⟨(Real.sqrt 3 * C) ^ 2, hRm⟩ }⟩
  change metricScalarAt (g 0) L.space.basepoint = 1
  rw [hg0]
  exact L.scalar_one

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
