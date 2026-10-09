import DifferentialGeometry.Geometry.Metric.Approximation.ClosedBall

set_option autoImplicit false

namespace DifferentialGeometry

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

def isMetricApproximationOnBall {D : Set M} (f : D → N)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (x : M) (r : ℝ) (p : ℕ) (ε : ℝ) : Prop :=
  0 < r ∧ riemannianClosedBallOf g x r ⊆ D ∧
    ∃ Φ : PartialDiffeomorph I I M N ∞,
      PartialDiffeomorph.isMetricApproximationOn Φ (riemannianClosedBallOf g x r) p ε g h ∧
      Set.EqOn (fun y : D => Φ y) f (Subtype.val ⁻¹' riemannianClosedBallOf g x r)

theorem isMetricApproximationOnBall.radius_pos
    {D : Set M} {f : D → N} {g : SmoothRiemannianMetric I M}
    {h : SmoothRiemannianMetric I N} {x : M} {r ε : ℝ} {p : ℕ}
    (hf : isMetricApproximationOnBall f g h x r p ε) : 0 < r :=
  hf.1

theorem isMetricApproximationOnBall.epsilon_pos
    {D : Set M} {f : D → N} {g : SmoothRiemannianMetric I M}
    {h : SmoothRiemannianMetric I N} {x : M} {r ε : ℝ} {p : ℕ}
    (hf : isMetricApproximationOnBall f g h x r p ε) : 0 < ε := by
  obtain ⟨Φ, hΦ, _⟩ := hf.2.2
  exact hΦ.epsilon_pos

theorem isMetricApproximationOnBall.basepoint_mem
    {D : Set M} {f : D → N} {g : SmoothRiemannianMetric I M}
    {h : SmoothRiemannianMetric I N} {x : M} {r ε : ℝ} {p : ℕ}
    (hf : isMetricApproximationOnBall f g h x r p ε) : x ∈ D := by
  apply hf.2.1
  change riemannianEDistOf g x x ≤ ENNReal.ofReal r
  rw [riemannianEDistOf_self]
  exact zero_le

theorem isMetricApproximationOnBall_congr_domain
    {D D' : Set M} (f : D → N) (f' : D' → N)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (x : M) (r : ℝ) (p : ℕ) (ε : ℝ)
    (hD : riemannianClosedBallOf g x r ⊆ D)
    (hD' : riemannianClosedBallOf g x r ⊆ D')
    (heq : ∀ y (hy : y ∈ riemannianClosedBallOf g x r), f ⟨y, hD hy⟩ = f' ⟨y, hD' hy⟩) :
    isMetricApproximationOnBall f g h x r p ε ↔
      isMetricApproximationOnBall f' g h x r p ε := by
  constructor
  · rintro ⟨hr, _, Φ, hΦ, hf⟩
    refine ⟨hr, hD', Φ, hΦ, ?_⟩
    intro y hy
    exact (hf (x := ⟨y, hD hy⟩) hy).trans (heq y hy)
  · rintro ⟨hr, _, Φ, hΦ, hf⟩
    refine ⟨hr, hD, Φ, hΦ, ?_⟩
    intro y hy
    exact (hf (x := ⟨y, hD' hy⟩) hy).trans (heq y hy).symm

theorem isMetricApproximationOnBall_restrict_iff
    {D D' : Set M} (hD'D : D' ⊆ D) (f : D → N)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (x : M) (r : ℝ) (p : ℕ) (ε : ℝ)
    (hD' : riemannianClosedBallOf g x r ⊆ D') :
    isMetricApproximationOnBall (fun y : D' => f ⟨y, hD'D y.property⟩) g h x r p ε ↔
      isMetricApproximationOnBall f g h x r p ε := by
  exact isMetricApproximationOnBall_congr_domain _ f g h x r p ε hD'
    (hD'.trans hD'D) (fun _ _ => rfl)

theorem isMetricApproximationOnBall_univ_iff
    (f : M → N) (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (x : M) (r : ℝ) (p : ℕ) (ε : ℝ) :
    isMetricApproximationOnBall (fun y : (Set.univ : Set M) => f y) g h x r p ε ↔
      0 < r ∧ ∃ Φ : PartialDiffeomorph I I M N ∞,
        PartialDiffeomorph.isMetricApproximationOn Φ (riemannianClosedBallOf g x r) p ε g h ∧
        Set.EqOn (Φ : M → N) f (riemannianClosedBallOf g x r) := by
  constructor
  · rintro ⟨hr, _, Φ, hΦ, hf⟩
    exact ⟨hr, Φ, hΦ, fun y hy => hf (x := ⟨y, Set.mem_univ y⟩) hy⟩
  · rintro ⟨hr, Φ, hΦ, hf⟩
    exact ⟨hr, Set.subset_univ _, Φ, hΦ, fun y hy => hf hy⟩

section Complete

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]

theorem isMetricApproximationOnBall_iff_of_eqOn
    {D : Set M} (f : D → N)
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (h : SmoothRiemannianMetric I N) (x : M) {r : ℝ} (hr : 0 < r)
    (hD : riemannianClosedBallOf g x r ⊆ D)
    (Φ : PartialDiffeomorph I I M N ∞)
    (hΦ : riemannianClosedBallOf g x r ⊆ Φ.source)
    (heq : Set.EqOn (fun y : D => Φ y) f (Subtype.val ⁻¹' riemannianClosedBallOf g x r))
    (p : ℕ) (ε : ℝ) :
    isMetricApproximationOnBall f g h x r p ε ↔
      PartialDiffeomorph.isMetricApproximationOn Φ (riemannianClosedBallOf g x r) p ε g h := by
  constructor
  · rintro ⟨_, _, Ψ, hΨ, hf⟩
    have hmaps : Set.EqOn (Φ : M → N) (Ψ : M → N) (riemannianBallOf g x r) := by
      intro y hy
      have hy' : y ∈ riemannianClosedBallOf g x r :=
        (show riemannianEDistOf g x y < ENNReal.ofReal r from hy).le
      exact (heq (x := ⟨y, hD hy'⟩) hy').trans (hf (x := ⟨y, hD hy'⟩) hy').symm
    exact (PartialDiffeomorph.isMetricApproximationOn_congr_of_eqOn_riemannianBallOf
      Φ Ψ g hg h x hr hΦ hΨ.1 hmaps p ε).mpr hΨ
  · intro happrox
    exact ⟨hr, hD, Φ, happrox, heq⟩

end Complete

end DifferentialGeometry
