import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Basic


open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
set_option autoImplicit false

noncomputable section

universe u uE uH uX uY

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]

namespace centerAverage

variable {g : SmoothRiemannianMetric I M} {X : Type uX} {ι : Type}
variable [Fintype ι]
variable {μ : X → ι → ℝ} {pts : X → ι → M} {join : M → M → ℝ → M}
  {p : X → M} {r : X → ℝ}
  (h : ∀ x : X, CenterInput (I := I) g (μ x) (pts x) join (p x) (r x))
theorem unif_tendsto {s : Set X} {qstar : X → M}
    {μSeq : ℕ → X → ι → ℝ} {ptsSeq : ℕ → X → ι → M}
    {pSeq : ℕ → X → M} {rSeq : ℕ → X → ℝ}
    (hSeq : ∀ n : ℕ, ∀ x : X,
      CenterInput (I := I) g (μSeq n x) (ptsSeq n x) join (pSeq n x) (rSeq n x))
    (hpts :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ ε > 0, ∀ᶠ n in Filter.atTop, ∀ x ∈ s, ∀ i : ι,
        dist (qstar x) (ptsSeq n x i) < ε) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    TendstoUniformlyOn
      (fun n x => centerAverage (I := I) g (μSeq n) (ptsSeq n) join (pSeq n) (rSeq n)
        (hSeq n) x) qstar Filter.atTop s := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hquarter : 0 < ε / 4 := by positivity
  refine (hpts (ε / 4) hquarter).mono ?_
  intro n hn x hx
  have hnear : ∀ i : ι, dist (qstar x) (ptsSeq n x i) ≤ ε / 4 := fun i =>
    le_of_lt (hn x hx i)
  have hdist :
      dist
        (centerAverage (I := I) g (μSeq n) (ptsSeq n) join (pSeq n) (rSeq n) (hSeq n) x)
        (qstar x) ≤ 2 * (ε / 4) :=
    dist_le (I := I) (g := g) (μ := μSeq n) (pts := ptsSeq n) (join := join)
      (p := pSeq n) (r := rSeq n) (hSeq n) (qstar := qstar) x (by positivity) hnear
  rw [dist_comm]
  calc
    dist
        (centerAverage (I := I) g (μSeq n) (ptsSeq n) join (pSeq n) (rSeq n) (hSeq n) x)
        (qstar x) ≤ 2 * (ε / 4) := hdist
    _ = ε / 2 := by ring
    _ < ε := by linarith

theorem unif_tendsto_i {s : Set X} {qstar : X → M}
    {μSeq : ℕ → X → ι → ℝ} {ptsSeq : ℕ → X → ι → M}
    {pSeq : ℕ → X → M} {rSeq : ℕ → X → ℝ}
    (hSeq : ∀ n : ℕ, ∀ x : X,
      CenterInput (I := I) g (μSeq n x) (ptsSeq n x) join (pSeq n x) (rSeq n x))
    (hpts :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, TendstoUniformlyOn (fun n x => ptsSeq n x i) qstar Filter.atTop s) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    TendstoUniformlyOn
      (fun n x => centerAverage (I := I) g (μSeq n) (ptsSeq n) join (pSeq n) (rSeq n)
        (hSeq n) x) qstar Filter.atTop s := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  refine unif_tendsto (I := I) (g := g) (join := join) hSeq ?_
  intro ε hε
  have hfin :
      ∀ᶠ n in Filter.atTop, ∀ i : ι, ∀ x ∈ s,
        dist (qstar x) (ptsSeq n x i) < ε := by
    refine Filter.eventually_all.mpr ?_
    intro i
    have hi := hpts i
    rw [Metric.tendstoUniformlyOn_iff] at hi
    exact hi ε hε
  exact hfin.mono fun n hn x hx i => by
    exact hn i x hx

theorem unif_tendsto_id {s : Set M}
    {μSeq : ℕ → M → ι → ℝ} {ptsSeq : ℕ → M → ι → M}
    {pSeq : ℕ → M → M} {rSeq : ℕ → M → ℝ}
    (hSeq : ∀ n : ℕ, ∀ x : M,
      CenterInput (I := I) g (μSeq n x) (ptsSeq n x) join (pSeq n x) (rSeq n x))
    (hpts :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, TendstoUniformlyOn (fun n x => ptsSeq n x i) (fun x : M => x)
        Filter.atTop s) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    TendstoUniformlyOn
      (fun n x => centerAverage (I := I) g (μSeq n) (ptsSeq n) join (pSeq n) (rSeq n)
        (hSeq n) x) (fun x : M => x) Filter.atTop s := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact unif_tendsto_i (I := I) (g := g) (join := join) hSeq hpts

theorem unif_two_index {s : Set X} {qstar : X → M}
    {μSeq : ℕ → ℕ → X → ι → ℝ} {ptsSeq : ℕ → ℕ → X → ι → M}
    {pSeq : ℕ → ℕ → X → M} {rSeq : ℕ → ℕ → X → ℝ}
    (hSeq : ∀ k l : ℕ, ∀ x : X,
      CenterInput (I := I) g (μSeq k l x) (ptsSeq k l x) join (pSeq k l x)
        (rSeq k l x))
    (hpts :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s, ∀ i : ι,
        dist (qstar x) (ptsSeq k l x i) < ε) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
      dist (qstar x)
        (centerAverage (I := I) g (μSeq k l) (ptsSeq k l) join (pSeq k l)
          (rSeq k l) (hSeq k l) x) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro ε hε
  have hquarter : 0 < ε / 4 := by positivity
  obtain ⟨N, hN⟩ := hpts (ε / 4) hquarter
  refine ⟨N, fun k hk l hl x hx => ?_⟩
  have hnear : ∀ i : ι, dist (qstar x) (ptsSeq k l x i) ≤ ε / 4 := fun i =>
    le_of_lt (hN k hk l hl x hx i)
  have hdist :
      dist
        (centerAverage (I := I) g (μSeq k l) (ptsSeq k l) join (pSeq k l) (rSeq k l)
          (hSeq k l) x)
        (qstar x) ≤ 2 * (ε / 4) :=
    dist_le (I := I) (g := g) (μ := μSeq k l) (pts := ptsSeq k l) (join := join)
      (p := pSeq k l) (r := rSeq k l) (hSeq k l) (qstar := qstar) x (by positivity)
      hnear
  rw [dist_comm]
  calc
    dist
        (centerAverage (I := I) g (μSeq k l) (ptsSeq k l) join (pSeq k l) (rSeq k l)
          (hSeq k l) x)
        (qstar x) ≤ 2 * (ε / 4) := hdist
    _ = ε / 2 := by ring
    _ < ε := by linarith

theorem unif_two_index_i {s : Set X} {qstar : X → M}
    {μSeq : ℕ → ℕ → X → ι → ℝ} {ptsSeq : ℕ → ℕ → X → ι → M}
    {pSeq : ℕ → ℕ → X → M} {rSeq : ℕ → ℕ → X → ℝ}
    (hSeq : ∀ k l : ℕ, ∀ x : X,
      CenterInput (I := I) g (μSeq k l x) (ptsSeq k l x) join (pSeq k l x)
        (rSeq k l x))
    (hpts :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
        dist (qstar x) (ptsSeq k l x i) < ε) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
      dist (qstar x)
        (centerAverage (I := I) g (μSeq k l) (ptsSeq k l) join (pSeq k l)
          (rSeq k l) (hSeq k l) x) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  refine unif_two_index (I := I) (g := g) (join := join) hSeq ?_
  intro ε hε
  classical
  choose N hN using fun i : ι => hpts i ε hε
  let Nmax : ℕ := Finset.univ.sup N
  refine ⟨Nmax, fun k hk l hl x hx i => ?_⟩
  have hNi : N i ≤ Nmax := by
    exact Finset.le_sup (s := Finset.univ) (f := N) (Finset.mem_univ i)
  exact hN i k (le_trans hNi hk) l (le_trans hNi hl) x hx

theorem unif_two_index_id {s : Set M}
    {μSeq : ℕ → ℕ → M → ι → ℝ} {ptsSeq : ℕ → ℕ → M → ι → M}
    {pSeq : ℕ → ℕ → M → M} {rSeq : ℕ → ℕ → M → ℝ}
    (hSeq : ∀ k l : ℕ, ∀ x : M,
      CenterInput (I := I) g (μSeq k l x) (ptsSeq k l x) join (pSeq k l x)
        (rSeq k l x))
    (hpts :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
        dist x (ptsSeq k l x i) < ε) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
      dist x
        (centerAverage (I := I) g (μSeq k l) (ptsSeq k l) join (pSeq k l)
          (rSeq k l) (hSeq k l) x) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact unif_two_index_i (I := I) (g := g) (join := join) hSeq hpts

theorem unif_two_id_fill {s : Set M}
    {μSeq : ℕ → ℕ → M → ι → ℝ} {ptsSeq : ℕ → ℕ → M → ι → M}
    {pSeq : ℕ → ℕ → M → M} {rSeq : ℕ → ℕ → M → ℝ}
    (hSeq : ∀ k l : ℕ, ∀ x : M,
      CenterInput (I := I) g (μSeq k l x)
        (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x) x) join
        (pSeq k l x) (rSeq k l x))
    (hpts :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
        μSeq k l x i ≠ 0 → dist x (ptsSeq k l x i) < ε) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
      dist x
        (centerAverage (I := I) g (μSeq k l)
          (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x)) join
          (pSeq k l) (rSeq k l) (hSeq k l) x) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  refine unif_two_index_id (I := I) (g := g) (join := join) hSeq ?_
  intro i ε hε
  obtain ⟨N, hN⟩ := hpts i ε hε
  refine ⟨N, fun k hk l hl x hx => ?_⟩
  by_cases hzero : μSeq k l x i = 0
  · simpa [activeFill, hzero] using hε
  · simpa [activeFill, hzero] using hN k hk l hl x hx hzero

theorem unif_two_id_fill_on {s : Set M}
    {μSeq : ℕ → ℕ → M → ι → ℝ} {ptsSeq : ℕ → ℕ → M → ι → M}
    {pSeq : ℕ → ℕ → M → M} {rSeq : ℕ → ℕ → M → ℝ}
    (hSeq : ∀ k l : ℕ, ∀ x : M, x ∈ s →
      CenterInput (I := I) g (μSeq k l x)
        (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x) x) join
        (pSeq k l x) (rSeq k l x))
    (hpts :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
        μSeq k l x i ≠ 0 → dist x (ptsSeq k l x i) < ε) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
      dist x
        (centerAverageOn (I := I) g s (μSeq k l)
          (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x)) join
          (pSeq k l) (rSeq k l) (fun x : M => x) (hSeq k l) x) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro ε hε
  have hquarter : 0 < ε / 4 := by positivity
  classical
  choose N hN using fun i : ι => hpts i (ε / 4) hquarter
  let Nmax : ℕ := Finset.univ.sup N
  refine ⟨Nmax, fun k hk l hl x hx => ?_⟩
  have hnear :
      ∀ i : ι,
        dist x (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x) x i) ≤
          ε / 4 := by
    intro i
    by_cases hzero : μSeq k l x i = 0
    · simpa [activeFill, hzero] using le_of_lt hquarter
    · have hNi : N i ≤ Nmax := by
        exact Finset.le_sup (s := Finset.univ) (f := N) (Finset.mem_univ i)
      exact le_of_lt <| by
        simpa [activeFill, hzero] using
          hN i k (le_trans hNi hk) l (le_trans hNi hl) x hx hzero
  have hdist :
      dist
          (centerOfMass (I := I) g (μSeq k l x)
            (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x) x) join
            (pSeq k l x) (rSeq k l x) (hSeq k l x hx)) x ≤
        2 * (ε / 4) := by
    simpa using
      centerOfMass.dist_le (I := I) (g := g) (μ := μSeq k l x)
        (pts := activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x) x)
        (join := join) (p := pSeq k l x) (r := rSeq k l x) (hSeq k l x hx)
        (qstar := x) (ε := ε / 4) (le_of_lt hquarter) hnear
  rw [centerAverageOn, dif_pos hx, dist_comm]
  exact lt_of_le_of_lt hdist (by nlinarith)

theorem unifTwoIdOfFill {s : Set M}
    {μSeq : ℕ → ℕ → M → ι → ℝ} {ptsSeq : ℕ → ℕ → M → ι → M}
    {pSeq : ℕ → ℕ → M → M} {rSeq : ℕ → ℕ → M → ℝ}
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hr : ∀ k l : ℕ, ∀ x : M, 0 < rSeq k l x)
    (hqstar :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ k l : ℕ, ∀ x : M, dist (pSeq k l x) x < rSeq k l x)
    (hactive_mem :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ k l : ℕ, ∀ x : M, ∀ i : ι, μSeq k l x i ≠ 0 →
        dist (pSeq k l x) (ptsSeq k l x i) < rSeq k l x)
    (hμ_nonneg : ∀ k l : ℕ, ∀ x : M, ∀ i : ι, 0 ≤ μSeq k l x i)
    (hμ_pos : ∀ k l : ℕ, ∀ x : M, ∃ i : ι, 0 < μSeq k l x i)
    (hstrict : ∀ k l : ℕ, ∀ x : M,
      StrictDistInput (I := I) g
        (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x) x) join
        (pSeq k l x) (rSeq k l x))
    (hpts :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
        μSeq k l x i ≠ 0 → dist x (ptsSeq k l x i) < ε) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
      dist x
        (centerAverage (I := I) g (μSeq k l)
          (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x)) join
          (pSeq k l) (rSeq k l)
          (fun x => inputOfFill (I := I) (g := g) (μ := μSeq k l)
            (pts := ptsSeq k l) (join := join) (p := pSeq k l)
            (r := rSeq k l) (qstar := fun x : M => x) x hcomplete (hr k l x)
            (hqstar k l x) (hactive_mem k l x) (hμ_nonneg k l x) (hμ_pos k l x)
            (hstrict k l x)) x) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact unif_two_id_fill (I := I) (g := g) (join := join)
    (fun k l x => inputOfFill (I := I) (g := g) (μ := μSeq k l)
      (pts := ptsSeq k l) (join := join) (p := pSeq k l)
      (r := rSeq k l) (qstar := fun x : M => x) x hcomplete (hr k l x)
      (hqstar k l x) (hactive_mem k l x) (hμ_nonneg k l x) (hμ_pos k l x)
      (hstrict k l x))
    hpts

theorem unifTwoIdOfFillOn {s : Set M}
    {μSeq : ℕ → ℕ → M → ι → ℝ} {ptsSeq : ℕ → ℕ → M → ι → M}
    {pSeq : ℕ → ℕ → M → M} {rSeq : ℕ → ℕ → M → ℝ}
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hr : ∀ k l : ℕ, ∀ x : M, x ∈ s → 0 < rSeq k l x)
    (hqstar :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ k l : ℕ, ∀ x : M, x ∈ s → dist (pSeq k l x) x < rSeq k l x)
    (hactive_mem :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ k l : ℕ, ∀ x : M, x ∈ s → ∀ i : ι, μSeq k l x i ≠ 0 →
        dist (pSeq k l x) (ptsSeq k l x i) < rSeq k l x)
    (hμ_nonneg : ∀ k l : ℕ, ∀ x : M, x ∈ s → ∀ i : ι, 0 ≤ μSeq k l x i)
    (hμ_pos : ∀ k l : ℕ, ∀ x : M, x ∈ s → ∃ i : ι, 0 < μSeq k l x i)
    (hstrict : ∀ k l : ℕ, ∀ x : M, x ∈ s →
      StrictDistInput (I := I) g
        (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x) x) join
        (pSeq k l x) (rSeq k l x))
    (hpts :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
        μSeq k l x i ≠ 0 → dist x (ptsSeq k l x i) < ε) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ s,
      dist x
        (centerAverageOn (I := I) g s (μSeq k l)
          (activeFill (μSeq k l) (ptsSeq k l) (fun x : M => x)) join
          (pSeq k l) (rSeq k l) (fun x : M => x)
          (fun x hx => inputOfFill (I := I) (g := g) (μ := μSeq k l)
            (pts := ptsSeq k l) (join := join) (p := pSeq k l)
            (r := rSeq k l) (qstar := fun x : M => x) x hcomplete (hr k l x hx)
            (hqstar k l x hx) (hactive_mem k l x hx) (hμ_nonneg k l x hx)
            (hμ_pos k l x hx) (hstrict k l x hx)) x) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  exact unif_two_id_fill_on (I := I) (g := g) (join := join)
    (fun k l x hx => inputOfFill (I := I) (g := g) (μ := μSeq k l)
      (pts := ptsSeq k l) (join := join) (p := pSeq k l)
      (r := rSeq k l) (qstar := fun x : M => x) x hcomplete (hr k l x hx)
      (hqstar k l x hx) (hactive_mem k l x hx) (hμ_nonneg k l x hx)
      (hμ_pos k l x hx) (hstrict k l x hx))
    hpts

end centerAverage
end HCGCompactness
end DifferentialGeometry
