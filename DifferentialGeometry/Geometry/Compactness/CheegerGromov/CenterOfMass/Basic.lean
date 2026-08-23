import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Existence


open DifferentialGeometry.Geometry.Curvature

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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M] [T3Space M] in
theorem metricEnorm (g : SmoothRiemannianMetric I M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  intro x v
  simpa using
    (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) g x v)

noncomputable def centerAverage (g : SmoothRiemannianMetric I M)
    {X : Type uX} {ι : Type} [Fintype ι] (μ : X → ι → ℝ)
    (pts : X → ι → M) (join : M → M → ℝ → M) (p : X → M) (r : X → ℝ)
    (h : ∀ x : X, CenterInput (I := I) g (μ x) (pts x) join (p x) (r x))
    (x : X) : M :=
  centerOfMass (I := I) g (μ x) (pts x) join (p x) (r x) (h x)

noncomputable def centerAverageOn (g : SmoothRiemannianMetric I M)
    {X : Type uX} {ι : Type} [Fintype ι] (s : Set X) (μ : X → ι → ℝ)
    (pts : X → ι → M) (join : M → M → ℝ → M) (p : X → M) (r : X → ℝ)
    (qstar : X → M)
    (h : ∀ x : X, x ∈ s → CenterInput (I := I) g (μ x) (pts x) join (p x) (r x))
    (x : X) : M :=
  by
    classical
    exact
      if hx : x ∈ s then
        centerOfMass (I := I) g (μ x) (pts x) join (p x) (r x) (h x hx)
      else qstar x

namespace centerAverage

variable {g : SmoothRiemannianMetric I M} {X : Type uX} {ι : Type}

noncomputable def activeFill (μ : X → ι → ℝ) (pts : X → ι → M)
    (qstar : X → M) : X → ι → M := by
  classical
  exact fun x i => if μ x i = 0 then qstar x else pts x i

omit [T3Space M] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem energy_activeFill [Fintype ι] (g : SmoothRiemannianMetric I M)
    (μ : X → ι → ℝ) (pts : X → ι → M) (qstar : X → M)
    (x : X) (q : M) :
    CenterOfMass.centerEnergy (I := I) g (μ x) (activeFill μ pts qstar x) q =
      CenterOfMass.centerEnergy (I := I) g (μ x) (pts x) q := by
  apply CenterOfMass.centerEnergy_congr
  intro i hi
  simp only [activeFill, hi, ↓reduceIte]

theorem uniqueMin_activeFill [Fintype ι] (g : SmoothRiemannianMetric I M)
    (μ : X → ι → ℝ) (pts : X → ι → M) (qstar : X → M)
    (join : M → M → ℝ → M) (p : X → M) (r : X → ℝ)
    (x : X) (h : CenterInput (I := I) g (μ x)
      (activeFill μ pts qstar x) join (p x) (r x)) :
    ∃! y : M, ∀ z : M,
      CenterOfMass.centerEnergy (I := I) g (μ x) (pts x) y ≤
        CenterOfMass.centerEnergy (I := I) g (μ x) (pts x) z := by
  letI : RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  obtain ⟨y, _hy, hmin, huniq⟩ := h.exists_cm
  refine ⟨y, ?_, ?_⟩
  · intro z
    rw [← energy_activeFill g μ pts qstar x y,
      ← energy_activeFill g μ pts qstar x z]
    exact hmin z
  · intro y' hy'
    apply huniq y'
    intro z
    rw [energy_activeFill g μ pts qstar x y',
      energy_activeFill g μ pts qstar x z]
    exact hy' z

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem activeFill_close {μ : X → ι → ℝ} {pts : X → ι → M} {qstar : X → M}
    {x : X} {ε : ℝ} (hε : 0 < ε)
    (hactive :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, μ x i ≠ 0 → dist (qstar x) (pts x i) < ε) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ i : ι, dist (qstar x) (activeFill μ pts qstar x i) < ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro i
  by_cases hzero : μ x i = 0
  · simpa [activeFill, hzero] using hε
  · simpa [activeFill, hzero] using hactive i hzero

variable [Fintype ι]

omit [Fintype ι] in
theorem exists_active_radius {Y : Type uY} [PseudoMetricSpace Y] {s : Set X}
    [Finite ι]
    {target : X → Y} {μSeq : ℕ → ℕ → X → ι → ℝ}
    {ptsSeq : ℕ → ℕ → X → ι → Y}
    (hpts : ∀ i : ι, ∀ ε > 0, ∃ N : ℕ, ∀ a ≥ N, ∀ b ≥ N, ∀ x ∈ s,
      μSeq a b x i ≠ 0 → dist (target x) (ptsSeq a b x i) < ε) :
    ∃ radSeq : ℕ → ℕ → X → ℝ,
      (∀ a b x, 0 < radSeq a b x) ∧
      (∀ a b x, x ∈ s → ∀ i : ι, μSeq a b x i ≠ 0 →
        dist (target x) (ptsSeq a b x i) < radSeq a b x) ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ a ≥ N, ∀ b ≥ N, ∀ x ∈ s, radSeq a b x < ε := by
  classical
  letI := Fintype.ofFinite ι
  let radSeq : ℕ → ℕ → X → ℝ := fun a b x =>
    (∑ i : ι, if μSeq a b x i = 0 then 0 else dist (target x) (ptsSeq a b x i)) +
      1 / ((a : ℝ) + 1)
  refine ⟨radSeq, ?_, ?_, ?_⟩
  · intro a b x
    have hsum : 0 ≤
        ∑ i : ι, if μSeq a b x i = 0 then 0 else dist (target x) (ptsSeq a b x i) := by
      exact Finset.sum_nonneg fun i _ => by
        split_ifs
        · exact le_rfl
        · exact dist_nonneg
    have htail : 0 < 1 / ((a : ℝ) + 1) := by positivity
    exact add_pos_of_nonneg_of_pos hsum htail
  · intro a b x hx i hi
    have hle : dist (target x) (ptsSeq a b x i) ≤
        ∑ j : ι, if μSeq a b x j = 0 then 0 else dist (target x) (ptsSeq a b x j) := by
      calc
        dist (target x) (ptsSeq a b x i) =
            (if μSeq a b x i = 0 then 0 else dist (target x) (ptsSeq a b x i)) := by
              simp [hi]
        _ ≤ ∑ j : ι,
            if μSeq a b x j = 0 then 0 else dist (target x) (ptsSeq a b x j) := by
              refine Finset.single_le_sum (s := Finset.univ)
                (f := fun j : ι =>
                  if μSeq a b x j = 0 then (0 : ℝ) else dist (target x) (ptsSeq a b x j))
                ?_ (Finset.mem_univ i)
              intro j _
              change 0 ≤ if μSeq a b x j = 0 then (0 : ℝ) else
                dist (target x) (ptsSeq a b x j)
              by_cases hj : μSeq a b x j = 0
              · simp [hj]
              · simp [hj, dist_nonneg]
    have htail : 0 < 1 / ((a : ℝ) + 1) := by positivity
    exact lt_of_le_of_lt hle (lt_add_of_pos_right _ htail)
  · intro ε hε
    let δ : ℝ := ε / (2 * ((Fintype.card ι : ℝ) + 1))
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    choose N hN using fun i : ι => hpts i δ hδ
    let Nmax : ℕ := Finset.univ.sup N
    have htail : ∀ᶠ a : ℕ in Filter.atTop, 1 / ((a : ℝ) + 1) < ε / 2 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (Iio_mem_nhds (by linarith))
    obtain ⟨Ntail, hNtail⟩ := Filter.eventually_atTop.mp htail
    refine ⟨max Nmax Ntail, fun a ha b hb x hx => ?_⟩
    have ha_max : Nmax ≤ a := le_trans (le_max_left _ _) ha
    have ha_tail : Ntail ≤ a := le_trans (le_max_right _ _) ha
    have hb_max : Nmax ≤ b := le_trans (le_max_left _ _) hb
    have hsum_le :
        (∑ i : ι,
          if μSeq a b x i = 0 then 0 else dist (target x) (ptsSeq a b x i)) ≤
          ∑ _i : ι, δ := by
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : μSeq a b x i = 0
      · simp [hi, hδ.le]
      · simp only [hi, ↓reduceIte]
        have hNi : N i ≤ Nmax :=
          Finset.le_sup (s := Finset.univ) (f := N) (Finset.mem_univ i)
        exact le_of_lt (hN i a (le_trans hNi ha_max) b (le_trans hNi hb_max) x hx hi)
    have hcard :
        (∑ _i : ι, δ) = (Fintype.card ι : ℝ) * δ := by simp
    have hcard_lt : (Fintype.card ι : ℝ) * δ < ε / 2 := by
      dsimp [δ]
      have hden : 0 < 2 * ((Fintype.card ι : ℝ) + 1) := by positivity
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hden).2
      have hcard_nonneg : 0 ≤ (Fintype.card ι : ℝ) := by positivity
      nlinarith
    have hsum_lt :
        (∑ i : ι,
          if μSeq a b x i = 0 then 0 else dist (target x) (ptsSeq a b x i)) <
          ε / 2 :=
      lt_of_le_of_lt hsum_le (hcard ▸ hcard_lt)
    simpa [radSeq] using add_lt_add_of_lt_of_lt hsum_lt (hNtail a ha_tail)

structure WeightDataOn (s : Set X) (U : ι → Set X) (μ : X → ι → ℝ) : Prop where
  nonneg : ∀ x ∈ s, ∀ i : ι, 0 ≤ μ x i
  pos : ∀ x ∈ s, ∃ i : ι, 0 < μ x i
  sum_one : ∀ x ∈ s, ∑ i : ι, μ x i = 1
  active_mem : ∀ x ∈ s, ∀ i : ι, μ x i ≠ 0 → x ∈ U i

theorem WeightDataOn.comp {Y : Type uY} {s : Set Y} {U : Set X}
    {R : ι → Set X} {μ : X → ι → ℝ} {f : Y → X}
    (h : WeightDataOn U R μ) (hf : Set.MapsTo f s U) :
    WeightDataOn s (fun i => f ⁻¹' R i) (fun y i => μ (f y) i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy i
    exact h.nonneg (f y) (hf hy) i
  · intro y hy
    exact h.pos (f y) (hf hy)
  · intro y hy
    exact h.sum_one (f y) (hf hy)
  · intro y hy i hne
    exact h.active_mem (f y) (hf hy) i hne

theorem WeightDataOn.data {s : Set X} {U : ι → Set X} {μ : X → ι → ℝ}
    (h : WeightDataOn s U μ) {x : X} (hx : x ∈ s) :
    ((∀ i : ι, 0 ≤ μ x i) ∧ (∃ i : ι, 0 < μ x i) ∧ ∑ i : ι, μ x i = 1) ∧
      ∀ i : ι, μ x i ≠ 0 → x ∈ U i := by
  exact ⟨⟨h.nonneg x hx, h.pos x hx, h.sum_one x hx⟩, h.active_mem x hx⟩

variable {μ : X → ι → ℝ} {pts : X → ι → M} {join : M → M → ℝ → M}
  {p : X → M} {r : X → ℝ}
  (h : ∀ x : X, CenterInput (I := I) g (μ x) (pts x) join (p x) (r x))

theorem on_eq {s : Set X} {qstar : X → M}
    (hOn : ∀ x : X, x ∈ s → CenterInput (I := I) g (μ x) (pts x) join (p x) (r x))
    {x : X} (hx : x ∈ s) :
    centerAverageOn (I := I) g s μ pts join p r qstar hOn x =
      centerOfMass (I := I) g (μ x) (pts x) join (p x) (r x) (hOn x hx) := by
  simp [centerAverageOn, hx]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem inputOfFill {qstar : X → M} (x : X)
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hr : 0 < r x)
    (hqstar :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      dist (p x) (qstar x) < r x)
    (hactive :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, μ x i ≠ 0 → dist (p x) (pts x i) < r x)
    (hμ_nonneg : ∀ i : ι, 0 ≤ μ x i)
    (hμ_pos : ∃ i : ι, 0 < μ x i)
    (hstrict :
      StrictDistInput (I := I) g (activeFill μ pts qstar x) join (p x) (r x)) :
    CenterInput (I := I) g (μ x) (activeFill μ pts qstar x) join (p x) (r x) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  refine
    { complete := hcomplete
      enorm := metricEnorm (I := I) g
      r_pos := hr
      pts_mem := ?_
      μ_nonneg := hμ_nonneg
      μ_pos := hμ_pos
      strict := hstrict }
  intro i
  by_cases hzero : μ x i = 0
  · simpa [activeFill, hzero] using hqstar
  · simpa [activeFill, hzero] using hactive i hzero

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem inputOfFillSelf {qstar : X -> M} (x : X)
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hr : 0 < r x)
    (hactive :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      forall i : ι, μ x i ≠ 0 -> dist (qstar x) (pts x i) < r x)
    (hμ_nonneg : forall i : ι, 0 ≤ μ x i)
    (hμ_pos : exists i : ι, 0 < μ x i)
    (hstrict :
      StrictDistInput (I := I) g (activeFill μ pts qstar x) join (qstar x) (r x)) :
    CenterInput (I := I) g (μ x) (activeFill μ pts qstar x) join (qstar x)
      (r x) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  refine inputOfFill (I := I) (g := g) (μ := μ) (pts := pts) (join := join)
    (p := qstar) (r := r) (qstar := qstar) x hcomplete hr ?_ hactive
    hμ_nonneg hμ_pos hstrict
  simpa using hr

theorem mem (x : X) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    centerAverage (I := I) g μ pts join p r h x ∈ Metric.closedBall (p x) (2 * r x) := by
  simpa [centerAverage] using
    centerOfMass.mem (I := I) (g := g) (μ := μ x) (pts := pts x) (join := join)
      (p := p x) (r := r x) (h x)

theorem mem_on {s : Set X} {qstar : X → M}
    (hOn : ∀ x : X, x ∈ s → CenterInput (I := I) g (μ x) (pts x) join (p x) (r x))
    {x : X} (hx : x ∈ s) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    centerAverageOn (I := I) g s μ pts join p r qstar hOn x ∈
      Metric.closedBall (p x) (2 * r x) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  rw [on_eq (I := I) (g := g) (μ := μ) (pts := pts) (join := join) (p := p)
    (r := r) hOn hx]
  exact centerOfMass.mem (I := I) (g := g) (μ := μ x) (pts := pts x)
    (join := join) (p := p x) (r := r x) (hOn x hx)

theorem eq_of_all_eq {qstar : X → M} (x : X)
    (hpts : ∀ i : ι, pts x i = qstar x) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    centerAverage (I := I) g μ pts join p r h x = qstar x := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hnear : ∀ i : ι, dist (qstar x) (pts x i) ≤ (0 : ℝ) := by
    intro i
    rw [hpts i, dist_self]
  have hdist :
      dist (centerAverage (I := I) g μ pts join p r h x) (qstar x) ≤ 0 :=
    by
      simpa [centerAverage] using
        centerOfMass.dist_le (I := I) (g := g) (μ := μ x) (pts := pts x)
          (join := join) (p := p x) (r := r x) (h x) (qstar := qstar x)
          (by norm_num) hnear
  exact dist_eq_zero.mp (le_antisymm hdist dist_nonneg)

theorem dist_le {qstar : X → M} {ε : ℝ} (x : X) (hε : 0 ≤ ε)
    (hnear :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, dist (qstar x) (pts x i) ≤ ε) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    dist (centerAverage (I := I) g μ pts join p r h x) (qstar x) ≤ 2 * ε := by
  simpa [centerAverage] using
    centerOfMass.dist_le (I := I) (g := g) (μ := μ x) (pts := pts x)
      (join := join) (p := p x) (r := r x) (h x) (qstar := qstar x) hε hnear

theorem dist_le_on {s : Set X} {default target : X → M} {ε : ℝ}
    (hOn : ∀ x : X, x ∈ s → CenterInput (I := I) g (μ x) (pts x) join (p x) (r x))
    {x : X} (hx : x ∈ s) (hε : 0 ≤ ε)
    (hnear :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ∀ i : ι, dist (target x) (pts x i) ≤ ε) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    dist (centerAverageOn (I := I) g s μ pts join p r default hOn x) (target x) ≤
      2 * ε := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  rw [on_eq (I := I) (g := g) (μ := μ) (pts := pts) (join := join) (p := p)
    (r := r) hOn hx]
  exact centerOfMass.dist_le (I := I) (g := g) (μ := μ x) (pts := pts x)
    (join := join) (p := p x) (r := r x) (hOn x hx) (qstar := target x) hε hnear

end centerAverage
end HCGCompactness
end DifferentialGeometry
