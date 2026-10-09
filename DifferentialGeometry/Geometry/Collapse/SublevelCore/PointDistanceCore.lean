import DifferentialGeometry.Geometry.Collapse.SublevelCore.CommonFieldCore
import DifferentialGeometry.Geometry.Collapse.SublevelCore.DirectionMargin
import DifferentialGeometry.Geometry.Metric.Path.RiemannianHopfRinow

/-!
# LC55 kernel: the smoothed point-distance core is a constant-height normal-flow core

Master207A, A:22905 (LC55), at the normalized scale. Let `ζ` be a selected radial function with
`|ζ - d_p| < 1/80` and `ζ - d_p` `ε`-Lipschitz, `ε ≤ 1/64`, smooth near the collar
`{3/4 < d_p < 5/4}`, and let `V` be a field with `|V| ≤ 2` and `g(V, w) ≤ -1/4` against every
inward unit minimizing direction on that collar (LC54's field after normalization). Let `u` be a
proper continuous coordinate (the normal-flow fibre radius), smooth with `du(V) > 0` beyond a
level `T₀` whose sublevel lies in `B(p, 1/2)`. Then `D = {ζ ≤ 1}` is compact,
`closedBall(p, 1/2) ⊆ int D`, `D ⊆ B(p, 2)`, its frontier lies in `{79/80 < d_p < 81/80}`,
`dζ(V) ≥ 7/32` on the collar (LC44), and for some `T₁ > T₀` and every `ρ ∈ (T₀, T₁)` one
compactly supported smooth isotopy carries `D` onto the constant-height core `{u ≤ ρ}` (LC47
with the common field `V`; the unique crossing of every fibre is inside LC47).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **LC55 kernel** (master207A, A:22905, normalized scale). The sublevel `{ζ ≤ 1}` of a selected
radial function with the LC55 errors `1/80`, `1/64` is a compact core strictly between the closed
`1/2`-ball and the open `2`-ball, with frontier in `{79/80 < d_p < 81/80}`; the collar field has
`dζ(V) ≥ 7/32`; and for a proper normal-flow coordinate `u` with `du(V) > 0` beyond a level
`T₀` inside `B(p, 1/2)` there is `T₁ > T₀` such that for every `ρ ∈ (T₀, T₁)` a compactly supported
smooth isotopy carries `{ζ ≤ 1}` onto `{u ≤ ρ}`. -/
theorem point_distance_core_isotopy
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    {ζ : M → ℝ} {ε : ℝ≥0} (hε : (ε : ℝ) ≤ 1 / 64)
    (hclose : ∀ x, |ζ x - dist p x| < 1 / 80)
    (hlip : LipschitzWith ε (fun x => ζ x - dist p x))
    {Wζ : Set M} (hWζ : IsOpen Wζ)
    (hcollarW : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → x ∈ Wζ)
    (hζW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ζ Wζ)
    (V : (x : M) → TangentSpace I x)
    (hVB : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → g.inner x (V x) (V x) ≤ 4)
    (hVdir : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 →
      ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm p x, g.inner x (V x) w ≤ -(1 / 4))
    {u : M → ℝ} (hu : Continuous u) (hucpt : ∀ T, IsCompact {x | u x ≤ T})
    {T₀ : ℝ} (hT₀ : {x | u x ≤ T₀} ⊆ Metric.ball p (1 / 2))
    {Wu : Set M} (hWu : IsOpen Wu) (hWuT : {x | T₀ ≤ u x} ⊆ Wu)
    (huW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ u Wu)
    (hVW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) Wu)
    (huV : ∀ x, T₀ ≤ u x → 0 < mvfderiv (I := I) u x (V x)) :
    IsCompact {x | ζ x ≤ 1} ∧
      Metric.closedBall p (1 / 2) ⊆ interior {x | ζ x ≤ 1} ∧
      {x | ζ x ≤ 1} ⊆ Metric.ball p 2 ∧
      frontier {x | ζ x ≤ 1} ⊆ {x | 79 / 80 < dist p x ∧ dist p x < 81 / 80} ∧
      (∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → 7 / 32 ≤ mvfderiv (I := I) ζ x (V x)) ∧
      ∃ T₁ : ℝ, T₀ < T₁ ∧ ∀ ρ ∈ Ioo T₀ T₁, ∃ Hs : ℝ → Diffeomorph I I M M ∞,
        Hs 0 = Diffeomorph.refl I M ∞ ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Hs q.1 q.2) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (Hs q.1).symm q.2) ∧
        (∃ S : Set M, IsCompact S ∧ S ⊆ u ⁻¹' Ioo T₀ T₁ ∧
          ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
        Hs 1 '' {x | ζ x ≤ 1} = {x | u x ≤ ρ} := by
  let : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  have hζ : Continuous ζ :=
    (hlip.continuous.add (continuous_const.dist continuous_id)).congr
      (fun x => sub_add_cancel (ζ x) (dist p x))
  set D : Set M := {x | ζ x ≤ 1} with hDdef
  have hDclosed : IsClosed D := isClosed_le hζ continuous_const
  have hDball : D ⊆ Metric.closedBall p (1 + 1 / 80) := by
    intro x hx
    have h := abs_lt.mp (hclose x)
    change ζ x ≤ 1 at hx
    rw [Metric.mem_closedBall, dist_comm]
    linarith [h.1]
  have hDcpt : IsCompact D := (isCompact_closedBall p _).of_isClosed_subset hDclosed hDball
  have hin : Metric.closedBall p (1 / 2) ⊆ interior D := by
    intro x hx
    apply interior_mono (show {y | ζ y < 1} ⊆ D from fun y (hy : ζ y < 1) =>
      (show ζ y ≤ 1 from le_of_lt hy))
    rw [(isOpen_lt hζ continuous_const).interior_eq]
    have h := abs_lt.mp (hclose x)
    rw [Metric.mem_closedBall, dist_comm] at hx
    change ζ x < 1
    linarith [h.2]
  have hout : D ⊆ Metric.ball p 2 := by
    intro x hx
    have h := abs_lt.mp (hclose x)
    change ζ x ≤ 1 at hx
    rw [Metric.mem_ball, dist_comm]
    linarith [h.1]
  have hfront : frontier D ⊆ {x | 79 / 80 < dist p x ∧ dist p x < 81 / 80} := by
    intro x hx
    have h1 : ζ x = 1 := frontier_le_subset_eq hζ continuous_const hx
    have h := abs_lt.mp (hclose x)
    rw [h1] at h
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  have hmargin : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 →
      7 / 32 ≤ mvfderiv (I := I) ζ x (V x) := by
    intro x h1 h2
    have hpx : p ≠ x := fun h => by rw [h, dist_self] at h1; linarith
    have hd : MDifferentiableAt I 𝓘(ℝ, ℝ) ζ x :=
      (hζW.contMDiffAt (hWζ.mem_nhds (hcollarW x h1 h2))).mdifferentiableAt (by norm_num)
    have hB : √(g.inner x (V x) (V x)) ≤ 2 :=
      (Real.sqrt_le_sqrt (hVB x h1 h2)).trans_eq (by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)])
    have h := sub_mul_le_mvfderiv_of_lipschitz_sub_dist (I := I) g hEnorm hpx hd hlip hB
      (hVdir x h1 h2)
    have hε2 : (ε : ℝ) * 2 ≤ 1 / 32 := by linarith
    linarith
  obtain ⟨Tm, hTm⟩ := (hDcpt.image hu).bddAbove
  set T₁ : ℝ := max (T₀ + 1) (Tm + 1) with hT₁def
  have hT₀₁ : T₀ < T₁ := lt_of_lt_of_le (lt_add_one T₀) (le_max_left _ _)
  have hDT₁ : D ⊆ {x | u x < T₁} := fun x hx =>
    lt_of_le_of_lt (hTm ⟨x, hx, rfl⟩) (lt_of_lt_of_le (lt_add_one Tm) (le_max_right _ _))
  refine ⟨hDcpt, hin, hout, hfront, hmargin, T₁, hT₀₁, fun ρ hρ => ?_⟩
  have hband : IsCompact (u ⁻¹' Icc T₀ T₁) :=
    (hucpt T₁).of_isClosed_subset (isClosed_Icc.preimage hu) (fun x hx => hx.2)
  have hbandW : u ⁻¹' Icc T₀ T₁ ⊆ Wu := fun x hx => hWuT hx.1
  have hAD : {x | u x ≤ T₀} ⊆ interior D := fun x hx =>
    hin (Metric.ball_subset_closedBall (hT₀ hx))
  have hdef : ∀ q ∈ frontier D, ∃ L : Set M, IsOpen L ∧ q ∈ L ∧ ∃ f : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f L ∧ D ∩ L = {x | f x ≤ 0} ∩ L ∧
        0 < mvfderiv (I := I) f q (V q) := by
    intro q hq
    have hq' := hfront hq
    have h1 : 3 / 4 < dist p q := by linarith [hq'.1]
    have h2 : dist p q < 5 / 4 := by linarith [hq'.2]
    let L : Set M := Wζ ∩ {x | 3 / 4 < dist p x ∧ dist p x < 5 / 4}
    have hL : IsOpen L :=
      hWζ.inter ((isOpen_lt continuous_const (continuous_const.dist continuous_id)).inter
        (isOpen_lt (continuous_const.dist continuous_id) continuous_const))
    have hqL : q ∈ L := ⟨hcollarW q h1 h2, h1, h2⟩
    refine ⟨L, hL, hqL, fun x => ζ x - 1, (hζW.mono inter_subset_left).sub contMDiffOn_const,
      ?_, ?_⟩
    · ext x
      simp only [hDdef, mem_inter_iff, mem_ofPred_eq, sub_nonpos]
    · have hd : MDifferentiableAt I 𝓘(ℝ, ℝ) ζ q :=
        (hζW.contMDiffAt (hWζ.mem_nhds (hcollarW q h1 h2))).mdifferentiableAt (by norm_num)
      rw [mvfderiv_fun_sub hd mdifferentiableAt_const, mvfderiv_const, sub_zero]
      linarith [hmargin q h1 h2]
  exact exists_isotopy_of_common_outward_field hu hWu huW hρ hband hbandW V hVW
    (fun x hx => huV x hx.1) hDclosed hAD hDT₁ hdef

end DifferentialGeometry.Geometry.Collapse
