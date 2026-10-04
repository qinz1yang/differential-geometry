import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointDistanceCore
import DifferentialGeometry.Geometry.Collapse.SublevelCore.PushedCollarPacket

/-!
# LC55 core transferred by LC51 (the noncompact branch of LC57 at a fixed normalized scale)

The LC55 kernel `point_distance_core_isotopy` produces the model core `D = {ζ ≤ 1}`; its own collar
field has LC51's explicit constants `α = 1/8`, `B = 2` (master207A, after LC55: "the explicit LC51
choices"). With LC50's actual maps and selected source radial functions `η i` with smoothing
tolerance `ε < 1/32` (the blueprint uses `ε < 1/64`), one tail carries `j i (D)` onto every
`{η i ≤ ρ}`, `ρ ∈ [1/5, 2]`, while in the model `D` is isotopic to the constant-height normal-flow
cores `{u ≤ ρ'}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [SigmaCompactSpace N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  [CompleteSpace N] [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
  [∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [∀ i, IsRiemannianManifold I (M i)] [∀ i, CompleteSpace (M i)]
  [∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ N]
  [SigmaCompactSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N] [CompleteSpace N]
  [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)] in
/-- The frontier of `{ζ ≤ 1}` has the local defining function `ζ - 1` with positive
`V`-derivative, once the frontier lies in the collar where `ζ` is smooth and `dζ(V) > 0`. -/
theorem sublevel_local_defining_functions {p : N} {ζ : N → ℝ} {Wζ : Set N} (hWζ : IsOpen Wζ)
    (hcollarW : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → x ∈ Wζ)
    (hζW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ζ Wζ) (V : (x : N) → TangentSpace I x)
    (hfront : frontier {x | ζ x ≤ 1} ⊆ {x | 79 / 80 < dist p x ∧ dist p x < 81 / 80})
    (hmargin : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → 7 / 32 ≤ mvfderiv (I := I) ζ x (V x)) :
    ∀ q ∈ frontier {x | ζ x ≤ 1}, ∃ L : Set N, IsOpen L ∧ q ∈ L ∧ ∃ f : N → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f L ∧ {x | ζ x ≤ 1} ∩ L = {x | f x ≤ 0} ∩ L ∧
        0 < mvfderiv (I := I) f q (V q) := by
  intro q hq
  have hq' := hfront hq
  have h1 : 3 / 4 < dist p q := by linarith [hq'.1]
  have h2 : dist p q < 5 / 4 := by linarith [hq'.2]
  refine ⟨Wζ, hWζ, hcollarW q h1 h2, fun x => ζ x - 1, hζW.sub contMDiffOn_const, ?_, ?_⟩
  · ext x
    simp only [mem_inter_iff, mem_ofPred_eq, sub_nonpos]
  · have hd : MDifferentiableAt I 𝓘(ℝ, ℝ) ζ q :=
      (hζW.contMDiffAt (hWζ.mem_nhds (hcollarW q h1 h2))).mdifferentiableAt (by norm_num)
    rw [mvfderiv_fun_sub hd mdifferentiableAt_const, mvfderiv_const, sub_zero]
    linarith [hmargin q h1 h2]

/-- **Consumer of LC55 (kernel) and LC51 (collar form).** At a fixed normalized scale, on the actual
LC50 data: the LC55 core `D = {ζ ≤ 1}` of the model is isotopic to the constant-height cores
`{u ≤ ρ'}`, `ρ' ∈ (T₀, T₁)`, and on one source tail, for every `ρ ∈ [1/5, 2]`, a compactly supported
smooth isotopy of `M i` carries `j i (D)` onto `{η i ≤ ρ}` (LC51 with `α = 1/8`, `B = 2`). -/
theorem eventually_core_isotopies_of_point_distance_core
    (g : SmoothRiemannianMetric I N) (hNorm : IsMetricNorm g)
    (U : TopologicalSpace.Opens N) (n : U)
    (hbuffer : Metric.closedBall (n : N) 10 ⊆ U)
    (hSeq : ℕ → SmoothRiemannianMetric I U)
    (gSeq : ∀ i, SmoothRiemannianMetric I (M i))
    (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
    (j : ∀ i, PartialDiffeomorph I I U (M i) ∞)
    (hj : ∀ i, (j i).source = univ)
    (hmetric : ∀ i, ∀ x : U, ∀ v w : TangentSpace I x,
      (hSeq i).inner x v w = (gSeq i).inner (j i x)
        (mfderiv I I (j i : U → M i) x v) (mfderiv I I (j i : U → M i) x w))
    (hconv : ∀ C : Set U, IsCompact C →
      MetricCPConvergenceOn C 1 hSeq (g.restrictOpen U) (g.restrictOpen U))
    {ζ : N → ℝ} {εN : ℝ≥0} (hεN : (εN : ℝ) ≤ 1 / 64)
    (hclose : ∀ x, |ζ x - dist (n : N) x| < 1 / 80)
    (hlip : LipschitzWith εN (fun x => ζ x - dist (n : N) x))
    {Wζ : Set N} (hWζ : IsOpen Wζ)
    (hcollarW : ∀ x, 3 / 4 < dist (n : N) x → dist (n : N) x < 5 / 4 → x ∈ Wζ)
    (hζW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ζ Wζ)
    (V : (x : N) → TangentSpace I x)
    (hVB : ∀ x, 3 / 4 < dist (n : N) x → dist (n : N) x < 5 / 4 → g.inner x (V x) (V x) ≤ 4)
    (hVdir : ∀ x, 3 / 4 < dist (n : N) x → dist (n : N) x < 5 / 4 →
      ∀ w ∈ inwardMinimizingDirections (I := I) g hNorm (n : N) x, g.inner x (V x) w ≤ -(1 / 4))
    {u : N → ℝ} (hu : Continuous u) (hucpt : ∀ T, IsCompact {x | u x ≤ T})
    {T₀ : ℝ} (hT₀ : {x | u x ≤ T₀} ⊆ Metric.ball (n : N) (1 / 2))
    {Wu : Set N} (hWu : IsOpen Wu) (hWuT : {x | T₀ ≤ u x} ⊆ Wu)
    (huW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ u Wu)
    (hVW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, V x⟩ : TangentBundle I N)) Wu)
    (huV : ∀ x, T₀ ≤ u x → 0 < mvfderiv (I := I) u x (V x))
    {ε : ℝ≥0} (hε : (ε : ℝ) < 1 / 32)
    (η : ∀ i, M i → ℝ) (e : ℕ → ℝ)
    (hη : ∀ᶠ i in atTop, e i < 1 / 40 ∧ (∀ x, |η i x - dist (j i n) x| < e i) ∧
      LipschitzWith ε (fun x => η i x - dist (j i n) x) ∧
      ∃ Wi : Set (M i), IsOpen Wi ∧
        (∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 → x ∈ Wi) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η i) Wi ∧
        ∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 →
          (1 - (ε : ℝ)) ^ 2 ≤ (gSeq i).inner x (gradientFun (I := I) (gSeq i) (η i) x)
            (gradientFun (I := I) (gSeq i) (η i) x)) :
    ∃ T₁ : ℝ, T₀ < T₁ ∧
      (∀ ρ' ∈ Ioo T₀ T₁, ∃ K : ℝ → Diffeomorph I I N N ∞, K 0 = Diffeomorph.refl I N ∞ ∧
        K 1 '' {x | ζ x ≤ 1} = {x | u x ≤ ρ'}) ∧
      ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∃ Hs : ℝ → Diffeomorph I I (M i) (M i) ∞,
        Hs 0 = Diffeomorph.refl I (M i) ∞ ∧
        Hs 1 '' ((j i : U → M i) '' (Subtype.val ⁻¹' {x | ζ x ≤ 1})) = {x | η i x ≤ ρ} := by
  obtain ⟨hDcpt, hin, hout, hfront, hmargin, T₁, hT₀₁, hiso⟩ :=
    point_distance_core_isotopy g hNorm (n : N) hεN hclose hlip hWζ hcollarW hζW V hVB hVdir
      hu hucpt hT₀ hWu hWuT huW hVW huV
  refine ⟨T₁, hT₀₁, fun ρ' hρ' => ?_, ?_⟩
  · obtain ⟨K, hK0, -, -, -, hK1⟩ := hiso ρ' hρ'
    exact ⟨K, hK0, hK1⟩
  -- the collar `7/8 < d < 9/8` and LC51 with `α = 1/8`, `B = 2`
  let W : Set N := {x | 7 / 8 < dist (n : N) x ∧ dist (n : N) x < 9 / 8}
  let O : Set N := {x | 3 / 4 < dist (n : N) x ∧ dist (n : N) x < 5 / 4}
  have hdc : Continuous (fun x : N => dist (n : N) x) := continuous_const.dist continuous_id
  have hW : IsOpen W := (isOpen_lt continuous_const hdc).inter (isOpen_lt hdc continuous_const)
  have hO : IsOpen O := (isOpen_lt continuous_const hdc).inter (isOpen_lt hdc continuous_const)
  have hclW : closure W ⊆ {x | 7 / 8 ≤ dist (n : N) x ∧ dist (n : N) x ≤ 9 / 8} :=
    closure_minimal (fun x hx => ⟨hx.1.le, hx.2.le⟩)
      ((isClosed_le continuous_const hdc).inter (isClosed_le hdc continuous_const))
  have hWsub : closure W ⊆ (Metric.ball (n : N) 3 \ {(n : N)}) ∩ O := by
    intro x hx
    have h := hclW hx
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_comm]; linarith [h.2]
    · intro hxn
      rw [mem_singleton_iff] at hxn
      have h1 : 7 / 8 ≤ dist (n : N) x := h.1
      rw [hxn, dist_self] at h1
      linarith
    · linarith [h.1]
    · linarith [h.2]
  have hWcpt : IsCompact (closure W) := by
    let : ProperSpace N := Manifold.properSpace_of_isRiemannianManifold I
    exact (isCompact_closedBall (n : N) 2).of_isClosed_subset isClosed_closure (fun x hx => by
      rw [Metric.mem_closedBall, dist_comm]; linarith [(hclW hx).2])
  have hfrW : frontier {x | ζ x ≤ 1} ⊆ W := fun x hx =>
    ⟨by linarith [(hfront hx).1], by linarith [(hfront hx).2]⟩
  have hOWu : O ⊆ Wu := by
    intro x hx
    apply hWuT
    change T₀ ≤ u x
    by_contra hlt
    push Not at hlt
    have hb := hT₀ (show u x ≤ T₀ from hlt.le)
    rw [Metric.mem_ball, dist_comm] at hb
    have : 3 / 4 < dist (n : N) x := hx.1
    linarith
  have hdef := sublevel_local_defining_functions hWζ hcollarW hζW V hfront hmargin
  have hiso' := eventually_core_isotopy_of_collar_margin g hNorm U n hbuffer hSeq gSeq hSeqNorm j
    hj hmetric hconv (isClosed_le (hlip.continuous.add hdc |>.congr
      (fun x => sub_add_cancel (ζ x) (dist (n : N) x))) continuous_const) hin hout hW hfrW hWcpt
    hWsub hO V (hVW.mono hOWu) hdef (α := 1 / 8) (B := 2) (by norm_num) (by norm_num)
    (fun q hq => by
      have h := (hWsub hq).2
      have := hVB q h.1 h.2
      linarith)
    (fun q hq v hv => by
      have h := (hWsub hq).2
      have := hVdir q h.1 h.2 v hv
      linarith)
    (by linarith) (by linarith) η e hη
  filter_upwards [hiso'] with i hi ρ hρ
  obtain ⟨Hs, h0, -, -, -, h1⟩ := hi ρ hρ
  exact ⟨Hs, h0, h1⟩

end DifferentialGeometry.Geometry.Collapse
