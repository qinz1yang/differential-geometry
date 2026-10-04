import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenBallCoreType
import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenBallDiffeomorph
import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointDistanceCoreApplications
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

/-!
# LC61 at a fixed normalized scale, with an abstract core coordinate

Master207A, A:23460 (LC61), noncompact branch, at the normalized scale of LC57: the version of
`eventually_open_ball_bundle_type` in which the normal-flow coordinate `u` is abstract (continuous,
proper, smooth beyond a level `T₀` with `du(V) > 0`), so that no vector-bundle structure enters.
One tail has, for every `ρ ∈ [1/5, 2]` and every `ρ'` in a nonempty interval `(T₀, T₁)`, a
diffeomorphism of the open ball `B(p_i, ρ)` onto the interior of the constant-height core
`{u ≤ ρ'}` of the model. (For LC54's `u` the latter interior is diffeomorphic to the model itself;
this is supplied separately, in the original metric.)

The metric-space, Riemannian-bundle and manifold instances carry names so that a caller can supply
rescaled ones (`m.rescale R⁻¹`, `radialScaledBundle`, …) explicitly.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Manifold

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type} [mN : MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [SigmaCompactSpace N]
  [rbN : RiemannianBundle (fun x : N => TangentSpace I x)] [rmN : IsRiemannianManifold I N]
  [cN : CompleteSpace N] [crN : IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)]
  {M : ℕ → Type} [mM : ∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
  [rbM : ∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [rmM : ∀ i, IsRiemannianManifold I (M i)] [cM : ∀ i, CompleteSpace (M i)]
  [crM : ∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]

/-- **LC61 at a fixed normalized scale, abstract core coordinate** (master207A, A:23460). With the
LC57 noncompact data at the normalized scale (LC50 maps, the model radial function `ζ`, the collar
field `V`, a proper coordinate `u` with `du(V) > 0` beyond `T₀`, selected source radial functions
`η i`), there is `T₁ > T₀` such that one tail has, for every `ρ ∈ [1/5, 2]` and `ρ' ∈ (T₀, T₁)`,
a diffeomorphism of the open ball `B(p_i, ρ)`, `p_i = j i n`, onto `int {u ≤ ρ'}`. -/
theorem eventually_open_ball_sublevel_type {m : ℕ} (hdim : Module.finrank ℝ E = m + 1)
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
    (η : ∀ i, M i → ℝ) (eη : ℕ → ℝ)
    (hη : ∀ᶠ i in atTop, eη i < 1 / 40 ∧ (∀ x, |η i x - dist (j i n) x| < eη i) ∧
      LipschitzWith ε (fun x => η i x - dist (j i n) x) ∧
      ∃ Wi : Set (M i), IsOpen Wi ∧
        (∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 → x ∈ Wi) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η i) Wi ∧
        ∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 →
          (1 - (ε : ℝ)) ^ 2 ≤ (gSeq i).inner x (gradientFun (I := I) (gSeq i) (η i) x)
            (gradientFun (I := I) (gSeq i) (η i) x)) :
    ∃ T₁ : ℝ, T₀ < T₁ ∧ ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∀ ρ' ∈ Ioo T₀ T₁,
      ∃ Ψ : PartialDiffeomorph I I (M i) N ∞,
        Ψ.source = Metric.ball (j i n) ρ ∧ Ψ.target = interior {x | u x ≤ ρ'} := by
  obtain ⟨T₁, hT₁, hK, hM⟩ := eventually_core_isotopies_of_point_distance_core g hNorm U n hbuffer
    hSeq gSeq hSeqNorm j hj hmetric hconv hεN hclose hlip hWζ hcollarW hζW V hVB hVdir hu hucpt
    hT₀ hWu hWuT huW hVW huV hε η eη hη
  have hD2 : {x | ζ x ≤ 1} ⊆ Metric.ball (n : N) 2 := fun x hx => by
    have h := abs_lt.mp (hclose x)
    change ζ x ≤ 1 at hx
    rw [Metric.mem_ball, dist_comm]
    linarith [h.1]
  have hDU : {x | ζ x ≤ 1} ⊆ U := fun x hx =>
    hbuffer (Metric.closedBall_subset_closedBall (by norm_num : (2 : ℝ) ≤ 10)
      (Metric.ball_subset_closedBall (hD2 hx)))
  refine ⟨T₁, hT₁, ?_⟩
  filter_upwards [hM, hη] with i hi hηi ρ hρ ρ' hρ'
  obtain ⟨heη, hclη, hlipη, Wi, hWi, hCWi, hηWi, hgradη⟩ := hηi
  obtain ⟨Hs, -, hHs⟩ := hi ρ hρ
  obtain ⟨K, -, hKD⟩ := hK ρ' hρ'
  obtain ⟨J, hJs, hJt, -⟩ := exists_open_distance_ball_diffeomorph hdim (gSeq i) (hSeqNorm i)
    (by linarith : (ε : ℝ) < 1 / 4) heη hclη hlipη hWi hCWi hηWi hgradη hρ
  let ι := openSubtypePartialDiffeomorph I U ⟨n⟩
  let Φ := ι.symm.trans (j i)
  have hDΦ : {x | ζ x ≤ 1} ⊆ Φ.source := by
    intro x hx
    rw [PartialDiffeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [PartialDiffeomorph.symm_source, openSubtypePartialDiffeomorph_target]
      exact hDU hx
    · rw [mem_preimage, hj i]
      exact mem_univ _
  have hΦD : Φ '' {x | ζ x ≤ 1} = (j i : U → M i) '' (Subtype.val ⁻¹' {x | ζ x ≤ 1}) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, hDU hx⟩, hx, ?_⟩
      change j i ⟨x, hDU hx⟩ = j i (ι.symm x)
      rw [openSubtypePartialDiffeomorph_symm_apply I U ⟨n⟩ (hDU hx)]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.1, hx, ?_⟩
      change j i (ι.symm x.1) = j i x
      rw [openSubtypePartialDiffeomorph_symm_apply I U ⟨n⟩ x.2]
  obtain ⟨Ψa, hΨas, hΨat, -⟩ := exists_partialDiffeomorph_interior_of_core_isotopies Φ hDΦ
    (Hs 1) (by rw [hΦD]; exact hHs) J hJs hJt (K 1) hKD
  refine ⟨Ψa.symm, ?_, ?_⟩
  · rw [PartialDiffeomorph.symm_source, hΨat]
  · rw [PartialDiffeomorph.symm_target, hΨas]

end DifferentialGeometry.Geometry.Collapse
