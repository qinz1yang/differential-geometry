import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.PulledCoreType

/-!
# LC38, closed form, for a finite model: the source sublevel is a model core

Frozen blueprint master207A, LFR54 (A:29526) / LPA05 (A:30555): the identifications "apply to the
ACTUAL sublevels and include their boundary". `PulledCoreType` (statement T3 of lane LFR49) moves
the pulled-back source core `D = B̄(n, 3) ∩ (η_i ∘ j_i)⁻¹(-∞, ρ]` onto the constant-height core
`{u ≤ ρ'}` by LC47's isotopy `K`, and records only the OPEN-ball consequence. The closed sublevel is
already carried: `j_i '' D = {η_i ≤ ρ}` and `K 1 '' D = {u ≤ ρ'}`, so the ambient partial
diffeomorphism `j_i⁻¹ ≫ K 1 : M_i ⇀ N` sends the ACTUAL source sublevel `{η_i ≤ ρ}` (with its
boundary) onto the model core `{u ≤ ρ'}`.

`eventually_closed_core_of_pulled_core` states this for EVERY radial function satisfying the
LC30-type bounds on one tail (the function is quantified inside the tail, after the threshold
`T₁`), so it applies to radial functions chosen afterwards (LPA02's LC67 function). Only the
bounds used by the isotopy are assumed (closeness `< 1/40`, `ε`-Lipschitz error, smoothness on the
annulus `1/10 ≤ d ≤ 10`); the gradient bound of T3 is used only for its open-ball clause.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type} [mM : ∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
  [rbM : ∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [rmM : ∀ i, IsRiemannianManifold I (M i)] [cM : ∀ i, CompleteSpace (M i)]
  [crM : ∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]

/-- **LC38, closed form (finite model, normalized scale).** In the setting of
`eventually_open_ball_core_type_of_pulled_core` (smooth comparison maps `j_i` with buffer,
distortion `< 1/40` and coverage; the pushed field `dj_i V` with LC44's source margins; a proper
core coordinate `u` with `du(V) > 0` beyond `T₀` and `{u ≤ T₀} ⊆ B(n, 1/20)`): there is `T₁ > T₀`
such that one tail has, for EVERY radial function `η` with `|η - d(j_i n, ·)| < e_η < 1/40`,
`ε`-Lipschitz error and smooth near `{1/10 ≤ d(j_i n, ·) ≤ 10}`, every `ρ ∈ [1/5, 2]` and every
`ρ' ∈ (T₀, T₁)`, an ambient partial diffeomorphism `Ψ : M_i ⇀ N` whose source contains the actual
sublevel `{η ≤ ρ}` and maps it onto the model core `{u ≤ ρ'}`. -/
theorem eventually_closed_core_of_pulled_core
    {N : Type} [mN : MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [pN : ProperSpace N]
    (gSeq : ∀ i, SmoothRiemannianMetric I (M i)) (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
    (n : N) (j : ∀ i, PartialDiffeomorph I I N (M i) ∞)
    (hsrc : ∀ᶠ i in atTop, Metric.closedBall n 4 ⊆ (j i).source)
    (hdist : ∀ᶠ i in atTop, ∀ x ∈ Metric.ball n 4, ∀ y ∈ Metric.ball n 4,
      |dist (j i x) (j i y) - dist x y| < 1 / 40)
    (hcov : ∀ᶠ i in atTop, Metric.ball (j i n) 3 ⊆ (j i : N → M i) '' Metric.ball n 4)
    (V : (x : N) → TangentSpace I x) {α B : ℝ} {ε : ℝ≥0}
    (hεB : (ε : ℝ) * B < α)
    (hpair : ∀ᶠ i in atTop, ∀ x ∈ (j i).source, 1 / 20 ≤ dist n x → dist n x ≤ 3 →
      √((gSeq i).inner (j i x) (mfderiv I I (j i : N → M i) x (V x))
        (mfderiv I I (j i : N → M i) x (V x))) ≤ B ∧
      ∀ w ∈ inwardMinimizingDirections (I := I) (gSeq i) (hSeqNorm i) (j i n) (j i x),
        (gSeq i).inner (j i x) (mfderiv I I (j i : N → M i) x (V x)) w ≤ -α)
    {u : N → ℝ} (hu : Continuous u) (hucpt : ∀ T, IsCompact {x | u x ≤ T})
    {T₀ : ℝ} (hT₀ : {x | u x ≤ T₀} ⊆ Metric.ball n (1 / 20))
    {Wu : Set N} (hWu : IsOpen Wu) (hWuT : {x | T₀ ≤ u x} ⊆ Wu)
    (huW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ u Wu)
    (hVW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, V x⟩ : TangentBundle I N)) Wu)
    (huV : ∀ x, T₀ ≤ u x → 0 < mvfderiv (I := I) u x (V x)) :
    ∃ T₁ : ℝ, T₀ < T₁ ∧ ∀ᶠ i in atTop, ∀ (η : M i → ℝ) (eη : ℝ), eη < 1 / 40 →
      (∀ x, |η x - dist (j i n) x| < eη) →
      LipschitzWith ε (fun x => η x - dist (j i n) x) →
      (∃ Wi : Set (M i), IsOpen Wi ∧
        (∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 → x ∈ Wi) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η Wi) →
      ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∀ ρ' ∈ Ioo T₀ T₁,
        ∃ Ψ : PartialDiffeomorph I I (M i) N ∞,
          {y | η y ≤ ρ} ⊆ Ψ.source ∧ Ψ '' {y | η y ≤ ρ} = {x | u x ≤ ρ'} := by
  -- the height bound of the model core region `B̄(n, 3)`
  obtain ⟨Tb, hTb⟩ : ∃ Tb : ℝ, ∀ x ∈ closedBall n 3, u x < Tb := by
    obtain ⟨c, hc⟩ := ((isCompact_closedBall n 3).image hu).isBounded.bddAbove
    exact ⟨c + 1, fun x hx => by linarith [hc (mem_image_of_mem u hx)]⟩
  set T₁ : ℝ := max Tb (T₀ + 1) with hT₁def
  have hT₀₁ : T₀ < T₁ := by linarith [le_max_right Tb (T₀ + 1)]
  refine ⟨T₁, hT₀₁, ?_⟩
  filter_upwards [hsrc, hdist, hcov, hpair] with i hsrci hdisti hcovi hpairi η eη heη hclη hlipη
    hηW ρ hρ ρ' hρ'
  obtain ⟨Wi, hWi, hCWi, hηWi⟩ := hηW
  have hηc : Continuous η :=
    (hlipη.continuous.add (continuous_const.dist continuous_id)).congr
      (fun x => sub_add_cancel (η x) (dist (j i n) x))
  have hn4 : n ∈ ball n 4 := mem_ball_self (by norm_num)
  have hb4 : ball n 4 ⊆ (j i).source := ball_subset_closedBall.trans hsrci
  have hb3 : closedBall n 3 ⊆ ball n 4 := closedBall_subset_ball (by norm_num)
  -- the pulled-back core
  set D : Set N := closedBall n 3 ∩ {x | η (j i x) ≤ ρ} with hDdef
  have hDsrc : D ⊆ (j i).source := fun x hx => hb4 (hb3 hx.1)
  have hsmall : ∀ x ∈ ball n 4, η (j i x) ≤ ρ → dist x n < 3 := by
    intro x hx hxη
    have h1 := (abs_lt.mp (hdisti n hn4 x hx)).1
    have h2 := (abs_lt.mp (hclη (j i x))).1
    rw [dist_comm]
    linarith [hρ.2]
  have hjD : (j i : N → M i) '' D = {y | η y ≤ ρ} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      have hy' : η y ≤ ρ := hy
      have hyb : y ∈ ball (j i n) 3 := by
        rw [mem_ball, dist_comm]
        have := (abs_lt.mp (hclη y)).1
        linarith [hρ.2]
      obtain ⟨x, hx, rfl⟩ := hcovi hyb
      exact ⟨x, ⟨mem_closedBall.mpr (hsmall x hx hy').le, hy'⟩, rfl⟩
  have hηjc : ContinuousOn (fun x => η (j i x)) (closedBall n 3) :=
    hηc.comp_continuousOn ((j i).contMDiffOn.continuousOn.mono fun x hx => hb4 (hb3 hx))
  have hDcl : IsClosed D := hηjc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Iic
  -- the open part `{η ∘ j < ρ}` of the core
  set O : Set N := ((j i).source ∩ ball n 4) ∩ (fun x => η (j i x)) ⁻¹' Iio ρ with hOdef
  have hOo : IsOpen O :=
    (hηc.comp_continuousOn ((j i).contMDiffOn.continuousOn.mono inter_subset_left)).isOpen_inter_preimage
      ((j i).open_source.inter isOpen_ball) isOpen_Iio
  have hOD : O ⊆ D := fun x hx => by
    have hlt : η (j i x) < ρ := hx.2
    exact ⟨mem_closedBall.mpr (hsmall x hx.1.2 hlt.le).le, show η (j i x) ≤ ρ from hlt.le⟩
  -- LC47 hypotheses
  have hAD : {x | u x ≤ T₀} ⊆ interior D := by
    intro x hx
    have hxn : x ∈ ball n (1 / 20) := hT₀ hx
    have hx4 : x ∈ ball n 4 := ball_subset_ball (by norm_num) hxn
    refine interior_maximal hOD hOo ⟨⟨hb4 hx4, hx4⟩, ?_⟩
    have h1 := (abs_lt.mp (hdisti n hn4 x hx4)).2
    have h2 := (abs_lt.mp (hclη (j i x))).2
    have h3 : dist n x < 1 / 20 := by rw [dist_comm]; exact mem_ball.mp hxn
    change η (j i x) < ρ
    linarith [hρ.1]
  have hDb : D ⊆ {x | u x < T₁} := fun x hx =>
    lt_of_lt_of_le (hTb x hx.1) (le_max_left _ _)
  have hKc : IsCompact (u ⁻¹' Icc T₀ T₁) :=
    (hucpt T₁).of_isClosed_subset (isClosed_Icc.preimage hu) fun x hx => hx.2
  have hKW : u ⁻¹' Icc T₀ T₁ ⊆ Wu := fun x hx => hWuT hx.1
  have hpos : ∀ x ∈ u ⁻¹' Icc T₀ T₁, 0 < mvfderiv (I := I) u x (V x) := fun x hx => huV x hx.1
  have hdef : ∀ q ∈ frontier D, ∃ U : Set N, IsOpen U ∧ q ∈ U ∧ ∃ f : N → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U ∧ D ∩ U = {x | f x ≤ 0} ∩ U ∧
        0 < mvfderiv (I := I) f q (V q) := by
    intro q hq
    have hqD : q ∈ D := hDcl.frontier_subset hq
    have hq4 : q ∈ ball n 4 := hb3 hqD.1
    have hqs : q ∈ (j i).source := hb4 hq4
    have hqρ : η (j i q) = ρ := by
      refine le_antisymm hqD.2 (not_lt.mp fun hlt => hq.2 ?_)
      exact interior_maximal hOD hOo ⟨⟨hqs, hq4⟩, hlt⟩
    have hcl := abs_lt.mp (hclη (j i q))
    have hdq := abs_lt.mp (hdisti n hn4 q hq4)
    have hlo : 1 / 10 ≤ dist (j i n) (j i q) := by linarith [hρ.1]
    have hhi : dist (j i n) (j i q) ≤ 10 := by linarith [hρ.2]
    have hjqW : j i q ∈ Wi := hCWi (j i q) hlo hhi
    refine ⟨((j i).source ∩ ball n 4) ∩ (j i : N → M i) ⁻¹' Wi,
      ((j i).contMDiffOn.continuousOn.mono inter_subset_left).isOpen_inter_preimage
        ((j i).open_source.inter isOpen_ball) hWi,
      ⟨⟨hqs, hq4⟩, hjqW⟩, fun x => η (j i x) - ρ, ?_, ?_, ?_⟩
    · intro x hx
      have hjx : ContMDiffAt I I ∞ (j i : N → M i) x :=
        (j i).contMDiffOn.contMDiffAt ((j i).open_source.mem_nhds hx.1.1)
      have hηx : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ η (j i x) :=
        hηWi.contMDiffAt (hWi.mem_nhds hx.2)
      exact ((hηx.comp x hjx).sub contMDiffAt_const).contMDiffWithinAt
    · ext x
      constructor
      · rintro ⟨hxD, hxU⟩
        have hxρ : η (j i x) ≤ ρ := hxD.2
        exact ⟨show η (j i x) - ρ ≤ 0 from sub_nonpos.mpr hxρ, hxU⟩
      · rintro ⟨hxf, hxU⟩
        have hxρ : η (j i x) ≤ ρ := sub_nonpos.mp (show η (j i x) - ρ ≤ 0 from hxf)
        exact ⟨⟨mem_closedBall.mpr (hsmall x hxU.1.2 hxρ).le, hxρ⟩, hxU⟩
    · have hjd : MDifferentiableAt I I (j i : N → M i) q :=
        (j i).mdifferentiableAt (by simp) hqs
      have hηd : MDifferentiableAt I 𝓘(ℝ, ℝ) η (j i q) :=
        (hηWi.contMDiffAt (hWi.mem_nhds hjqW)).mdifferentiableAt (by simp)
      have hcomp : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => η (j i x)) q := hηd.comp q hjd
      have hsub : mvfderiv (I := I) (fun x => η (j i x) - ρ) q (V q) =
          mvfderiv (I := I) η (j i q) (mfderiv I I (j i : N → M i) q (V q)) := by
        have h1 : mvfderiv (I := I) (fun x => η (j i x) - ρ) q =
            mvfderiv (I := I) (fun x => η (j i x)) q -
              mvfderiv (I := I) (fun _ : N => ρ) q :=
          mvfderiv_fun_sub hcomp mdifferentiableAt_const
        rw [h1, mvfderiv_const, sub_zero]
        exact mvfderiv_comp_apply q hηd hjd (V q)
      rw [hsub]
      have hpq : j i n ≠ j i q := fun h => by
        rw [h, dist_self] at hlo
        norm_num at hlo
      have hann1 : 1 / 20 ≤ dist n q := by linarith [hρ.1]
      have hann2 : dist n q ≤ 3 := by linarith [hρ.2]
      obtain ⟨hZB, hdir⟩ := hpairi q hqs hann1 hann2
      have h := sub_mul_le_mvfderiv_of_lipschitz_sub_dist (I := I) (gSeq i) (hSeqNorm i) hpq
        hηd hlipη hZB hdir
      linarith
  -- LC47: the model isotopy onto the constant-height core
  obtain ⟨K, -, -, -, -, hK1⟩ := exists_isotopy_of_common_outward_field hu hWu huW
    (⟨hρ'.1, hρ'.2⟩ : ρ' ∈ Ioo T₀ T₁) hKc hKW V hVW hpos hDcl hAD hDb hdef
  -- the ambient map `j_i⁻¹ ≫ K 1`
  refine ⟨(j i).symm.trans (K 1).toPartialDiffeomorph, ?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source, PartialDiffeomorph.symm_source, ← hjD]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(j i).map_source (hDsrc hx), mem_univ _⟩
  · rw [← hjD, ← hK1, image_image]
    refine image_congr fun x hx => ?_
    change (K 1) ((j i).toPartialEquiv.symm ((j i).toPartialEquiv x)) = (K 1) x
    rw [(j i).toPartialEquiv.left_inv (hDsrc hx)]

end DifferentialGeometry.Geometry.Collapse
