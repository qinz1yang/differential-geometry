import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenBallCoreType
import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenBallDiffeomorph
import DifferentialGeometry.Geometry.Collapse.SublevelCore.CommonFieldCore
import DifferentialGeometry.Geometry.Collapse.SublevelCore.DirectionMargin

/-!
# LC57 (3) and the model side of LC48 for a finite model: the pulled-back core

Frozen blueprint master207A, LFR49 (A:29096), noncompact branch: "LC48's smooth common-field
isotopy then modifies the actual smooth comparison embedding to send this core to `A_1` … LC38
supplies all indicated sublevel types at once", and LC61 (A:23460): the open distance balls have
the smooth type of the model.

For a FINITE model the blueprint's model core `{ζ_R ≤ 1}` needs a finite LC30 on the model (and so
a finite LC27, concentration of the finite minimizing directions), which this tree does not have.
The kernel here avoids every model metric: the model core at index `i` and level `ρ` is the
pulled-back source sublevel `D = B̄(n, 3) ∩ (η_i ∘ j_i)⁻¹(-∞, ρ]`, so `j_i(D) = {η_i ≤ ρ}` and the
source isotopy of LC51/LC48 is the identity. The common field `V` of the model crosses `∂D`
strictly outward because its push-forward has LC44's source margins (`|dj V| ≤ B`, pairing `≤ -α`
with every source inward minimizing direction, `ε B < α`), so `d(η_i ∘ j_i)(V) ≥ α - ε B > 0`
(`sub_mul_le_mvfderiv_of_lipschitz_sub_dist`). LC47 (`exists_isotopy_of_common_outward_field`,
field `V`, height `u`) then moves `D` onto the constant-height core `{u ≤ ρ'}`; LC60 and the LC61
kernel give `B(j_i n, ρ) ≃ int {u ≤ ρ'}`.

`eventually_open_ball_core_type_of_pulled_core` is statement T3 of lane LFR49. The model is only a
proper metric space with a smooth structure; the margins of the push-forward are hypotheses (in
the finite application they come from B4, `eventually_pushforward_inner_le_of_finite_limit`).
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

/-- **LC57 (3) + LC48 model side, finite category, normalized scale.** The model `N` is any
proper smooth manifold with a distance (no model metric is used); `j i` are smooth comparison
maps with an eventual buffer, distortion `< 1/40` and coverage; the pushed model field `dj_i V`
has the LC44 source margins (`|dj V| ≤ B`, pairing `≤ -α` with every source inward minimizing
direction, `ε B < α`) over the model annulus `1/20 ≤ d_n ≤ 3`; `u` is a proper core coordinate,
smooth with `du(V) > 0` beyond `T₀`, `{u ≤ T₀} ⊆ B(n, 1/20)`. With LC30-type source radial
functions `η i`, there is `T₁ > T₀` such that one tail has, for every `ρ ∈ [1/5, 2]` and
`ρ' ∈ (T₀, T₁)`, a diffeomorphism of `B(j_i n, ρ)` onto `int {u ≤ ρ'}`. -/
theorem eventually_open_ball_core_type_of_pulled_core {m : ℕ}
    (hdim : Module.finrank ℝ E = m + 1)
    {N : Type} [mN : MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [pN : ProperSpace N]
    (gSeq : ∀ i, SmoothRiemannianMetric I (M i)) (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
    (n : N) (j : ∀ i, PartialDiffeomorph I I N (M i) ∞)
    (hsrc : ∀ᶠ i in atTop, Metric.closedBall n 4 ⊆ (j i).source)
    (hdist : ∀ᶠ i in atTop, ∀ x ∈ Metric.ball n 4, ∀ y ∈ Metric.ball n 4,
      |dist (j i x) (j i y) - dist x y| < 1 / 40)
    (hcov : ∀ᶠ i in atTop, Metric.ball (j i n) 3 ⊆ (j i : N → M i) '' Metric.ball n 4)
    (V : (x : N) → TangentSpace I x) {α B : ℝ} {ε : ℝ≥0} (hε : (ε : ℝ) < 1 / 32)
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
    (huV : ∀ x, T₀ ≤ u x → 0 < mvfderiv (I := I) u x (V x))
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
  -- the height bound of the model core region `B̄(n, 3)`
  obtain ⟨Tb, hTb⟩ : ∃ Tb : ℝ, ∀ x ∈ closedBall n 3, u x < Tb := by
    obtain ⟨c, hc⟩ := ((isCompact_closedBall n 3).image hu).isBounded.bddAbove
    exact ⟨c + 1, fun x hx => by linarith [hc (mem_image_of_mem u hx)]⟩
  set T₁ : ℝ := max Tb (T₀ + 1) with hT₁def
  have hT₀₁ : T₀ < T₁ := by linarith [le_max_right Tb (T₀ + 1)]
  refine ⟨T₁, hT₀₁, ?_⟩
  filter_upwards [hsrc, hdist, hcov, hpair, hη] with i hsrci hdisti hcovi hpairi hηi ρ hρ ρ' hρ'
  obtain ⟨heη, hclη, hlipη, Wi, hWi, hCWi, hηWi, hgradη⟩ := hηi
  have heη0 : 0 ≤ eη i := (abs_nonneg _).trans (hclη (j i n)).le
  have hηc : Continuous (η i) :=
    (hlipη.continuous.add (continuous_const.dist continuous_id)).congr
      (fun x => sub_add_cancel (η i x) (dist (j i n) x))
  have hn4 : n ∈ ball n 4 := mem_ball_self (by norm_num)
  have hb4 : ball n 4 ⊆ (j i).source := ball_subset_closedBall.trans hsrci
  have hb3 : closedBall n 3 ⊆ ball n 4 := closedBall_subset_ball (by norm_num)
  -- LC60: the open ball is the interior of the radial sublevel
  obtain ⟨J, hJs, hJt, -⟩ := exists_open_distance_ball_diffeomorph hdim (gSeq i) (hSeqNorm i)
    (by linarith : (ε : ℝ) < 1 / 4) heη hclη hlipη hWi hCWi hηWi hgradη hρ
  -- the pulled-back core
  set D : Set N := closedBall n 3 ∩ {x | η i (j i x) ≤ ρ} with hDdef
  have hDsrc : D ⊆ (j i).source := fun x hx => hb4 (hb3 hx.1)
  -- `η ∘ j ≤ ρ` near `n` forces `d(n, ·) < 3`
  have hsmall : ∀ x ∈ ball n 4, η i (j i x) ≤ ρ → dist x n < 3 := by
    intro x hx hxη
    have h1 := (abs_lt.mp (hdisti n hn4 x hx)).1
    have h2 := (abs_lt.mp (hclη (j i x))).1
    rw [dist_comm]
    linarith [hρ.2]
  have hjD : (j i : N → M i) '' D = {y | η i y ≤ ρ} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      have hy' : η i y ≤ ρ := hy
      have hyb : y ∈ ball (j i n) 3 := by
        rw [mem_ball, dist_comm]
        have := (abs_lt.mp (hclη y)).1
        linarith [hρ.2]
      obtain ⟨x, hx, rfl⟩ := hcovi hyb
      exact ⟨x, ⟨mem_closedBall.mpr (hsmall x hx hy').le, hy'⟩, rfl⟩
  have hηjc : ContinuousOn (fun x => η i (j i x)) (closedBall n 3) :=
    hηc.comp_continuousOn ((j i).contMDiffOn.continuousOn.mono fun x hx => hb4 (hb3 hx))
  have hDcl : IsClosed D := hηjc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Iic
  -- the open part `{η ∘ j < ρ}` of the core
  set O : Set N := ((j i).source ∩ ball n 4) ∩ (fun x => η i (j i x)) ⁻¹' Iio ρ with hOdef
  have hOo : IsOpen O :=
    (hηc.comp_continuousOn ((j i).contMDiffOn.continuousOn.mono inter_subset_left)).isOpen_inter_preimage
      ((j i).open_source.inter isOpen_ball) isOpen_Iio
  have hOD : O ⊆ D := fun x hx => by
    have hlt : η i (j i x) < ρ := hx.2
    exact ⟨mem_closedBall.mpr (hsmall x hx.1.2 hlt.le).le, show η i (j i x) ≤ ρ from hlt.le⟩
  -- LC47 hypotheses
  have hAD : {x | u x ≤ T₀} ⊆ interior D := by
    intro x hx
    have hxn : x ∈ ball n (1 / 20) := hT₀ hx
    have hx4 : x ∈ ball n 4 := ball_subset_ball (by norm_num) hxn
    refine interior_maximal hOD hOo ⟨⟨hb4 hx4, hx4⟩, ?_⟩
    have h1 := (abs_lt.mp (hdisti n hn4 x hx4)).2
    have h2 := (abs_lt.mp (hclη (j i x))).2
    have h3 : dist n x < 1 / 20 := by rw [dist_comm]; exact mem_ball.mp hxn
    change η i (j i x) < ρ
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
    -- the level of `q`
    have hqρ : η i (j i q) = ρ := by
      refine le_antisymm hqD.2 (not_lt.mp fun hlt => hq.2 ?_)
      exact interior_maximal hOD hOo ⟨⟨hqs, hq4⟩, hlt⟩
    have hcl := abs_lt.mp (hclη (j i q))
    have hdq := abs_lt.mp (hdisti n hn4 q hq4)
    have hlo : 1 / 10 ≤ dist (j i n) (j i q) := by linarith [hρ.1]
    have hhi : dist (j i n) (j i q) ≤ 10 := by linarith [hρ.2]
    have hjqW : j i q ∈ Wi := hCWi (j i q) hlo hhi
    -- the defining function
    refine ⟨((j i).source ∩ ball n 4) ∩ (j i : N → M i) ⁻¹' Wi,
      ((j i).contMDiffOn.continuousOn.mono inter_subset_left).isOpen_inter_preimage
        ((j i).open_source.inter isOpen_ball) hWi,
      ⟨⟨hqs, hq4⟩, hjqW⟩, fun x => η i (j i x) - ρ, ?_, ?_, ?_⟩
    · intro x hx
      have hjx : ContMDiffAt I I ∞ (j i : N → M i) x :=
        (j i).contMDiffOn.contMDiffAt ((j i).open_source.mem_nhds hx.1.1)
      have hηx : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (η i) (j i x) :=
        hηWi.contMDiffAt (hWi.mem_nhds hx.2)
      exact ((hηx.comp x hjx).sub contMDiffAt_const).contMDiffWithinAt
    · ext x
      constructor
      · rintro ⟨hxD, hxU⟩
        have hxρ : η i (j i x) ≤ ρ := hxD.2
        exact ⟨show η i (j i x) - ρ ≤ 0 from sub_nonpos.mpr hxρ, hxU⟩
      · rintro ⟨hxf, hxU⟩
        have hxρ : η i (j i x) ≤ ρ := sub_nonpos.mp (show η i (j i x) - ρ ≤ 0 from hxf)
        exact ⟨⟨mem_closedBall.mpr (hsmall x hxU.1.2 hxρ).le, hxρ⟩, hxU⟩
    · have hjd : MDifferentiableAt I I (j i : N → M i) q :=
        (j i).mdifferentiableAt (by simp) hqs
      have hηd : MDifferentiableAt I 𝓘(ℝ, ℝ) (η i) (j i q) :=
        (hηWi.contMDiffAt (hWi.mem_nhds hjqW)).mdifferentiableAt (by simp)
      have hcomp : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => η i (j i x)) q := hηd.comp q hjd
      have hsub : mvfderiv (I := I) (fun x => η i (j i x) - ρ) q (V q) =
          mvfderiv (I := I) (η i) (j i q) (mfderiv I I (j i : N → M i) q (V q)) := by
        have h1 : mvfderiv (I := I) (fun x => η i (j i x) - ρ) q =
            mvfderiv (I := I) (fun x => η i (j i x)) q -
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
  -- LC61 kernel
  have hA : (Diffeomorph.refl I (M i) ∞) '' ((j i : N → M i) '' D) = {y | η i y ≤ ρ} := by
    rw [hjD]
    exact image_id _
  obtain ⟨Ψ, hΨs, hΨt, -⟩ := exists_partialDiffeomorph_interior_of_core_isotopies (j i) hDsrc
    (Diffeomorph.refl I (M i) ∞) hA J hJs hJt (K 1) hK1
  exact ⟨Ψ.symm, by rw [PartialDiffeomorph.symm_source, hΨt],
    by rw [PartialDiffeomorph.symm_target, hΨs]⟩

end DifferentialGeometry.Geometry.Collapse
