import DifferentialGeometry.Geometry.Collapse.SublevelCore.Defs

/-!
# A uniform model collar from strict point-directions (LC49)

Frozen blueprint master207A, lemma `lem:collapse-model-collar-margin` (LC49, lines 22462–22504).

Let `C₀` be a compact subset of `B(n, 3) ∖ {n}` and let `V` be a section of the tangent bundle that
is continuous on an open set `O ⊇ C₀`. If `g(V_q, v) < 0` for every `q ∈ C₀` and EVERY inward unit
minimizing direction `v ∈ 𝒰_n(q)`, then there are `α, B > 0` and an open neighbourhood `U` of `C₀`
whose closure is compact, lies in `(B(n, 3) ∖ {n}) ∩ O`, and on which `|V| ≤ B` and
`g(V, v) ≤ -2α` for every `v ∈ 𝒰_n(q)`.

The blueprint asks `V` to be smooth near `C₀`; only continuity on an open neighbourhood is used.
`C₀ = ∅` is allowed. The proof is the compact-neighbourhood packaging of the PC openness argument
`eventually_minimizing_inner_lt` (`Soul/SoulAngles.lean`): the unit tangent bundle over a compact
set is compact, the endpoint condition is closed, and the projection is proper.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
/-- Rescaling a continuous family of tangent vectors by a continuous scalar stays continuous in the
tangent bundle. -/
theorem continuous_tangent_smul
    {P : Type*} [TopologicalSpace P] {b : P → M}
    {v : (x : P) → TangentSpace I (b x)} {f : P → ℝ}
    (hv : Continuous (fun x => (⟨b x, v x⟩ : TangentBundle I M)))
    (hf : Continuous f) :
    Continuous (fun x => (⟨b x, f x • v x⟩ : TangentBundle I M)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hvc := (FiberBundle.continuousAt_totalSpace E _).mp (hv.continuousAt (x := x))
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hvc.1, ?_⟩
  let e := trivializationAt E (TangentSpace I) (b x)
  have he : ∀ᶠ y in 𝓝 x, b y ∈ e.baseSet :=
    hvc.1.preimage_mem_nhds (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E _ _))
  apply (hf.continuousAt.smul hvc.2).congr_of_eventuallyEq
  filter_upwards [he] with y hy
  exact (e.linear ℝ hy).map_smul (f y) (v y)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
/-- The `g`-inner product of two families of tangent vectors that are continuous on a set is
continuous on that set. -/
theorem continuousOn_metric_inner (g : SmoothRiemannianMetric I M)
    {P : Type*} [TopologicalSpace P] {s : Set P} {b : P → M}
    {v w : (x : P) → TangentSpace I (b x)}
    (hv : ContinuousOn (fun x => (⟨b x, v x⟩ : TangentBundle I M)) s)
    (hw : ContinuousOn (fun x => (⟨b x, w x⟩ : TangentBundle I M)) s) :
    ContinuousOn (fun x => g.inner (b x) (v x) (w x)) s := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  exact hv.inner_bundle hw

/-- In the unit tangent bundle, the inward minimizing condition toward `n` is closed. -/
theorem isClosed_inwardMinimizing_unitTangent (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (n : M) :
    IsClosed {z : MetricUnitTangent (I := I) g |
      intrinsicGeodesic (I := I) g hEnorm (MetricUnitTangent.base z) (MetricUnitTangent.vec z)
        (dist n (MetricUnitTangent.base z)) = n} := by
  let b : MetricUnitTangent (I := I) g → M := MetricUnitTangent.base
  let v : (z : MetricUnitTangent (I := I) g) → TangentSpace I (b z) := MetricUnitTangent.vec
  have hb : Continuous b :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_subtype_val
  have hv : Continuous (fun z => (⟨b z, v z⟩ : TangentBundle I M)) := continuous_subtype_val
  have hscale := continuous_tangent_smul (I := I) (f := fun z => dist n (b z)) hv
    (continuous_const.dist hb)
  have hend : Continuous (fun z => expMapIntrinsic (I := I) g hEnorm (b z)
      (dist n (b z) • v z)) := (intrinsicExp_smooth (I := I) g hEnorm).continuous.comp hscale
  have hset : {z : MetricUnitTangent (I := I) g |
      intrinsicGeodesic (I := I) g hEnorm (b z) (v z) (dist n (b z)) = n} =
      {z | expMapIntrinsic (I := I) g hEnorm (b z) (dist n (b z) • v z) = n} := by
    ext z
    simp only [mem_ofPred_eq, expMapIntrinsic_def, intrinsicGeodesic_smul]
  exact hset ▸ isClosed_eq hend continuous_const

/-- **LC49, any radius.** A strict pairing of `V` with every inward unit minimizing direction toward
`n`, along a compact `C₀ ⊆ B(n, R) ∖ {n}`, gives a uniform margin `-2α`, a norm bound `B` and an open
collar `U` with compact closure inside `(B(n, R) ∖ {n}) ∩ O`. -/
theorem exists_uniform_collar_of_strict_point_directions_of_radius
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (n : M) {R : ℝ} {C₀ O : Set M} (hC₀ : IsCompact C₀) (hC₀n : C₀ ⊆ ball n R \ {n})
    (hO : IsOpen O) (hC₀O : C₀ ⊆ O) (V : (y : M) → TangentSpace I y)
    (hV : ContinuousOn (fun y => (⟨y, V y⟩ : TangentBundle I M)) O)
    (hneg : ∀ q ∈ C₀, ∀ v ∈ inwardMinimizingDirections (I := I) g hEnorm n q,
      g.inner q (V q) v < 0) :
    ∃ α B : ℝ, 0 < α ∧ 0 < B ∧ ∃ U : Set M, IsOpen U ∧ C₀ ⊆ U ∧ IsCompact (closure U) ∧
      closure U ⊆ (ball n R \ {n}) ∩ O ∧
      ∀ q ∈ closure U, g.inner q (V q) (V q) ≤ B ^ 2 ∧
        ∀ v ∈ inwardMinimizingDirections (I := I) g hEnorm n q, g.inner q (V q) v ≤ -(2 * α) := by
  classical
  -- The open target set and a compact buffer `K = cthickening δ C₀` inside it.
  set W : Set M := (ball n R \ {n}) ∩ O with hWdef
  have hWopen : IsOpen W := (isOpen_ball.sdiff isClosed_singleton).inter hO
  have hC₀W : C₀ ⊆ W := fun q hq => ⟨hC₀n hq, hC₀O hq⟩
  obtain ⟨δ, hδ, hδW⟩ := hC₀.exists_cthickening_subset_open hWopen hC₀W
  set K : Set M := cthickening δ C₀ with hKdef
  have hKW : K ⊆ W := hδW
  have hKball : K ⊆ closedBall n R := fun q hq =>
    ball_subset_closedBall (hKW hq).1.1
  have hK : IsCompact K :=
    (soul_isCompact_closedBall (I := I) g hEnorm n R).of_isClosed_subset isClosed_cthickening hKball
  have hKO : K ⊆ O := fun q hq => (hKW hq).2
  -- The unit tangent bundle, the base map, and the compact set `P` of inward minimizing unit
  -- vectors over `K`.
  let b : MetricUnitTangent (I := I) g → M := MetricUnitTangent.base
  let v : (z : MetricUnitTangent (I := I) g) → TangentSpace I (b z) := MetricUnitTangent.vec
  have hb : Continuous b :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_subtype_val
  have hv : Continuous (fun z => (⟨b z, v z⟩ : TangentBundle I M)) := continuous_subtype_val
  set P : Set (MetricUnitTangent (I := I) g) :=
    {z | b z ∈ K} ∩ {z | intrinsicGeodesic (I := I) g hEnorm (b z) (v z) (dist n (b z)) = n}
    with hPdef
  have hP : IsCompact P :=
    (metricUnitOn_compact (I := I) g hK).inter_right
      (isClosed_inwardMinimizing_unitTangent (I := I) g hEnorm n)
  have hPclosed : IsClosed P := (isClosed_cthickening.preimage hb).inter
    (isClosed_inwardMinimizing_unitTangent (I := I) g hEnorm n)
  -- The pairing `f z = g(V, v)` is continuous on `b⁻¹ O ⊇ P`.
  let f : MetricUnitTangent (I := I) g → ℝ := fun z => g.inner (b z) (V (b z)) (v z)
  have hVb : ContinuousOn (fun z => (⟨b z, V (b z)⟩ : TangentBundle I M)) (b ⁻¹' O) :=
    hV.comp hb.continuousOn (fun _ hz => hz)
  have hf : ContinuousOn f (b ⁻¹' O) :=
    continuousOn_metric_inner (I := I) g hVb hv.continuousOn
  have hPO : P ⊆ b ⁻¹' O := fun z hz => hKO hz.1
  have hfP : ContinuousOn f P := hf.mono hPO
  -- A uniform strict margin `-4α` on the part of `P` over `C₀`.
  set P₀ : Set (MetricUnitTangent (I := I) g) := P ∩ {z | b z ∈ C₀} with hP₀def
  have hP₀ : IsCompact P₀ := hP.inter_right (hC₀.isClosed.preimage hb)
  have hfP₀neg : ∀ z ∈ P₀, f z < 0 := by
    intro z hz
    exact hneg (b z) hz.2 (v z) ⟨z.2, hz.1.2⟩
  obtain ⟨α, hα, hαP₀⟩ : ∃ α : ℝ, 0 < α ∧ ∀ z ∈ P₀, f z ≤ -(4 * α) := by
    rcases P₀.eq_empty_or_nonempty with hempty | hne
    · exact ⟨1, one_pos, fun z hz => by simp [hempty] at hz⟩
    · obtain ⟨z₀, hz₀, hmax⟩ := hP₀.exists_isMaxOn hne (hfP.mono inter_subset_left)
      refine ⟨-(f z₀) / 4, by linarith [hfP₀neg z₀ hz₀], fun z hz => ?_⟩
      have := hmax hz
      simp only [mem_ofPred_eq] at this
      linarith
  -- The compact bad set where the margin `-3α` fails, and its compact base image.
  set Bad : Set (MetricUnitTangent (I := I) g) := P ∩ f ⁻¹' Ici (-(3 * α)) with hBaddef
  have hBadClosed : IsClosed Bad := hfP.preimage_isClosed_of_isClosed hPclosed isClosed_Ici
  have hBad : IsCompact Bad := hP.of_isClosed_subset hBadClosed inter_subset_left
  have hBadImg : IsCompact (b '' Bad) := hBad.image hb
  have hC₀Bad : C₀ ⊆ (b '' Bad)ᶜ := by
    rintro q hq ⟨z, hz, rfl⟩
    have h4 := hαP₀ z ⟨hz.1, hq⟩
    have h3 : -(3 * α) ≤ f z := hz.2
    linarith
  -- The open set `G` and a thickening `U` of `C₀` with closure inside `G`.
  set G : Set M := thickening δ C₀ ∩ (b '' Bad)ᶜ with hGdef
  have hGopen : IsOpen G := isOpen_thickening.inter hBadImg.isClosed.isOpen_compl
  have hC₀G : C₀ ⊆ G := fun q hq => ⟨self_subset_thickening hδ C₀ hq, hC₀Bad hq⟩
  obtain ⟨δ', hδ', hδ'G⟩ := hC₀.exists_cthickening_subset_open hGopen hC₀G
  set U : Set M := thickening δ' C₀ with hUdef
  have hclU : closure U ⊆ G := (closure_thickening_subset_cthickening δ' C₀).trans hδ'G
  have hGK : G ⊆ K := fun q hq => thickening_subset_cthickening δ C₀ hq.1
  have hclUK : closure U ⊆ K := hclU.trans hGK
  -- A norm bound on `K`.
  have hnormK : ContinuousOn (fun q => g.inner q (V q) (V q)) K :=
    (continuousOn_metric_inner (I := I) (b := id) g hV hV).mono hKO
  obtain ⟨C, hC⟩ := hK.bddAbove_image hnormK
  set B : ℝ := max C 0 + 1 with hBdef
  have hB1 : 1 ≤ B := by simp only [hBdef]; linarith [le_max_right C 0]
  refine ⟨α, B, hα, by linarith, U, isOpen_thickening, self_subset_thickening hδ' C₀,
    hK.of_isClosed_subset isClosed_closure hclUK, fun q hq => hKW (hclUK hq), ?_⟩
  intro q hq
  refine ⟨?_, ?_⟩
  · have hle : g.inner q (V q) (V q) ≤ C := hC ⟨q, hclUK hq, rfl⟩
    have hB2 : B ≤ B ^ 2 := by nlinarith
    have : C < B := by simp only [hBdef]; linarith [le_max_left C 0]
    linarith
  · intro w hw
    by_contra hlt
    push Not at hlt
    let z : MetricUnitTangent (I := I) g := ⟨⟨q, w⟩, hw.1⟩
    have hzBad : z ∈ Bad := by
      refine ⟨⟨hclUK hq, hw.2⟩, ?_⟩
      change -(3 * α) ≤ g.inner q (V q) w
      linarith
    exact (hclU hq).2 ⟨z, hzBad, rfl⟩

/-- **LC49** (master207A 22462, verbatim radius `3`). A strict pairing of `V` with every inward unit
minimizing direction toward `n`, along a compact `C₀ ⊆ B(n, 3) ∖ {n}`, gives `α, B > 0` and an open
collar `U ⊇ C₀` whose closure is compact, lies in `(B(n, 3) ∖ {n}) ∩ O`, and carries `|V| ≤ B` and
`g(V, v) ≤ -2α` for every `v ∈ 𝒰_n(q)`. All constants are chosen from the model data alone. -/
theorem exists_uniform_collar_of_strict_point_directions
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (n : M) {C₀ O : Set M} (hC₀ : IsCompact C₀) (hC₀n : C₀ ⊆ ball n 3 \ {n})
    (hO : IsOpen O) (hC₀O : C₀ ⊆ O) (V : (y : M) → TangentSpace I y)
    (hV : ContinuousOn (fun y => (⟨y, V y⟩ : TangentBundle I M)) O)
    (hneg : ∀ q ∈ C₀, ∀ v ∈ inwardMinimizingDirections (I := I) g hEnorm n q,
      g.inner q (V q) v < 0) :
    ∃ α B : ℝ, 0 < α ∧ 0 < B ∧ ∃ U : Set M, IsOpen U ∧ C₀ ⊆ U ∧ IsCompact (closure U) ∧
      closure U ⊆ (ball n 3 \ {n}) ∩ O ∧
      ∀ q ∈ closure U, g.inner q (V q) (V q) ≤ B ^ 2 ∧
        ∀ v ∈ inwardMinimizingDirections (I := I) g hEnorm n q, g.inner q (V q) v ≤ -(2 * α) :=
  exists_uniform_collar_of_strict_point_directions_of_radius g hEnorm n hC₀ hC₀n hO hC₀O V hV hneg

end DifferentialGeometry.Geometry.Collapse
