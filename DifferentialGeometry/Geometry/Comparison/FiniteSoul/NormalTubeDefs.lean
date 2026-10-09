import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SliceOfOrderTangent
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelChart
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCoefficients
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.UniformInverse
import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# The normal set of a slice and the linear algebra of the normal tube (lane CMS3-FLOW, S3-TUBE, G1)

Design `docs/geometrization/chapter13/design-finite-soul-three-20261004.md` §0.6, §3 "S3-TUBE".

* `normalSetFinite g S` — the frozen definition (body verbatim from
  `build-logs/scratch/D-CMS3/FiniteSoulThreeInterfaces.lean` §1): the `g`-normal vectors of `S`, a
  subset of `TM` (the total space of `ν_g S`).
* `gramOpFinite B` (the Lax–Milgram operator `⟪gramOpFinite B v, w⟫ = B v w`) and its ring inverse
  `normalRaiseFinite B`: `B (normalRaiseFinite B w) e = ⟪w, e⟫` for coercive `B`; the raise is `C^m` in
  a `C^m` coercive family (`contDiffOn_normalRaiseFinite`).
* `slicePullbackFinite g c y` — the metric read in a partial diffeomorphism `c : M → E` (pullback along
  `c.symm`), `C^m` when `c` is `C^(m+1)` (`contDiffOn_slicePullbackFinite`) and coercive on `c.target`.
* `contMDiffAt_mk_mfderiv_apply` — `z ↦ ⟨f (φ z), df_{φ z} (a z)⟩ ∈ TM` is `C^m` when `f` is `C^(m+1)`.
* `exists_forall_mem_of_mem_nhds_zero` — tangent vectors with base near `s₀` and small `g`-length lie in
  any prescribed neighbourhood of `⟨s₀, 0⟩` in `TM`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteSoul

section Def

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The `g`-normal vectors of `S` (as a subset of `TM`): the total space of `ν_g S`. -/
def normalSetFinite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (S : Set M) :
    Set (TangentBundle I M) :=
  {v | v.proj ∈ S ∧ ∀ w ∈ sliceTangent I S v.proj, g.inner v.proj v.snd w = 0}

theorem mem_normalSetFinite {n : ℕ∞ω}
    {g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)} {S : Set M}
    {v : TangentBundle I M} :
    v ∈ normalSetFinite g S ↔
      v.proj ∈ S ∧ ∀ w ∈ sliceTangent I S v.proj, g.inner v.proj v.snd w = 0 :=
  Iff.rfl

/-- The zero vector at a point of `S` is normal. -/
theorem zero_mem_normalSetFinite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) {S : Set M} {s : M}
    (hs : s ∈ S) : (⟨s, 0⟩ : TangentBundle I M) ∈ normalSetFinite g S := by
  refine ⟨hs, fun w _ => ?_⟩
  change g.inner s 0 w = 0
  rw [map_zero]
  rfl

/-- Normal vectors are stable under scaling. -/
theorem smul_mem_normalSetFinite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) {S : Set M}
    {v : TangentBundle I M} (hv : v ∈ normalSetFinite g S) (t : ℝ) :
    (⟨v.proj, t • v.snd⟩ : TangentBundle I M) ∈ normalSetFinite g S := by
  refine ⟨hv.1, fun w hw => ?_⟩
  change g.inner v.proj (t • v.snd) w = 0
  rw [map_smul, smul_apply, hv.2 w hw, smul_zero]

omit [IsManifold I ∞ M] in
/-- Equality of tangent vectors from equality of base points and of (model) fibre coordinates. -/
theorem tangentBundle_mk_eq {x y : M} {v w : E} (h : x = y) (hvw : v = w) :
    (⟨x, v⟩ : TangentBundle I M) = ⟨y, w⟩ := by
  subst h
  subst hvw
  rfl

end Def

section Linear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Lax–Milgram operator of a bilinear form: `⟪gramOpFinite B v, w⟫ = B v w`. -/
def gramOpFinite (B : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) B

theorem inner_gramOpFinite (B : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    ⟪gramOpFinite B v, w⟫_ℝ = B v w :=
  InnerProductSpace.continuousLinearMapOfBilin_apply (𝕜 := ℝ) B v w

/-- `gramOpFinite` as a continuous linear map of the form. -/
def gramCLMFinite : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E) :=
  ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
    ((InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv :
      E ≃L[ℝ] (E →L[ℝ] ℝ)).symm.toContinuousLinearMap

theorem gramCLMFinite_apply (B : E →L[ℝ] E →L[ℝ] ℝ) : gramCLMFinite B = gramOpFinite B :=
  rfl

theorem isUnit_gramOpFinite {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : IsCoercive B) :
    IsUnit (gramOpFinite B) :=
  ⟨hB.continuousLinearEquivOfBilin.toUnit, rfl⟩

/-- The raise of a form: the inverse of its Lax–Milgram operator. -/
def normalRaiseFinite (B : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  Ring.inverse (gramOpFinite B)

theorem gramOpFinite_normalRaiseFinite {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : IsCoercive B) (w : E) :
    gramOpFinite B (normalRaiseFinite B w) = w := by
  obtain ⟨u, hu⟩ := isUnit_gramOpFinite hB
  have h : gramOpFinite B * normalRaiseFinite B = 1 := by
    rw [normalRaiseFinite, ← hu, Ring.inverse_unit, Units.mul_inv]
  exact congrArg (fun T : E →L[ℝ] E => T w) h

theorem normalRaiseFinite_gramOpFinite {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : IsCoercive B) (v : E) :
    normalRaiseFinite B (gramOpFinite B v) = v := by
  obtain ⟨u, hu⟩ := isUnit_gramOpFinite hB
  have h : normalRaiseFinite B * gramOpFinite B = 1 := by
    rw [normalRaiseFinite, ← hu, Ring.inverse_unit, Units.inv_mul]
  exact congrArg (fun T : E →L[ℝ] E => T v) h

/-- **The raise represents the inner product through the form.** -/
theorem apply_normalRaiseFinite {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : IsCoercive B) (w e : E) :
    B (normalRaiseFinite B w) e = ⟪w, e⟫_ℝ := by
  rw [← inner_gramOpFinite, gramOpFinite_normalRaiseFinite hB]

/-- The raise depends smoothly on a coercive family. -/
theorem contDiffOn_normalRaiseFinite {U : Set E} {m : WithTop ℕ∞}
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} (hBc : ContDiffOn ℝ m B U) (hco : ∀ y ∈ U, IsCoercive (B y)) :
    ContDiffOn ℝ m (fun y => normalRaiseFinite (B y)) U := by
  intro y hy
  have h1 : ContDiffOn ℝ m (fun y => gramOpFinite (B y)) U :=
    ((gramCLMFinite (E := E)).contDiff.comp_contDiffOn hBc :)
  obtain ⟨u, hu⟩ := isUnit_gramOpFinite (hco y hy)
  have h2 : ContDiffAt ℝ m Ring.inverse (gramOpFinite (B y)) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact h2.comp_contDiffWithinAt y (h1 y hy)

end Linear

section Push

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The differential of a `C^s` map `V → M`, as a section of `Hom(V, TM)` along the map, is `C^m`
(`m + 1 ≤ s`). -/
theorem contMDiffAt_mfderiv_section_tube [IsManifold I ∞ M] {m s : ℕ∞ω} {f : V → M} {y : V}
    (hf : ContMDiffAt 𝓘(ℝ, V) I s f y) (hms : m + 1 ≤ s) :
    ContMDiffAt 𝓘(ℝ, V) (I.prod 𝓘(ℝ, V →L[ℝ] E)) m
      (fun z => (⟨f z, mfderiv 𝓘(ℝ, V) I f z⟩ :
        TotalSpace (V →L[ℝ] E) (fun x => Bundle.Trivial M V x →L[ℝ] TangentSpace I x))) y := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨hf.of_le ((le_add_of_nonneg_right zero_le_one).trans hms), ?_⟩
  have hd := hf.mfderiv_const (m := m) hms
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with z
  ext v
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_def]
  rfl

/-- A section of the trivial bundle `M × V` along a `C^m` map is `C^m` when its fibre part is. -/
theorem contMDiffAt_trivial_section_tube {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {X : Type*} [TopologicalSpace X] [ChartedSpace G X] {m : ℕ∞ω} {b : X → M} {a : X → V} {x : X}
    (hb : ContMDiffAt J I m b x) (ha : ContMDiffAt J 𝓘(ℝ, V) m a x) :
    ContMDiffAt J (I.prod 𝓘(ℝ, V)) m
      (fun z => (TotalSpace.mk' V (E := Bundle.Trivial M V) (b z) (a z))) x := by
  rw [contMDiffAt_totalSpace]
  exact ⟨hb, ha⟩

/-- **Push-forward of a moving vector.** If `f : V → M` is `C^s` at `φ x` and `φ`, `a` are `C^m`
(`m + 1 ≤ s`), then `z ↦ ⟨f (φ z), df_{φ z} (a z)⟩ ∈ TM` is `C^m` at `x`. -/
theorem contMDiffAt_mk_mfderiv_apply [IsManifold I ∞ M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {X : Type*} [TopologicalSpace X] [ChartedSpace G X] {m s : ℕ∞ω} {f : V → M} {φ a : X → V}
    {x : X} (hf : ContMDiffAt 𝓘(ℝ, V) I s f (φ x)) (hms : m + 1 ≤ s)
    (hφ : ContMDiffAt J 𝓘(ℝ, V) m φ x) (ha : ContMDiffAt J 𝓘(ℝ, V) m a x) :
    ContMDiffAt J I.tangent m
      (fun z => (⟨f (φ z), mfderiv 𝓘(ℝ, V) I f (φ z) (a z)⟩ : TangentBundle I M)) x := by
  have h1 := (contMDiffAt_mfderiv_section_tube hf hms).comp x hφ
  have hfφ : ContMDiffAt J I m (fun z => f (φ z)) x :=
    (hf.of_le ((le_add_of_nonneg_right zero_le_one).trans hms)).comp x hφ
  have h2 := contMDiffAt_trivial_section_tube (V := V) hfφ ha
  exact ContMDiffAt.clm_bundle_apply (E₁ := Bundle.Trivial M V) (E₂ := TangentSpace I)
    (b := fun z => f (φ z)) h1 h2

end Push

section Pullback

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The metric read in a partial diffeomorphism `c : M → E`: `y ↦ (c.symm)^* g` at `y`. -/
def slicePullbackFinite {n k : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (c : PartialDiffeomorph I 𝓘(ℝ, E) M E k) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (g.inner (c.symm y) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (E := E) (F := E) (E' := E) (F' := E)
    (mfderiv 𝓘(ℝ, E) I c.symm y : E →L[ℝ] E) (mfderiv 𝓘(ℝ, E) I c.symm y : E →L[ℝ] E)

omit [FiniteDimensional ℝ E] in
theorem slicePullbackFinite_apply {n k : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (c : PartialDiffeomorph I 𝓘(ℝ, E) M E k) (y a b : E) :
    slicePullbackFinite g c y a b =
      g.inner (c.symm y) (mfderiv 𝓘(ℝ, E) I c.symm y a) (mfderiv 𝓘(ℝ, E) I c.symm y b) :=
  rfl

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_slicePullbackFinite {n k m : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (c : PartialDiffeomorph I 𝓘(ℝ, E) M E k) (hmn : m ≤ n) (hmk : m + 1 ≤ k) :
    ContDiffOn ℝ m (slicePullbackFinite g c) c.target :=
  g.contDiffOn_pullback_inner hmn hmk c.open_target c.symm.contMDiffOn

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- `dc ∘ dc⁻¹ = id` at a point of the target of a partial diffeomorphism of order `k ≠ 0`. -/
theorem mfderiv_apply_mfderiv_symm_tube {k : ℕ∞ω} (hk : k ≠ 0)
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} {y : E} (hy : y ∈ c.target) (a : E) :
    mfderiv I 𝓘(ℝ, E) c (c.symm y) (mfderiv 𝓘(ℝ, E) I c.symm y a) = a := by
  have hsy : c.symm y ∈ c.source := c.toPartialEquiv.map_target hy
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I c.symm y := c.symm.mdifferentiableAt hk hy
  have hcdiff : MDifferentiableAt I 𝓘(ℝ, E) c (c.symm y) := c.mdifferentiableAt hk hsy
  have hcomp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E => c (c.symm z)) y =
      (mfderiv I 𝓘(ℝ, E) c (c.symm y)).comp (mfderiv 𝓘(ℝ, E) I c.symm y) :=
    mfderiv_comp y hcdiff hsymm
  have heq : (fun z : E => c (c.symm z)) =ᶠ[𝓝 y] id := by
    filter_upwards [c.open_target.mem_nhds hy] with z hz
    exact c.toPartialEquiv.right_inv hz
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  exact (congrArg (fun L : E →L[ℝ] E => L a) hcomp).symm

/-- The pulled-back metric is coercive on the target. -/
theorem isCoercive_slicePullbackFinite {n k : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hk : k ≠ 0)
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} {y : E} (hy : y ∈ c.target) :
    IsCoercive (slicePullbackFinite g c y) := by
  apply ContinuousLinearMap.isCoercive_of_posDef
  intro v hv
  rw [slicePullbackFinite_apply]
  apply g.pos
  intro hzero
  apply hv
  have h := mfderiv_apply_mfderiv_symm_tube hk hy v
  rw [← h]
  exact (congrArg (mfderiv I 𝓘(ℝ, E) c (c.symm y)) hzero).trans (map_zero _)

end Pullback

section ZeroSection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Small vectors near a point are near its zero vector.** For a neighbourhood `O` of `⟨s₀, 0⟩` in
`TM` there is `δ > 0` such that every tangent vector based within `δ` of `s₀` with `g`-length
`< δ` lies in `O`. -/
theorem exists_forall_mem_of_mem_nhds_zero {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (s₀ : M)
    {O : Set (TangentBundle I M)} (hO : O ∈ 𝓝 (⟨s₀, 0⟩ : TangentBundle I M)) :
    ∃ δ > 0, ∀ v : TangentBundle I M, dist s₀ v.proj < δ →
      g.inner v.proj v.snd v.snd < δ ^ 2 → v ∈ O := by
  set p : TangentBundle I M := ⟨s₀, 0⟩ with hp
  set e := extChartAt I.tangent p with he
  set φ := extChartAt I s₀ with hφ
  have hep : e p = (φ s₀, (0 : E)) :=
    Bundle.ContMDiffRiemannianMetric.extChartAt_tangent_zero (I := I) s₀ (mem_chart_source H s₀)
  have h1 : e.symm ⁻¹' O ∈ 𝓝 (e p) := extChartAt_preimage_mem_nhds hO
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp h1
  set b := chartCoeffFinite g s₀ with hb
  obtain ⟨c, hc, hcoer⟩ := isCoercive_chartCoeffFinite g (mem_extChartAt_target (I := I) s₀)
  have hbc : ContinuousAt b (φ s₀) :=
    (contDiffOn_chartCoeffFinite g (m := 0) zero_le (by simp) s₀).continuousOn.continuousAt
      ((isOpen_extChartAt_target s₀).mem_nhds (mem_extChartAt_target s₀))
  obtain ⟨δ₂, hδ₂, hbδ⟩ := Metric.continuousAt_iff.mp hbc (c / 2) (by positivity)
  have hφc : ContinuousAt φ s₀ := continuousAt_extChartAt s₀
  have hsrc : (chartAt H s₀).source ∈ 𝓝 s₀ := (chartAt H s₀).open_source.mem_nhds
    (mem_chart_source H s₀)
  have hφball : φ ⁻¹' ball (φ s₀) (min η δ₂) ∈ 𝓝 s₀ :=
    hφc.preimage_mem_nhds (ball_mem_nhds _ (lt_min hη hδ₂))
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hsrc hφball)
  refine ⟨min δ₁ (η * Real.sqrt (c / 2)), lt_min hδ₁ (mul_pos hη (Real.sqrt_pos.mpr
    (by positivity))), fun v hv hvg => ?_⟩
  set x := v.proj with hx
  have hxmem : x ∈ ball s₀ δ₁ := by
    rw [mem_ball, dist_comm]
    exact lt_of_lt_of_le hv (min_le_left _ _)
  obtain ⟨hxc, hxφ⟩ := hδ₁sub hxmem
  have hxφ' : dist (φ x) (φ s₀) < min η δ₂ := hxφ
  set a : E := mfderiv I 𝓘(ℝ, E) (extChartAt I s₀) x v.snd with ha
  have hread : g.inner x v.snd v.snd = b (φ x) a a := inner_eq_chartCoeffFinite g hxc _ _
  have hBy : ‖b (φ x) - b (φ s₀)‖ < c / 2 := by
    rw [← dist_eq_norm]
    exact hbδ (lt_of_lt_of_le hxφ' (min_le_right _ _))
  have hlow : c / 2 * ‖a‖ * ‖a‖ ≤ g.inner x v.snd v.snd := by
    rw [hread]
    have h1 := hcoer a
    have h2 : |(b (φ x) - b (φ s₀)) a a| ≤ c / 2 * ‖a‖ * ‖a‖ := by
      calc _ ≤ ‖b (φ x) - b (φ s₀)‖ * ‖a‖ * ‖a‖ := by
            rw [← Real.norm_eq_abs]
            exact ContinuousLinearMap.le_opNorm₂ _ _ _
        _ ≤ c / 2 * ‖a‖ * ‖a‖ := by gcongr
    have h3 := neg_abs_le ((b (φ x) - b (φ s₀)) a a)
    simp only [sub_apply] at h2 h3
    nlinarith
  have hvg' : g.inner x v.snd v.snd < (η * Real.sqrt (c / 2)) ^ 2 :=
    lt_of_lt_of_le hvg (pow_le_pow_left₀ (le_min hδ₁.le (mul_pos hη (Real.sqrt_pos.mpr
      (by positivity))).le) (min_le_right _ _) 2)
  have hsq : (η * Real.sqrt (c / 2)) ^ 2 = η ^ 2 * (c / 2) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have haη : ‖a‖ < η := by
    rw [hsq] at hvg'
    have hc2 : 0 < c / 2 := by positivity
    have : ‖a‖ ^ 2 < η ^ 2 := by nlinarith [norm_nonneg a]
    exact lt_of_pow_lt_pow_left₀ 2 hη.le this
  have hev : e v = (φ x, a) :=
    Bundle.ContMDiffRiemannianMetric.extChartAt_tangent_mk (I := I) s₀ hxc v.snd
  have hvsrc : v ∈ e.source := by
    rw [he, extChartAt_source, TangentBundle.mem_chart_source_iff]
    exact hxc
  have hmem : e v ∈ ball (e p) η := by
    rw [hev, hep, mem_ball, Prod.dist_eq]
    refine max_lt (lt_of_lt_of_le hxφ' (min_le_left _ _)) ?_
    rw [dist_zero_right]
    exact haη
  have := hball hmem
  rwa [Set.mem_preimage, e.left_inv hvsrc] at this

end ZeroSection

end DifferentialGeometry.Geometry.FiniteSoul
