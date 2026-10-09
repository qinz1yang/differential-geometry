import DifferentialGeometry.Topology.Manifold.SubmersionOpenMap
import DifferentialGeometry.Topology.VectorBundle.DiscCoreTransport
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images

/-!
# Boundaries of the closed cores: regular levels, disc cores, ambient transport

Items (2) and (3) of review 43's checklist for the relative compact core packet of LFR49/LPA02:
the boundary of the actual sublevel is the level set, the outward field is strictly transverse to
it, and the ambient identification carries boundary onto boundary.

* `mem_closure_superlevel_of_mfderiv_ne_zero`, `frontier_sublevel_eq_level_of_regular`: on a
  boundaryless manifold, a continuous function that is `C¹` with nonzero differential at every
  point of the level `{f = c}` has `frontier {f ≤ c} = {f = c}` (open mapping of a submersion,
  `map_nhds_eq_of_mfderiv_surjective_at`).
* `mfderiv_ne_zero_of_gradFun_ne_zero`, `mfderiv_gradFun_pos`: a nonzero gradient is a nonzero
  differential, and the gradient is strictly transverse to the level, `df(∇f) = g(∇f, ∇f) > 0`.
* `frontier_discCore_eq`: the frontier of a disc core `{‖(D⁻¹ x).2‖ ≤ T}`, `T > 0`, is the level
  `{‖(D⁻¹ x).2‖ = T}` (radial rescaling in the fibres).
* `partialDiffeomorph_image_frontier_of_subset_source`: a partial diffeomorphism carries the frontier
  of a closed set inside its source onto the frontier of its (closed) image (adapter of the tree's
  `OpenPartialHomeomorph.image_frontier_of_subset_source`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

section Regular

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]

/-- **A regular point is a limit of strictly higher values.** -/
theorem mem_closure_superlevel_of_mfderiv_ne_zero {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f x) (hd : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    x ∈ closure {y | f x < f y} := by
  have hsurj : Surjective (mfderiv I 𝓘(ℝ, ℝ) f x) := by
    let L : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f x
    obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
      by_contra h
      push Not at h
      exact hd (ContinuousLinearMap.ext h)
    intro t
    refine ⟨((show ℝ from t) / L v) • v, ?_⟩
    change L (((show ℝ from t) / L v) • v) = t
    rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ _ hv
  have hmap := DifferentialGeometry.Topology.map_nhds_eq_of_mfderiv_surjective_at hf hsurj
  rw [mem_closure_iff_nhds]
  intro U hU
  have himg : f '' U ∈ 𝓝 (f x) := by
    rw [← hmap]
    exact image_mem_map hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp himg
  obtain ⟨y, hyU, hy⟩ := hball (show f x + ε / 2 ∈ Metric.ball (f x) ε by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [show f x + ε / 2 - f x = ε / 2 by ring, abs_of_pos (by positivity)]
    linarith)
  exact ⟨y, hyU, show f x < f y by rw [hy]; linarith⟩

/-- **The boundary of a regular sublevel is the level set.** -/
theorem frontier_sublevel_eq_level_of_regular {f : M → ℝ} (hfc : Continuous f) {c : ℝ}
    (hreg : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ, ℝ) 1 f x ∧ mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    frontier {x | f x ≤ c} = {x | f x = c} := by
  ext x
  rw [(isClosed_le hfc continuous_const).frontier_eq]
  constructor
  · rintro ⟨hx, hxi⟩
    refine le_antisymm hx (not_lt.mp fun hlt => hxi ?_)
    exact interior_mono (fun y (hy : f y < c) => le_of_lt hy)
      ((isOpen_lt hfc continuous_const).interior_eq ▸ hlt)
  · intro hx
    have hx' : f x = c := hx
    refine ⟨le_of_eq hx', fun hint => ?_⟩
    obtain ⟨hcd, hne⟩ := hreg x hx'
    have hcl := mem_closure_superlevel_of_mfderiv_ne_zero hcd hne
    rw [mem_closure_iff_nhds] at hcl
    obtain ⟨y, hy1, hy2⟩ := hcl _ (isOpen_interior.mem_nhds hint)
    have hyc : y ∈ {b | f b ≤ c} := interior_subset hy1
    have hyc' : f y ≤ c := hyc
    have hxy : f x < f y := hy2
    linarith

end Regular

section Gradient

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A nonzero gradient is a nonzero differential. -/
theorem mfderiv_ne_zero_of_gradFun_ne_zero (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (h : DifferentialGeometry.Geometry.Operator.gradFun (I := I) g f x ≠ 0) :
    mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 := fun hd =>
  h (DifferentialGeometry.Geometry.Operator.gradFun_eq_zero_of_mfderiv_eq_zero g f hd)

/-- **Strict transversality of the gradient.** `df(∇f) = g(∇f, ∇f) > 0` where `∇f ≠ 0`. -/
theorem mvfderiv_gradFun_pos (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (h : DifferentialGeometry.Geometry.Operator.gradFun (I := I) g f x ≠ 0) :
    0 < mvfderiv I f x (DifferentialGeometry.Geometry.Operator.gradFun (I := I) g f x) := by
  have h1 := DifferentialGeometry.Geometry.Operator.inner_gradFun (I := I) g f x
    (DifferentialGeometry.Geometry.Operator.gradFun (I := I) g f x)
  have h2 := g.pos x _ h
  rw [h1] at h2
  exact h2

end Gradient

section DiscCore

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

omit [NormedSpace ℝ F] [VectorBundle ℝ F V] in
/-- **The boundary of a disc core is its top level.** For `T > 0` and a homeomorphism (here the
carrier diffeomorphism) `D : TotalSpace F V ≃ N`, the frontier of `{‖(D⁻¹ x).2‖ ≤ T}` is
`{‖(D⁻¹ x).2‖ = T}`. -/
theorem frontier_discCore_eq (D : TotalSpace F V ≃ₜ N) (hu : Continuous fun x : N => ‖(D.symm x).2‖)
    {T : ℝ} (hT : 0 < T) :
    frontier {x : N | ‖(D.symm x).2‖ ≤ T} = {x : N | ‖(D.symm x).2‖ = T} := by
  ext x
  rw [(isClosed_le hu continuous_const).frontier_eq]
  constructor
  · rintro ⟨hx, hxi⟩
    refine le_antisymm hx (not_lt.mp fun hlt => hxi ?_)
    have hopen : IsOpen {y : N | ‖(D.symm y).2‖ < T} := isOpen_lt hu continuous_const
    exact interior_mono (fun y (hy : ‖(D.symm y).2‖ < T) => le_of_lt hy) (hopen.interior_eq ▸ hlt)
  · intro hx
    have hx' : ‖(D.symm x).2‖ = T := hx
    refine ⟨le_of_eq hx', fun hint => ?_⟩
    -- the radial curve `t ↦ D ⟨q, t v⟩` leaves the core for `t > 1`
    set z := D.symm x with hz
    have hcurve : Continuous fun t : ℝ => D (⟨z.proj, t • z.2⟩ : TotalSpace F V) :=
      D.continuous.comp ((FiberBundle.continuous_totalSpaceMk F V z.proj).comp
        (continuous_id.smul continuous_const))
    have h1 : D (⟨z.proj, (1 : ℝ) • z.2⟩ : TotalSpace F V) = x := by
      rw [one_smul]
      exact D.apply_symm_apply x
    have hmem : ∀ᶠ t in 𝓝 (1 : ℝ),
        D (⟨z.proj, t • z.2⟩ : TotalSpace F V) ∈ interior {y : N | ‖(D.symm y).2‖ ≤ T} :=
      hcurve.continuousAt.preimage_mem_nhds (h1 ▸ isOpen_interior.mem_nhds hint)
    obtain ⟨t, ht1, ht⟩ := hmem.exists_gt
    have hin := interior_subset ht
    change ‖(D.symm (D ⟨z.proj, t • z.2⟩)).2‖ ≤ T at hin
    rw [D.symm_apply_apply] at hin
    change ‖t • z.2‖ ≤ T at hin
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hx'] at hin
    nlinarith

end DiscCore

section Transport

variable {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H N]

/-- **Ambient transport of the boundary** (adapter of the tree's
`OpenPartialHomeomorph.image_frontier_of_subset_source` to partial diffeomorphisms). -/
theorem partialDiffeomorph_image_frontier_of_subset_source (Ψ : PartialDiffeomorph I I M N ∞)
    {A : Set M} (hA : IsClosed A) (hAs : A ⊆ Ψ.source) (hΨA : IsClosed (Ψ '' A)) :
    Ψ '' frontier A = frontier (Ψ '' A) :=
  Ψ.toOpenPartialHomeomorph.image_frontier_of_subset_source hAs hA hΨA

end Transport

end DifferentialGeometry.Geometry.Collapse
