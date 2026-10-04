import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelTransport
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SliceOfOrderTangent

/-!
# Parallel fields stay tangent to totally geodesic slices: S3-PT.b (lane CMS3-PT, group G3)

In a slice chart `c` of order `k ≥ 2` (carrying `Z` onto an affine subspace `A`), the metric has
coefficients `sliceCoeffFinite g c` of class `C¹` and Christoffel operator `sliceChristoffelFinite g c`.
* the parallel ODE transfers from an extended chart to the slice chart (`hasDerivWithinAt_sliceRep`);
* total geodesy gives `Q Γ(u, w) = 0` for `u, w ∈ A.direction`, `Q` a projection with kernel
  `A.direction` (`projection_sliceChristoffelFinite_eq_zero`; diagonal from `x_⊥'' = 0`, then polarization);
* the `Q`-part of a parallel field solves a homogeneous linear ODE, so it vanishes identically once it
  vanishes once (Grönwall), and connectedness gives the frozen S3-PT.b
  `isParallel_mem_sliceTangent_of_totallyGeodesic`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.MetricKoszul (raisedKoszulOp)

section SliceChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {k : WithTop ℕ∞}

local instance continuousDualEquivPTs : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroupPTs : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpacePTs : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

omit [I.Boundaryless] in
/-- Coefficients of `g` in a partial diffeomorphism `c : M → E` (pullback along `c⁻¹`). -/
def sliceCoeffFinite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (c : PartialDiffeomorph I 𝓘(ℝ, E) M E k) (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (g.inner (c.symm z) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (E := E) (F := E) (E' := E) (F' := E)
    (mfderiv 𝓘(ℝ, E) I c.symm z : E →L[ℝ] E) (mfderiv 𝓘(ℝ, E) I c.symm z : E →L[ℝ] E)

omit [I.Boundaryless] in
/-- Christoffel operator of `g` in the partial diffeomorphism `c`. -/
def sliceChristoffelFinite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (c : PartialDiffeomorph I 𝓘(ℝ, E) M E k) (z : E) : E →L[ℝ] E →L[ℝ] E :=
  raisedKoszulOp (sliceCoeffFinite g c z) (fderiv ℝ (sliceCoeffFinite g c) z)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
/-- `dc ∘ d(c⁻¹) = id` on the target of a partial diffeomorphism of order `k ≠ 0`. -/
theorem mfderiv_apply_mfderiv_symm_ofOrder (hk : k ≠ 0)
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} {z : E} (hz : z ∈ c.target) (w : E) :
    (mfderiv I 𝓘(ℝ, E) c (c.symm z) (mfderiv 𝓘(ℝ, E) I c.symm z w) : E) = w := by
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I c.symm z := c.symm.mdifferentiableAt hk hz
  have hcd : MDifferentiableAt I 𝓘(ℝ, E) c (c.symm z) :=
    c.mdifferentiableAt hk (c.toPartialEquiv.map_target hz)
  have hcomp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y : E => c (c.symm y)) z =
      (mfderiv I 𝓘(ℝ, E) c (c.symm z)).comp (mfderiv 𝓘(ℝ, E) I c.symm z) :=
    mfderiv_comp z hcd hsymm
  have heq : (fun y : E => c (c.symm y)) =ᶠ[𝓝 z] id := by
    filter_upwards [c.open_target.mem_nhds hz] with y hy
    exact c.toPartialEquiv.right_inv hy
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  exact congrArg (fun L : E →L[ℝ] E => L w) hcomp.symm

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
/-- `dc_x ∘ d(c⁻¹)_{c x} = id` at a point of the source. -/
theorem mfderiv_apply_mfderiv_symm_of_mem_source_ofOrder (hk : k ≠ 0)
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} {x : M} (hx : x ∈ c.source) (w : E) :
    (mfderiv I 𝓘(ℝ, E) c x (mfderiv 𝓘(ℝ, E) I c.symm (c x) w) : E) = w := by
  have h := mfderiv_apply_mfderiv_symm_ofOrder hk (c.toPartialEquiv.map_source hx) w
  have hl : c.symm (c x) = x := c.toPartialEquiv.left_inv hx
  have hL : (mfderiv I 𝓘(ℝ, E) c (c.symm (c x)) : E →L[ℝ] E) =
      (mfderiv I 𝓘(ℝ, E) c x : E →L[ℝ] E) := by rw [hl]
  exact (congrArg (fun L : E →L[ℝ] E => L (mfderiv 𝓘(ℝ, E) I c.symm (c x) w)) hL).symm.trans h

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The metric read in the partial diffeomorphism `c`. -/
theorem inner_eq_sliceCoeffFinite (hk : k ≠ 0) {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} {x : M} (hx : x ∈ c.source) (v w : E) :
    g.inner x v w = sliceCoeffFinite g c (c x) (mfderiv I 𝓘(ℝ, E) c x v)
      (mfderiv I 𝓘(ℝ, E) c x w) := by
  have hl : c.symm (c x) = x := c.toPartialEquiv.left_inv hx
  change g.inner x v w = g.inner (c.symm (c x))
    (mfderiv 𝓘(ℝ, E) I c.symm (c x) (mfderiv I 𝓘(ℝ, E) c x v))
    (mfderiv 𝓘(ℝ, E) I c.symm (c x) (mfderiv I 𝓘(ℝ, E) c x w))
  rw [mfderiv_symm_apply_mfderiv_ofOrder hk hx v, mfderiv_symm_apply_mfderiv_ofOrder hk hx w, hl]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem sliceCoeffFinite_symm {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (c : PartialDiffeomorph I 𝓘(ℝ, E) M E k) (z u v : E) :
    sliceCoeffFinite g c z u v = sliceCoeffFinite g c z v u := by
  change g.inner (c.symm z) (mfderiv 𝓘(ℝ, E) I c.symm z u) (mfderiv 𝓘(ℝ, E) I c.symm z v) =
    g.inner (c.symm z) (mfderiv 𝓘(ℝ, E) I c.symm z v) (mfderiv 𝓘(ℝ, E) I c.symm z u)
  exact g.symm _ _ _

omit [I.Boundaryless] in
theorem isCoercive_sliceCoeffFinite (hk : k ≠ 0) {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} {z : E} (hz : z ∈ c.target) :
    IsCoercive (sliceCoeffFinite g c z) := by
  apply ContinuousLinearMap.isCoercive_of_posDef
  intro v hv
  change 0 < g.inner (c.symm z) (mfderiv 𝓘(ℝ, E) I c.symm z v) (mfderiv 𝓘(ℝ, E) I c.symm z v)
  apply g.pos
  intro hzero
  apply hv
  have h := mfderiv_apply_mfderiv_symm_ofOrder hk hz v
  rw [← h]
  exact (congrArg (mfderiv I 𝓘(ℝ, E) c (c.symm z)) hzero).trans (map_zero _)

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem contDiffOn_sliceCoeffFinite {n m : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hmn : m ≤ n)
    (hmk : m + 1 ≤ k) (c : PartialDiffeomorph I 𝓘(ℝ, E) M E k) :
    ContDiffOn ℝ m (sliceCoeffFinite g c) c.target :=
  g.contDiffOn_pullback_inner hmn hmk c.open_target c.contMDiffOn_invFun

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem isOpen_sliceTransition_source (q : M) (c : PartialDiffeomorph I 𝓘(ℝ, E) M E k) :
    IsOpen ((extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' c.source) :=
  (continuousOn_extChartAt_symm q).isOpen_inter_preimage (isOpen_extChartAt_target q) c.open_source

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem contDiffOn_sliceTransition (hk : 2 ≤ k) (q : M)
    (c : PartialDiffeomorph I 𝓘(ℝ, E) M E k) :
    ContDiffOn ℝ 2 (c ∘ (extChartAt I q).symm)
      ((extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' c.source) := by
  have h1 := (c.contMDiffOn_toFun.of_le hk).comp
    ((contMDiffOn_extChartAt_symm (n := 2) q).mono inter_subset_left)
    (fun z hz => hz.2)
  exact contMDiffOn_iff_contDiffOn.mp h1

omit [FiniteDimensional ℝ E] in
theorem fderiv_sliceTransition_apply (hk : k ≠ 0) {q : M}
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} {z : E}
    (hz : z ∈ (extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' c.source) (w : E) :
    fderiv ℝ (c ∘ (extChartAt I q).symm) z w =
      (mfderiv I 𝓘(ℝ, E) c ((extChartAt I q).symm z)
        (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm z w) : E) := by
  have hcd : MDifferentiableAt I 𝓘(ℝ, E) c ((extChartAt I q).symm z) := c.mdifferentiableAt hk hz.2
  have hsd : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I q).symm z :=
    (DifferentialGeometry.PartialDiffeomorph.extChartAt I ∞ q).symm.mdifferentiableAt (by simp)
      hz.1
  have hcomp := mfderiv_comp z hcd hsd
  rw [mfderiv_eq_fderiv] at hcomp
  exact congrArg (fun L : E →L[ℝ] E => L w) hcomp

omit [FiniteDimensional ℝ E] in
theorem mfderiv_eq_fderiv_sliceTransition (hk : 2 ≤ k) {q x : M}
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} (hxq : x ∈ (chartAt H q).source)
    (hxc : x ∈ c.source) (v : E) :
    (mfderiv I 𝓘(ℝ, E) c x v : E) = fderiv ℝ (c ∘ (extChartAt I q).symm) (extChartAt I q x)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I q) x v) := by
  have hxsrc : x ∈ (extChartAt I q).source := by rwa [extChartAt_source]
  have hmem : extChartAt I q x ∈ (extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' c.source :=
    ⟨(extChartAt I q).map_source hxsrc, by
      change (extChartAt I q).symm (extChartAt I q x) ∈ c.source
      rw [(extChartAt I q).left_inv hxsrc]; exact hxc⟩
  have hT : DifferentiableAt ℝ (c ∘ (extChartAt I q).symm) (extChartAt I q x) :=
    ((contDiffOn_sliceTransition hk q c).contDiffAt
      ((isOpen_sliceTransition_source q c).mem_nhds hmem)).differentiableAt (by norm_num)
  have heq : ((c ∘ (extChartAt I q).symm) ∘ extChartAt I q) =ᶠ[𝓝 x] c := by
    filter_upwards [(isOpen_extChartAt_source (I := I) q).mem_nhds hxsrc] with y hy
    exact congrArg c ((extChartAt I q).left_inv hy)
  have hcomp := mfderiv_comp x hT.mdifferentiableAt (mdifferentiableAt_extChartAt (I := I) hxq)
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at hcomp
  exact congrArg (fun L : TangentSpace I x →L[ℝ] E => L v) hcomp

omit [FiniteDimensional ℝ E] in
theorem isInvertible_fderiv_sliceTransition (hk : k ≠ 0) {q : M}
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} {z : E}
    (hz : z ∈ (extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' c.source) :
    (fderiv ℝ (c ∘ (extChartAt I q).symm) z).IsInvertible := by
  let A : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) c ((extChartAt I q).symm z)
  let B : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm z
  have hA : A.IsInvertible := (c.isLocalDiffeomorphAt _ _ _ hz.2).isInvertible_mfderiv hk
  have hB : B.IsInvertible := by
    have h1 := isInvertible_mfderivWithin_extChartAt_symm (I := I) hz.1
    rw [I.range_eq_univ, mfderivWithin_univ] at h1
    exact h1
  have heq : fderiv ℝ (c ∘ (extChartAt I q).symm) z = A.comp B :=
    ContinuousLinearMap.ext fun w => fderiv_sliceTransition_apply hk hz w
  rw [heq]
  exact hA.comp hB

omit [FiniteDimensional ℝ E] in
theorem chartCoeffFinite_sliceTransition (hk : k ≠ 0) {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) {q : M}
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} {z : E}
    (hz : z ∈ (extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' c.source) (u v : E) :
    chartCoeffFinite g q z u v = sliceCoeffFinite g c ((c ∘ (extChartAt I q).symm) z)
      (fderiv ℝ (c ∘ (extChartAt I q).symm) z u) (fderiv ℝ (c ∘ (extChartAt I q).symm) z v) := by
  rw [fderiv_sliceTransition_apply hk hz, fderiv_sliceTransition_apply hk hz]
  calc chartCoeffFinite g q z u v
      = g.inner ((extChartAt I q).symm z) (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm z u)
          (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm z v) := rfl
    _ = _ := inner_eq_sliceCoeffFinite hk g hz.2 _ _

end SliceChart


section SliceGeodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {k : WithTop ℕ∞} {r : ℕ∞}

local instance continuousDualEquivPTsg : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroupPTsg : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpacePTsg : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- **Transfer of the parallel ODE to a slice chart** (order `k ≥ 2`): if the chart representative in
the extended chart at `q` solves the parallel ODE at `t`, the slice-chart representative
`τ ↦ dc (V τ)` solves `Y' = −Γ_c(c(γ t))(dc γ'(t), Y)`. -/
theorem hasDerivWithinAt_sliceRep (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hk : 2 ≤ k) {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain)
    {V : ℝ → E} {s : Set ℝ} {t : ℝ} {q : M} {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k}
    (hq : (g.geodesicFlow p t).proj ∈ (chartAt H q).source)
    (hc : (g.geodesicFlow p t).proj ∈ c.source)
    (h : HasDerivWithinAt (chartRepFinite g p q V)
      (parallelCoeffFinite g p q t (chartRepFinite g p q V t)) s t) :
    HasDerivWithinAt (fun τ => (mfderiv I 𝓘(ℝ, E) c (g.geodesicFlow p τ).proj (V τ) : E))
      (-(sliceChristoffelFinite g c (c (g.geodesicFlow p t).proj)
        (mfderiv I 𝓘(ℝ, E) c (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd)
        (mfderiv I 𝓘(ℝ, E) c (g.geodesicFlow p t).proj (V t)))) s t := by
  have hk0 : k ≠ 0 := by
    intro h0; rw [h0] at hk; exact absurd hk (by norm_num)
  have hcont : Continuous fun σ => (g.geodesicFlow p σ).proj :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
      (continuous_geodesicFlow_of_forall_mem hr g hdom)
  set Φ : E → E := c ∘ (extChartAt I q).symm with hΦ
  have hev : ∀ᶠ τ in 𝓝 t, (g.geodesicFlow p τ).proj ∈ (chartAt H q).source ∧
      (g.geodesicFlow p τ).proj ∈ c.source :=
    (hcont.continuousAt.eventually ((chartAt H q).open_source.mem_nhds hq)).and
      (hcont.continuousAt.eventually (c.open_source.mem_nhds hc))
  have hY : ∀ τ, (g.geodesicFlow p τ).proj ∈ (chartAt H q).source →
      (g.geodesicFlow p τ).proj ∈ c.source →
      (mfderiv I 𝓘(ℝ, E) c (g.geodesicFlow p τ).proj (V τ) : E) =
        fderiv ℝ Φ (extChartAt I q (g.geodesicFlow p τ).proj) (chartRepFinite g p q V τ) := by
    intro τ hτq hτc
    rw [chartRepFinite_eq_mfderiv g p V hτq]
    exact mfderiv_eq_fderiv_sliceTransition hk hτq hτc (V τ)
  have hxsrc : (g.geodesicFlow p t).proj ∈ (extChartAt I q).source := by rwa [extChartAt_source]
  have hmem : extChartAt I q (g.geodesicFlow p t).proj ∈
      (extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' c.source :=
    ⟨(extChartAt I q).map_source hxsrc, by
      change (extChartAt I q).symm (extChartAt I q (g.geodesicFlow p t).proj) ∈ c.source
      rw [(extChartAt I q).left_inv hxsrc]; exact hc⟩
  have hmaps : MapsTo Φ ((extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' c.source) c.target :=
    fun z hz => c.toPartialEquiv.map_source hz.2
  have key := hasDerivWithinAt_fderiv_apply_of_pullback (isOpen_sliceTransition_source q c)
    c.open_target (b := chartCoeffFinite g q) (c := sliceCoeffFinite g c) (Φ := Φ)
    (contDiffOn_sliceCoeffFinite g (m := 1) (by exact_mod_cast le_add_self)
      (by rw [one_add_one_eq_two]; exact hk) c)
    (fun z _ u v => sliceCoeffFinite_symm g c z u v)
    (fun z hz => isCoercive_sliceCoeffFinite hk0 g hz) (contDiffOn_sliceTransition hk q c) hmaps
    (fun z hz => isInvertible_fderiv_sliceTransition hk0 hz)
    (fun z hz u v => chartCoeffFinite_sliceTransition hk0 g hz u v)
    (x := fun τ => extChartAt I q (g.geodesicFlow p τ).proj) hmem
    (hasDerivAt_extChartAt_geodesicFlow hr g (hdom t) hq) h
  have e1 : Φ (extChartAt I q (g.geodesicFlow p t).proj) = c (g.geodesicFlow p t).proj :=
    congrArg c ((extChartAt I q).left_inv hxsrc)
  have e2 : fderiv ℝ Φ (extChartAt I q (g.geodesicFlow p t).proj)
      (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).2 =
      (mfderiv I 𝓘(ℝ, E) c (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd : E) := by
    rw [extChartAt_tangent_geodesicFlow_snd_eq g p t hq]
    exact (mfderiv_eq_fderiv_sliceTransition hk hq hc _).symm
  have e3 := (hY t hq hc).symm
  rw [e2, e3, e1] at key
  refine key.congr_of_eventuallyEq ?_ (hY t hq hc)
  filter_upwards [nhdsWithin_le_nhds hev] with τ hτ
  exact hY τ hτ.1 hτ.2

/-- The geodesic read in a slice chart has derivative its slice-chart velocity. -/
theorem hasDerivAt_slice_geodesicFlow_proj (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hk : 2 ≤ k) {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {t : ℝ}
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} (hc : (g.geodesicFlow p t).proj ∈ c.source) :
    HasDerivAt (fun τ => c (g.geodesicFlow p τ).proj)
      (mfderiv I 𝓘(ℝ, E) c (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd) t := by
  have hcont : Continuous fun σ => (g.geodesicFlow p σ).proj :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
      (continuous_geodesicFlow_of_forall_mem hr g hdom)
  obtain ⟨q, hq⟩ : ∃ q : M, (g.geodesicFlow p t).proj ∈ (chartAt H q).source :=
    ⟨_, mem_chart_source H _⟩
  have hxsrc : (g.geodesicFlow p t).proj ∈ (extChartAt I q).source := by rwa [extChartAt_source]
  have hmem : extChartAt I q (g.geodesicFlow p t).proj ∈
      (extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' c.source :=
    ⟨(extChartAt I q).map_source hxsrc, by
      change (extChartAt I q).symm (extChartAt I q (g.geodesicFlow p t).proj) ∈ c.source
      rw [(extChartAt I q).left_inv hxsrc]; exact hc⟩
  have hT : DifferentiableAt ℝ (c ∘ (extChartAt I q).symm)
      (extChartAt I q (g.geodesicFlow p t).proj) :=
    ((contDiffOn_sliceTransition hk q c).contDiffAt
      ((isOpen_sliceTransition_source q c).mem_nhds hmem)).differentiableAt (by norm_num)
  have h1 := hT.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_extChartAt_geodesicFlow hr g (hdom t) hq)
  have hvel : fderiv ℝ (c ∘ (extChartAt I q).symm) (extChartAt I q (g.geodesicFlow p t).proj)
      (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (g.geodesicFlow p t)).2 =
      (mfderiv I 𝓘(ℝ, E) c (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd : E) := by
    rw [extChartAt_tangent_geodesicFlow_snd_eq g p t hq]
    exact (mfderiv_eq_fderiv_sliceTransition hk hq hc _).symm
  refine (h1.congr_deriv hvel).congr_of_eventuallyEq ?_
  filter_upwards [hcont.continuousAt.eventually ((chartAt H q).open_source.mem_nhds hq)] with τ hτ
  exact congrArg c ((extChartAt I q).left_inv (by rwa [extChartAt_source])).symm

/-- The slice-chart velocity of a geodesic solves the geodesic equation of the slice chart. -/
theorem hasDerivAt_slice_geodesicFlow_vel (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hk : 2 ≤ k) {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {t : ℝ}
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} (hc : (g.geodesicFlow p t).proj ∈ c.source) :
    HasDerivAt (fun τ => (mfderiv I 𝓘(ℝ, E) c (g.geodesicFlow p τ).proj
        (g.geodesicFlow p τ).snd : E))
      (-(sliceChristoffelFinite g c (c (g.geodesicFlow p t).proj)
        (mfderiv I 𝓘(ℝ, E) c (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd)
        (mfderiv I 𝓘(ℝ, E) c (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd))) t := by
  have hq : (g.geodesicFlow p t).proj ∈ (chartAt H (g.geodesicFlow p t).proj).source :=
    mem_chart_source H _
  exact hasDerivWithinAt_univ.mp (hasDerivWithinAt_sliceRep hr g hk hdom
    (V := fun σ => ((g.geodesicFlow p σ).snd : E)) (s := univ) hq hc
    (hasDerivAt_extChartAt_tangent_geodesicFlow hr g (hdom t) hq).hasDerivWithinAt)

/-- Continuity of the slice-chart representative of a field continuous along the geodesic. -/
theorem continuousWithinAt_sliceRep (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hk : 2 ≤ k) {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain)
    {V : ℝ → E} {s : Set ℝ} {t : ℝ} {q : M} {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k}
    (hq : (g.geodesicFlow p t).proj ∈ (chartAt H q).source)
    (hc : (g.geodesicFlow p t).proj ∈ c.source)
    (h : ContinuousWithinAt (fun σ => (⟨(g.geodesicFlow p σ).proj, V σ⟩ : TangentBundle I M)) s t) :
    ContinuousWithinAt (fun τ => (mfderiv I 𝓘(ℝ, E) c (g.geodesicFlow p τ).proj (V τ) : E)) s t := by
  have hcont : Continuous fun σ => (g.geodesicFlow p σ).proj :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
      (continuous_geodesicFlow_of_forall_mem hr g hdom)
  have hW := (continuousWithinAt_iff_chartRepFinite hr hdom hq).1 h
  have hev : ∀ᶠ τ in 𝓝 t, (g.geodesicFlow p τ).proj ∈ (chartAt H q).source ∧
      (g.geodesicFlow p τ).proj ∈ c.source :=
    (hcont.continuousAt.eventually ((chartAt H q).open_source.mem_nhds hq)).and
      (hcont.continuousAt.eventually (c.open_source.mem_nhds hc))
  have hY : ∀ τ, (g.geodesicFlow p τ).proj ∈ (chartAt H q).source →
      (g.geodesicFlow p τ).proj ∈ c.source →
      (mfderiv I 𝓘(ℝ, E) c (g.geodesicFlow p τ).proj (V τ) : E) =
        fderiv ℝ (c ∘ (extChartAt I q).symm) (extChartAt I q (g.geodesicFlow p τ).proj)
          (chartRepFinite g p q V τ) := by
    intro τ hτq hτc
    rw [chartRepFinite_eq_mfderiv g p V hτq]
    exact mfderiv_eq_fderiv_sliceTransition hk hτq hτc (V τ)
  have hxsrc : (g.geodesicFlow p t).proj ∈ (extChartAt I q).source := by rwa [extChartAt_source]
  have hmem : extChartAt I q (g.geodesicFlow p t).proj ∈
      (extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' c.source :=
    ⟨(extChartAt I q).map_source hxsrc, by
      change (extChartAt I q).symm (extChartAt I q (g.geodesicFlow p t).proj) ∈ c.source
      rw [(extChartAt I q).left_inv hxsrc]; exact hc⟩
  have hx : ContinuousAt (fun σ => extChartAt I q (g.geodesicFlow p σ).proj) t :=
    ContinuousAt.comp (f := fun σ => (g.geodesicFlow p σ).proj)
      (continuousAt_extChartAt' (I := I) hxsrc) hcont.continuousAt
  have hD : ContinuousOn (fderiv ℝ (c ∘ (extChartAt I q).symm))
      ((extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' c.source) :=
    (contDiffOn_sliceTransition hk q c).continuousOn_fderiv_of_isOpen
      (isOpen_sliceTransition_source q c) (by norm_num)
  have hDx : ContinuousAt (fun σ => fderiv ℝ (c ∘ (extChartAt I q).symm)
      (extChartAt I q (g.geodesicFlow p σ).proj)) t :=
    ContinuousAt.comp (f := fun σ => extChartAt I q (g.geodesicFlow p σ).proj)
      (hD.continuousAt ((isOpen_sliceTransition_source q c).mem_nhds hmem)) hx
  refine (hDx.continuousWithinAt.clm_apply hW).congr_of_eventuallyEq ?_ (hY t hq hc)
  filter_upwards [nhdsWithin_le_nhds hev] with τ hτ
  exact hY τ hτ.1 hτ.2

end SliceGeodesic


section Tangency

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

local instance continuousDualEquivPTse : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

/-- The Koszul operator is symmetric when `D` is symmetric in its last two slots. -/
theorem raisedKoszulOp_comm (B : E →L[ℝ] E →L[ℝ] ℝ) {D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ}
    (hDsymm : ∀ a u v : E, D a u v = D a v u) (u w : E) :
    raisedKoszulOp B D u w = raisedKoszulOp B D w u := by
  rw [MetricKoszul.raisedKoszulOp_apply, MetricKoszul.raisedKoszulOp_apply]
  congr 2
  ext z
  rw [MetricKoszul.koszul_cov_apply, MetricKoszul.koszul_cov_apply, hDsymm z u w]
  ring

end Tangency

section SliceTangency

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {k : WithTop ℕ∞} {r : ℕ∞}

local instance continuousDualEquivPTst : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroupPTst : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpacePTst : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- **Normal Christoffel components vanish on tangent pairs.** For a totally geodesic `Z` read in a
slice chart `c` (onto `A`), and `Q` killing `A.direction`: `Q Γ_c(c x)(u, w) = 0` for
`u, w ∈ A.direction`. Diagonal: the geodesic with initial velocity `dc⁻¹ u` stays in `Z`, so its
`Q`-coordinate is locally constant and `Q x'' = −Q Γ(u, u) = 0`; then polarization. -/
theorem projection_sliceChristoffelFinite_eq_zero (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hk : 2 ≤ k) (hD : g.geodesicFlowDomain = univ) {Z : Set M} (htg : IsTotallyGeodesicFinite g Z)
    {c : PartialDiffeomorph I 𝓘(ℝ, E) M E k} {A : AffineSubspace ℝ E}
    (hA : FiniteDimensional ℝ A.direction) (himage : c.toPartialEquiv.IsImage Z (A : Set E))
    {x : M} (hxZ : x ∈ Z) (hxc : x ∈ c.source) (Q : E →L[ℝ] E)
    (hQ : ∀ w ∈ A.direction, Q w = 0) {u w : E} (hu : u ∈ A.direction) (hw : w ∈ A.direction) :
    Q (sliceChristoffelFinite g c (c x) u w) = 0 := by
  have hk0 : k ≠ 0 := by
    intro h0; rw [h0] at hk; exact absurd hk (by norm_num)
  have hdiag : ∀ u ∈ A.direction, Q (sliceChristoffelFinite g c (c x) u u) = 0 := by
    intro u hu
    set v : E := mfderiv 𝓘(ℝ, E) I c.symm (c x) u with hv
    have hcv : (mfderiv I 𝓘(ℝ, E) c x v : E) = u := mfderiv_apply_mfderiv_symm_of_mem_source_ofOrder hk0 hxc u
    have hvT : v ∈ sliceTangent I Z x :=
      (mem_sliceTangent_chart_iff_ofOrder hk0 hxZ hA hxc himage).2 (by rw [hcv]; exact hu)
    obtain ⟨δ, hδ, hZδ⟩ := htg x hxZ v hvT
    set p' : TangentBundle I M := ⟨x, v⟩ with hp'
    have hdom' : ∀ t : ℝ, (p', t) ∈ g.geodesicFlowDomain := fun t => by rw [hD]; exact mem_univ _
    have h0 : g.geodesicFlow p' 0 = p' := g.geodesicFlow_zero hr p'
    have hcont : Continuous fun σ => (g.geodesicFlow p' σ).proj :=
      (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
        (continuous_geodesicFlow_of_forall_mem hr g hdom')
    have hx0c : (g.geodesicFlow p' 0).proj ∈ c.source := by rw [h0]; exact hxc
    have hev : ∀ᶠ σ in 𝓝 (0 : ℝ), (g.geodesicFlow p' σ).proj ∈ c.source ∧
        (g.geodesicFlow p' σ).proj ∈ Z :=
      (hcont.continuousAt.eventually (c.open_source.mem_nhds hx0c)).and
        (Filter.eventually_of_mem (Ioo_mem_nhds (neg_lt_zero.2 hδ) hδ) fun σ hσ => hZδ σ hσ)
    obtain ⟨N, hNsub, hNopen, h0N⟩ := _root_.eventually_nhds_iff.1 hev
    have hcxA : c x ∈ A := (himage hxc).2 hxZ
    have hFconst : ∀ σ ∈ N, Q (c (g.geodesicFlow p' σ).proj) = Q (c x) := by
      intro σ hσ
      have h1 : c (g.geodesicFlow p' σ).proj ∈ A := (himage (hNsub σ hσ).1).2 (hNsub σ hσ).2
      have h3 := hQ _ (A.vsub_mem_direction h1 hcxA)
      rwa [vsub_eq_sub, map_sub, sub_eq_zero] at h3
    have hvel0 : ∀ σ ∈ N, Q (mfderiv I 𝓘(ℝ, E) c (g.geodesicFlow p' σ).proj
        (g.geodesicFlow p' σ).snd) = 0 := by
      intro σ hσ
      have hd := Q.hasFDerivAt.comp_hasDerivAt σ
        (hasDerivAt_slice_geodesicFlow_proj hr g hk hdom' (hNsub σ hσ).1)
      have hconst : HasDerivAt (Q ∘ fun τ => c (g.geodesicFlow p' τ).proj) 0 σ :=
        (hasDerivAt_const σ (Q (c x))).congr_of_eventuallyEq
          (Filter.eventually_of_mem (hNopen.mem_nhds hσ) fun τ hτ => hFconst τ hτ)
      exact hd.unique hconst
    have hd2 := Q.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_slice_geodesicFlow_vel hr g hk hdom' hx0c)
    have hconst2 : HasDerivAt (Q ∘ fun τ => (mfderiv I 𝓘(ℝ, E) c (g.geodesicFlow p' τ).proj
        (g.geodesicFlow p' τ).snd : E)) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (0 : E)).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hNopen.mem_nhds h0N) fun τ hτ => hvel0 τ hτ)
    have key := hd2.unique hconst2
    rw [h0] at key
    change Q (-(sliceChristoffelFinite g c (c x) (mfderiv I 𝓘(ℝ, E) c x v)
      (mfderiv I 𝓘(ℝ, E) c x v))) = 0 at key
    rw [hcv, map_neg, neg_eq_zero] at key
    exact key
  have hcx : c x ∈ c.target := c.toPartialEquiv.map_source hxc
  have hbd : DifferentiableAt ℝ (sliceCoeffFinite g c) (c x) :=
    ((contDiffOn_sliceCoeffFinite g (m := 1) (by exact_mod_cast le_add_self)
      (by rw [one_add_one_eq_two]; exact hk) c).contDiffAt (c.open_target.mem_nhds hcx)).differentiableAt
      (by norm_num)
  have hDsymm := fderiv_apply_symm_of_eventually hbd
    (Filter.Eventually.of_forall fun z u v => sliceCoeffFinite_symm g c z u v)
  have hcomm : sliceChristoffelFinite g c (c x) w u = sliceChristoffelFinite g c (c x) u w :=
    raisedKoszulOp_comm _ hDsymm w u
  have h1 := hdiag (u + w) (A.direction.add_mem hu hw)
  simp only [map_add, add_apply, hdiag u hu, hdiag w hw, hcomm, zero_add, add_zero] at h1
  have h2 : (2 : ℝ) • Q (sliceChristoffelFinite g c (c x) u w) = 0 := by
    rw [two_smul]; exact h1
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- The velocity of a geodesic arc inside `Z` is tangent to `Z` along the arc. -/
theorem geodesicFlow_snd_mem_sliceTangent (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {p : TangentBundle I M} (hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain) {Z : Set M}
    {a b : ℝ} (hab : a < b) (hγ : ∀ t ∈ Icc a b, (g.geodesicFlow p t).proj ∈ Z) {τ : ℝ}
    (hτ : τ ∈ Icc a b) :
    (g.geodesicFlow p τ).snd ∈ sliceTangent I Z (g.geodesicFlow p τ).proj := by
  have hm := g.hasMFDerivAt_geodesicFlow_proj hr (hdom τ)
  rcases lt_or_eq_of_le hτ.2 with hτb | hτb
  · have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => τ + s) 0 (ContinuousLinearMap.id ℝ ℝ) :=
      hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id (0 : ℝ)).const_add τ)
    have hm' : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => (g.geodesicFlow p s).proj) (τ + 0)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (g.geodesicFlow p τ).snd) := by
      rw [add_zero]; exact hm
    have hcomp := hm'.comp 0 hshift
    have hS : ∀ᶠ s in 𝓝[>] (0 : ℝ), (fun s => (g.geodesicFlow p s).proj) (τ + s) ∈ Z := by
      filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hτb)] with s hs
      exact hγ (τ + s) ⟨by linarith [hτ.1, hs.1], by linarith [hs.2]⟩
    have hmem := mem_sliceTangent_of_curve (I := I) (S := Z) (x := (g.geodesicFlow p τ).proj)
      (f := (fun s => (g.geodesicFlow p s).proj) ∘ fun s : ℝ => τ + s) (by simp) hS
      hcomp.mdifferentiableAt
    rw [hcomp.mfderiv] at hmem
    change ((1 : ℝ →L[ℝ] ℝ).smulRight (g.geodesicFlow p τ).snd)
      ((ContinuousLinearMap.id ℝ ℝ) (1 : ℝ)) ∈ sliceTangent I Z (g.geodesicFlow p τ).proj at hmem
    simpa using hmem
  · have hτa : a < τ := hτb ▸ hab
    have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => τ - s) 0
        (-ContinuousLinearMap.id ℝ ℝ) :=
      hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id (0 : ℝ)).const_sub τ)
    have hm' : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => (g.geodesicFlow p s).proj) (τ - 0)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (g.geodesicFlow p τ).snd) := by
      rw [sub_zero]; exact hm
    have hcomp := hm'.comp 0 hshift
    have hS : ∀ᶠ s in 𝓝[>] (0 : ℝ), (fun s => (g.geodesicFlow p s).proj) (τ - s) ∈ Z := by
      filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hτa)] with s hs
      exact hγ (τ - s) ⟨by linarith [hs.2], by linarith [hτ.2, hs.1]⟩
    have hmem := mem_sliceTangent_of_curve (I := I) (S := Z) (x := (g.geodesicFlow p τ).proj)
      (f := (fun s => (g.geodesicFlow p s).proj) ∘ fun s : ℝ => τ - s) (by simp) hS
      hcomp.mdifferentiableAt
    rw [hcomp.mfderiv] at hmem
    change ((1 : ℝ →L[ℝ] ℝ).smulRight (g.geodesicFlow p τ).snd)
      ((-ContinuousLinearMap.id ℝ ℝ) (1 : ℝ)) ∈ sliceTangent I Z (g.geodesicFlow p τ).proj at hmem
    simpa using hmem

end SliceTangency


/-- The parallel ODE in every chart, on a set `s` of times (velocity form); `H` is the model space. -/
local macro "PVF[" H:term ", " g:term ", " p:term ", " V:term ", " s:term "]" : term =>
  `(∀ t ∈ $s, ∀ q, (Bundle.ContMDiffRiemannianMetric.geodesicFlow $g $p t).proj ∈
    (chartAt $H q).source →
    HasDerivWithinAt (DifferentialGeometry.Geometry.FiniteSoul.chartRepFinite $g $p q $V)
      (DifferentialGeometry.Geometry.FiniteSoul.parallelCoeffFinite $g $p q t
        (DifferentialGeometry.Geometry.FiniteSoul.chartRepFinite $g $p q $V t)) $s t)

section Frozen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

local instance continuousDualEquivPTsf : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroupPTsf : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpacePTsf : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- **S3-PT.b** (`2 ≤ r`, slice of order `k ≥ 3`). Along a geodesic arc inside a totally geodesic `C^k`
slice `Z`, a continuous parallel field tangent to `Z` at time `0` stays tangent to `Z`. Route: in an adapted
slice chart, total geodesy gives `Γ^⊥(TZ, TZ) = 0` on `Z` (polarization of `x_⊥'' = 0` along tangent
geodesics); the normal components of `V` solve a homogeneous linear ODE with zero initial value. -/
theorem isParallel_mem_sliceTangent_of_totallyGeodesic
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {k : ℕ∞} (hk : 3 ≤ k) {d : ℕ} {Z : Set M} (hZ : IsEmbeddedSliceOfOrder I (k : ℕ∞ω) d Z)
    (htg : IsTotallyGeodesicFinite g Z) (p : TangentBundle I M) {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (hγ : ∀ t ∈ Icc a b, (g.geodesicFlow p t).proj ∈ Z) (V : ℝ → E)
    (hVc : ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj, V t⟩ : TangentBundle I M)) (Icc a b))
    (hV : IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) V (Icc a b))
    (h0 : V 0 ∈ sliceTangent I Z p.proj) :
    ∀ t ∈ Icc a b, V t ∈ sliceTangent I Z (g.geodesicFlow p t).proj := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ_of_one_le g hr1 hnorm
  have hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain := fun t => by rw [hD]; exact mem_univ _
  have hk2 : (2 : ℕ∞ω) ≤ (k : ℕ∞ω) := by
    have h : (2 : ℕ∞) ≤ k := le_trans (by norm_num) hk
    exact WithTop.coe_le_coe.2 h
  have hk0 : (k : ℕ∞ω) ≠ 0 := by
    intro h0; rw [h0] at hk2; exact absurd hk2 (by norm_num)
  have hcont : Continuous fun σ => (g.geodesicFlow p σ).proj :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
      (continuous_geodesicFlow_of_forall_mem hr1 g hdom)
  have h0' : V 0 ∈ sliceTangent I Z (g.geodesicFlow p 0).proj := by
    rw [g.geodesicFlow_zero hr1 p]; exact h0
  intro t ht
  rcases lt_or_ge a b with hab | hab
  swap
  · have ht0 : t = 0 := by linarith [ht.1, ht.2]
    rw [ht0]; exact h0'
  have hVP : PVF[H, g, p, V, Icc a b] :=
    (isParallelAlongFinite_geodesicFlow_iff hr1 (fun t _ => hdom t)
      (fun t ht => uniqueDiffOn_Icc hab t ht)).1 hV
  have hloc : ∀ x ∈ Icc a b, ∃ J ∈ 𝓝[Icc a b] x, ∀ y ∈ J, ∀ z ∈ J,
      V y ∈ sliceTangent I Z (g.geodesicFlow p y).proj →
        V z ∈ sliceTangent I Z (g.geodesicFlow p z).proj := by
    intro x hx
    obtain ⟨cZ, A, hA, hxs, -, himage⟩ := hZ _ (hγ x hx)
    obtain ⟨q, hq⟩ : ∃ q : M, (g.geodesicFlow p x).proj ∈ (chartAt H q).source :=
      ⟨_, mem_chart_source H _⟩
    have hopen : IsOpen ((fun σ => (g.geodesicFlow p σ).proj) ⁻¹'
        ((chartAt H q).source ∩ cZ.source)) :=
      ((chartAt H q).open_source.inter cZ.open_source).preimage hcont
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen x ⟨hq, hxs⟩
    have hsub : ∀ σ ∈ Icc (x - ε / 2) (x + ε / 2),
        (g.geodesicFlow p σ).proj ∈ (chartAt H q).source ∧ (g.geodesicFlow p σ).proj ∈ cZ.source :=
      fun σ hσ => hball (by rw [Real.ball_eq_Ioo]; constructor <;> linarith [hσ.1, hσ.2])
    obtain ⟨N, hN⟩ := Submodule.exists_isCompl A.direction
    set Q : E →L[ℝ] E := LinearMap.toContinuousLinearMap (N.projection A.direction hN.symm) with hQdef
    have hQ0 : ∀ w, Q w = 0 ↔ w ∈ A.direction := fun w =>
      Submodule.projection_apply_eq_zero_iff hN.symm
    have hQsub : ∀ w, w - Q w ∈ A.direction := fun w => Submodule.sub_projection_mem hN.symm w
    set B : ℝ → E →L[ℝ] E := fun τ => -(Q.comp (sliceChristoffelFinite g cZ
      (cZ (g.geodesicFlow p τ).proj)
      (mfderiv I 𝓘(ℝ, E) cZ (g.geodesicFlow p τ).proj (g.geodesicFlow p τ).snd))) with hBdef
    have hΓ : ContinuousOn (sliceChristoffelFinite g cZ) cZ.target :=
      (MetricKoszul.raisedOp_contDiffOn_succ (n := 0) cZ.open_target
        (contDiffOn_sliceCoeffFinite g (m := 0 + 1) (by exact_mod_cast le_add_self)
          (by rw [zero_add, one_add_one_eq_two]; exact hk2) cZ)
        (fun z hz => isCoercive_sliceCoeffFinite hk0 g hz)).continuousOn
    have hBc : ∀ τ ∈ Icc (x - ε / 2) (x + ε / 2), ContinuousAt B τ := by
      intro τ hτ
      have hτc := (hsub τ hτ).2
      have hy := (hasDerivAt_slice_geodesicFlow_proj hr1 g hk2 hdom hτc).continuousAt
      have hvel := (hasDerivAt_slice_geodesicFlow_vel hr1 g hk2 hdom hτc).continuousAt
      have hΓy : ContinuousAt (fun σ => sliceChristoffelFinite g cZ (cZ (g.geodesicFlow p σ).proj)) τ :=
        ContinuousAt.comp (f := fun σ => cZ (g.geodesicFlow p σ).proj)
          (hΓ.continuousAt (cZ.open_target.mem_nhds (cZ.toPartialEquiv.map_source hτc))) hy
      exact (continuousAt_const.clm_comp (hΓy.clm_apply hvel)).neg
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := x - ε / 2) (b := x + ε / 2)).exists_bound_of_continuousOn
      (f := B) (fun τ hτ => (hBc τ hτ).continuousWithinAt)
    set J := Icc (a ⊔ (x - ε / 2)) (b ⊓ (x + ε / 2)) with hJdef
    have hJ : Icc a b ∩ Icc (x - ε / 2) (x + ε / 2) = J := Icc_inter_Icc
    have hJ₁ : J ⊆ Icc a b := hJ ▸ inter_subset_left
    have hJ₂ : J ⊆ Icc (x - ε / 2) (x + ε / 2) := hJ ▸ inter_subset_right
    set Y : ℝ → E := fun τ => (mfderiv I 𝓘(ℝ, E) cZ (g.geodesicFlow p τ).proj (V τ) : E) with hYdef
    have hQY : ∀ τ ∈ J, HasDerivWithinAt (fun σ => Q (Y σ)) (B τ (Q (Y τ))) J τ := by
      intro τ hτ
      have hτq := (hsub τ (hJ₂ hτ)).1
      have hτc := (hsub τ (hJ₂ hτ)).2
      have hτZ := hγ τ (hJ₁ hτ)
      have hY := hasDerivWithinAt_sliceRep hr1 g hk2 hdom hτq hτc ((hVP τ (hJ₁ hτ) q hτq).mono hJ₁)
      have h1 := Q.hasFDerivAt.comp_hasDerivWithinAt τ hY
      refine h1.congr_deriv ?_
      have hvelA : (mfderiv I 𝓘(ℝ, E) cZ (g.geodesicFlow p τ).proj (g.geodesicFlow p τ).snd : E) ∈
          A.direction :=
        (mem_sliceTangent_chart_iff_ofOrder hk0 hτZ hA hτc himage).1
          (geodesicFlow_snd_mem_sliceTangent hr1 g hdom hab hγ (hJ₁ hτ))
      have htan := projection_sliceChristoffelFinite_eq_zero hr1 g hk2 hD htg hA himage hτZ hτc Q
        (fun w hw => (hQ0 w).2 hw) hvelA (hQsub (Y τ))
      have hsplit : sliceChristoffelFinite g cZ (cZ (g.geodesicFlow p τ).proj)
          (mfderiv I 𝓘(ℝ, E) cZ (g.geodesicFlow p τ).proj (g.geodesicFlow p τ).snd) (Y τ) =
          sliceChristoffelFinite g cZ (cZ (g.geodesicFlow p τ).proj)
            (mfderiv I 𝓘(ℝ, E) cZ (g.geodesicFlow p τ).proj (g.geodesicFlow p τ).snd) (Y τ - Q (Y τ)) +
          sliceChristoffelFinite g cZ (cZ (g.geodesicFlow p τ).proj)
            (mfderiv I 𝓘(ℝ, E) cZ (g.geodesicFlow p τ).proj (g.geodesicFlow p τ).snd) (Q (Y τ)) := by
        rw [← map_add, sub_add_cancel]
      simp only [hBdef, neg_apply, ContinuousLinearMap.comp_apply, map_neg]
      rw [hsplit, map_add, htan, zero_add]
    refine ⟨J, ?_, fun y hy z hz hyT => ?_⟩
    · rw [← hJ]
      exact inter_mem_nhdsWithin _ (Icc_mem_nhds (by linarith) (by linarith))
    · have hYy : Q (Y y) = 0 := (hQ0 _).2
        ((mem_sliceTangent_chart_iff_ofOrder hk0 (hγ y (hJ₁ hy)) hA (hsub y (hJ₂ hy)).2 himage).1 hyT)
      have heq := eqOn_Icc_of_hasDerivWithinAt_linear (K := C.toNNReal)
        (fun σ hσ => (hC σ (hJ₂ hσ)).trans (Real.le_coe_toNNReal C))
        (Y₁ := fun σ => Q (Y σ)) (Y₂ := fun _ => 0)
        (fun σ hσ => Q.continuous.continuousAt.comp_continuousWithinAt
          ((continuousWithinAt_sliceRep hr1 g hk2 hdom (hsub σ (hJ₂ hσ)).1 (hsub σ (hJ₂ hσ)).2
            (hVc σ (hJ₁ hσ))).mono hJ₁)) continuousOn_const hQY
        (fun σ _ => by simpa using hasDerivWithinAt_const σ J (0 : E)) hy hYy
      exact (mem_sliceTangent_chart_iff_ofOrder hk0 (hγ z (hJ₁ hz)) hA (hsub z (hJ₂ hz)).2
        himage).2 ((hQ0 _).1 (heq hz))
  refine isPreconnected_Icc.induction₂' (fun x y => V x ∈ sliceTangent I Z (g.geodesicFlow p x).proj →
    V y ∈ sliceTangent I Z (g.geodesicFlow p y).proj) ?_ ?_ ⟨ha, hb⟩ ht h0'
  · intro x hx
    obtain ⟨J, hJ, hJprop⟩ := hloc x hx
    have hxJ : x ∈ J := mem_of_mem_nhdsWithin hx hJ
    filter_upwards [hJ] with y hy
    exact ⟨fun h => hJprop x hxJ y hy h, fun h => hJprop y hy x hxJ h⟩
  · intro x y z _ _ _ hxy hyz h
    exact hyz (hxy h)

end Frozen

end DifferentialGeometry.Geometry.FiniteSoul
