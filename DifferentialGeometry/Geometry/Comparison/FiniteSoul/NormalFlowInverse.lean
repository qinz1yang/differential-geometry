import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalFlowGradient
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalParamGlobal

/-!
# The inverse of a normal parametrization along the tube (lane CMS3-FLOW2, G2)

LFR46's inner inverse `Φ⁻¹ = ι⁻¹ ∘ ψ` (A:28965–28970) for ANY smooth Riemannian vector bundle
`V → B` with a `C^m` fibrewise linear isometry `ι` onto the normal vectors over the base map `b`
(the hypotheses of `exists_finite_normalFlowMap`), plus the BASE inverse contract (`hbinv`, D1).

* `inner_iota_eq_tube`: polarization, `g(ι(s, w), ι(s, w')) = ⟪w, w'⟫`.
* `injective_iota_tube`: `ι` is injective when `b` is.
* `trivGram_apply_tube`, `isInvertible_trivGram_tube`: the Gram operator of a trivialization in an
  orthonormal basis of the model fibre, `T a = Σ_i ⟪e⁻¹ fᵢ, e⁻¹ a⟫ fᵢ`, invertible on the base set.
* `contMDiffAt_of_iota_eq_tube`: a map `κ` into the total space with `ι ∘ κ = β` and base `σ` is
  `C^m` where `β` and `σ` are: in a trivialization its fibre coordinate is `T(σ)⁻¹ c` with
  `cᵢ = g(β, ι(σ, e⁻¹ fᵢ))`. No inverse function theorem.
* `exists_normalTube_partialDiffeomorph`: the tube `Φ = exp ∘ ι` on `{|z| < ε}` is a
  `C^(r−1)` partial diffeomorphism onto `{d_S < ε}` with inverse `ι⁻¹ ∘ ψ`, for the SAME tube
  `(ε, ψ)` of S3-TUBE; `|z| = d_S (Φ z)`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteSoul

section Gram

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ s, NormedAddCommGroup (V s)]
  [∀ s, InnerProductSpace ℝ (V s)] [FiberBundle F V] [VectorBundle ℝ F V]

/-- The Gram operator of the trivialization `e` at `s` in the orthonormal basis `fb` of `F`. -/
def trivGramTube (e : Trivialization F (TotalSpace.proj : TotalSpace F V → B))
    {k : ℕ} (fb : OrthonormalBasis (Fin k) ℝ F) (s : B) : F →L[ℝ] F :=
  ∑ i, ∑ j, ⟪e.symm s (fb i), e.symm s (fb j)⟫_ℝ • (innerSL ℝ (fb j)).smulRight (fb i)

omit [FiniteDimensional ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- `e.symm s` expanded in the basis. -/
theorem symm_eq_sum_tube (e : Trivialization F (TotalSpace.proj : TotalSpace F V → B))
    [e.IsLinear ℝ] {k : ℕ} (fb : OrthonormalBasis (Fin k) ℝ F) {s : B} (hs : s ∈ e.baseSet)
    (a : F) : e.symm s a = ∑ j, ⟪fb j, a⟫_ℝ • e.symm s (fb j) := by
  have hlin : ∀ y, e.symm s y = e.symmₗ ℝ s y := fun y => (e.symmₗ_apply (R := ℝ) hs y).symm
  conv_lhs => rw [← fb.sum_repr' a]
  rw [hlin, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hlin]

omit [FiniteDimensional ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
theorem trivGram_apply_tube (e : Trivialization F (TotalSpace.proj : TotalSpace F V → B))
    [e.IsLinear ℝ] {k : ℕ} (fb : OrthonormalBasis (Fin k) ℝ F) {s : B} (hs : s ∈ e.baseSet)
    (a : F) : trivGramTube e fb s a = ∑ i, ⟪e.symm s (fb i), e.symm s a⟫_ℝ • fb i := by
  unfold trivGramTube
  rw [sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_apply, symm_eq_sum_tube e fb hs a, inner_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    real_inner_smul_right, smul_smul, mul_comm]

omit [FiberBundle F V] [VectorBundle ℝ F V] in
theorem isInvertible_trivGram_tube (e : Trivialization F (TotalSpace.proj : TotalSpace F V → B))
    [e.IsLinear ℝ] {k : ℕ} (fb : OrthonormalBasis (Fin k) ℝ F) {s : B} (hs : s ∈ e.baseSet) :
    (trivGramTube e fb s).IsInvertible := by
  have hinj : Injective (trivGramTube e fb s : F →ₗ[ℝ] F) := by
    intro a a' haa'
    have h0 : trivGramTube e fb s (a - a') = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr haa'
    set c := a - a' with hc
    have hq1 : ⟪trivGramTube e fb s c, c⟫_ℝ =
        ∑ i, ⟪e.symm s (fb i), e.symm s c⟫_ℝ * ⟪fb i, c⟫_ℝ := by
      rw [trivGram_apply_tube e fb hs, sum_inner]
      simp only [real_inner_smul_left]
    have hq2 : ⟪e.symm s c, e.symm s c⟫_ℝ =
        ∑ i, ⟪fb i, c⟫_ℝ * ⟪e.symm s (fb i), e.symm s c⟫_ℝ := by
      nth_rewrite 1 [symm_eq_sum_tube e fb hs c]
      rw [sum_inner]
      simp only [real_inner_smul_left]
    have hcomm : ∑ i, ⟪fb i, c⟫_ℝ * ⟪e.symm s (fb i), e.symm s c⟫_ℝ =
        ∑ i, ⟪e.symm s (fb i), e.symm s c⟫_ℝ * ⟪fb i, c⟫_ℝ :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hq : ⟪e.symm s c, e.symm s c⟫_ℝ = 0 := by
      rw [hq2, hcomm, ← hq1, h0, inner_zero_left]
    have hz : e.symm s c = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hq
    have h0' : e.symm s 0 = 0 := by
      rw [← e.symmₗ_apply (R := ℝ) hs, map_zero]
    have h1 := e.apply_mk_symm hs c
    rw [hz, ← h0', e.apply_mk_symm hs] at h1
    have h2 := congrArg Prod.snd h1
    exact sub_eq_zero.mp h2.symm
  let L : F ≃ₗ[ℝ] F := LinearEquiv.ofInjectiveEndo (trivGramTube e fb s : F →ₗ[ℝ] F) hinj
  refine ⟨L.toContinuousLinearEquiv, ?_⟩
  ext a
  rfl

end Gram

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ s, NormedAddCommGroup (V s)]
  [∀ s, InnerProductSpace ℝ (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)] [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] [FiniteDimensional ℝ EB] [IsManifold 𝓘(ℝ, EB) ∞ B]
  [FiniteDimensional ℝ F] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)] [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V]
  [TopologicalSpace B] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace (TotalSpace F V)] in
/-- **Polarization**: `ι` is fibrewise isometric for the inner products. -/
theorem inner_iota_eq_tube {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (ι : TotalSpace F V → TangentBundle I M) (b : B → M) (hιb : ∀ z, (ι z).proj = b z.proj)
    (hιlin : ∀ s : B, ∃ A : V s →L[ℝ] E, ∀ w : V s, @Eq E (ι ⟨s, w⟩).snd (A w))
    (hιnorm : ∀ z : TotalSpace F V, g.inner (ι z).proj (ι z).snd (ι z).snd = ‖z.2‖ ^ 2)
    (s : B) (w w' : V s) :
    g.inner (b s) (ι ⟨s, w⟩).snd (ι ⟨s, w'⟩).snd = ⟪w, w'⟫_ℝ := by
  obtain ⟨A, hA⟩ := hιlin s
  have hq : ∀ v : V s, g.inner (b s) (A v) (A v) = ‖v‖ ^ 2 := by
    intro v
    have h := (inner_congr_base_tube g (hιb ⟨s, v⟩) _ _).symm.trans (hιnorm ⟨s, v⟩)
    rw [hA v] at h
    exact h
  rw [hA w, hA w']
  set u : TangentSpace I (b s) := A w with hu
  set u' : TangentSpace I (b s) := A w' with hu'
  have hsum : g.inner (b s) (u + u') (u + u') = ‖w + w'‖ ^ 2 := by
    have h := hq (w + w')
    rwa [show (A (w + w') : TangentSpace I (b s)) = u + u' from map_add A w w'] at h
  have hexp : g.inner (b s) (u + u') (u + u') =
      g.inner (b s) u u + 2 * g.inner (b s) u u' + g.inner (b s) u' u' := by
    have hsym : g.inner (b s) u' u = g.inner (b s) u u' := g.symm _ _ _
    simp only [map_add, add_apply]
    rw [hsym]
    ring
  rw [hexp, hu, hu', hq w, hq w', norm_add_sq_real] at hsum
  linarith

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] [FiniteDimensional ℝ EB] [IsManifold 𝓘(ℝ, EB) ∞ B]
  [FiniteDimensional ℝ F] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)] [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V]
  [TopologicalSpace B] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace (TotalSpace F V)] in
/-- **`ι` is injective** when the base map is. -/
theorem injective_iota_tube {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (ι : TotalSpace F V → TangentBundle I M) {b : B → M} (hbinj : Injective b)
    (hιb : ∀ z, (ι z).proj = b z.proj)
    (hιlin : ∀ s : B, ∃ A : V s →L[ℝ] E, ∀ w : V s, @Eq E (ι ⟨s, w⟩).snd (A w))
    (hιnorm : ∀ z : TotalSpace F V, g.inner (ι z).proj (ι z).snd (ι z).snd = ‖z.2‖ ^ 2) :
    Injective ι := by
  rintro ⟨s, w⟩ ⟨s', w'⟩ h
  have hs : s = s' := hbinj (by
    have h1 := hιb ⟨s, w⟩
    have h2 := hιb ⟨s', w'⟩
    rw [← h1, ← h2, h])
  subst hs
  have h1 := inner_iota_eq_tube g ι b hιb hιlin hιnorm s w w
  have h2 := inner_iota_eq_tube g ι b hιb hιlin hιnorm s w w'
  have h3 := inner_iota_eq_tube g ι b hιb hιlin hιnorm s w' w'
  rw [h] at h1 h2
  have hz : ⟪w - w', w - w'⟫_ℝ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm w w']
    linarith
  rw [sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp hz)]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] [FiniteDimensional ℝ EB]
  [IsManifold 𝓘(ℝ, EB) ∞ B] in
/-- **Smoothness of a lift through `ι`.** A map `κ` into the total space with `ι ∘ κ = β` and base
`σ` near `x₀` is `C^m` at `x₀` when `β` and `σ` are. -/
theorem contMDiffAt_of_iota_eq_tube {n m : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hmn : m ≤ n)
    (hm : m ≤ ((⊤ : ℕ∞) : ℕ∞ω))
    (ι : TotalSpace F V → TangentBundle I M)
    (hι : ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I.tangent m ι) (b : B → M)
    (hιb : ∀ z, (ι z).proj = b z.proj)
    (hιlin : ∀ s : B, ∃ A : V s →L[ℝ] E, ∀ w : V s, @Eq E (ι ⟨s, w⟩).snd (A w))
    (hιnorm : ∀ z : TotalSpace F V, g.inner (ι z).proj (ι z).snd (ι z).snd = ‖z.2‖ ^ 2)
    {κ : M → TotalSpace F V} {σ : M → B} {β : M → TangentBundle I M} {x₀ : M}
    (hσ : ContMDiffAt I 𝓘(ℝ, EB) m σ x₀) (hβ : ContMDiffAt I I.tangent m β x₀)
    (hκ : ∀ᶠ x in 𝓝 x₀, ι (κ x) = β x ∧ (κ x).proj = σ x) :
    ContMDiffAt I (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) m κ x₀ := by
  obtain ⟨-, h0proj⟩ := hκ.self_of_nhds
  rw [contMDiffAt_totalSpace]
  refine ⟨hσ.congr_of_eventuallyEq (hκ.mono fun x hx => hx.2), ?_⟩
  rw [h0proj]
  set e := trivializationAt F V (σ x₀) with he
  have hbase : ∀ᶠ x in 𝓝 x₀, σ x ∈ e.baseSet := hσ.continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V (σ x₀)))
  set fb := stdOrthonormalBasis ℝ F with hfb
  have hs₀ : σ x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V (σ x₀)
  -- the frame sections, smooth on the base set
  have hsecB : ∀ v : F, ContMDiffAt 𝓘(ℝ, EB) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞
      (fun s => (⟨s, e.symm s v⟩ : TotalSpace F V)) (σ x₀) := by
    intro v
    have hs : ContMDiffOn 𝓘(ℝ, EB) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞
        (fun s => TotalSpace.mk' F s (e.symm s v)) e.baseSet := by
      rw [e.contMDiffOn_section_baseSet_iff]
      exact (contMDiffOn_const (c := v)).congr fun s hs => by rw [e.apply_mk_symm hs v]
    exact hs.contMDiffAt (e.open_baseSet.mem_nhds hs₀)
  have hsec : ∀ v : F, ContMDiffAt I (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) m
      (fun x => (⟨σ x, e.symm (σ x) v⟩ : TotalSpace F V)) x₀ := fun v =>
    ((hsecB v).of_le hm).comp x₀ hσ
  -- the Gram operator on the base, then along `σ`
  have hKB : ∀ i j, ContMDiffAt 𝓘(ℝ, EB) 𝓘(ℝ, ℝ) ∞
      (fun s => ⟪e.symm s (fb i), e.symm s (fb j)⟫_ℝ) (σ x₀) := fun i j =>
    (hsecB (fb i)).inner_bundle (hsecB (fb j))
  have hTB : ContMDiffAt 𝓘(ℝ, EB) 𝓘(ℝ, F →L[ℝ] F) ∞ (trivGramTube e fb) (σ x₀) := by
    unfold trivGramTube
    refine contMDiffAt_finsetSum fun i _ => contMDiffAt_finsetSum fun j _ => ?_
    exact (hKB i j).smul contMDiffAt_const
  have hT : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) m (fun x => trivGramTube e fb (σ x)) x₀ :=
    (hTB.of_le hm).comp x₀ hσ
  have hTinv : (trivGramTube e fb (σ x₀)).IsInvertible := isInvertible_trivGram_tube e fb hs₀
  have hinv : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) m
      (fun x => (trivGramTube e fb (σ x)).inverse) x₀ :=
    ContDiffAt.comp_contMDiffAt (f := fun x => trivGramTube e fb (σ x))
      hTinv.contDiffAt_map_inverse hT
  -- the pairing coefficients
  have hβb : ∀ᶠ x in 𝓝 x₀, (β x).proj = b (σ x) := hκ.mono fun x hx => by
    rw [← hx.1, hιb, hx.2]
  have hc : ContMDiffAt I 𝓘(ℝ, F) m (fun x => ∑ i, g.inner (β x).proj (β x).snd
      (ι ⟨σ x, e.symm (σ x) (fb i)⟩).snd • fb i) x₀ := by
    refine contMDiffAt_finsetSum fun i _ => ?_
    have hw : ContMDiffAt I I.tangent m (fun x => (⟨(β x).proj,
        (ι ⟨σ x, e.symm (σ x) (fb i)⟩).snd⟩ : TangentBundle I M)) x₀ := by
      apply (hι.contMDiffAt.comp x₀ (hsec (fb i))).congr_of_eventuallyEq
      filter_upwards [hβb] with x hx
      exact (mk_snd_eq_of_proj_eq_tube _ (by rw [hιb, hx])).symm
    exact (contMDiffAt_inner_along g hmn (β := fun x => (β x).proj) (v := fun x => (β x).snd)
      (w := fun x => (ι ⟨σ x, e.symm (σ x) (fb i)⟩).snd) hβ hw).smul
        (contMDiffAt_const (c := fb i))
  -- the fibre coordinate
  apply (hinv.clm_apply hc).congr_of_eventuallyEq
  filter_upwards [hκ, hbase] with x hx hxb
  obtain ⟨hιx, hpx⟩ := hx
  have hrep : ∀ z : TotalSpace F V, z.proj ∈ e.baseSet →
      (⟨z.proj, e.symm z.proj (e z).2⟩ : TotalSpace F V) = z := by
    rintro ⟨s, w⟩ hz
    change (⟨s, e.symm s (e ⟨s, w⟩).2⟩ : TotalSpace F V) = ⟨s, w⟩
    rw [e.symm_apply_apply_mk hz w]
  have hκx : κ x = (⟨σ x, e.symm (σ x) (e (κ x)).2⟩ : TotalSpace F V) := by
    rw [← hpx]
    exact (hrep (κ x) (hpx ▸ hxb)).symm
  generalize (e (κ x)).2 = a at hκx ⊢
  have hTa : trivGramTube e fb (σ x) a = ∑ i, g.inner (β x).proj (β x).snd
      (ι ⟨σ x, e.symm (σ x) (fb i)⟩).snd • fb i := by
    rw [trivGram_apply_tube e fb hxb]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← hιx, hκx]
    have h := inner_iota_eq_tube g ι b hιb hιlin hιnorm (σ x) (e.symm (σ x) a)
      (e.symm (σ x) (fb i))
    rw [real_inner_comm]
    exact ((inner_congr_base_tube g (hιb _) _ _).trans h).symm
  rw [← hTa, (isInvertible_trivGram_tube e fb hxb).inverse_apply_self]

omit [FiniteDimensional ℝ EB] [IsManifold 𝓘(ℝ, EB) ∞ B] in
/-- **The tube as a partial diffeomorphism of the bundle** (`2 ≤ r`): for the SAME tube `(ε, ψ)`
of S3-TUBE and a normal parametrization `ι` over a base map with the BASE inverse contract,
`Φ = exp ∘ ι` maps `{|z| < ε}` onto `{d_S < ε}`, `C^(r−1)` both ways, with inverse `ι⁻¹ ∘ ψ`, and
`|z| = d_S (Φ z)`. -/
theorem exists_normalTube_partialDiffeomorph
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSne : S.Nonempty) {ε : ℝ} {ψ : M → TangentBundle I M}
    (hψs : ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ {x | infDist x S < ε})
    (hψ : ∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
      Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S)
    (hψexp : ∀ v ∈ normalSetFinite g S, Real.sqrt (g.inner v.proj v.snd v.snd) < ε →
      ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = Real.sqrt (g.inner v.proj v.snd v.snd))
    (b : B → M) (hbinj : Injective b) (hbS : range b = S)
    (hbinv : ∃ R : M → B, (∀ s, R (b s) = s) ∧
      ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x)
    (ι : TotalSpace F V → TangentBundle I M)
    (hι : ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ι)
    (hιb : ∀ z, (ι z).proj = b z.proj)
    (hιlin : ∀ s : B, ∃ A : V s →L[ℝ] E, ∀ w : V s, @Eq E (ι ⟨s, w⟩).snd (A w))
    (hιnorm : ∀ z : TotalSpace F V, g.inner (ι z).proj (ι z).snd (ι z).snd = ‖z.2‖ ^ 2)
    (hιν : ∀ z, ι z ∈ normalSetFinite g S)
    (hιonto : ∀ v ∈ normalSetFinite g S, ∃ z, ι z = v) :
    ∃ Φ : PartialDiffeomorph (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I (TotalSpace F V) M ((r - 1 : ℕ∞) : ℕ∞ω),
      Φ.source = {z | ‖z.2‖ < ε} ∧ Φ.target = {x | infDist x S < ε} ∧
      (∀ z, Φ z = g.expMap (ι z)) ∧ (∀ x, infDist x S < ε → ι (Φ.symm x) = ψ x) ∧
      ∀ z ∈ Φ.source, ‖z.2‖ = infDist (Φ z) S := by
  classical
  have hr1 : 1 ≤ r := one_le_two.trans hr
  obtain ⟨R, hRb, hRs⟩ := hbinv
  have hinj : Injective ι := injective_iota_tube g ι hbinj hιb hιlin hιnorm
  obtain ⟨s₀, hs₀⟩ := hSne
  have hneT : Nonempty (TotalSpace F V) :=
    ⟨(hιonto _ (zero_mem_normalSetFinite g (S := S) hs₀)).choose⟩
  set ιinv : TangentBundle I M → TotalSpace F V := Function.invFun ι with hιinvdef
  have hleft : ∀ z, ιinv (ι z) = z := Function.leftInverse_invFun hinj
  have hright : ∀ v ∈ normalSetFinite g S, ι (ιinv v) = v := fun v hv =>
    Function.invFun_eq (hιonto v hv)
  have hlen : ∀ z : TotalSpace F V, Real.sqrt (g.inner (ι z).proj (ι z).snd (ι z).snd) = ‖z.2‖ :=
    fun z => by rw [hιnorm z, Real.sqrt_sq (norm_nonneg _)]
  have hdc : Continuous (fun x => infDist x S) := continuous_infDist_pt S
  have hnormc : Continuous (fun z : TotalSpace F V => ‖z.2‖) := by
    have h : ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞
        (fun z : TotalSpace F V => ⟪z.2, z.2⟫_ℝ) := contMDiff_id.inner_bundle contMDiff_id
    have heq : (fun z : TotalSpace F V => ‖z.2‖) = fun z => Real.sqrt ⟪z.2, z.2⟫_ℝ := by
      funext z
      rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    rw [heq]
    exact h.continuous.sqrt
  have hexpS : ContMDiff I.tangent I (r : ℕ∞ω) g.expMap := by
    have h := g.contMDiffOn_expMap hr1
    have hdom : g.expDomain = univ := by
      unfold Bundle.ContMDiffRiemannianMetric.expDomain
      rw [g.geodesicFlowDomain_eq_univ hr hnorm, preimage_univ]
    rw [hdom, contMDiffOn_univ] at h
    exact h
  have hle : ((r - 1 : ℕ∞) : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast tsub_le_self
  have hopenT : IsOpen {x : M | infDist x S < ε} := isOpen_lt hdc continuous_const
  let Φ : PartialDiffeomorph (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I (TotalSpace F V) M
      ((r - 1 : ℕ∞) : ℕ∞ω) :=
    { toFun := fun z => g.expMap (ι z)
      invFun := fun x => ιinv (ψ x)
      source := {z | ‖z.2‖ < ε}
      target := {x | infDist x S < ε}
      map_source' := fun z hz => by
        change infDist (g.expMap (ι z)) S < ε
        rw [(hψexp (ι z) (hιν z) (by rw [hlen]; exact hz)).2, hlen]
        exact hz
      map_target' := fun x hx => by
        change ‖(ιinv (ψ x)).2‖ < ε
        rw [← hlen, hright _ (hψ x hx).1, (hψ x hx).2.2]
        exact hx
      left_inv' := fun z hz => by
        change ιinv (ψ (g.expMap (ι z))) = z
        rw [(hψexp (ι z) (hιν z) (by rw [hlen]; exact hz)).1, hleft]
      right_inv' := fun x hx => by
        rw [hright _ (hψ x hx).1, (hψ x hx).2.1]
      open_source := isOpen_lt hnormc continuous_const
      open_target := hopenT
      contMDiffOn_toFun := ((hexpS.of_le hle).comp hι).contMDiffOn
      contMDiffOn_invFun := by
        intro x hx
        apply ContMDiffAt.contMDiffWithinAt
        have hψx : ContMDiffAt I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ x :=
          (hψs x hx).contMDiffAt (hopenT.mem_nhds hx)
        have hfootS : (ψ x).proj ∈ S := (hψ x hx).1.1
        have hσ : ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) (fun y => R (ψ y).proj) x :=
          (hRs _ hfootS).comp x ((Bundle.contMDiff_proj (TangentSpace I)).contMDiffAt.comp x hψx)
        refine contMDiffAt_of_iota_eq_tube g coe_sub_one_le_add_one_tube
          (WithTop.coe_le_coe.mpr le_top) ι hι b hιb hιlin hιnorm hσ hψx ?_
        filter_upwards [hopenT.mem_nhds hx] with y hy
        have hn := (hψ y hy).1
        refine ⟨hright _ hn, ?_⟩
        obtain ⟨s', hs'⟩ : (ψ y).proj ∈ range b := by rw [hbS]; exact hn.1
        apply hbinj
        rw [← hιb, hright _ hn, ← hs', hRb] }
  refine ⟨Φ, rfl, rfl, fun z => rfl, fun x hx => hright _ (hψ x hx).1, fun z hz => ?_⟩
  change ‖z.2‖ = infDist (g.expMap (ι z)) S
  rw [(hψexp (ι z) (hιν z) (by rw [hlen]; exact hz)).2, hlen]

end DifferentialGeometry.Geometry.FiniteSoul
