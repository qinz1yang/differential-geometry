import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyFinal_CX3
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

set_option autoImplicit false

/-! # CH12-S102 G1a: `exp(t X)` is a global diffeomorphism for small compactly supported `X`

`X` smooth, vanishing off a compact `D2 ⊆ A.cover`, `C¹`-`ε₀`-small w.r.t. the atlas `A`.  Then for
`|t| ≤ 2`, `scaledExp X t` is the identity off `D2`, a local diffeomorphism, injective (S15 gives
injectivity on a compact neighbourhood `D'` of `D2`; points leave `D2` by `< δ`), and surjective
(its range is clopen on a connected manifold). -/

noncomputable section
open scoped Manifold ContDiff Topology ENNReal
open Set Function Bundle Filter Metric

namespace GC.LongTime.Ch12
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Complete
variable [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [LocallyCompactSpace M]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)

omit [LocallyCompactSpace M] in
theorem scaledExp_zero_field_S102 (X : ∀ y : M, TangentSpace I y) (t : ℝ) {p : M}
    (hp : X p = 0) : scaledExp_S15 g hEnorm X t p = p := by
  simp only [scaledExp_S15, hp, smul_zero]
  exact expMapIntrinsic_zero g hEnorm p

omit [LocallyCompactSpace M] in
theorem contMDiff_scaledExp_slice_S102 (X : ∀ y : M, TangentSpace I y)
    (hX : ContMDiff I I.tangent ∞ (secBundle_S15 X)) (t : ℝ) :
    ContMDiff I I ∞ (scaledExp_S15 g hEnorm X t) :=
  contMDiff_scaledExp_S15 (J := I) g hEnorm (secBundle_S15 X) (fun _ => t) hX contMDiff_const

omit [FiniteDimensional ℝ E] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] [T2Space M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [PseudoEMetricSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [LocallyCompactSpace M] in
/-- a `C¹`-small field vanishing off `D2 ⊆ A.cover` has pointwise `g`-length `< ε`. -/
theorem tanLen_lt_of_CkSmall_S102 (A : CkAtlas_S15 I M) {D2 : Set M} (hD2A : D2 ⊆ A.cover)
    (X : ∀ y : M, TangentSpace I y) (hX0 : ∀ p, p ∉ D2 → X p = 0) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hsmall : CkSmall_S15 g A X k ε) (p : M) : tanLen_S15 g (secBundle_S15 X p) < ε := by
  by_cases hp : p ∈ D2
  · obtain ⟨i, hpi⟩ := mem_iUnion.mp (hD2A hp)
    have hxb : extChartAt I (A.ctr i) p ∈
        closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i) := ball_subset_closedBall hpi.2
    have h1 := (hsmall i _ hxb).1
    rwa [(extChartAt I (A.ctr i)).left_inv hpi.1] at h1
  · have h0 : secBundle_S15 X p = ⟨p, (0 : E)⟩ := by simp only [secBundle_S15, hX0 p hp]; rfl
    have : tanLen_S15 g (secBundle_S15 X p) = 0 := by
      rw [h0]
      have h00 : g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0 := by
        rw [(g.inner p).map_zero]; rfl
      change Real.sqrt (g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p)) = 0
      rw [h00, Real.sqrt_zero]
    rwa [this]

/-- **G1a.**  For `A` and compact `D2 ⊆ A.cover` there is `ε₀ > 0` such that for every smooth field
`X` vanishing off `D2` and `C¹`-`ε₀`-small, each `exp(t X)`, `|t| ≤ 2`, is a global diffeomorphism
(local diffeomorphism + bijective). -/
theorem scaledExp_global_S102 [ConnectedSpace M] (A : CkAtlas_S15 I M) {D2 : Set M}
    (hD2 : IsCompact D2) (hD2A : D2 ⊆ A.cover) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ X : (∀ y : M, TangentSpace I y),
      ContMDiff I I.tangent ∞ (secBundle_S15 X) → (∀ p, p ∉ D2 → X p = 0) →
      CkSmall_S15 g A X 1 ε₀ → ∀ t : ℝ, |t| ≤ 2 →
        IsLocalDiffeomorph I I ∞ (scaledExp_S15 g hEnorm X t) ∧
        (∀ x : M, Function.Injective (mfderiv I I (scaledExp_S15 g hEnorm X t) x)) ∧
        Function.Bijective (scaledExp_S15 g hEnorm X t) := by
  have hU : IsOpen A.cover := isOpen_iUnion fun i => A.isOpen_U i
  obtain ⟨D', hD'c, hD2D', hD'U⟩ := exists_compact_between hD2 hU hD2A
  obtain ⟨ε₁, hε₁, hgood⟩ := transfer_family_good_S15 g hEnorm A hD'c hD'U
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_riemannian_S15 (I := I) hD2
    (U := fun _ : Unit => interior D') (fun _ => isOpen_interior) (by rw [iUnion_const]; exact hD2D')
  obtain ⟨δ0, hδ0, hδ0le⟩ : ∃ δ0 : ℝ, 0 < δ0 ∧ ENNReal.ofReal δ0 ≤ δ := by
    rcases eq_top_or_lt_top δ with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨δ.toReal, ENNReal.toReal_pos hδ.ne' h.ne, by rw [ENNReal.ofReal_toReal h.ne]⟩
  refine ⟨min ε₁ (δ0 / 4), lt_min hε₁ (by linarith), ?_⟩
  intro X hX hX0 hsmall t ht
  have hε0 : 0 < min ε₁ (δ0 / 4) := lt_min hε₁ (by linarith)
  have hsmall1 : CkSmall_S15 g A X 1 ε₁ := CkSmall_mono_CX3 g hsmall le_rfl (min_le_left _ _)
  have hgt := hgood X hX hsmall1 t ht
  set Et := scaledExp_S15 g hEnorm X t with hEt
  have hsm : ContMDiff I I ∞ Et := contMDiff_scaledExp_slice_S102 g hEnorm X hX t
  have hid : ∀ p, p ∉ D2 → Et p = p := fun p hp =>
    scaledExp_zero_field_S102 g hEnorm X t (hX0 p hp)
  have hdist : ∀ p, Manifold.riemannianEDist I p (Et p) < δ := by
    intro p
    have hlen := tanLen_lt_of_CkSmall_S102 g A hD2A X hX0 hε0 hsmall p
    have hm : |t| * tanLen_S15 g (secBundle_S15 X p) ≤ 2 * (min ε₁ (δ0 / 4)) :=
      mul_le_mul ht hlen.le (Real.sqrt_nonneg _) (by norm_num)
    have h2 : 2 * (min ε₁ (δ0 / 4)) < δ0 := by
      have := min_le_right ε₁ (δ0 / 4); linarith
    refine lt_of_le_of_lt ((edist_scaledExp_le_S15 g hEnorm X t p).trans
      (ENNReal.ofReal_le_ofReal hm)) ?_
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hδ0).mpr h2) hδ0le
  have hmemD' : ∀ p ∈ D2, Et p ∈ D' := by
    intro p hp
    obtain ⟨_, _, h⟩ := hleb p hp (Et p) (hdist p)
    exact interior_subset h
  have hinj : Injective Et := by
    intro p q hpq
    have key : ∀ p q, p ∈ D' → q ∈ D' → Et p = Et q → p = q :=
      fun p q hp hq h => hgt.2 hp hq h
    by_cases hp : p ∈ D2
    · by_cases hq : q ∈ D2
      · exact key p q ((hD2D'.trans interior_subset) hp) ((hD2D'.trans interior_subset) hq) hpq
      · have hqE : q = Et p := by rw [hpq, hid q hq]
        exact key p q ((hD2D'.trans interior_subset) hp) (hqE ▸ hmemD' p hp) hpq
    · by_cases hq : q ∈ D2
      · have hpE : p = Et q := by rw [← hpq, hid p hp]
        exact key p q (hpE ▸ hmemD' q hq) ((hD2D'.trans interior_subset) hq) hpq
      · rw [← hid p hp, ← hid q hq, hpq]
  have himm : ∀ p, Injective (mfderiv I I Et p) := by
    intro p
    by_cases hp : p ∈ D2
    · exact hgt.1 p (hD2A hp)
    · have hev : Et =ᶠ[𝓝 p] id := by
        filter_upwards [hD2.isClosed.isOpen_compl.mem_nhds hp] with y hy
        exact hid y hy
      rw [hev.mfderiv_eq, mfderiv_id]
      exact fun a b h => h
  have hloc : IsLocalDiffeomorph I I ∞ Et :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv Et hsm himm rfl
  refine ⟨hloc, himm, hinj, ?_⟩
  have hclosed : IsClosed (range Et) := by
    have heq : range Et = Et '' D2 ∪ closure D2ᶜ := by
      apply Subset.antisymm
      · rintro _ ⟨x, rfl⟩
        by_cases hx : x ∈ D2
        · exact Or.inl ⟨x, hx, rfl⟩
        · exact Or.inr (by rw [hid x hx]; exact subset_closure hx)
      · rintro y (⟨x, _, rfl⟩ | hy)
        · exact ⟨x, rfl⟩
        · have hfix : closure D2ᶜ ⊆ {p | Et p = p} :=
            closure_minimal (fun p hp => hid p hp) (isClosed_eq hsm.continuous continuous_id)
          exact ⟨y, hfix hy⟩
    rw [heq]
    exact (hD2.image hsm.continuous).isClosed.union isClosed_closure
  have hclopen : IsClopen (range Et) := ⟨hclosed, hloc.isOpen_range⟩
  rcases isClopen_iff.mp hclopen with h | h
  · exact absurd h (Set.range_nonempty Et).ne_empty
  · exact range_eq_univ.mp h


end Complete

/-! ### the time clamp `φ`: smooth, `φ = id` near `[0,1]`, `|φ| ≤ 2` -/

/-- the bump with `1` on `[-1/2, 3/2]` and support in `(-1, 2)`. -/
def clampBump_S102 : ContDiffBump (1 / 2 : ℝ) := ⟨1, 3 / 2, one_pos, by norm_num⟩

/-- `φ t = t · b t`. -/
def clamp_S102 (t : ℝ) : ℝ := t * clampBump_S102 t

theorem contDiff_clamp_S102 : ContDiff ℝ ∞ clamp_S102 :=
  contDiff_id.mul clampBump_S102.contDiff

theorem contMDiff_clamp_S102 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ clamp_S102 :=
  contDiff_clamp_S102.contMDiff

theorem abs_clamp_le_S102 (t : ℝ) : |clamp_S102 t| ≤ 2 := by
  by_cases h : clampBump_S102.rOut ≤ dist t (1 / 2 : ℝ)
  · rw [clamp_S102, clampBump_S102.zero_of_le_dist h]; simp
  · have h' : dist t (1 / 2 : ℝ) < 3 / 2 := not_le.mp h
    rw [Real.dist_eq, abs_lt] at h'
    rw [clamp_S102, abs_mul, abs_of_nonneg (clampBump_S102.nonneg)]
    have h1 := clampBump_S102.le_one (x := t)
    have h2 : |t| ≤ 2 := abs_le.mpr ⟨by linarith [h'.1], by linarith [h'.2]⟩
    nlinarith [abs_nonneg t, clampBump_S102.nonneg (x := t)]

theorem clamp_eq_self_S102 {t : ℝ} (ht : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) : clamp_S102 t = t := by
  have : clampBump_S102 t = 1 := by
    apply clampBump_S102.one_of_mem_closedBall
    rw [mem_closedBall, Real.dist_eq, abs_le]
    change -1 ≤ t - 1 / 2 ∧ t - 1 / 2 ≤ 1
    constructor <;> linarith [ht.1, ht.2]
  rw [clamp_S102, this, mul_one]

theorem clamp_eventuallyEq_id_S102 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    clamp_S102 =ᶠ[𝓝 t] id := by
  filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo (-1 / 2 : ℝ) (3 / 2) from
    ⟨by linarith [ht.1], by linarith [ht.2]⟩)] with s hs
  exact clamp_eq_self_S102 hs

theorem clamp_zero_S102 : clamp_S102 0 = 0 := by simp [clamp_S102]

section Family
variable [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [LocallyCompactSpace M]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)

/-- the skew product `Θ (μ, x) = (μ, exp_x (φ μ • X x))` on `ℝ × M`. -/
def thetaMap_S102 (X : ∀ y : M, TangentSpace I y) : ℝ × M → ℝ × M :=
  fun q => (q.1, scaledExp_S15 g hEnorm X (clamp_S102 q.1) q.2)

omit [LocallyCompactSpace M] in
theorem contMDiff_thetaS_S102 (X : ∀ y : M, TangentSpace I y)
    (hX : ContMDiff I I.tangent ∞ (secBundle_S15 X)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => scaledExp_S15 g hEnorm X (clamp_S102 q.1) q.2) :=
  contMDiff_scaledExp_S15 (J := 𝓘(ℝ, ℝ).prod I) g hEnorm
    (fun q : ℝ × M => secBundle_S15 X q.2) (fun q : ℝ × M => clamp_S102 q.1)
    (hX.comp contMDiff_snd) (contMDiff_clamp_S102.comp contMDiff_fst)

omit [LocallyCompactSpace M] in
theorem contMDiff_thetaMap_S102 (X : ∀ y : M, TangentSpace I y)
    (hX : ContMDiff I I.tangent ∞ (secBundle_S15 X)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ (thetaMap_S102 g hEnorm X) :=
  contMDiff_fst.prodMk (contMDiff_thetaS_S102 g hEnorm X hX)

omit [LocallyCompactSpace M] in
theorem thetaMap_mfderiv_injective_S102 (X : ∀ y : M, TangentSpace I y)
    (hX : ContMDiff I I.tangent ∞ (secBundle_S15 X))
    (hmf : ∀ μ : ℝ, |μ| ≤ 2 → ∀ x : M,
      Injective (mfderiv I I (scaledExp_S15 g hEnorm X μ) x)) (q : ℝ × M) :
    Injective (mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (thetaMap_S102 g hEnorm X) q) := by
  obtain ⟨μ, x⟩ := q
  have hS := contMDiff_thetaS_S102 g hEnorm X hX
  have hmd : mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (thetaMap_S102 g hEnorm X) (μ, x) =
      (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (@Prod.fst ℝ M) (μ, x)).prod
        (mfderiv (𝓘(ℝ, ℝ).prod I) I
          (fun q : ℝ × M => scaledExp_S15 g hEnorm X (clamp_S102 q.1) q.2) (μ, x)) :=
    mfderiv_prodMk (mdifferentiableAt_fst) (hS.mdifferentiableAt (by simp))
  rw [injective_iff_map_eq_zero]
  intro w hw
  rw [hmd, mfderiv_fst] at hw
  have hw' : (w.1, (mfderiv (𝓘(ℝ, ℝ).prod I) I
      (fun q : ℝ × M => scaledExp_S15 g hEnorm X (clamp_S102 q.1) q.2) (μ, x)) w) =
      ((0 : ℝ), (0 : TangentSpace I (scaledExp_S15 g hEnorm X (clamp_S102 μ) x))) := hw
  obtain ⟨h1, h2⟩ := Prod.mk.inj hw'
  have hι : mfderiv I (𝓘(ℝ, ℝ).prod I) (fun y : M => (μ, y)) x =
      (mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => μ) x).prod (mfderiv I I (@id M) x) :=
    mfderiv_prodMk mdifferentiableAt_const mdifferentiableAt_id
  have hιw : mfderiv I (𝓘(ℝ, ℝ).prod I) (fun y : M => (μ, y)) x w.2 = w := by
    rw [hι, mfderiv_const, mfderiv_id]
    refine Prod.ext ?_ rfl
    change (0 : ℝ) = w.1
    exact h1.symm
  have hcomp : mfderiv I I (scaledExp_S15 g hEnorm X (clamp_S102 μ)) x =
      (mfderiv (𝓘(ℝ, ℝ).prod I) I
        (fun q : ℝ × M => scaledExp_S15 g hEnorm X (clamp_S102 q.1) q.2) (μ, x)).comp
        (mfderiv I (𝓘(ℝ, ℝ).prod I) (fun y : M => (μ, y)) x) :=
    mfderiv_comp x (hS.mdifferentiableAt (by simp))
      ((contMDiff_const.prodMk contMDiff_id :
        ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => (μ, y))).mdifferentiableAt (by simp))
  have h3 : mfderiv I I (scaledExp_S15 g hEnorm X (clamp_S102 μ)) x w.2 = 0 := by
    rw [hcomp]
    change (mfderiv (𝓘(ℝ, ℝ).prod I) I
      (fun q : ℝ × M => scaledExp_S15 g hEnorm X (clamp_S102 q.1) q.2) (μ, x))
        (mfderiv I (𝓘(ℝ, ℝ).prod I) (fun y : M => (μ, y)) x w.2) = 0
    rw [hιw]; exact h2
  have h4 : w.2 = 0 :=
    (injective_iff_map_eq_zero _).mp (hmf (clamp_S102 μ) (abs_clamp_le_S102 μ) x) w.2 h3
  exact Prod.ext h1 h4

/-- **G1b.**  For small compactly supported `X`, the family of inverses of `exp(φ(μ) X)` is
jointly smooth in `(μ, y)`. -/
theorem exists_inverse_family_S102 [ConnectedSpace M] (A : CkAtlas_S15 I M) {D2 : Set M}
    (hD2 : IsCompact D2) (hD2A : D2 ⊆ A.cover) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ X : (∀ y : M, TangentSpace I y),
      ContMDiff I I.tangent ∞ (secBundle_S15 X) → (∀ p, p ∉ D2 → X p = 0) →
      CkSmall_S15 g A X 1 ε₀ →
      ∃ G : ℝ → M → M, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => G q.1 q.2) ∧
        (∀ μ x, G μ (scaledExp_S15 g hEnorm X (clamp_S102 μ) x) = x) ∧
        (∀ μ y, scaledExp_S15 g hEnorm X (clamp_S102 μ) (G μ y) = y) := by
  obtain ⟨ε₀, hε₀, hglob⟩ := scaledExp_global_S102 g hEnorm A hD2 hD2A
  refine ⟨ε₀, hε₀, fun X hX hX0 hsmall => ?_⟩
  have hall := fun t (ht : |t| ≤ 2) => hglob X hX hX0 hsmall t ht
  have hbij : Bijective (thetaMap_S102 g hEnorm X) := by
    constructor
    · rintro ⟨μ, x⟩ ⟨μ', x'⟩ h
      have h1 : μ = μ' := congrArg Prod.fst h
      subst h1
      have h2 : scaledExp_S15 g hEnorm X (clamp_S102 μ) x =
          scaledExp_S15 g hEnorm X (clamp_S102 μ) x' := congrArg Prod.snd h
      rw [(hall _ (abs_clamp_le_S102 μ)).2.2.1 h2]
    · rintro ⟨μ, y⟩
      obtain ⟨x, hx⟩ := (hall _ (abs_clamp_le_S102 μ)).2.2.2 y
      exact ⟨(μ, x), by simp only [thetaMap_S102, hx]⟩
  have hloc : IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ (thetaMap_S102 g hEnorm X) :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
      (contMDiff_thetaMap_S102 g hEnorm X hX)
      (thetaMap_mfderiv_injective_S102 g hEnorm X hX
        (fun μ hμ x => (hall μ hμ).2.1 x)) rfl
  let Td := hloc.diffeomorphOfBijective hbij
  have hTd : ∀ q, Td q = thetaMap_S102 g hEnorm X q := fun q => rfl
  have hfst : ∀ μ y, (Td.symm (μ, y)).1 = μ := by
    intro μ y
    have := hTd (Td.symm (μ, y))
    rw [Td.apply_symm_apply] at this
    exact (congrArg Prod.fst this).symm
  refine ⟨fun μ y => (Td.symm (μ, y)).2,
    contMDiff_snd.comp (Td.symm.contMDiff.comp (contMDiff_fst.prodMk contMDiff_snd)), ?_, ?_⟩
  · intro μ x
    have : Td (μ, x) = (μ, scaledExp_S15 g hEnorm X (clamp_S102 μ) x) := rfl
    have h2 := Td.symm_apply_apply (μ, x)
    rw [this] at h2
    exact congrArg Prod.snd h2
  · intro μ y
    have h2 := hTd (Td.symm (μ, y))
    rw [Td.apply_symm_apply] at h2
    have h3 := congrArg Prod.snd h2
    simp only [thetaMap_S102, hfst] at h3
    exact h3.symm

end Family
end GC.LongTime.Ch12
