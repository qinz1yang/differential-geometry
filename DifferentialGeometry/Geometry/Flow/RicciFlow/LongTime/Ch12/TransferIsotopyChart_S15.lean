import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyCalc_S15
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyInverse_S15
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyExp_S15
import DifferentialGeometry.Geometry.Exponential.Trivialization
import DifferentialGeometry.Geometry.Comparison.Convexity.Geodesic

/-!
# CH12-S15, H1 group D (charts): coordinate expression of the transfer isotopy
-/

set_option autoImplicit false
open scoped Manifold ContDiff Topology ENNReal
open Set Function Bundle Filter Metric
noncomputable section
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
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)

/-- `Ξ_c (y, w) = exp_y (e_c⁻¹ (y, w))`, the exponential map in the trivialization at `c`. -/
def chartExp_S15 (c : M) (z : M × E) : M :=
  expMapIntrinsic g hEnorm z.1 ((trivializationAt E (TangentSpace I) c).symmL ℝ z.1 z.2)

/-- coordinate expression `ψ_c (x, w) = ext_c (Ξ_c (ext_c⁻¹ x, w))`. -/
def chartPsi_S15 (c : M) (z : E × E) : E :=
  extChartAt I c (chartExp_S15 g hEnorm c ((extChartAt I c).symm z.1, z.2))

/-- the open set where `ψ_c` is smooth: `x` in the chart and the output in the chart. -/
def chartDom_S15 (c : M) : Set (E × E) :=
  {z | z.1 ∈ (extChartAt I c).target ∧
    chartExp_S15 g hEnorm c ((extChartAt I c).symm z.1, z.2) ∈ (extChartAt I c).source}

theorem chartExp_contMDiffOn_S15 (c : M) :
    ContMDiffOn (I.prod 𝓘(ℝ, E)) I ∞ (chartExp_S15 g hEnorm c)
      (trivializationAt E (TangentSpace I) c).target :=
  contMDiffOn_expMapIntrinsic_trivialization g hEnorm _

theorem chartExp_zero_S15 (c : M) (y : M) :
    chartExp_S15 g hEnorm c (y, 0) = y := by
  simp only [chartExp_S15, map_zero]
  exact expMapIntrinsic_zero g hEnorm y


theorem baseSet_eq_source_S15 (c : M) :
    (trivializationAt E (TangentSpace I) c).baseSet = (extChartAt I c).source := by
  rw [TangentBundle.trivializationAt_baseSet, extChartAt_source]

theorem chartLift_contMDiffOn_S15 (c : M) :
    ContMDiffOn 𝓘(ℝ, E × E) (I.prod 𝓘(ℝ, E)) ∞
      (fun z : E × E => ((extChartAt I c).symm z.1, z.2)) ((extChartAt I c).target ×ˢ univ) := by
  have h1 : ContMDiffOn 𝓘(ℝ, E × E) I ∞ (fun z : E × E => (extChartAt I c).symm z.1)
      ((extChartAt I c).target ×ˢ univ) :=
    (contMDiffOn_extChartAt_symm c).comp (contDiff_fst.contMDiff.contMDiffOn)
      (fun z hz => hz.1)
  exact h1.prodMk (contDiff_snd.contMDiff.contMDiffOn)

theorem chartLift_mapsTo_S15 (c : M) :
    MapsTo (fun z : E × E => ((extChartAt I c).symm z.1, z.2)) ((extChartAt I c).target ×ˢ univ)
      (trivializationAt E (TangentSpace I) c).target := by
  intro z hz
  rw [Bundle.Trivialization.target_eq, baseSet_eq_source_S15]
  exact ⟨(extChartAt I c).map_target hz.1, trivial⟩

theorem chartDom_isOpen_S15 (c : M) : IsOpen (chartDom_S15 g hEnorm (I := I) c) := by
  have hc : ContinuousOn (fun z : E × E =>
      chartExp_S15 g hEnorm c ((extChartAt I c).symm z.1, z.2))
      ((extChartAt I c).target ×ˢ univ) :=
    ((chartExp_contMDiffOn_S15 g hEnorm c).comp (chartLift_contMDiffOn_S15 c)
      (chartLift_mapsTo_S15 c)).continuousOn
  have := hc.isOpen_inter_preimage ((isOpen_extChartAt_target (I := I) c).prod isOpen_univ)
    (isOpen_extChartAt_source (I := I) c)
  convert this using 1
  ext z
  simp only [chartDom_S15, mem_setOf_eq, mem_inter_iff, mem_prod, mem_univ, and_true, mem_preimage]

theorem chartPsi_contDiffOn_S15 (c : M) :
    ContDiffOn ℝ ∞ (chartPsi_S15 g hEnorm c) (chartDom_S15 g hEnorm (I := I) c) := by
  have h1 : ContMDiffOn 𝓘(ℝ, E × E) I ∞ (fun z : E × E =>
      chartExp_S15 g hEnorm c ((extChartAt I c).symm z.1, z.2))
      ((extChartAt I c).target ×ˢ univ) :=
    (chartExp_contMDiffOn_S15 g hEnorm c).comp (chartLift_contMDiffOn_S15 c)
      (chartLift_mapsTo_S15 c)
  have h2 : ContMDiffOn 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞ (chartPsi_S15 g hEnorm c)
      (chartDom_S15 g hEnorm (I := I) c) := by
    have hext : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I c) (extChartAt I c).source :=
      by rw [extChartAt_source]; exact contMDiffOn_extChartAt
    refine hext.comp (h1.mono ?_) ?_
    · intro z hz; exact ⟨hz.1, trivial⟩
    · intro z hz; simpa [extChartAt_source] using hz.2
  exact contMDiffOn_iff_contDiffOn.mp h2

theorem chartPsi_zero_S15 (c : M) {x : E} (hx : x ∈ (extChartAt I c).target) :
    chartPsi_S15 g hEnorm c (x, 0) = x := by
  simp only [chartPsi_S15, chartExp_zero_S15]
  exact (extChartAt I c).right_inv hx

theorem chartDom_zero_S15 (c : M) {x : E} (hx : x ∈ (extChartAt I c).target) :
    (x, (0 : E)) ∈ chartDom_S15 g hEnorm (I := I) c := by
  refine ⟨hx, ?_⟩
  rw [chartExp_zero_S15]
  exact (extChartAt I c).map_target hx


/-- a vector field `X` as a map `M → TM`. -/
def secBundle_S15 (X : ∀ y : M, TangentSpace I y) : M → TangentBundle I M := fun y => ⟨y, X y⟩

/-- the vector field `X` in the trivialization at `c`, read in the chart at `c`. -/
def coordSec_S15 (c : M) (X : ∀ y : M, TangentSpace I y) : E → E := fun x =>
  ((trivializationAt E (TangentSpace I) c) (secBundle_S15 X ((extChartAt I c).symm x))).2

/-- the isotopy `y ↦ exp_y (μ • X y)`. -/
def scaledExp_S15 (X : ∀ y : M, TangentSpace I y) (μ : ℝ) : M → M :=
  fun y => expMapIntrinsic g hEnorm y (μ • X y)

theorem coordSec_contDiffOn_S15 (c : M) (X : ∀ y : M, TangentSpace I y)
    (hX : ContMDiff I I.tangent ∞ (secBundle_S15 X)) :
    ContDiffOn ℝ ∞ (coordSec_S15 c X) (extChartAt I c).target := by
  have h1 : ContMDiffOn 𝓘(ℝ, E) I.tangent ∞
      (fun x : E => secBundle_S15 X ((extChartAt I c).symm x)) (extChartAt I c).target :=
    hX.comp_contMDiffOn (contMDiffOn_extChartAt_symm c)
  have he : ContMDiffOn I.tangent (I.prod 𝓘(ℝ, E)) ∞ (trivializationAt E (TangentSpace I) c)
      (trivializationAt E (TangentSpace I) c).source :=
    (trivializationAt E (TangentSpace I) c).contMDiffOn
  have h2 := he.comp h1 (fun x hx => by
    refine ((trivializationAt E (TangentSpace I) c).mem_source).mpr ?_
    rw [baseSet_eq_source_S15]
    exact (extChartAt I c).map_target hx)
  have h3 := contMDiff_snd.comp_contMDiffOn h2
  exact contMDiffOn_iff_contDiffOn.mp h3

theorem scaledExp_coord_S15 (c : M) (X : ∀ y : M, TangentSpace I y) (μ : ℝ) {x : E}
    (hx : x ∈ (extChartAt I c).target) :
    scaledExp_S15 g hEnorm X μ ((extChartAt I c).symm x) =
      chartExp_S15 g hEnorm c ((extChartAt I c).symm x, μ • coordSec_S15 c X x) := by
  set p := (extChartAt I c).symm x with hp
  have hpb : p ∈ (trivializationAt E (TangentSpace I) c).baseSet := by
    rw [baseSet_eq_source_S15]; exact (extChartAt I c).map_target hx
  have hcoord : coordSec_S15 c X x = (trivializationAt E (TangentSpace I) c).continuousLinearMapAt ℝ p (X p) := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ (trivializationAt E (TangentSpace I) c) hpb]; rfl
  simp only [chartExp_S15, scaledExp_S15]
  rw [hcoord, ← map_smul, Bundle.Trivialization.symmL_continuousLinearMapAt _ hpb]

theorem scaledExp_ext_S15 (c : M) (X : ∀ y : M, TangentSpace I y) (μ : ℝ) {x : E}
    (hx : x ∈ (extChartAt I c).target) :
    extChartAt I c (scaledExp_S15 g hEnorm X μ ((extChartAt I c).symm x)) =
      chartPsi_S15 g hEnorm c (x, μ • coordSec_S15 c X x) := by
  rw [scaledExp_coord_S15 g hEnorm c X μ hx]; rfl


theorem contMDiff_scaledExp_fam_S15 (X : ∀ y : M, TangentSpace I y)
    (hX : ContMDiff I I.tangent ∞ (secBundle_S15 X)) (μ : ℝ) :
    ContMDiff I I ∞ (scaledExp_S15 g hEnorm X μ) :=
  contMDiff_scaledExp_S15 g hEnorm (secBundle_S15 X) (fun _ => μ) hX contMDiff_const

theorem fderiv_injective_of_close_S15 {L : E →L[ℝ] E}
    (hLb : ‖L - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) : Function.Injective L := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h1 : ‖v‖ ≤ 1 / 2 * ‖v‖ := by
    have : (L - ContinuousLinearMap.id ℝ E) v = -v := by
      have hv' : L v = 0 := hv
      simp [hv']
    calc ‖v‖ = ‖(L - ContinuousLinearMap.id ℝ E) v‖ := by rw [this, norm_neg]
      _ ≤ ‖L - ContinuousLinearMap.id ℝ E‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 / 2 * ‖v‖ := mul_le_mul_of_nonneg_right hLb (norm_nonneg _)
  have : ‖v‖ ≤ 0 := by linarith
  exact norm_le_zero_iff.mp this

/-- **immersion from the coordinate estimate.** -/
theorem scaledExp_immersion_S15 (c : M) (X : ∀ y : M, TangentSpace I y)
    (hX : ContMDiff I I.tangent ∞ (secBundle_S15 X)) (μ : ℝ) {x : E}
    (hx : x ∈ (extChartAt I c).target) {L : E →L[ℝ] E}
    (hL : HasFDerivAt (fun y => chartPsi_S15 g hEnorm c (y, μ • coordSec_S15 c X y)) L x)
    (hLb : ‖L - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2)
    (hq : scaledExp_S15 g hEnorm X μ ((extChartAt I c).symm x) ∈ (extChartAt I c).source) :
    Function.Injective (mfderiv I I (scaledExp_S15 g hEnorm X μ) ((extChartAt I c).symm x)) := by
  set p := (extChartAt I c).symm x with hp
  set F := scaledExp_S15 g hEnorm X μ with hF
  have hpS : p ∈ (extChartAt I c).source := (extChartAt I c).map_target hx
  have hFd : MDifferentiableAt I I F p :=
    ((contMDiff_scaledExp_fam_S15 g hEnorm X hX μ) p).mdifferentiableAt (by simp)
  have hqS : F p ∈ (chartAt H c).source := by rwa [extChartAt_source] at hq
  have hpS' : p ∈ (chartAt H c).source := by rwa [extChartAt_source] at hpS
  have hextq : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I c) (F p) := mdifferentiableAt_extChartAt hqS
  have hextp : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I c) p := mdifferentiableAt_extChartAt hpS'
  set G : E → E := fun y => chartPsi_S15 g hEnorm c (y, μ • coordSec_S15 c X y) with hG
  have hextpx : extChartAt I c p = x := (extChartAt I c).right_inv hx
  have hLd : HasFDerivAt G L (extChartAt I c p) := by rw [hextpx]; exact hL
  have hGd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) G (extChartAt I c p) := hLd.differentiableAt.mdifferentiableAt
  have h1 : mfderiv I 𝓘(ℝ, E) (fun y => extChartAt I c (F y)) p =
      (mfderiv I 𝓘(ℝ, E) (extChartAt I c) (F p)).comp (mfderiv I I F p) :=
    mfderiv_comp p hextq hFd
  have hev : (fun y => extChartAt I c (F y)) =ᶠ[𝓝 p] (G ∘ extChartAt I c) := by
    filter_upwards [(isOpen_extChartAt_source (I := I) c).mem_nhds hpS] with y hy
    have := scaledExp_ext_S15 g hEnorm c X μ (x := extChartAt I c y) ((extChartAt I c).map_source hy)
    rw [(extChartAt I c).left_inv hy] at this
    exact this
  have h2 : mfderiv I 𝓘(ℝ, E) (fun y => extChartAt I c (F y)) p =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) G (extChartAt I c p)).comp (mfderiv I 𝓘(ℝ, E) (extChartAt I c) p) := by
    rw [hev.mfderiv_eq]
    exact mfderiv_comp p hGd hextp
  have hGm : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) G (extChartAt I c p) = L := by
    rw [mfderiv_eq_fderiv]; exact hLd.fderiv
  have hinj1 : Function.Injective (mfderiv I 𝓘(ℝ, E) (extChartAt I c) p) :=
    (isInvertible_mfderiv_extChartAt hpS).bijective.1
  have hinj2 : Function.Injective
      ((mfderiv I 𝓘(ℝ, E) (extChartAt I c) (F p)).comp (mfderiv I I F p)) := by
    rw [h1.symm.trans h2, hGm]
    exact (fderiv_injective_of_close_S15 hLb).comp hinj1
  exact Function.Injective.of_comp hinj2


end Complete

/-- A fixed finite compact atlas: finitely many chart balls `closedBall x_i r_i` inside the chart
targets.  It is chosen before `Φ` and before `ε`. -/
structure CkAtlas_S15 (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] where
  n : ℕ
  ctr : Fin n → M
  rad : Fin n → ℝ
  closedBall_sub : ∀ i, closedBall (extChartAt I (ctr i) (ctr i)) (rad i) ⊆
    (extChartAt I (ctr i)).target

/-- the open chart ball `U_i` of the atlas -/
def CkAtlas_S15.U {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (A : CkAtlas_S15 I M) (i : Fin A.n) : Set M :=
  (extChartAt I (A.ctr i)).source ∩
    extChartAt I (A.ctr i) ⁻¹' ball (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i)

/-- the union of the chart balls -/
def CkAtlas_S15.cover {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (A : CkAtlas_S15 I M) : Set M := ⋃ i, A.U i

theorem CkAtlas_S15.isOpen_U {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (A : CkAtlas_S15 I M) (i : Fin A.n) : IsOpen (A.U i) :=
  by
    unfold CkAtlas_S15.U
    rw [extChartAt_source]
    exact isOpen_extChartAt_preimage (I := I) (A.ctr i) isOpen_ball

section Complete2
variable [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [LocallyCompactSpace M]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)

/-- **`C^k`-smallness of the vector field `X` with respect to the fixed atlas `A`**: the `g`-length
of `X` and the first `k` derivatives of its coordinate expression in the trivialization at each
chart centre are `< ε` on the chart balls. -/
def CkSmall_S15 (A : CkAtlas_S15 I M) (X : ∀ y : M, TangentSpace I y) (k : ℕ) (ε : ℝ) : Prop :=
  ∀ i, ∀ x ∈ closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i),
    tanLen_S15 g (secBundle_S15 X ((extChartAt I (A.ctr i)).symm x)) < ε ∧
    ∀ j ≤ k, ‖iteratedFDeriv ℝ j (coordSec_S15 (A.ctr i) X) x‖ < ε


theorem edist_scaledExp_le_S15 (X : ∀ y : M, TangentSpace I y) (μ : ℝ) (p : M) :
    Manifold.riemannianEDist I p (scaledExp_S15 g hEnorm X μ p) ≤
      ENNReal.ofReal (|μ| * tanLen_S15 g (secBundle_S15 X p)) := by
  have h := intrinsicGeodesic_riemannianEDist_le_radius (I := I) g hEnorm p (μ • X p)
    (t := 1) zero_le_one
  have h2 : tanLen_S15 g (⟨p, μ • X p⟩ : TangentBundle I M) =
      |μ| * tanLen_S15 g (secBundle_S15 X p) := tanLen_smul_S15 g p μ (X p)
  rw [mul_one] at h
  simp only [scaledExp_S15, expMapIntrinsic_def]
  refine h.trans (le_of_eq ?_)
  rw [← h2]; rfl

/-- Lebesgue number lemma for the Riemannian distance (no metric-space topology needed). -/
theorem lebesgue_riemannian_S15 [RegularSpace M] {ι : Type*} {D : Set M} (hD : IsCompact D)
    {U : ι → Set M} (hU : ∀ i, IsOpen (U i)) (hDU : D ⊆ ⋃ i, U i) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ p ∈ D, ∀ q : M, Manifold.riemannianEDist I p q < δ →
      ∃ i, p ∈ U i ∧ q ∈ U i := by
  have hc : ∀ x ∈ D, ∃ c : ℝ≥0∞, 0 < c ∧ ∃ i, {y | Manifold.riemannianEDist I x y < c} ⊆ U i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hDU hx)
    obtain ⟨c, hc, hsub⟩ := setOfPred_riemannianEDist_lt_subset_nhds' I ((hU i).mem_nhds hi)
    exact ⟨c, hc, i, hsub⟩
  choose! c hcpos hci using hc
  have hnb : ∀ x ∈ D, {y | Manifold.riemannianEDist I x y < c x / 2} ∈ 𝓝 x := by
    intro x hx
    exact eventually_riemannianEDist_lt I x (ENNReal.half_pos (hcpos x hx).ne')
  obtain ⟨t, htcov⟩ := hD.elim_nhds_subcover' (fun x _ => {y | Manifold.riemannianEDist I x y < c x / 2})
    (fun x hx => hnb x hx)
  refine ⟨t.inf (fun x : D => c x / 2), ?_, ?_⟩
  · exact (Finset.lt_inf_iff ENNReal.zero_lt_top).mpr (fun x _ => ENNReal.half_pos (hcpos x x.2).ne')
  · intro p hp q hpq
    obtain ⟨x, hxt, hpx⟩ := mem_iUnion₂.mp (htcov hp)
    have hle : t.inf (fun x : D => c x / 2) ≤ c x / 2 := Finset.inf_le hxt
    obtain ⟨i, hi⟩ := hci x x.2
    refine ⟨i, hi ?_, hi ?_⟩
    · exact lt_of_lt_of_le hpx (ENNReal.half_le_self)
    · calc Manifold.riemannianEDist I (x : M) q
          ≤ Manifold.riemannianEDist I (x : M) p + Manifold.riemannianEDist I p q :=
            Manifold.riemannianEDist_triangle
        _ < c x / 2 + c x / 2 := ENNReal.add_lt_add hpx (lt_of_lt_of_le hpq hle)
        _ = c x := ENNReal.add_halves _

theorem exists_pos_forall_le_fin_S15 (n : ℕ) (e : Fin n → ℝ) (he : ∀ i, 0 < e i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i, ρ ≤ e i := by
  obtain ⟨ρ, hρ, h⟩ := exists_pos_le_finset_S15 (Finset.univ : Finset (Fin n)) e he
  exact ⟨ρ, hρ, fun i => h i (Finset.mem_univ i)⟩

/-- **H1-D (i)+(ii).**  For a fixed atlas `A` and compact `D ⊆ A.cover` there is `ε > 0` such that for
every smooth vector field `X` that is `C¹`-`ε`-small (w.r.t. `A`), every `exp(μ X)`, `|μ| ≤ 2`, is an
immersion on `A.cover` and injective on `D`. -/
theorem transfer_family_good_S15 (A : CkAtlas_S15 I M) {D : Set M} (hD : IsCompact D)
    (hDA : D ⊆ A.cover) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ X : (∀ y : M, TangentSpace I y),
      ContMDiff I I.tangent ∞ (secBundle_S15 X) → CkSmall_S15 g A X 1 ε →
      ∀ μ : ℝ, |μ| ≤ 2 →
        (∀ p ∈ A.cover, Function.Injective (mfderiv I I (scaledExp_S15 g hEnorm X μ) p)) ∧
        InjOn (scaledExp_S15 g hEnorm X μ) D := by
  have hcalc : ∀ i : Fin A.n, ∃ e : ℝ, 0 < e ∧ ∀ cc : E → E,
      ContDiffOn ℝ 1 cc (extChartAt I (A.ctr i)).target →
      (∀ x ∈ closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i),
        ‖cc x‖ ≤ e ∧ ‖fderiv ℝ cc x‖ ≤ e) → ∀ μ : ℝ, |μ| ≤ 2 →
      (∀ x ∈ closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i),
        (x, μ • cc x) ∈ chartDom_S15 g hEnorm (I := I) (A.ctr i)) ∧
      (∀ x ∈ closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i), ∃ L : E →L[ℝ] E,
        HasFDerivAt (fun y => chartPsi_S15 g hEnorm (A.ctr i) (y, μ • cc y)) L x ∧
          ‖L - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) ∧
      (∀ x ∈ closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i),
        ∀ y ∈ closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i),
        ‖x - y‖ ≤ 2 * ‖chartPsi_S15 g hEnorm (A.ctr i) (x, μ • cc x) -
          chartPsi_S15 g hEnorm (A.ctr i) (y, μ • cc y)‖) := fun i =>
    calc_C1_small_S15 (chartDom_isOpen_S15 g hEnorm (A.ctr i)) (isOpen_extChartAt_target (A.ctr i))
      ((chartPsi_contDiffOn_S15 g hEnorm (A.ctr i)).of_le (by exact_mod_cast le_top))
      (A.closedBall_sub i) (fun x hx => chartPsi_zero_S15 g hEnorm (A.ctr i) hx)
      (fun x hx => chartDom_zero_S15 g hEnorm (A.ctr i) hx)
  choose e he hcalc using hcalc
  obtain ⟨ε0, hε0, hε0le⟩ := exists_pos_forall_le_fin_S15 A.n e he
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_riemannian_S15 (I := I) hD (fun i => A.isOpen_U i)
    (by simpa [CkAtlas_S15.cover] using hDA)
  obtain ⟨δ0, hδ0, hδ0le⟩ : ∃ δ0 : ℝ, 0 < δ0 ∧ ENNReal.ofReal δ0 ≤ δ := by
    rcases eq_top_or_lt_top δ with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨δ.toReal, ENNReal.toReal_pos hδ.ne' h.ne, by rw [ENNReal.ofReal_toReal h.ne]⟩
  refine ⟨min ε0 (δ0 / 8), lt_min hε0 (by linarith), ?_⟩
  intro X hX hsmall μ hμ
  set ε := min ε0 (δ0 / 8) with hε
  have hεpos : 0 < ε := lt_min hε0 (by linarith)
  have hε1 : ε ≤ ε0 := min_le_left _ _
  have hε2 : ε ≤ δ0 / 8 := min_le_right _ _
  have hcoord : ∀ i, ∀ x ∈ closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i),
      ‖coordSec_S15 (A.ctr i) X x‖ ≤ e i ∧ ‖fderiv ℝ (coordSec_S15 (A.ctr i) X) x‖ ≤ e i := by
    intro i x hx
    have h0 := (hsmall i x hx).2 0 (by norm_num)
    have h1 := (hsmall i x hx).2 1 le_rfl
    rw [norm_iteratedFDeriv_zero] at h0
    have h1' : ‖fderiv ℝ (coordSec_S15 (A.ctr i) X) x‖ < ε := by
      have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := coordSec_S15 (A.ctr i) X) (x := x) (n := 0)
      rw [norm_iteratedFDeriv_zero] at this
      rw [this]; exact h1
    exact ⟨(h0.trans_le (hε1.trans (hε0le i))).le, (h1'.trans_le (hε1.trans (hε0le i))).le⟩
  have hres := fun i => hcalc i (coordSec_S15 (A.ctr i) X)
    ((coordSec_contDiffOn_S15 (A.ctr i) X hX).of_le (by exact_mod_cast le_top)) (hcoord i) μ hμ
  constructor
  · intro p hp
    obtain ⟨i, hpi⟩ := mem_iUnion.mp hp
    have hpS : p ∈ (extChartAt I (A.ctr i)).source := hpi.1
    set x := extChartAt I (A.ctr i) p with hx
    have hxb : x ∈ closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i) :=
      ball_subset_closedBall hpi.2
    have hxT : x ∈ (extChartAt I (A.ctr i)).target := (extChartAt I (A.ctr i)).map_source hpS
    have hpx : (extChartAt I (A.ctr i)).symm x = p := (extChartAt I (A.ctr i)).left_inv hpS
    obtain ⟨L, hL, hLb⟩ := (hres i).2.1 x hxb
    have hq : scaledExp_S15 g hEnorm X μ ((extChartAt I (A.ctr i)).symm x) ∈
        (extChartAt I (A.ctr i)).source := by
      rw [scaledExp_coord_S15 g hEnorm _ X μ hxT]
      exact ((hres i).1 x hxb).2
    have := scaledExp_immersion_S15 g hEnorm (A.ctr i) X hX μ hxT hL hLb hq
    rwa [hpx] at this
  · intro p hpD q hqD hpq
    have hpA := hDA hpD
    obtain ⟨j, hpj⟩ := mem_iUnion.mp hpA
    have hqA := hDA hqD
    obtain ⟨j2, hqj2⟩ := mem_iUnion.mp hqA
    have hlen : ∀ (k : Fin A.n) (y : M), y ∈ A.U k →
        Manifold.riemannianEDist I y (scaledExp_S15 g hEnorm X μ y) ≤ ENNReal.ofReal (2 * ε) := by
      intro k y hyk
      have hxb : extChartAt I (A.ctr k) y ∈
          closedBall (extChartAt I (A.ctr k) (A.ctr k)) (A.rad k) :=
        ball_subset_closedBall hyk.2
      have h1 := (hsmall k _ hxb).1
      have hli := (extChartAt I (A.ctr k)).left_inv hyk.1
      rw [hli] at h1
      have hm : |μ| * tanLen_S15 g (secBundle_S15 X y) ≤ 2 * ε :=
        mul_le_mul hμ h1.le (Real.sqrt_nonneg _) (by norm_num)
      exact (edist_scaledExp_le_S15 g hEnorm X μ y).trans (ENNReal.ofReal_le_ofReal hm)
    have hd : Manifold.riemannianEDist I p q < δ := by
      have h4 : Manifold.riemannianEDist I p q ≤ ENNReal.ofReal (2 * ε) + ENNReal.ofReal (2 * ε) := by
        have htri : Manifold.riemannianEDist I p q ≤
            Manifold.riemannianEDist I p (scaledExp_S15 g hEnorm X μ p) +
              Manifold.riemannianEDist I (scaledExp_S15 g hEnorm X μ p) q :=
          Manifold.riemannianEDist_triangle
        refine htri.trans ?_
        refine add_le_add (hlen j p hpj) ?_
        rw [hpq, Manifold.riemannianEDist_comm]
        exact hlen j2 q hqj2
      have h5 : ENNReal.ofReal (2 * ε) + ENNReal.ofReal (2 * ε) = ENNReal.ofReal (4 * ε) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1; ring
      rw [h5] at h4
      exact lt_of_le_of_lt h4 (lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hδ0).mpr (by linarith)) hδ0le)
    obtain ⟨i, hpi, hqi⟩ := hleb p hpD q hd
    have hxp := ball_subset_closedBall hpi.2
    have hxq := ball_subset_closedBall hqi.2
    have hTp : extChartAt I (A.ctr i) p ∈ (extChartAt I (A.ctr i)).target :=
      (extChartAt I (A.ctr i)).map_source hpi.1
    have hTq : extChartAt I (A.ctr i) q ∈ (extChartAt I (A.ctr i)).target :=
      (extChartAt I (A.ctr i)).map_source hqi.1
    have hep := scaledExp_ext_S15 g hEnorm (A.ctr i) X μ hTp
    have heq2 := scaledExp_ext_S15 g hEnorm (A.ctr i) X μ hTq
    have hli1 := (extChartAt I (A.ctr i)).left_inv hpi.1
    have hli2 := (extChartAt I (A.ctr i)).left_inv hqi.1
    rw [hli1] at hep
    rw [hli2] at heq2
    have hGeq : chartPsi_S15 g hEnorm (A.ctr i)
          (extChartAt I (A.ctr i) p, μ • coordSec_S15 (A.ctr i) X (extChartAt I (A.ctr i) p)) =
        chartPsi_S15 g hEnorm (A.ctr i)
          (extChartAt I (A.ctr i) q, μ • coordSec_S15 (A.ctr i) X (extChartAt I (A.ctr i) q)) := by
      rw [← hep, ← heq2, hpq]
    have hb := (hres i).2.2 _ hxp _ hxq
    rw [hGeq, sub_self, norm_zero, mul_zero] at hb
    have hxe : extChartAt I (A.ctr i) p = extChartAt I (A.ctr i) q :=
      sub_eq_zero.mp (norm_le_zero_iff.mp hb)
    have hpq' := congrArg (extChartAt I (A.ctr i)).symm hxe
    rw [hli1, hli2] at hpq'
    exact hpq'

end Complete2
end GC.LongTime.Ch12
