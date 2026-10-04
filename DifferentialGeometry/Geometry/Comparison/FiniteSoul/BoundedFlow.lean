import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SpeedBound
import DifferentialGeometry.Geometry.Metric.Path.RiemannianHopfRinow
import DifferentialGeometry.External.TauCeti.Geometry.Manifold.IntegralCurve.Flow

/-!
# S-FLOW: complete flows of bounded fields on a complete finite-order manifold (F-bounded)

Package CM-S (finite soul), lane CMS-H. Design `docs/geometrization/chapter13/design-finite-soul-20261004.md`
§4.2 "S-FLOW", blueprint master207A LFR46 proof (A:28944–28947): *a bounded field on a complete
proper Riemannian manifold has a complete flow: a trajectory in finite time has bounded length and
remains in a compact ball, where the finite ODE continuation theorem applies.*

Setting: a smooth carrier `M` whose distance is the Riemannian distance of a bundle metric with the
norm of `g` (`hnorm`), `M` complete. The field `V` is a `C^n` section (`1 ≤ n ≤ ∞`) with
`g(V, V) ≤ B²`. No compact support is needed (compare F-1's `exists_compactSupport_flow_Ck`).

* `dist_maximalIntegralCurve_le`: along TauCeti's maximal integral curve the distance grows at most
  at rate `|B|` (length bound, `riemannianEDist_le_pathELength`).
* `maximalIntegralCurveInterval_eq_univ_of_bounded`: completeness, by the escape lemma
  `eventually_notMem_nhdsLT_maximalIntegralCurve` in the compact ball `closedBall x (|B| b)`.
* `exists_complete_flow_of_bounded_ENat`: the joint `C^n` flow with the group law, the equation,
  the speed bound and uniqueness of integral curves.
* `exists_complete_flow_of_bounded`: the frozen interface statement (order `k : ℕ`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric MeasureTheory TauCeti
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **Speed bound along a maximal integral curve.** If `g(V, V) ≤ B²` everywhere, the distance
between two positions of the maximal integral curve of `V` through `x` is at most `|B|` times the
elapsed time. -/
theorem dist_maximalIntegralCurve_le
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent 1 (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    {B : ℝ} (hB : ∀ x, g.inner x (V x) (V x) ≤ B ^ 2) (x : M) {s t : ℝ}
    (hs : s ∈ maximalIntegralCurveInterval V x) (ht : t ∈ maximalIntegralCurveInterval V x)
    (hst : s ≤ t) :
    dist (maximalIntegralCurve V x s) (maximalIntegralCurve V x t) ≤ |B| * (t - s) := by
  set J := maximalIntegralCurveInterval V x with hJ
  set γ := maximalIntegralCurve V x with hγ
  have hsub : Icc s t ⊆ J := ordConnected_maximalIntegralCurveInterval.out hs ht
  have hJo : IsOpen J := isOpen_maximalIntegralCurveInterval
  -- `γ` is `C¹` on the maximal interval.
  have hflow := contMDiffOn_maximalIntegralCurve (I := I) (n := 1) le_rfl hV
  have hγc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc s t) := by
    have hpair : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) 1 (fun τ : ℝ => ((x, τ) : M × ℝ)) :=
      contMDiff_const.prodMk contMDiff_id
    refine (hflow.comp hpair.contMDiffOn fun τ hτ => ?_)
    exact (mem_maximalIntegralCurveFlowDomain).mpr (hsub hτ)
  -- the velocity is `V ∘ γ`
  have hcurve := isMIntegralCurveOn_maximalIntegralCurve (x := x) hV
  have hder : ∀ τ ∈ Icc s t, HasMFDerivAt 𝓘(ℝ, ℝ) I γ τ ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ τ))) :=
    fun τ hτ => (hcurve τ (hsub hτ)).hasMFDerivAt (hJo.mem_nhds (hsub hτ))
  have hle := riemannianEDist_le_pathELength (I := I) hγc rfl rfl hst
  rw [pathELength_eq_lintegral_mfderiv_Icc, ← IsRiemannianManifold.out (I := I)] at hle
  have hbound : ∀ τ ∈ Icc s t, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ 1‖ₑ ≤ ENNReal.ofReal |B| := by
    intro τ hτ
    have h1 : (mfderiv 𝓘(ℝ, ℝ) I γ τ 1 : TangentSpace I (γ τ)) = V (γ τ) := by
      rw [(hder τ hτ).mfderiv]
      exact one_smul ℝ _
    rw [h1, hnorm]
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (hB _)
  have hint : ∫⁻ τ in Icc s t, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ 1‖ₑ ≤
      ENNReal.ofReal (|B| * (t - s)) := by
    calc ∫⁻ τ in Icc s t, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ 1‖ₑ
        ≤ ∫⁻ _ in Icc s t, ENNReal.ofReal |B| := setLIntegral_mono' measurableSet_Icc hbound
      _ = ENNReal.ofReal (|B| * (t - s)) := by
          rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (abs_nonneg _)]
  have h2 := hle.trans hint
  rw [edist_dist] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (abs_nonneg _) (sub_nonneg.mpr hst))).mp h2

/-- **Completeness.** A bounded `C¹` field on a complete manifold has maximal integral curves
defined for all time. -/
theorem maximalIntegralCurveInterval_eq_univ_of_bounded [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent 1 (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    {B : ℝ} (hB : ∀ x, g.inner x (V x) (V x) ≤ B ^ 2) (x : M) :
    maximalIntegralCurveInterval V x = univ := by
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  set J := maximalIntegralCurveInterval V x with hJ
  have h0 : (0 : ℝ) ∈ J := zero_mem_maximalIntegralCurveInterval hV.contMDiffAt
  have hγ0 : maximalIntegralCurve V x 0 = x := maximalIntegralCurve_zero h0
  have hup : ¬ BddAbove J := by
    intro hbdd
    set b := sSup J
    have hlub : IsLUB J b := isLUB_csSup ⟨0, h0⟩ hbdd
    obtain ⟨a, ha, hb0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isLUB h0 hlub
    have hesc := eventually_notMem_nhdsLT_maximalIntegralCurve hV h0 hlub
      (isCompact_closedBall x (|B| * b))
    have hev : ∀ᶠ τ in 𝓝[<] b, τ ∈ Ioo 0 b := Ioo_mem_nhdsLT hb0
    obtain ⟨τ, hτ, hτK⟩ := (hev.and hesc).exists
    apply hτK
    have hτJ : τ ∈ J := hsub ⟨ha.trans hτ.1, hτ.2⟩
    have hd := dist_maximalIntegralCurve_le g hnorm V hV hB x h0 hτJ hτ.1.le
    rw [hγ0, sub_zero] at hd
    rw [mem_closedBall, dist_comm]
    exact hd.trans (mul_le_mul_of_nonneg_left hτ.2.le (abs_nonneg _))
  have hlow : ¬ BddBelow J := by
    intro hbdd
    set a := sInf J
    have hglb : IsGLB J a := isGLB_csInf ⟨0, h0⟩ hbdd
    obtain ⟨b, hb, ha0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isGLB h0 hglb
    have hesc := eventually_notMem_nhdsGT_maximalIntegralCurve hV h0 hglb
      (isCompact_closedBall x (|B| * (-a)))
    have hev : ∀ᶠ τ in 𝓝[>] a, τ ∈ Ioo a 0 := Ioo_mem_nhdsGT ha0
    obtain ⟨τ, hτ, hτK⟩ := (hev.and hesc).exists
    apply hτK
    have hτJ : τ ∈ J := hsub ⟨hτ.1, hτ.2.trans hb⟩
    have hd := dist_maximalIntegralCurve_le g hnorm V hV hB x hτJ h0 hτ.2.le
    rw [hγ0] at hd
    rw [mem_closedBall]
    exact hd.trans (mul_le_mul_of_nonneg_left (by linarith [hτ.1]) (abs_nonneg _))
  exact maximalIntegralCurveInterval_eq_univ_of_not_bddAbove_not_bddBelow h0 hup hlow

/-- **S-FLOW (F-bounded), general order `1 ≤ n ≤ ∞`.** A bounded `C^n` field on a complete
finite-order Riemannian manifold has a global flow that is jointly `C^n`, satisfies the group law
and the equation `∂ₜ Φ t x = V (Φ t x)`, moves points at speed at most `|B|`, and through which every
global integral curve runs. -/
theorem exists_complete_flow_of_bounded_ENat [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {n : ℕ∞} (hn : 1 ≤ n) (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent n (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    {B : ℝ} (hB : ∀ x, g.inner x (V x) (V x) ≤ B ^ 2) :
    ∃ Φ : ℝ → M → M,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I n (fun q : ℝ × M => Φ q.1 q.2) ∧ (∀ x, Φ 0 x = x) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      (∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ t x)))) ∧
      (∀ s t x, dist (Φ s x) (Φ t x) ≤ |B| * |t - s|) ∧
      ∀ γ : ℝ → M, (∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ t)))) →
        ∀ t, γ t = Φ t (γ 0) := by
  have hn' : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have hV1 : ContMDiff I I.tangent 1 (fun x => (⟨x, V x⟩ : TangentBundle I M)) := hV.of_le hn'
  have : IsManifold I n M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have huniv : ∀ x, maximalIntegralCurveInterval V x = univ :=
    maximalIntegralCurveInterval_eq_univ_of_bounded g hnorm V hV1 hB
  have hmem : ∀ x t, t ∈ maximalIntegralCurveInterval V x := fun x t => by
    rw [huniv x]; exact mem_univ t
  set Φ : ℝ → M → M := fun t x => maximalIntegralCurve V x t with hΦ
  have hzero : ∀ x, Φ 0 x = x := fun x => maximalIntegralCurve_zero (hmem x 0)
  have hder : ∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ t x))) := by
    intro t x
    have h := isMIntegralCurveOn_maximalIntegralCurve (x := x) hV1 t (hmem x t)
    rw [huniv x] at h
    exact h.hasMFDerivAt univ_mem
  refine ⟨Φ, ?_, hzero, ?_, hder, ?_, ?_⟩
  · have hdom : maximalIntegralCurveFlowDomain V = univ :=
      eq_univ_of_forall fun p => (mem_maximalIntegralCurveFlowDomain).mpr (hmem p.1 p.2)
    have hψ := contMDiffOn_maximalIntegralCurve (I := I) hn hV
    rw [hdom, contMDiffOn_univ] at hψ
    have hswap : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, ℝ)) n
        (fun q : ℝ × M => ((q.2, q.1) : M × ℝ)) := contMDiff_snd.prodMk contMDiff_fst
    exact hψ.comp hswap
  · intro s t x
    change maximalIntegralCurve V x (s + t) = maximalIntegralCurve V (maximalIntegralCurve V x t) s
    rw [add_comm]
    exact maximalIntegralCurve_add hV1 (hmem x t) (hmem x (t + s))
  · intro s t x
    rcases le_total s t with hst | hts
    · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
      exact dist_maximalIntegralCurve_le g hnorm V hV1 hB x (hmem x s) (hmem x t) hst
    · rw [dist_comm, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hts)]
      exact dist_maximalIntegralCurve_le g hnorm V hV1 hB x (hmem x t) (hmem x s) hts
  · intro γ hγ t
    have hon : IsMIntegralCurveOn γ V (Ioo (-(|t| + 1)) (|t| + 1)) := fun τ _ =>
      (hγ τ).hasMFDerivWithinAt
    have h0 : (0 : ℝ) ∈ Ioo (-(|t| + 1)) (|t| + 1) :=
      ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩
    have heq := hon.eqOn_maximalIntegralCurve hV1 h0 rfl
    have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) :=
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    exact (heq ht).symm

/-- **S-FLOW, frozen interface form** (`build-logs/scratch/D-CMS/FiniteSoulInterfaces.lean`,
`exists_complete_flow_of_bounded`): a bounded `C^k` field (`1 ≤ k`) on a complete finite manifold
has a complete `C^k` flow with the cocycle law. -/
theorem exists_complete_flow_of_bounded [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {k : ℕ} (hk : 1 ≤ k) (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent k (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    {B : ℝ} (hB : ∀ x, g.inner x (V x) (V x) ≤ B ^ 2) :
    ∃ Φ : ℝ → M → M,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I k (fun q : ℝ × M => Φ q.1 q.2) ∧ (∀ x, Φ 0 x = x) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      ∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ t x))) := by
  obtain ⟨Φ, hc, h0, hadd, hder, -, -⟩ :=
    exists_complete_flow_of_bounded_ENat g hnorm (n := (k : ℕ∞)) (by exact_mod_cast hk) V hV hB
  exact ⟨Φ, hc, h0, hadd, hder⟩

/-- **Consumer of S-FLOW.** The complete smooth flow of the zero field is the identity: the
constant curves are integral curves, and uniqueness identifies them with the flow lines. -/
theorem exists_complete_flow_zero_eq_id [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))) :
    ∃ Φ : ℝ → M → M,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) ∧ ∀ t x, Φ t x = x := by
  have hV : ContMDiff I I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (⟨x, (0 : TangentSpace I x)⟩ : TangentBundle I M)) :=
    Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _)
  obtain ⟨Φ, hc, -, -, -, -, huniq⟩ :=
    exists_complete_flow_of_bounded_ENat g hnorm (n := ⊤) le_top
      (fun x => (0 : TangentSpace I x)) hV (B := 0)
      (fun x => by rw [map_zero]; norm_num)
  refine ⟨Φ, hc, fun t x => ?_⟩
  have hconst : ∀ τ : ℝ, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun _ : ℝ => x) τ
      ((1 : ℝ →L[ℝ] ℝ).smulRight (0 : TangentSpace I x)) := fun τ => by
    rw [ContinuousLinearMap.smulRight_zero]
    exact hasMFDerivAt_const x τ
  exact (huniq (fun _ => x) hconst t).symm

end DifferentialGeometry.Geometry.FiniteSoul
