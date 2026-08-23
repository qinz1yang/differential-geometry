import DifferentialGeometry.Analysis.Calculus.BumpClamp
import DifferentialGeometry.Analysis.Calculus.MovingImplicit
import DifferentialGeometry.Geometry.Comparison.CGTWhiteheadBase
import DifferentialGeometry.Geometry.Comparison.HessianAlongGeodesic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential Geodesic NormalCoordinates
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

noncomputable local instance {R : Real} :
    SigmaCompactSpace (intrPullBall (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (intrPullBall (E := E) R).isOpen)

theorem exists_short_scale
    {R a K : Real} (h4aR : 4 * a < R)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2) :
    ∃ L : Real,
      2 * a < L ∧
      a + L < 3 * R / 4 ∧
      K * L ^ 2 < (Real.pi / 2) ^ 2 := by
  let cap : Real := 3 * R / 4 - a
  have h2aCap : 2 * a < cap := by
    dsimp only [cap]
    linarith
  have hcont :
      Continuous (fun L : Real => K * L ^ 2) :=
    continuous_const.mul (continuous_id.pow 2)
  have hcurv :
      ∀ᶠ L in 𝓝 (2 * a), K * L ^ 2 < (Real.pi / 2) ^ 2 :=
    hcont.continuousAt (Iio_mem_nhds hsmall)
  have hcurvGT :
      ∀ᶠ L in 𝓝[>] (2 * a), K * L ^ 2 < (Real.pi / 2) ^ 2 :=
    hcurv.filter_mono inf_le_left
  have hwindow :
      ∀ᶠ L in 𝓝[>] (2 * a), L ∈ Set.Ioo (2 * a) cap :=
    Ioo_mem_nhdsGT h2aCap
  obtain ⟨L, hcurvL, hL, hLcap⟩ :=
    (hcurvGT.and hwindow).exists
  refine ⟨L, hL, ?_, hcurvL⟩
  dsimp only [cap] at hLcap
  linarith

theorem intrCore_min_regular
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    {pt q : intrPullBall (E := E) R}
    (hpt : pt ∈ intrCore (E := E) R a)
    (hq : q ∈ intrCore (E := E) R a) :
    let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
    letI : EMetricSpace E :=
      EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    letI : CompleteSpace E :=
      (intrExt_complete (I := I) g hEnorm p hR hloc).complete
    let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
      fun z v =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z v
    let u :=
      minimizingVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
    ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (u : E) := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  let u :=
    minimizingVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
  change
    ¬ IsConjVec
      (I := 𝓘(Real, E)) gExt hExt (pt : E) (u : E)
  obtain ⟨L, h2aL, hbudget, hsmallL⟩ :=
    exists_short_scale h4aR hsmall
  have ha : 0 ≤ a := (norm_nonneg (pt : E)).trans hpt
  have haInner : a ≤ 3 * R / 4 := by linarith
  have hdist :
      riemannianEDistOf (I := 𝓘(Real, E)) gExt (pt : E) (q : E) ≤
        ENNReal.ofReal (2 * a) :=
    intrExt_edist_le (I := I) g hEnorm p hR hloc hpt hq haInner
  have hdistReal :
      (riemannianEDistOf
        (I := 𝓘(Real, E)) gExt (pt : E) (q : E)).toReal ≤
          2 * a :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by norm_num) ha) hdist
  have hu2a :
      Real.sqrt (gExt.inner (pt : E) u u) ≤ 2 * a := by
    rw [minimizingVec_len
      (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)]
    exact hdistReal
  have huL : Real.sqrt (gExt.inner (pt : E) u u) ≤ L :=
    hu2a.trans h2aL.le
  have hfence :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        ‖intrExtLaunch (I := I) g hEnorm p hR hloc
          (pt : E) u t‖ < 3 * R / 4 :=
    intrExt_shortLaunch_fenced
      (I := I) g hEnorm p hR hloc hpt u huL hbudget
  have hnot :=
    intrExt_not_conj_of_shortLaunch
      (I := I) g hEnorm p hR hloc u hfence huL hK hRm hsmallL
  change
    ¬ IsConjVec
      (I := 𝓘(Real, E)) gExt hExt (pt : E) (u : E) at hnot
  exact hnot


omit [NeZero (Module.finrank ℝ E)] in
private theorem pinned_inj_nhds
    (F : E × E → E) (hF : ContDiff Real ∞ F)
    {x u : E}
    (hinj : Function.Injective (Analysis.partialFDeriv₂ F x u)) :
    ∃ U ∈ 𝓝 (x, u),
      Set.InjOn
        (fun z : E × E =>
          (F z, z.1))
        U := by
  classical
  have hsurj :
      Function.Surjective (Analysis.partialFDeriv₂ F x u) :=
    LinearMap.surjective_of_injective hinj
  let A : E ≃L[Real] E :=
    ContinuousLinearEquiv.ofBijective
      (Analysis.partialFDeriv₂ F x u)
      (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurj)
  have hpartialInv :
      (Analysis.partialFDeriv₂ F x u).IsInvertible := by
    refine ⟨A, ?_⟩
    rfl
  let H : E × E → E × E := Analysis.pinnedRootMap F
  have hH : ContDiff Real ∞ H := by
    simpa only [H, Analysis.pinnedRootMap] using
      hF.prodMk contDiff_fst
  have hHInv :
      (fderiv Real H (x, u)).IsInvertible := by
    simpa only [H] using
      Analysis.pinnedFDeriv_inv
        ((hF.differentiable (by simp)).differentiableAt) hpartialInv
  rcases hHInv with ⟨B, hB⟩
  have hHD :
      HasFDerivAt H (B : (E × E) →L[Real] (E × E)) (x, u) := by
    rw [hB]
    exact ((hH.differentiable (by simp)).differentiableAt).hasFDerivAt
  let e := hH.contDiffAt.toOpenPartialHomeomorph H hHD (by simp)
  have hmem : (x, u) ∈ e.source := by
    exact hH.contDiffAt.mem_toOpenPartialHomeomorph_source hHD (by simp)
  refine ⟨e.source, e.open_source.mem_nhds hmem, ?_⟩
  simpa only [e, H, Analysis.pinnedRootMap] using e.injOn

private def shortBigons
    (F : E × E → E) (ell : E × E → Real) (a L : Real) :
    Set (E × E × E) :=
  {z |
    ‖z.1‖ ≤ a ∧
    ‖F (z.1, z.2.1)‖ ≤ a ∧
    F (z.1, z.2.1) = F (z.1, z.2.2) ∧
    ell (z.1, z.2.1) ≤ L ∧
    ell (z.1, z.2.2) ≤ L ∧
    z.2.1 ≠ z.2.2}


omit [NeZero (Module.finrank ℝ E)] in
private theorem shortBigons_compact
    (F : E × E → E) (ell : E × E → Real) (a L B : Real)
    (hF : Continuous F) (hell : Continuous ell)
    (hdiag :
      ∀ x u : E, ‖x‖ ≤ a → ell (x, u) ≤ L →
        ∃ U ∈ 𝓝 (x, u),
          Set.InjOn (fun z : E × E => (F z, z.1)) U)
    (hbound :
      ∀ z ∈ shortBigons F ell a L,
        ‖z.2.1‖ ≤ B ∧ ‖z.2.2‖ ≤ B) :
    IsCompact (shortBigons F ell a L) := by
  let pu : E × E × E → E × E := fun z => (z.1, z.2.1)
  let pv : E × E × E → E × E := fun z => (z.1, z.2.2)
  let Raw : Set (E × E × E) :=
    {z |
      ‖z.1‖ ≤ a ∧
      ‖F (pu z)‖ ≤ a ∧
      F (pu z) = F (pv z) ∧
      ell (pu z) ≤ L ∧
      ell (pv z) ≤ L}
  have hpu : Continuous pu :=
    continuous_fst.prodMk continuous_snd.fst
  have hpv : Continuous pv :=
    continuous_fst.prodMk continuous_snd.snd
  have hRawClosed : IsClosed Raw := by
    have hxClosed : IsClosed {z : E × E × E | ‖z.1‖ ≤ a} :=
      isClosed_le (continuous_norm.comp continuous_fst) continuous_const
    have hyClosed : IsClosed {z : E × E × E | ‖F (pu z)‖ ≤ a} :=
      isClosed_le (continuous_norm.comp (hF.comp hpu)) continuous_const
    have heqClosed : IsClosed {z : E × E × E | F (pu z) = F (pv z)} :=
      isClosed_eq (hF.comp hpu) (hF.comp hpv)
    have huClosed : IsClosed {z : E × E × E | ell (pu z) ≤ L} :=
      isClosed_le (hell.comp hpu) continuous_const
    have hvClosed : IsClosed {z : E × E × E | ell (pv z) ≤ L} :=
      isClosed_le (hell.comp hpv) continuous_const
    simpa only [Raw, Set.mem_setOf_eq] using
      hxClosed.inter
        (hyClosed.inter
          (heqClosed.inter (huClosed.inter hvClosed)))
  have hBadRaw :
      shortBigons F ell a L =
        Raw ∩ {z : E × E × E | z.2.1 ≠ z.2.2} := by
    ext z
    simp only [shortBigons, Raw, pu, pv, Set.mem_setOf_eq,
      Set.mem_inter_iff]
    tauto
  have hBadClosed : IsClosed (shortBigons F ell a L) := by
    rw [hBadRaw, ← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    change z ∉ Raw ∩ {w : E × E × E | w.2.1 ≠ w.2.2} at hz
    by_cases hzRaw : z ∈ Raw
    · have huv : z.2.1 = z.2.2 := by
        by_contra hne
        exact hz ⟨hzRaw, hne⟩
      obtain ⟨U, hU, hUinj⟩ :=
        hdiag z.1 z.2.1 hzRaw.1 hzRaw.2.2.2.1
      have hUu : U ∈ 𝓝 (pu z) := by
        simpa only [pu] using hU
      have hUv : U ∈ 𝓝 (pv z) := by
        simpa only [pu, pv, huv] using hU
      have hV :
          {w : E × E × E | pu w ∈ U ∧ pv w ∈ U} ∈ 𝓝 z :=
        Filter.inter_mem (hpu.continuousAt hUu) (hpv.continuousAt hUv)
      refine Filter.mem_of_superset hV ?_
      intro w hw
      change w ∉ Raw ∩ {r : E × E × E | r.2.1 ≠ r.2.2}
      intro hwBad
      have hpairs : pu w = pv w := by
        apply hUinj hw.1 hw.2
        apply Prod.ext
        · exact hwBad.1.2.2.1
        · rfl
      exact hwBad.2 (congrArg Prod.snd hpairs)
    · have hRawCompl : Rawᶜ ∈ 𝓝 z :=
        hRawClosed.isOpen_compl.mem_nhds hzRaw
      refine Filter.mem_of_superset hRawCompl ?_
      intro w hw
      change w ∉ Raw ∩ {r : E × E × E | r.2.1 ≠ r.2.2}
      exact fun h => hw h.1
  let Box : Set (E × E × E) :=
    Metric.closedBall (0 : E) a ×ˢ
      (Metric.closedBall (0 : E) B ×ˢ Metric.closedBall (0 : E) B)
  have hBox : IsCompact Box :=
    (isCompact_closedBall (0 : E) a).prod
      ((isCompact_closedBall (0 : E) B).prod
        (isCompact_closedBall (0 : E) B))
  apply hBox.of_isClosed_subset hBadClosed
  intro z hz
  have hb := hbound z hz
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hb.1
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hb.2

theorem intrExt_minVec_mem
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {pt q u : E} :
    let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
    letI : EMetricSpace E :=
      EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    letI : CompleteSpace E :=
      (intrExt_complete (I := I) g hEnorm p hR hloc).complete
    let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
      fun z v =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z v
    ∀ (B : ExpInvBranch (I := 𝓘(Real, E)) gExt hExt pt),
      u ∈ B.hom.source →
      (∀ v : E,
        expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt pt v = q →
        Real.sqrt (gExt.inner pt v v) =
          (riemannianEDist 𝓘(Real, E) pt q).toReal →
        v = u) →
      ∀ᶠ z in 𝓝 q,
        (minimizingVec (I := 𝓘(Real, E)) gExt hExt pt z : E) ∈
          B.hom.source := by
  classical
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  dsimp only
  intro B hu huniq
  let mv : E → E := fun z =>
    (minimizingVec (I := 𝓘(Real, E)) gExt hExt pt z : E)
  let d : E → Real := fun z =>
    (riemannianEDist 𝓘(Real, E) pt z).toReal
  have hfinite :
      {z : E |
        riemannianEDist 𝓘(Real, E) pt z ≠ (⊤ : ENNReal)} = Set.univ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact riemannianEDist_ne_top (I := 𝓘(Real, E)) pt z
  have hd : Continuous d := by
    have hdOn :=
      continuousOn_riemannianEDist_toReal_on_finite gExt pt
    rw [hfinite] at hdOn
    exact continuousOn_univ.mp hdOn
  have hmv :
      Filter.Tendsto mv (𝓝 q) (𝓝 u) := by
    rw [Filter.tendsto_iff_seq_tendsto]
    intro seq hseq
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    have hz :
        Filter.Tendsto (fun n => seq (ns n)) Filter.atTop (𝓝 q) :=
      hseq.comp hns
    have hdseq :
        Filter.Tendsto (fun n => d (seq (ns n)))
          Filter.atTop (𝓝 (d q)) :=
      (hd.tendsto q).comp hz
    have hdbdd :
        Bornology.IsBounded (Set.range fun n => d (seq (ns n))) :=
      Metric.isBounded_range_of_tendsto _ hdseq
    rw [isBounded_iff_forall_norm_le] at hdbdd
    obtain ⟨C, hC⟩ := hdbdd
    let C₀ : Real := max 0 C
    let K : Set E :=
      {v : E | Real.sqrt (gExt.inner pt v v) ≤ C₀}
    have hK : IsCompact K := by
      simpa only [K] using
        gLenBall_isCompact (I := 𝓘(Real, E)) gExt pt C₀
    have hmvK : ∀ n, mv (seq (ns n)) ∈ K := by
      intro n
      have hdC : d (seq (ns n)) ≤ C := by
        have hnorm := hC _ ⟨n, rfl⟩
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hnorm
        exact hnorm
      have hdC₀ : d (seq (ns n)) ≤ C₀ :=
        hdC.trans (le_max_right _ _)
      change
        Real.sqrt
            (gExt.inner pt
              (minimizingVec (I := 𝓘(Real, E)) gExt hExt pt (seq (ns n)))
              (minimizingVec (I := 𝓘(Real, E)) gExt hExt pt (seq (ns n)))) ≤
          C₀
      rw [minimizingVec_len
        (I := 𝓘(Real, E)) gExt hExt pt (seq (ns n))]
      exact hdC₀
    obtain ⟨v, _hvK, φ, hφ, hv⟩ :=
      hK.tendsto_subseq hmvK
    have hzφ :
        Filter.Tendsto (fun n => seq (ns (φ n)))
          Filter.atTop (𝓝 q) :=
      hz.comp hφ.tendsto_atTop
    have hexp_v :
        Filter.Tendsto
          (fun n =>
            expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt pt
              (mv (seq (ns (φ n)))))
          Filter.atTop
          (𝓝 (expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt pt v)) :=
      by
        simpa only [Function.comp_apply] using
          ((expMapIntrinsic_continuous
            (I := 𝓘(Real, E)) gExt hExt pt).tendsto v).comp hv
    have hexp_q :
        Filter.Tendsto
          (fun n =>
            expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt pt
              (mv (seq (ns (φ n)))))
          Filter.atTop (𝓝 q) := by
      apply hzφ.congr'
      exact Filter.Eventually.of_forall fun n => by
        simpa only [mv] using
          (minimizingVec_exp
            (I := 𝓘(Real, E)) gExt hExt pt (seq (ns (φ n)))).symm
    have hexp :
        expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt pt v = q :=
      tendsto_nhds_unique hexp_v hexp_q
    have hlen_v :
        Filter.Tendsto
          (fun n =>
            Real.sqrt
              (gExt.inner pt (mv (seq (ns (φ n))))
                (mv (seq (ns (φ n))))))
          Filter.atTop
          (𝓝 (Real.sqrt (gExt.inner pt v v))) :=
      by
        simpa only [Function.comp_apply] using
          ((continuous_sqrt_gInner_self
            (I := 𝓘(Real, E)) gExt pt).tendsto v).comp hv
    have hdist_q :
        Filter.Tendsto
          (fun n =>
            Real.sqrt
              (gExt.inner pt (mv (seq (ns (φ n))))
                (mv (seq (ns (φ n))))))
          Filter.atTop (𝓝 (d q)) := by
      have hdistφ :
          Filter.Tendsto (fun n => d (seq (ns (φ n))))
            Filter.atTop (𝓝 (d q)) :=
        (hd.tendsto q).comp hzφ
      apply hdistφ.congr'
      exact Filter.Eventually.of_forall fun n => by
        simpa only [mv, d] using
          (minimizingVec_len
            (I := 𝓘(Real, E)) gExt hExt pt (seq (ns (φ n)))).symm
    have hlen :
        Real.sqrt (gExt.inner pt v v) =
          (riemannianEDist 𝓘(Real, E) pt q).toReal :=
      tendsto_nhds_unique hlen_v hdist_q
    refine ⟨φ, ?_⟩
    rw [show v = u from huniq v hexp hlen] at hv
    simpa only [mv] using hv
  have hBopen : B.hom.source ∈ 𝓝 u :=
    B.hom.open_source.mem_nhds hu
  exact hmv hBopen

theorem branchEnergy_min_germ
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {pt q : M} (B : ExpInvBranch (I := I) g hEnorm pt)
    (hmem :
      ∀ᶠ z in 𝓝 q,
        (minimizingVec (I := I) g hEnorm pt z : E) ∈
          B.hom.source) :
    branchEnergy (I := I) g B =ᶠ[𝓝 q]
      (fun z =>
        (1 / 2 : Real) *
          (riemannianEDist I pt z).toReal ^ 2) := by
  filter_upwards [hmem] with z hz
  let v : E :=
    (minimizingVec (I := I) g hEnorm pt z : E)
  have hvexp :
      expMapIntrinsic (I := I) g hEnorm pt v = z := by
    simpa only [v] using
      minimizingVec_exp (I := I) g hEnorm pt z
  have henergy :
      branchEnergy (I := I) g B z =
        (1 / 2 : Real) * g.inner pt v v := by
    rw [← hvexp]
    exact branchEnergy_exp (I := I) B hz
  have hlen :
      Real.sqrt (g.inner pt v v) =
        (riemannianEDist I pt z).toReal := by
    simpa only [v] using
      minimizingVec_len (I := I) g hEnorm pt z
  rw [henergy, ← hlen]
  congr 1
  exact
    (Real.sq_sqrt
      (gInner_self_nonneg (I := I) g pt v)).symm

private theorem intrExt_radial_geo
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {z : E} (hz : ‖z‖ < 3 * R / 4) :
    ∃ c : Real, 1 < c ∧
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc)
        (fun t : Real => t • z) (Set.Ioo (-c) c) := by
  classical
  let B : Real := 3 * R / 4
  let n : Real := ‖z‖
  let gap : Real := B - n
  let ε : Real := gap / (4 * (n + 1))
  let c : Real := 1 + ε
  let d : Real := 1 + 2 * ε
  have hn : 0 ≤ n := by
    exact norm_nonneg z
  have hgap : 0 < gap := by
    simpa only [gap, B, n] using sub_pos.mpr hz
  have hden : 0 < 4 * (n + 1) := by positivity
  have hε : 0 < ε := div_pos hgap hden
  have hc : 1 < c := by
    dsimp only [c]
    linarith
  have hcd : c < d := by
    dsimp only [c, d]
    linarith
  have hd_mul : d * n < B := by
    have hsmall : 2 * ε * n < gap := by
      rw [show 2 * ε * n = (2 * gap * n) / (4 * (n + 1)) by
        dsimp only [ε]
        ring]
      rw [div_lt_iff₀ hden]
      nlinarith
    dsimp only [d]
    dsimp only [gap] at hsmall
    linarith
  have hBR : B < R := by
    dsimp only [B]
    nlinarith
  let b : ContDiffBump (0 : Real) :=
    { rIn := c
      rOut := d
      rIn_pos := lt_trans zero_lt_one hc
      rIn_lt_rOut := hcd }
  let φ : Real → Real := b.radial
  have hφ_smooth : ContDiff Real (∞ : WithTop ℕ∞) φ := by
    simpa only [φ] using b.radial_contDiff
  have hφ_bound : ∀ t : Real, ‖φ t • z‖ < B := by
    intro t
    have ht := b.radial_mapsTo (Set.mem_univ t)
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    rw [norm_smul, Real.norm_eq_abs]
    by_cases hn0 : n = 0
    · have hz0 : ‖z‖ = 0 := by simpa only [n] using hn0
      rw [hz0, mul_zero]
      simpa only [hn0, mul_zero] using hd_mul
    · calc
        |φ t| * ‖z‖ = |φ t| * n := by rfl
        _ < d * n :=
          mul_lt_mul_of_pos_right ht (lt_of_le_of_ne hn (Ne.symm hn0))
        _ < B := hd_mul
  have hφ_eq : ∀ {t : Real}, t ∈ Set.Ioo (-c) c → φ t = t := by
    intro t ht
    apply b.radial_eq_self
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact (abs_lt.mpr ht).le
  let γ : Real → intrPullBall (E := E) R := fun t =>
    ⟨φ t • z, by
      change φ t • z ∈ Metric.ball (0 : E) R
      rw [Metric.mem_ball, dist_zero_right]
      exact (hφ_bound t).trans hBR⟩
  have hγ_smooth :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    intro t
    exact codRestr_contMDiffAt
      (I := 𝓘(Real, Real)) (J := 𝓘(Real, E))
      (V := intrPullBall (E := E) R)
      (f := fun s : Real => φ s • z)
      (fun s => (γ s).property)
      ((hφ_smooth.smul contDiff_const).contMDiff.contMDiffAt)
  let gPull := intrPullMetric (I := I) g hEnorm p hloc
  letI : RiemannianBundle
      (fun x : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) x) :=
    ⟨gPull.toRiemannianMetric⟩
  have hmap_geo :
      IsGeodesicOn (I := I) g
        (fun t => intrExpOn (I := I) g hEnorm p R (γ t))
        (Set.Ioo (-c) c) := by
    intro t ht
    have heq :
        (fun s => intrExpOn (I := I) g hEnorm p R (γ s)) =ᶠ[𝓝 t]
          intrinsicGeodesic (I := I) g hEnorm p
            (normalFrame (I := I) g p z) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      change intrinsicFramedExp (I := I) g hEnorm p (γ s : E) =
        intrinsicGeodesic (I := I) g hEnorm p
          (normalFrame (I := I) g p z) s
      rw [show (γ s : E) = s • z by
        change φ s • z = s • z
        rw [hφ_eq hs]]
      simp only [intrFrame_apply, map_smul,
        expMapIntrinsic_def, intrinsicGeodesic_smul]
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
      (I := I) (g := g) heq.eq_of_nhds heq
      (intrinsicGeodesic_isGeodesic
        (I := I) g hEnorm p (normalFrame (I := I) g p z) t)
  have hpull_geo :
      IsGeodesicOn (I := 𝓘(Real, E)) gPull γ
        (Set.Ioo (-c) c) := by
    intro t ht
    apply Geodesic.geoEq_of_map_localIso
      (I := 𝓘(Real, E)) (J := I) gPull g
      (intrExpOn_local (I := I) g hEnorm p hloc)
      (γ := γ) (t := t)
    · intro x v w
      change
        (intrPullMetric (I := I) g hEnorm p hloc).inner x v w =
          g.inner (intrExpOn (I := I) g hEnorm p R x)
            (mfderiv 𝓘(Real, E) I
              (intrExpOn (I := I) g hEnorm p R) x v)
            (mfderiv 𝓘(Real, E) I
              (intrExpOn (I := I) g hEnorm p R) x w)
      rw [intrPullMetric, localPullMetric_inner]
    · exact hγ_smooth t
    · exact hmap_geo t ht
  have hext_geo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc)
        (fun t => ((γ t : intrPullBall (E := E) R) : E))
        (Set.Ioo (-c) c) := by
    exact intrExt_geo_of_pull (I := I) g hEnorm p hR hloc γ
      (Set.Ioo (-c) c) hγ_smooth
      (fun t _ht => by
        change ‖φ t • z‖ < 3 * R / 4
        simpa only [B] using hφ_bound t)
      (by simpa only [gPull] using hpull_geo)
  refine ⟨c, hc, ?_⟩
  intro t ht
  have heq :
      (fun s => ((γ s : intrPullBall (E := E) R) : E)) =ᶠ[𝓝 t]
        (fun s : Real => s • z) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    change φ s • z = s • z
    rw [hφ_eq hs]
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
    (I := 𝓘(Real, E))
    (g := intrExtMetric (I := I) g hEnorm p hR hloc)
    heq.eq_of_nhds.symm heq.symm (hext_geo t ht)

theorem intrExt_radial_eq
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {z : E} (hz : ‖z‖ < 3 * R / 4)
    {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) :
    intrExtLaunch (I := I) g hEnorm p hR hloc (0 : E) z t =
      t • z := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun x : E ↦ TangentSpace 𝓘(Real, E) x) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (x : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) x) :=
    inferInstance
  letI (x : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) x) :=
    inferInstance
  letI : ∀ x : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) x) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun x : E ↦ TangentSpace 𝓘(Real, E) x) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (x : E) (v : TangentSpace 𝓘(Real, E) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner x v v)) :=
    fun x v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt x v
  obtain ⟨c, hc, hline⟩ :=
    intrExt_radial_geo (I := I) g hEnorm p hR hloc hz
  let O : Set Real := Set.Ioo (-c) c
  let Γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt (0 : E) z
  have hΓ :
      IsGeodesicOn (I := 𝓘(Real, E)) gExt Γ O := by
    intro t _ht
    exact intrinsicGeodesic_isGeodesic
      (I := 𝓘(Real, E)) gExt hExt (0 : E) z t
  have hline' :
      IsGeodesicOn (I := 𝓘(Real, E)) gExt
        (fun t : Real => t • z) O := by
    simpa only [O] using hline
  have hΓcont : ContinuousOn Γ O :=
    (intrinsicGeodesic_contMDiff
      (I := 𝓘(Real, E)) gExt hExt (0 : E) z).continuous.continuousOn
  have hlineCont : ContinuousOn (fun t : Real => t • z) O :=
    (continuous_id.smul continuous_const).continuousOn
  have hvel :
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E) Γ 0 (1 : Real) : E) =
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (fun t : Real => t • z) 0 (1 : Real) : E) := by
    have hleft :
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E) Γ 0 (1 : Real) : E) = z := by
      simpa only [Γ] using
        intrinsicGeodesic_mfderiv_zero
          (I := 𝓘(Real, E)) gExt hExt (0 : E) z
    have hright :
        mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (fun t : Real => t • z) 0 (1 : Real) = z := by
      rw [mfderiv_eq_fderiv]
      have hfd :
          HasFDerivAt (fun t : Real => t • z)
            (ContinuousLinearMap.smulRight (1 : Real →L[Real] Real) z) 0 := by
        simpa using (hasFDerivAt_id (0 : Real)).smul_const z
      rw [hfd.fderiv]
      change (ContinuousLinearMap.smulRight
        (1 : Real →L[Real] Real) z) (1 : Real) = z
      change (1 : Real) • z = z
      exact one_smul Real z
    rw [hleft, hright]
  have h0O : (0 : Real) ∈ O := by
    dsimp only [O]
    constructor <;> linarith
  have heq :=
    geo_eqOn_of_init (I := 𝓘(Real, E)) gExt
      (O := O) isOpen_Ioo isPreconnected_Ioo h0O hΓ hline'
      hΓcont hlineCont
      (by simp only [Γ, intrinsicGeodesic_zero, zero_smul])
      hvel
  have htO : t ∈ O := by
    dsimp only [O]
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hΓt : Γ t = t • z := heq htO
  simpa only [Γ, gExt, hExt, intrExtLaunch] using hΓt

theorem intrExt_exp_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {z : E} (hz : ‖z‖ < 3 * R / 4) :
    intrExtLaunch (I := I) g hEnorm p hR hloc (0 : E) z 1 = z := by
  simpa only [one_smul] using
    intrExt_radial_eq (I := I) g hEnorm p hR hloc hz
      (t := (1 : Real)) ⟨zero_le_one, le_rfl⟩

private noncomputable def intrOriginHom {R : Real} :
    PartialDiffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞ where
  toPartialEquiv :=
    PartialEquiv.ofSet (Metric.ball (0 : E) (3 * R / 4))
  open_source := Metric.isOpen_ball
  open_target := Metric.isOpen_ball
  contMDiffOn_toFun := contMDiff_id.contMDiffOn
  contMDiffOn_invFun := contMDiff_id.contMDiffOn

section OriginEnergy

variable
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))

theorem intrExt_inner_zero (v w : E) :
    (intrExtMetric (I := I) g hEnorm p hR hloc).inner (0 : E) v w =
      Inner.inner Real v w := by
  have hzero :
      (0 : E) ∈ Metric.closedBall (0 : E) (3 * R / 4) := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_zero]
    linarith
  rw [intrExt_inner (I := I) g hEnorm p hR hloc hzero,
    intrPullMetric_inner, intrFrameMetric_zero]
  rfl

theorem intrOrigin_energy (z : E) :
    (1 / 2 : Real) *
        (intrExtMetric (I := I) g hEnorm p hR hloc).inner (0 : E) z z =
      (1 / 2 : Real) * ‖z‖ ^ 2 := by
  rw [intrExt_inner_zero (I := I) g hEnorm p hR hloc,
    real_inner_self_eq_norm_sq]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] in
private theorem halfSq_line_deriv2 (z : E) (t : Real) :
    (deriv^[2]
      ((fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) ∘
        fun s : Real => s • z)) t =
      ‖z‖ ^ 2 := by
  have hfun :
      ((fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) ∘
          fun s : Real => s • z) =
        fun s : Real => (1 / 2 : Real) * s ^ 2 * ‖z‖ ^ 2 := by
    funext s
    simp only [Function.comp_apply, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring
  rw [hfun]
  have hfirst :
      deriv (fun s : Real => (1 / 2 : Real) * s ^ 2 * ‖z‖ ^ 2) =
        fun s : Real => s * ‖z‖ ^ 2 := by
    funext s
    have hd :
        HasDerivAt
          (fun r : Real => (1 / 2 : Real) * r ^ 2 * ‖z‖ ^ 2)
          (s * ‖z‖ ^ 2) s := by
      convert
        (((hasDerivAt_id s).pow 2).const_mul (1 / 2 : Real)).mul_const
          (‖z‖ ^ 2) using 1
      all_goals simp only [id_eq]
      all_goals ring
    exact hd.deriv
  change
    deriv
        (deriv
          (fun s : Real => (1 / 2 : Real) * s ^ 2 * ‖z‖ ^ 2))
        t =
      ‖z‖ ^ 2
  rw [hfirst]
  simpa only [one_mul] using
    ((hasDerivAt_id t).mul_const (‖z‖ ^ 2)).deriv

theorem intrOrigin_hess_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (Y : E) :
    hessFun (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc)
        (fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) 0 Y Y =
      ‖Y‖ ^ 2 := by
  classical
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun y : E ↦ TangentSpace 𝓘(Real, E) y) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (y : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) y) :=
    inferInstance
  letI (y : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) y) :=
    inferInstance
  letI : ∀ y : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) y) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun y : E ↦ TangentSpace 𝓘(Real, E) y) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro y v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let f : E → Real := fun y => (1 / 2 : Real) * ‖y‖ ^ 2
  change hessFun (I := 𝓘(Real, E)) gExt f 0 Y Y = ‖Y‖ ^ 2
  let B : Real := 3 * R / 4
  let n : Real := ‖Y‖
  let ε : Real := B / (2 * (n + 1))
  let z₀ : E := ε • Y
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  have hn : 0 ≤ n := by
    dsimp only [n]
    exact norm_nonneg Y
  have hden : 0 < 2 * (n + 1) := by positivity
  have hε : 0 < ε := div_pos hB hden
  have hfrac : n / (2 * (n + 1)) < 1 := by
    rw [div_lt_one hden]
    linarith
  have hz₀ : ‖z₀‖ < 3 * R / 4 := by
    rw [show ‖z₀‖ = ε * n by
      dsimp only [z₀, n]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]]
    calc
      ε * n = B * (n / (2 * (n + 1))) := by
        dsimp only [ε]
        ring
      _ < B * 1 := mul_lt_mul_of_pos_left hfrac hB
      _ = 3 * R / 4 := by
        dsimp only [B]
        ring
  obtain ⟨c, hc, hline⟩ :=
    intrExt_radial_geo (I := I) g hEnorm p hR hloc hz₀
  let line : Real → E := fun t => t • z₀
  have hlineSmooth :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ line := by
    exact (contDiff_id.smul contDiff_const).contMDiff
  have h0O : (0 : Real) ∈ Set.Ioo (-c) c := by
    constructor <;> linarith
  have hfd :
      HasFDerivAt line
        (ContinuousLinearMap.smulRight
          (1 : Real →L[Real] Real) z₀) 0 := by
    simpa only [line] using
      (hasFDerivAt_id (0 : Real)).smul_const z₀
  have hf :
      ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞ f :=
    (contDiff_const.mul (contDiff_norm_sq Real)).contMDiff
  have hd2 :=
    deriv2_geo_on_at (I := 𝓘(Real, E)) gExt
      (U := Set.univ) isOpen_univ hf.contMDiffOn hlineSmooth
      (hline 0 h0O) (Set.mem_univ (line 0))
  rw [halfSq_line_deriv2 z₀ 0] at hd2
  rw [show line 0 = 0 by simp only [line, zero_smul],
    mfderiv_eq_fderiv, hfd.fderiv] at hd2
  have happ :
      (ContinuousLinearMap.smulRight
        (1 : Real →L[Real] Real) z₀) (1 : Real) = z₀ := by
    change (1 : Real) • z₀ = z₀
    exact one_smul Real z₀
  have hdiag :
      hessFun (I := 𝓘(Real, E)) gExt f 0 z₀ z₀ = ‖z₀‖ ^ 2 :=
    (congrArg₂
        (fun v w : E =>
          hessFun (I := 𝓘(Real, E)) gExt f 0 v w)
        happ.symm happ.symm).trans hd2.symm
  have hleft :=
    LinearMap.map_smul₂
      (hessFun (I := 𝓘(Real, E)) gExt f 0) ε Y (ε • Y)
  have hright :=
    (hessFun (I := 𝓘(Real, E)) gExt f 0 Y).map_smul ε Y
  have hscale :
      hessFun (I := 𝓘(Real, E)) gExt f 0
          (ε • Y) (ε • Y) =
        ε ^ 2 * hessFun (I := 𝓘(Real, E)) gExt f 0 Y Y := by
    calc
      _ = ε *
          hessFun (I := 𝓘(Real, E)) gExt f 0 Y (ε • Y) := by
        simpa only [smul_eq_mul] using hleft
      _ = ε * (ε *
          hessFun (I := 𝓘(Real, E)) gExt f 0 Y Y) := by
        exact congrArg (fun r : Real => ε * r)
          (by simpa only [smul_eq_mul] using hright)
      _ = _ := by ring
  have hnorm : ‖z₀‖ ^ 2 = ε ^ 2 * ‖Y‖ ^ 2 := by
    dsimp only [z₀]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    ring
  rw [show z₀ = ε • Y by rfl, hscale, hnorm] at hdiag
  nlinarith [sq_pos_of_pos hε]

theorem intrOrigin_hess_pos
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R K L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    {z Y : E} (hz : ‖z‖ < 3 * R / 4) (hzL : ‖z‖ ≤ L)
    (hz0 : z ≠ 0) (hY : Y ≠ 0) :
    0 <
      hessFun (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc)
        (fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) z Y Y := by
  classical
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun y : E ↦ TangentSpace 𝓘(Real, E) y) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (y : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) y) :=
    inferInstance
  letI (y : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) y) :=
    inferInstance
  letI : ∀ y : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) y) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun y : E ↦ TangentSpace 𝓘(Real, E) y) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro y v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (y : E) (v : TangentSpace 𝓘(Real, E) y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner y v v)) :=
    fun y v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt y v
  let hom : PartialDiffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞ :=
    intrOriginHom (E := E) (R := R)
  let B : ExpInvBranch (I := 𝓘(Real, E)) gExt hExt (0 : E) :=
    { hom := hom
      hom_eq := by
        intro y hy
        have hy' : ‖y‖ < 3 * R / 4 := by
          simpa only [hom, intrOriginHom, PartialEquiv.ofSet_source,
            Metric.mem_ball, dist_zero_right] using hy
        simpa only [expMapIntrinsic_def, gExt, hExt, intrExtLaunch] using
          intrExt_exp_zero (I := I) g hEnorm p hR hloc hy' }
  let f : E → Real := fun y => (1 / 2 : Real) * ‖y‖ ^ 2
  change
    0 < hessFun (I := 𝓘(Real, E)) gExt f z Y Y
  have hBsrc : (z : E) ∈ B.hom.source := by
    simpa only [B, hom, intrOriginHom, PartialEquiv.ofSet_source,
      Metric.mem_ball, dist_zero_right] using hz
  have henergy :
      branchEnergy (I := 𝓘(Real, E)) gExt B = f := by
    funext y
    change
      (1 / 2 : Real) * gExt.inner (0 : E) y y =
        (1 / 2 : Real) * ‖y‖ ^ 2
    simpa only [gExt] using
      intrOrigin_energy (I := I) g hEnorm p hR hloc y
  let expf : E → E := fun u =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt (0 : E) u
  have hzBall : z ∈ Metric.ball (0 : E) (3 * R / 4) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hexpid : expf =ᶠ[𝓝 z] id := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzBall] with y hy
    have hy' : ‖y‖ < 3 * R / 4 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hy
    simpa only [expf, id_eq, expMapIntrinsic_def, gExt, hExt,
      intrExtLaunch] using
      intrExt_exp_zero (I := I) g hEnorm p hR hloc hy'
  have hDexp (W : E) :
      mfderiv 𝓘(Real, E) 𝓘(Real, E) expf z W = W := by
    rw [hexpid.mfderiv_eq, mfderiv_id]
    rfl
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt (0 : E) z
  let J : E → Real → E := fun W =>
    intrinsicJacobi (I := 𝓘(Real, E)) gExt hExt (0 : E) z W
  have hγone : γ 1 = z := by
    simpa only [γ, gExt, hExt, intrExtLaunch] using
      intrExt_exp_zero (I := I) g hEnorm p hR hloc hz
  have hJone (W : E) : J W 1 = W := by
    have hraw :=
      congrArg (fun V => (V : E))
        (intrinsic_jacobi_one
          (I := 𝓘(Real, E)) gExt hExt (0 : E) z W)
    have hraw' :
        J W 1 =
          mfderiv 𝓘(Real, E) 𝓘(Real, E) expf z W := by
      simpa only [J, intrinsicJacobi, expf] using hraw
    exact hraw'.trans (hDexp W)
  have hγone' :
      intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt (0 : E) z 1 =
        z := by
    simpa only [γ] using hγone
  have hJone' (V : E) :
      intrinsicJacobi
          (I := 𝓘(Real, E)) gExt hExt (0 : E) z V 1 =
        V := by
    simpa only [J] using hJone V
  have hfence :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        ‖intrExtLaunch (I := I) g hEnorm p hR hloc
          (0 : E) z t‖ < 3 * R / 4 := by
    intro t ht
    have htAbs : |t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    calc
      ‖intrExtLaunch (I := I) g hEnorm p hR hloc
          (0 : E) z t‖ =
          ‖t • z‖ := congrArg norm
            (intrExt_radial_eq (I := I) g hEnorm p hR hloc hz ht)
      _ = |t| * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖z‖ := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right htAbs (norm_nonneg z)
      _ < 3 * R / 4 := hz
  have hspeedLe : Real.sqrt (gExt.inner (0 : E) z z) ≤ L := by
    rw [show gExt.inner (0 : E) z z = Inner.inner Real z z by
      simpa only [gExt] using
        intrExt_inner_zero (I := I) g hEnorm p hR hloc z z,
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)]
    exact hzL
  let d : Real := Inner.inner Real z z
  let α : Real := Inner.inner Real z Y / d
  let W : E := Y - α • z
  have hdpos : 0 < d := by
    dsimp only [d]
    exact real_inner_self_pos.mpr hz0
  have hperpE : Inner.inner Real z W = 0 := by
    change (innerSL Real z) W = 0
    rw [show W = Y - α • z by rfl, map_sub, map_smul]
    change
      Inner.inner Real z Y - α * Inner.inner Real z z = 0
    dsimp only [α, d]
    field_simp [ne_of_gt hdpos]
    ring
  have hperp : gExt.inner (0 : E) z W = 0 := by
    rw [show gExt.inner (0 : E) z W = Inner.inner Real z W by
      simpa only [gExt] using
        intrExt_inner_zero (I := I) g hEnorm p hR hloc z W]
    exact hperpE
  have hdecomp : Y = W + α • z := by
    dsimp only [W]
    abel
  have hf :
      ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞ f := by
    exact
      (contDiff_const.mul (contDiff_norm_sq Real)).contMDiff
  have hdiag :
      hessFun (I := 𝓘(Real, E)) gExt f z z z = ‖z‖ ^ 2 := by
    obtain ⟨c, hc, hline⟩ :=
      intrExt_radial_geo (I := I) g hEnorm p hR hloc hz
    let line : Real → E := fun t => t • z
    have hlineSmooth :
        ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ line := by
      exact (contDiff_id.smul contDiff_const).contMDiff
    have h1O : (1 : Real) ∈ Set.Ioo (-c) c := by
      constructor <;> linarith
    have hfd :
        HasFDerivAt line
          (ContinuousLinearMap.smulRight
            (1 : Real →L[Real] Real) z) 1 := by
      simpa only [line] using
        (hasFDerivAt_id (1 : Real)).smul_const z
    have hd2 :=
      deriv2_geo_on_at (I := 𝓘(Real, E)) gExt
        (U := Set.univ) isOpen_univ hf.contMDiffOn hlineSmooth
        (hline 1 h1O) (Set.mem_univ (line 1))
    rw [halfSq_line_deriv2 z 1] at hd2
    rw [show line 1 = z by simp only [line, one_smul],
      mfderiv_eq_fderiv, hfd.fderiv] at hd2
    have happ :
        (ContinuousLinearMap.smulRight
          (1 : Real →L[Real] Real) z) (1 : Real) = z := by
      change (1 : Real) • z = z
      exact one_smul Real z
    exact
      (congrArg₂
          (fun v w : E =>
            hessFun (I := 𝓘(Real, E)) gExt f z v w)
          happ.symm happ.symm).trans hd2.symm
  have hcross :
      hessFun (I := 𝓘(Real, E)) gExt f z W z = 0 := by
    have hh :=
      branchEnergy_hess
        (I := 𝓘(Real, E)) B (u := z) (w₁ := W) (w₂ := z) hBsrc
    dsimp only at hh
    rw [henergy, hγone', hJone' W, hJone' z] at hh
    have hself :
        J z 1 =
          Variation.curveVelocity (I := 𝓘(Real, E)) γ 1 := by
      simpa only [γ, J] using
        intrJacobi_self
          (I := 𝓘(Real, E)) gExt hExt (0 : E) z
    have hdperp :=
      intrJacobi_dperp
        (I := 𝓘(Real, E)) gExt hExt (0 : E) z W
          one_ne_zero hperp
    have hpair :
        gExt.inner (γ 1)
            (CovariantDerivativeAlong.covDerivAlong
              (I := 𝓘(Real, E)) gExt γ (J W) 1)
            (J z 1) = 0 := by
      rw [hself, gExt.symm]
      simpa only [γ, J] using hdperp
    dsimp only [γ, J] at hpair
    rw [hγone', hJone' z] at hpair
    exact hh.trans hpair
  have hcross' :
      hessFun (I := 𝓘(Real, E)) gExt f z z W = 0 := by
    rw [(hessFun_symm_of_boundaryless
      (I := 𝓘(Real, E)) gExt hf) z z W]
    exact hcross
  have hscale :
      hessFun (I := 𝓘(Real, E)) gExt f z
          (α • z) (α • z) =
        α ^ 2 *
          hessFun (I := 𝓘(Real, E)) gExt f z z z := by
    have hleft :=
      LinearMap.map_smul₂
        (hessFun (I := 𝓘(Real, E)) gExt f z)
        α z (α • z)
    have hright :=
      (hessFun (I := 𝓘(Real, E)) gExt f z z).map_smul α z
    calc
      _ = α *
          hessFun (I := 𝓘(Real, E)) gExt f z z (α • z) := by
        simpa only [smul_eq_mul] using hleft
      _ = α * (α *
          hessFun (I := 𝓘(Real, E)) gExt f z z z) := by
        exact congrArg (fun r : Real => α * r)
          (by simpa only [smul_eq_mul] using hright)
      _ = _ := by ring
  by_cases hW : W = 0
  · have hYeq : Y = α • z := by
      rw [hdecomp, hW, zero_add]
    have hα : α ≠ 0 := by
      intro hα
      apply hY
      rw [hYeq, hα, zero_smul]
    rw [hYeq]
    rw [hscale, hdiag]
    positivity
  · have hpair :=
      intrExt_pair_pos
        (I := I) g hEnorm p hR hloc z W hfence hspeedLe
          hz0 hW hperp hK hRm hsmall
    have hh :=
      branchEnergy_hess
        (I := 𝓘(Real, E)) B (u := z) (w₁ := W) (w₂ := W) hBsrc
    dsimp only at hh
    rw [henergy] at hh
    have hWW :
        0 < hessFun (I := 𝓘(Real, E)) gExt f z W W := by
      dsimp only at hpair
      have hraw :
          0 <
            hessFun (I := 𝓘(Real, E)) gExt f
              (intrinsicGeodesic
                (I := 𝓘(Real, E)) gExt hExt (0 : E) z 1)
              (intrinsicJacobi
                (I := 𝓘(Real, E)) gExt hExt (0 : E) z W 1)
              (intrinsicJacobi
                (I := 𝓘(Real, E)) gExt hExt (0 : E) z W 1) := by
        rw [hh]
        exact hpair
      rw [hJone' W] at hraw
      rw [hγone'] at hraw
      exact hraw
    have hcrossA :
        hessFun (I := 𝓘(Real, E)) gExt f z W (α • z) = 0 := by
      have hs :=
        (hessFun (I := 𝓘(Real, E)) gExt f z W).map_smul α z
      calc
        _ = α *
            hessFun (I := 𝓘(Real, E)) gExt f z W z := by
          simpa only [smul_eq_mul] using hs
        _ = 0 := by rw [hcross, mul_zero]
    have hcrossA' :
        hessFun (I := 𝓘(Real, E)) gExt f z (α • z) W = 0 := by
      rw [(hessFun_symm_of_boundaryless
        (I := 𝓘(Real, E)) gExt hf) z (α • z) W]
      exact hcrossA
    have hexpand :
        hessFun (I := 𝓘(Real, E)) gExt f z
            (W + α • z) (W + α • z) =
          (hessFun (I := 𝓘(Real, E)) gExt f z W W +
            hessFun (I := 𝓘(Real, E)) gExt f z W (α • z)) +
          (hessFun (I := 𝓘(Real, E)) gExt f z (α • z) W +
            hessFun (I := 𝓘(Real, E)) gExt f z
              (α • z) (α • z)) := by
      have hleft :=
        LinearMap.map_add₂
          (hessFun (I := 𝓘(Real, E)) gExt f z)
          W (α • z) (W + α • z)
      have hrightW :=
        (hessFun (I := 𝓘(Real, E)) gExt f z W).map_add W (α • z)
      have hrightA :=
        (hessFun (I := 𝓘(Real, E)) gExt f z (α • z)).map_add
          W (α • z)
      exact hleft.trans
        (congrArg₂ (fun a b : Real => a + b) hrightW hrightA)
    have hrad : 0 ≤ α ^ 2 * ‖z‖ ^ 2 :=
      mul_nonneg (sq_nonneg α) (sq_nonneg ‖z‖)
    rw [hdecomp, hexpand, hcrossA, hcrossA', hscale, hdiag,
      add_zero, zero_add]
    exact add_pos_of_pos_of_nonneg hWW hrad

theorem intrOrigin_hess_all
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R K L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    {z Y : E} (hz : ‖z‖ < 3 * R / 4) (hzL : ‖z‖ ≤ L)
    (hY : Y ≠ 0) :
    0 <
      hessFun (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc)
        (fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) z Y Y := by
  by_cases hz0 : z = 0
  · subst z
    rw [intrOrigin_hess_zero (I := I) g hEnorm p hR hloc Y]
    exact sq_pos_of_pos (norm_pos_iff.mpr hY)
  · exact
      intrOrigin_hess_pos (I := I) g hEnorm p hR hloc
        hK hRm hsmall hz hzL hz0 hY

theorem intrOrigin_strict
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R K L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    {γ : Real → E} (hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ)
    {D : Set Real}
    (hgeo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc) γ
        (interior D))
    (hD : Convex Real D)
    (hfence : ∀ t ∈ interior D, ‖γ t‖ < 3 * R / 4)
    (hbound : ∀ t ∈ interior D, ‖γ t‖ ≤ L)
    (hvel : ∀ t ∈ interior D,
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real) : E) ≠ 0) :
    StrictConvexOn Real D
      ((fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) ∘ γ) := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  let f : E → Real := fun y => (1 / 2 : Real) * ‖y‖ ^ 2
  have hf :
      ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞ f :=
    (contDiff_const.mul (contDiff_norm_sq Real)).contMDiff
  have hcont : ContinuousOn (f ∘ γ) D :=
    (hf.continuous.comp hγ.continuous).continuousOn
  refine
    strictConvex_geo_on (I := 𝓘(Real, E)) gExt
      (U := Set.univ) isOpen_univ hf.contMDiffOn hγ hgeo hD hcont
      (fun _ _ => Set.mem_univ _) ?_
  intro t ht
  simpa only [gExt, f] using
    intrOrigin_hess_all (I := I) g hEnorm p hR hloc
      hK hRm hsmall (hfence t ht) (hbound t ht) (hvel t ht)

theorem intrExt_edge_core
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a K L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    (h2aL : 2 * a < L) (hbudget : a + L < 3 * R / 4)
    {x y : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a)
    (v : TangentSpace 𝓘(Real, E) x)
    (hv :
      Real.sqrt
          ((intrExtMetric (I := I) g hEnorm p hR hloc).inner x v v) ≤
        L)
    (hend : intrExtLaunch (I := I) g hEnorm p hR hloc x v 1 = y) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖intrExtLaunch (I := I) g hEnorm p hR hloc x v t‖ ≤ a := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v
  have hγ0 : γ 0 = x :=
    intrinsicGeodesic_zero (I := 𝓘(Real, E)) gExt hExt x v
  have hγ1 : γ 1 = y := by
    simpa only [γ, gExt, hExt, intrExtLaunch] using hend
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  intro t ht
  by_cases hv0 : v = 0
  · have hdist :=
      intrinsicGeodesic_riemannianEDist_le
        (I := 𝓘(Real, E)) gExt hExt x v
        (s := 0) (t := t) ht.1
    have hspeed0 : Real.sqrt (gExt.inner x v v) = 0 := by
      rw [hv0]
      simp
    rw [hspeed0, zero_mul, ENNReal.ofReal_zero] at hdist
    have heq : γ 0 = γ t :=
      riemannianEDist_eq_zero_imp_eq
        (I := 𝓘(Real, E)) (γ 0) (γ t)
        (le_antisymm (by simpa only [γ, sub_zero] using hdist) bot_le)
    rw [hγ0] at heq
    simpa only [γ, gExt, hExt, intrExtLaunch, ← heq] using hx
  · have hfence :
        ∀ s ∈ Set.Icc (0 : Real) 1, ‖γ s‖ < 3 * R / 4 := by
      simpa only [γ, gExt, hExt, intrExtLaunch] using
        intrExt_shortLaunch_fenced
          (I := I) g hEnorm p hR hloc hx v hv hbudget
    have hscale :
        ∀ s ∈ Set.Icc (0 : Real) 1, ‖γ s‖ ≤ a + L / 2 := by
      simpa only [γ, gExt, hExt, intrExtLaunch] using
        intrExt_scale_bound
          (I := I) g hEnorm p hR hloc hx hy v hv hbudget hend
    have hstrict :
        StrictConvexOn Real (Set.Icc (0 : Real) 1)
          ((fun z : E => (1 / 2 : Real) * ‖z‖ ^ 2) ∘ γ) :=
      intrOrigin_strict (I := I) g hEnorm p hR hloc
        hK hRm hsmall
        (intrinsicGeodesic_contMDiff
          (I := 𝓘(Real, E)) gExt hExt x v)
        (D := Set.Icc (0 : Real) 1)
        (by
          simpa only [interior_Icc] using
            (intrinsicGeodesic_isGeodesic
              (I := 𝓘(Real, E)) gExt hExt x v).isGeodesicOn
                (Set.Ioo (0 : Real) 1))
        (convex_Icc (0 : Real) 1)
        (fun s hs => by
          have hs' : s ∈ Set.Ioo (0 : Real) 1 := by
            simpa only [interior_Icc] using hs
          exact hfence s ⟨hs'.1.le, hs'.2.le⟩)
        (fun s hs => by
          have hs' : s ∈ Set.Ioo (0 : Real) 1 := by
            simpa only [interior_Icc] using hs
          have hsBound := hscale s ⟨hs'.1.le, hs'.2.le⟩
          linarith)
        (fun s _hs =>
          intrGeo_vel_ne
            (I := 𝓘(Real, E)) gExt hExt x v hv0 s)
    have hjensen :=
      hstrict.convexOn.2
        (Set.left_mem_Icc.mpr zero_le_one)
        (Set.right_mem_Icc.mpr zero_le_one)
        (sub_nonneg.mpr ht.2) ht.1 (by ring : (1 - t) + t = 1)
    have henergy :
        (1 / 2 : Real) * ‖γ t‖ ^ 2 ≤
          (1 - t) * ((1 / 2 : Real) * ‖γ 0‖ ^ 2) +
            t * ((1 / 2 : Real) * ‖γ 1‖ ^ 2) := by
      simpa only [Function.comp_apply, smul_eq_mul, mul_zero, zero_add,
        mul_one] using hjensen
    rw [hγ0, hγ1] at henergy
    have hxSq : ‖x‖ ^ 2 ≤ a ^ 2 :=
      (sq_le_sq₀ (norm_nonneg x) ha).2 hx
    have hySq : ‖y‖ ^ 2 ≤ a ^ 2 :=
      (sq_le_sq₀ (norm_nonneg y) ha).2 hy
    have hxt :
        (1 - t) * ‖x‖ ^ 2 ≤ (1 - t) * a ^ 2 :=
      mul_le_mul_of_nonneg_left hxSq (sub_nonneg.mpr ht.2)
    have hyt : t * ‖y‖ ^ 2 ≤ t * a ^ 2 :=
      mul_le_mul_of_nonneg_left hySq ht.1
    have hγSq : ‖γ t‖ ^ 2 ≤ a ^ 2 := by
      nlinarith
    have hnorm : ‖γ t‖ ≤ a :=
      (sq_le_sq₀ (norm_nonneg (γ t)) ha).1 hγSq
    simpa only [γ, gExt, hExt, intrExtLaunch] using hnorm

theorem intrOrigin_no_return
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R K L T : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    (hT : 0 < T)
    {γ : Real → E} (hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ)
    (hgeo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc) γ
        (Set.Ioo (0 : Real) (2 * T)))
    (hfence :
      ∀ t ∈ Set.Ioo (0 : Real) (2 * T), ‖γ t‖ < 3 * R / 4)
    (hbound : ∀ t ∈ Set.Ioo (0 : Real) (2 * T), ‖γ t‖ ≤ L)
    (hvel : ∀ t ∈ Set.Ioo (0 : Real) (2 * T),
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real) : E) ≠ 0)
    (h0T : γ 0 = γ T) (hT2 : γ T = γ (2 * T)) :
    False := by
  have hstrict :=
    intrOrigin_strict (I := I) g hEnorm p hR hloc hK hRm hsmall
      hγ (D := Set.Icc (0 : Real) (2 * T))
      (by simpa only [interior_Icc] using hgeo)
      (convex_Icc (0 : Real) (2 * T))
      (by simpa only [interior_Icc] using hfence)
      (by simpa only [interior_Icc] using hbound)
      (by simpa only [interior_Icc] using hvel)
  have h2T : 0 < 2 * T := mul_pos (by norm_num) hT
  have hlt :
      (((fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) ∘ γ)
          ((1 / 2 : Real) • (0 : Real) +
            (1 / 2 : Real) • (2 * T))) <
        (1 / 2 : Real) •
            (((fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) ∘ γ) 0) +
          (1 / 2 : Real) •
            (((fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) ∘ γ) (2 * T)) := by
    exact hstrict.2
      ⟨le_rfl, h2T.le⟩ ⟨h2T.le, le_rfl⟩
      (ne_of_lt h2T) (by norm_num) (by norm_num) (by norm_num)
  have hmid :
      (1 / 2 : Real) • (0 : Real) +
          (1 / 2 : Real) • (2 * T) = T := by
    simp only [smul_eq_mul]
    ring
  rw [hmid] at hlt
  simp only [Function.comp_apply, smul_eq_mul] at hlt
  rw [h0T, ← hT2] at hlt
  linarith

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
private theorem periodic_core_bound
    {γu γv : Real → E} {a c d T : Real}
    (hTdef : T = 1 + d) (hcPos : 0 < c) (hcd : c * d = 1)
    (hjoin : ∀ s : Real, γu (s + 1) = γv (1 - c * s))
    (hperiod : ∀ s : Real, γu (s + T) = γu s)
    (hcoreU : ∀ t ∈ Set.Icc (0 : Real) 1, ‖γu t‖ ≤ a)
    (hcoreV : ∀ t ∈ Set.Icc (0 : Real) 1, ‖γv t‖ ≤ a) :
    ∀ t ∈ Set.Ioo (0 : Real) (2 * T), ‖γu t‖ ≤ a := by
  have honeCore :
      ∀ t ∈ Set.Icc (0 : Real) T, ‖γu t‖ ≤ a := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · exact hcoreU t ⟨ht.1, ht1⟩
    · have hs0 : 0 ≤ t - 1 := sub_nonneg.mpr (le_of_not_ge ht1)
      have hsd : t - 1 ≤ d := by
        have ht' : t ≤ 1 + d := by
          simpa only [hTdef] using ht.2
        exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using ht')
      have hcs : 0 ≤ c * (t - 1) :=
        mul_nonneg hcPos.le hs0
      have hcs1 : c * (t - 1) ≤ 1 := by
        calc
          c * (t - 1) ≤ c * d :=
            mul_le_mul_of_nonneg_left hsd hcPos.le
          _ = 1 := hcd
      have hj := hjoin (t - 1)
      have htime : (t - 1) + 1 = t := by ring
      rw [htime] at hj
      rw [hj]
      exact hcoreV (1 - c * (t - 1))
        ⟨sub_nonneg.mpr hcs1, sub_le_self 1 hcs⟩
  intro t ht
  by_cases htT : t ≤ T
  · exact honeCore t ⟨ht.1.le, htT⟩
  · have hred : t - T ∈ Set.Icc (0 : Real) T := by
      constructor
      · exact sub_nonneg.mpr (le_of_not_ge htT)
      · apply sub_le_iff_le_add.mpr
        simpa only [two_mul] using ht.2.le
    have hp := hperiod (t - T)
    have heq : (t - T) + T = t := by ring
    rw [heq] at hp
    rw [hp]
    exact honeCore (t - T) hred

private theorem midpoint_minimal_loop
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a K L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    (h2aL : 2 * a < L) (hbudget : a + L < 3 * R / 4) :
    let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
      fun _ => inferInstance
    letI : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
    letI : EMetricSpace E :=
      EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    letI : CompleteSpace E :=
      (intrExt_complete (I := I) g hEnorm p hR hloc).complete
    let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
      fun z w =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z w
    let F : E × E → E := fun z =>
      expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
    let ell : E × E → Real := fun z =>
      Real.sqrt (gExt.inner z.1 z.2 z.2)
    let total : E × E × E → Real := fun z =>
      ell (z.1, z.2.1) + ell (z.1, z.2.2)
    ∀ (z₀ : E × E × E),
      IsMinOn total (shortBigons F ell a L) z₀ →
      total z₀ < 2 * L →
      ∀ (x₀ q₀ : E), ‖x₀‖ ≤ a →
        ell (x₀, q₀) ≤ L → q₀ ≠ 0 →
        F (x₀, q₀) = x₀ → total z₀ = ell (x₀, q₀) →
        ∃ z₁ : E × E × E,
          z₁ ∈ shortBigons F ell a L ∧
          IsMinOn total (shortBigons F ell a L) z₁ ∧
          z₁.2.1 ≠ 0 ∧ z₁.2.2 ≠ 0 ∧
          ell (z₁.1, z₁.2.1) < L ∧
          ell (z₁.1, z₁.2.2) < L := by
  dsimp only
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  let F : E × E → E := fun z =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
  let ell : E × E → Real := fun z =>
    Real.sqrt (gExt.inner z.1 z.2 z.2)
  let total : E × E × E → Real := fun z =>
    ell (z.1, z.2.1) + ell (z.1, z.2.2)
  intro z₀ hmin htotalLt x₀ q₀ hx₀ hqL hqne hloop htot
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x₀ q₀
  let m : E := γ (1 / 2)
  let w : E :=
    mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ (1 / 2) (1 : Real)
  have hγ0 : γ 0 = x₀ :=
    intrinsicGeodesic_zero
      (I := 𝓘(Real, E)) gExt hExt x₀ q₀
  have hγ1 : γ 1 = x₀ := by
    simpa only [γ, F, expMapIntrinsic_def] using hloop
  have hm : ‖m‖ ≤ a := by
    apply intrExt_edge_core
      (I := I) g hEnorm p hR hloc hK hRm hsmall h2aL hbudget
      hx₀ hx₀ q₀
    · simpa only [ell, gExt] using hqL
    · simpa only [γ, m, gExt, hExt, intrExtLaunch] using hγ1
    · norm_num
  have hcont :
      (fun s : Real => γ (s + 1 / 2)) =
        intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt m w := by
    simpa only [γ, m, w] using
      intrinsicGeodesic_continuation
        (I := 𝓘(Real, E)) gExt hExt x₀ q₀ (1 / 2)
  have hplus : F (m, (1 / 2 : Real) • w) = x₀ := by
    change
      intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt
        m ((1 / 2 : Real) • w) 1 = x₀
    have hscale :
        intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt
            m ((1 / 2 : Real) • w) 1 =
          intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt m w (1 / 2) :=
      intrinsicGeodesic_smul
        (I := 𝓘(Real, E)) gExt hExt m w (1 / 2)
    rw [hscale]
    rw [← congrFun hcont (1 / 2)]
    norm_num
    exact hγ1
  have hminus : F (m, (-1 / 2 : Real) • w) = x₀ := by
    change
      intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt
        m ((-1 / 2 : Real) • w) 1 = x₀
    have hscale :
        intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt
            m ((-1 / 2 : Real) • w) 1 =
          intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt m w (-1 / 2) :=
      intrinsicGeodesic_smul
        (I := 𝓘(Real, E)) gExt hExt m w (-1 / 2)
    rw [hscale]
    rw [← congrFun hcont (-1 / 2)]
    norm_num
    exact hγ0
  have hspeed :
      gExt.inner m w w = gExt.inner x₀ q₀ q₀ := by
    simpa only [γ, m, w] using
      intrinsicGeodesic_speedSq_eq
        (I := 𝓘(Real, E)) gExt hExt x₀ q₀ (1 / 2)
  have hellPlus :
      ell (m, (1 / 2 : Real) • w) =
        (1 / 2 : Real) * ell (x₀, q₀) := by
    simp only [ell]
    have hscale :
        Real.sqrt
            (gExt.inner m ((1 / 2 : Real) • w)
              ((1 / 2 : Real) • w)) =
          (1 / 2 : Real) * Real.sqrt (gExt.inner m w w) :=
      sqrt_gInner_smul_self
        (I := 𝓘(Real, E)) gExt m (by norm_num) w
    rw [hscale, hspeed]
  have hellMinus :
      ell (m, (-1 / 2 : Real) • w) =
        (1 / 2 : Real) * ell (x₀, q₀) := by
    simp only [ell]
    rw [show (-1 / 2 : Real) • w =
        (1 / 2 : Real) • (-w) by module]
    have hscale :
        Real.sqrt
            (gExt.inner m ((1 / 2 : Real) • (-w))
              ((1 / 2 : Real) • (-w))) =
          (1 / 2 : Real) * Real.sqrt (gExt.inner m (-w) (-w)) :=
      sqrt_gInner_smul_self
        (I := 𝓘(Real, E)) gExt m (by norm_num) (-w)
    have hneg : gExt.inner m (-w) (-w) = gExt.inner m w w := by
      have h :=
        gInner_smul_self
          (I := 𝓘(Real, E)) gExt m (-1 : Real) w
      simpa only [neg_one_smul, neg_sq, one_pow, one_mul] using h
    rw [hscale, hneg, hspeed]
  have hwne : w ≠ 0 := by
    simpa only [γ, w] using
      intrGeo_vel_ne
        (I := 𝓘(Real, E)) gExt hExt x₀ q₀ hqne (1 / 2)
  have hplusNe : (1 / 2 : Real) • w ≠ 0 :=
    smul_ne_zero (by norm_num) hwne
  have hminusNe : (-1 / 2 : Real) • w ≠ 0 :=
    smul_ne_zero (by norm_num) hwne
  let z₁ : E × E × E :=
    (m, ((1 / 2 : Real) • w, (-1 / 2 : Real) • w))
  have hz₁ : z₁ ∈ shortBigons F ell a L := by
    change
      ‖m‖ ≤ a ∧
      ‖F (m, (1 / 2 : Real) • w)‖ ≤ a ∧
      F (m, (1 / 2 : Real) • w) = F (m, (-1 / 2 : Real) • w) ∧
      ell (m, (1 / 2 : Real) • w) ≤ L ∧
      ell (m, (-1 / 2 : Real) • w) ≤ L ∧
      (1 / 2 : Real) • w ≠ (-1 / 2 : Real) • w
    refine ⟨hm, ?_, hplus.trans hminus.symm, ?_, ?_, ?_⟩
    · rw [hplus]
      exact hx₀
    · rw [hellPlus]
      have hqnonneg : 0 ≤ ell (x₀, q₀) := Real.sqrt_nonneg _
      exact (mul_le_of_le_one_left hqnonneg (by norm_num)).trans hqL
    · rw [hellMinus]
      have hqnonneg : 0 ≤ ell (x₀, q₀) := Real.sqrt_nonneg _
      exact (mul_le_of_le_one_left hqnonneg (by norm_num)).trans hqL
    · intro heq
      let q : E := (1 / 2 : Real) • w
      have hqneg : q = -q := by
        calc
          q = (-1 / 2 : Real) • w := heq
          _ = -q := by simp only [q]; module
      have htwo : (2 : Real) • q = 0 := by
        rw [two_smul]
        nth_rewrite 1 [hqneg]
        exact neg_add_cancel q
      have hq0 : q = 0 :=
        (smul_eq_zero.mp htwo).resolve_left (by norm_num)
      exact hplusNe (by simpa only [q] using hq0)
  have htotal₁ : total z₁ = total z₀ := by
    calc
      total z₁ =
          ell (m, (1 / 2 : Real) • w) +
            ell (m, (-1 / 2 : Real) • w) := by
              rfl
      _ = ell (x₀, q₀) := by
        rw [hellPlus, hellMinus]
        ring
      _ = total z₀ := htot.symm
  have hmin₁ : IsMinOn total (shortBigons F ell a L) z₁ := by
    apply isMinOn_iff.mpr
    intro z hz
    rw [htotal₁]
    exact (isMinOn_iff.mp hmin) z hz
  have hqLt : ell (x₀, q₀) < 2 * L := by
    have hqLtRaw := htotalLt
    rw [htot] at hqLtRaw
    simpa only [ell, gExt] using hqLtRaw
  have hplusLt : ell (m, (1 / 2 : Real) • w) < L := by
    rw [hellPlus]
    calc
      (1 / 2 : Real) * ell (x₀, q₀) < (1 / 2 : Real) * (2 * L) :=
        mul_lt_mul_of_pos_left hqLt (by norm_num)
      _ = L := by ring
  have hminusLt : ell (m, (-1 / 2 : Real) • w) < L := by
    rw [hellMinus]
    calc
      (1 / 2 : Real) * ell (x₀, q₀) < (1 / 2 : Real) * (2 * L) :=
        mul_lt_mul_of_pos_left hqLt (by norm_num)
      _ = L := by ring
  exact
    ⟨z₁, hz₁, hmin₁,
      by simpa only [z₁] using hplusNe,
      by simpa only [z₁] using hminusNe,
      by simpa only [z₁] using hplusLt,
      by simpa only [z₁] using hminusLt⟩

theorem intrCore_short_inj
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a K L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    (h2aL : 2 * a < L) (hbudget : a + L < 3 * R / 4)
    {x y u v : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a)
    (huL :
      Real.sqrt
          ((intrExtMetric (I := I) g hEnorm p hR hloc).inner x u u) <
        L)
    (hvL :
      Real.sqrt
          ((intrExtMetric (I := I) g hEnorm p hR hloc).inner x v v) <
        L)
    (huEnd : intrExtLaunch (I := I) g hEnorm p hR hloc x u 1 = y)
    (hvEnd : intrExtLaunch (I := I) g hEnorm p hR hloc x v 1 = y) :
    u = v := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  let F : E × E → E := fun z =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
  let ell : E × E → Real := fun z =>
    Real.sqrt (gExt.inner z.1 z.2 z.2)
  have hlift :
      ContMDiff
        (𝓘(Real, E).prod 𝓘(Real, E))
        𝓘(Real, E).tangent ∞
        (fun z : E × E =>
          (⟨z.1, z.2⟩ : TangentBundle 𝓘(Real, E) E)) := by
    have h :=
      contMDiff_tangentBundleModelSpaceHomeomorph_symm
        (I := 𝓘(Real, E)) (n := (∞ : WithTop ℕ∞))
    unfold ModelProd at h
    rw [← chartedSpaceSelf_prod] at h
    simpa only [tangentBundleModelSpaceHomeomorph_coe_symm,
      TotalSpace.toProd, Equiv.coe_fn_symm_mk] using h
  have hFmd :
      ContMDiff
        (𝓘(Real, E).prod 𝓘(Real, E))
        𝓘(Real, E) ∞ F := by
    simpa only [F, Function.comp_apply] using
      (intrinsicExp_smooth (I := 𝓘(Real, E)) gExt hExt).comp hlift
  have hFcd : ContDiff Real ∞ F := by
    rw [← contMDiff_iff_contDiff, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hFmd
  have hFcont : Continuous F := hFcd.continuous
  have hellCont : Continuous ell := by
    have hquad :=
      (metricQuad_cont (I := 𝓘(Real, E)) gExt).comp hlift.continuous
    simpa only [ell, TotalSpace.proj, TotalSpace.snd] using
      Real.continuous_sqrt.comp hquad
  have hshortNotConj :
      ∀ x₀ u₀ : E, ‖x₀‖ ≤ a → ell (x₀, u₀) ≤ L →
        ¬ IsConjVec
          (I := 𝓘(Real, E)) gExt hExt x₀ u₀ := by
    intro x₀ u₀ hx₀ hu₀
    have hfence :
        ∀ t ∈ Set.Icc (0 : Real) 1,
          ‖intrExtLaunch (I := I) g hEnorm p hR hloc x₀ u₀ t‖ <
            3 * R / 4 := by
      apply intrExt_shortLaunch_fenced
        (I := I) g hEnorm p hR hloc hx₀ u₀
      · simpa only [ell, gExt] using hu₀
      · exact hbudget
    exact intrExt_not_conj_of_shortLaunch
      (I := I) g hEnorm p hR hloc u₀ hfence
        (by simpa only [ell, gExt] using hu₀)
        hK hRm hsmall
  have hdiag :
      ∀ x₀ u₀ : E, ‖x₀‖ ≤ a → ell (x₀, u₀) ≤ L →
        ∃ U ∈ 𝓝 (x₀, u₀),
          Set.InjOn (fun z : E × E => (F z, z.1)) U := by
    intro x₀ u₀ hx₀ hu₀
    have hnot :
        ¬ IsConjVec
          (I := 𝓘(Real, E)) gExt hExt x₀ u₀ := by
      exact hshortNotConj x₀ u₀ hx₀ hu₀
    let f : E → E := fun w =>
      expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x₀ w
    have hfM :
        HasMFDerivAt 𝓘(Real, E) 𝓘(Real, E) f u₀
          (mfderiv 𝓘(Real, E) 𝓘(Real, E) f u₀) :=
      ((intrinsicFiber_smooth
        (I := 𝓘(Real, E)) gExt hExt x₀).contMDiffAt
          |>.mdifferentiableAt (by simp)).hasMFDerivAt
    have hf :
        HasFDerivAt f
          (mfderiv 𝓘(Real, E) 𝓘(Real, E) f u₀) u₀ :=
      hasMFDerivAt_iff_hasFDerivAt.mp hfM
    have hpartial :
        Analysis.partialFDeriv₂ F x₀ u₀ =
          mfderiv 𝓘(Real, E) 𝓘(Real, E) f u₀ := by
      apply Analysis.partialFDeriv₂_eq
        ((hFcd.differentiable (by simp)).differentiableAt)
      simpa only [F, f] using hf
    have hinj :
        Function.Injective (Analysis.partialFDeriv₂ F x₀ u₀) := by
      rw [hpartial]
      simpa only [IsConjVec, f, not_not] using hnot
    exact pinned_inj_nhds F hFcd hinj
  have hLpos : 0 < L :=
    lt_of_le_of_lt (Real.sqrt_nonneg _) huL
  obtain ⟨c, hc, hlower⟩ :=
    metric_lower_on
      (I := 𝓘(Real, E))
      (K := Metric.closedBall (0 : E) a)
      (isCompact_closedBall (0 : E) a)
      gExt (flatModelMetric E)
  let B : Real := Real.sqrt (L ^ 2 / c)
  have hlaunchBound :
      ∀ x₀ : E, ‖x₀‖ ≤ a → ∀ w : E,
        ell (x₀, w) ≤ L → ‖w‖ ≤ B := by
    intro x₀ hx₀ w hw
    have hxBall : x₀ ∈ Metric.closedBall (0 : E) a := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx₀
    have hl := hlower x₀ hxBall w
    change c * Inner.inner Real w w ≤ gExt.inner x₀ w w at hl
    rw [real_inner_self_eq_norm_sq] at hl
    have hinner : 0 ≤ gExt.inner x₀ w w :=
      gInner_self_nonneg (I := 𝓘(Real, E)) gExt x₀ w
    have hellSq : gExt.inner x₀ w w ≤ L ^ 2 := by
      have hsqrtSq :
          Real.sqrt (gExt.inner x₀ w w) ^ 2 =
            gExt.inner x₀ w w :=
        Real.sq_sqrt hinner
      rw [← hsqrtSq]
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) hLpos.le).2
        (by simpa only [ell] using hw)
    have hwSq : ‖w‖ ^ 2 ≤ L ^ 2 / c :=
      (le_div_iff₀ hc).2 (by
        simpa only [mul_comm] using hl.trans hellSq)
    have hquot : 0 ≤ L ^ 2 / c :=
      div_nonneg (sq_nonneg L) hc.le
    have hBSq : B ^ 2 = L ^ 2 / c := by
      simpa only [B] using Real.sq_sqrt hquot
    exact
      (sq_le_sq₀ (norm_nonneg w) (Real.sqrt_nonneg _)).1
        (by simpa only [B, hBSq] using hwSq)
  have hbadCompact : IsCompact (shortBigons F ell a L) := by
    apply shortBigons_compact F ell a L B hFcont hellCont hdiag
    intro z hz
    exact ⟨
      hlaunchBound z.1 hz.1 z.2.1 hz.2.2.2.1,
      hlaunchBound z.1 hz.1 z.2.2 hz.2.2.2.2.1⟩
  by_contra huv
  let zInit : E × E × E := (x, u, v)
  have hzInit : zInit ∈ shortBigons F ell a L := by
    refine ⟨hx, ?_, ?_, huL.le, hvL.le, huv⟩
    · have hFu : F (x, u) = y := by
        simpa only [F, gExt, hExt, expMapIntrinsic_def,
          intrExtLaunch] using huEnd
      simpa only [zInit, hFu] using hy
    · have hFu : F (x, u) = y := by
        simpa only [F, gExt, hExt, expMapIntrinsic_def,
          intrExtLaunch] using huEnd
      have hFv : F (x, v) = y := by
        simpa only [F, gExt, hExt, expMapIntrinsic_def,
          intrExtLaunch] using hvEnd
      simp only [zInit, hFu, hFv]
  have hbadNonempty : (shortBigons F ell a L).Nonempty :=
    ⟨zInit, hzInit⟩
  let total : E × E × E → Real := fun z =>
    ell (z.1, z.2.1) + ell (z.1, z.2.2)
  have htotal : Continuous total :=
    (hellCont.comp
      (continuous_fst.prodMk continuous_snd.fst)).add
      (hellCont.comp
        (continuous_fst.prodMk continuous_snd.snd))
  obtain ⟨z₀, hz₀, hmin⟩ :=
    hbadCompact.exists_isMinOn hbadNonempty htotal.continuousOn
  have hminInit : total z₀ ≤ total zInit :=
    (isMinOn_iff.mp hmin) zInit hzInit
  have htotalLt : total z₀ < 2 * L := by
    dsimp only [total, zInit] at hminInit ⊢
    exact hminInit.trans_lt
      (by simpa only [ell, gExt, two_mul] using add_lt_add huL hvL)
  have hslack :
      ell (z₀.1, z₀.2.1) < L ∨
        ell (z₀.1, z₀.2.2) < L := by
    by_contra h
    push Not at h
    dsimp only [total] at htotalLt
    have htwo : 2 * L ≤ ell (z₀.1, z₀.2.1) + ell (z₀.1, z₀.2.2) := by
      calc
        2 * L = L + L := by ring
        _ ≤ ell (z₀.1, z₀.2.1) + ell (z₀.1, z₀.2.2) :=
          add_le_add h.1 h.2
    exact (not_lt_of_ge htwo) htotalLt
  have midpoint_min
      (x₀ q₀ : E) (hx₀ : ‖x₀‖ ≤ a)
      (hqL : ell (x₀, q₀) ≤ L) (hqne : q₀ ≠ 0)
      (hloop : F (x₀, q₀) = x₀)
      (htot : total z₀ = ell (x₀, q₀)) :
      ∃ z₁ : E × E × E,
        z₁ ∈ shortBigons F ell a L ∧
        IsMinOn total (shortBigons F ell a L) z₁ ∧
        z₁.2.1 ≠ 0 ∧ z₁.2.2 ≠ 0 ∧
        ell (z₁.1, z₁.2.1) < L ∧
        ell (z₁.1, z₁.2.2) < L :=
    midpoint_minimal_loop (I := I) g hEnorm p hR hloc hK hRm hsmall
      h2aL hbudget z₀ hmin htotalLt x₀ q₀ hx₀ hqL hqne hloop htot
  have hnormalize :
      ∃ z₁ : E × E × E,
        z₁ ∈ shortBigons F ell a L ∧
        IsMinOn total (shortBigons F ell a L) z₁ ∧
        z₁.2.1 ≠ 0 ∧ z₁.2.2 ≠ 0 ∧
        (ell (z₁.1, z₁.2.1) < L ∨
          ell (z₁.1, z₁.2.2) < L) := by
    by_cases hu₀ : z₀.2.1 = 0
    · have hv₀ : z₀.2.2 ≠ 0 := by
        intro hv₀
        exact hz₀.2.2.2.2.2 (hu₀.trans hv₀.symm)
      have hFzero : F (z₀.1, 0) = z₀.1 := by
        simpa only [F] using
          expMapIntrinsic_zero
            (I := 𝓘(Real, E)) gExt hExt z₀.1
      have hloop : F (z₀.1, z₀.2.2) = z₀.1 := by
        rw [← hz₀.2.2.1, hu₀, hFzero]
      have htot :
          total z₀ = ell (z₀.1, z₀.2.2) := by
        have hell0 : ell (z₀.1, 0) = 0 := by
          simp only [ell]
          have hzero :=
            sqrt_gInner_smul_self
              (I := 𝓘(Real, E)) gExt z₀.1
                (b := (0 : Real)) (by norm_num) z₀.2.2
          simpa only [zero_smul, zero_mul] using hzero
        dsimp only [total]
        rw [hu₀, hell0, zero_add]
      obtain ⟨z₁, hz₁, hmin₁, hu₁, hv₁, huLt, hvLt⟩ :=
        midpoint_min z₀.1 z₀.2.2 hz₀.1 hz₀.2.2.2.2.1
          hv₀ hloop htot
      exact ⟨z₁, hz₁, hmin₁, hu₁, hv₁, Or.inl huLt⟩
    · by_cases hv₀ : z₀.2.2 = 0
      · have hFzero : F (z₀.1, 0) = z₀.1 := by
          simpa only [F] using
            expMapIntrinsic_zero
              (I := 𝓘(Real, E)) gExt hExt z₀.1
        have hloop : F (z₀.1, z₀.2.1) = z₀.1 := by
          rw [hz₀.2.2.1, hv₀, hFzero]
        have htot :
            total z₀ = ell (z₀.1, z₀.2.1) := by
          have hell0 : ell (z₀.1, 0) = 0 := by
            simp only [ell]
            have hzero :=
              sqrt_gInner_smul_self
                (I := 𝓘(Real, E)) gExt z₀.1
                  (b := (0 : Real)) (by norm_num) z₀.2.1
            simpa only [zero_smul, zero_mul] using hzero
          dsimp only [total]
          rw [hv₀, hell0, add_zero]
        obtain ⟨z₁, hz₁, hmin₁, hu₁, hv₁, huLt, hvLt⟩ :=
          midpoint_min z₀.1 z₀.2.1 hz₀.1 hz₀.2.2.2.1
            hu₀ hloop htot
        exact ⟨z₁, hz₁, hmin₁, hu₁, hv₁, Or.inl huLt⟩
      · exact ⟨z₀, hz₀, hmin, hu₀, hv₀, hslack⟩
  obtain ⟨z₁, hz₁, hmin₁, hu₁, hv₁, hslack₁⟩ := hnormalize
  have terminal_opposite
      (z : E × E × E) (hz : z ∈ shortBigons F ell a L)
      (hzmin : IsMinOn total (shortBigons F ell a L) z)
      (hzu : z.2.1 ≠ 0) (hzv : z.2.2 ≠ 0)
      (hzvLt : ell (z.1, z.2.2) < L) :
      (ell (z.1, z.2.1))⁻¹ •
          mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (intrinsicGeodesic
              (I := 𝓘(Real, E)) gExt hExt z.1 z.2.1) 1 (1 : Real) =
        -((ell (z.1, z.2.2))⁻¹ •
          mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (intrinsicGeodesic
              (I := 𝓘(Real, E)) gExt hExt z.1 z.2.2) 1
              (1 : Real)) := by
    let x₀ : E := z.1
    let u₀ : E := z.2.1
    let v₀ : E := z.2.2
    let y₀ : E := F (x₀, u₀)
    let lu : Real := ell (x₀, u₀)
    let lv : Real := ell (x₀, v₀)
    let γu : Real → E :=
      intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x₀ u₀
    let γv : Real → E :=
      intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x₀ v₀
    let U : E :=
      mfderiv 𝓘(Real, Real) 𝓘(Real, E) γu 1 (1 : Real)
    let V : E :=
      mfderiv 𝓘(Real, Real) 𝓘(Real, E) γv 1 (1 : Real)
    have hx₀ : ‖x₀‖ ≤ a := hz.1
    have hy₀ : ‖y₀‖ ≤ a := hz.2.1
    have huvEnd : F (x₀, u₀) = F (x₀, v₀) := hz.2.2.1
    have huLe : lu ≤ L := hz.2.2.2.1
    have hvLe : lv ≤ L := hz.2.2.2.2.1
    have huv : u₀ ≠ v₀ := hz.2.2.2.2.2
    have hluPos : 0 < lu := by
      exact Real.sqrt_pos.2 (gExt.pos x₀ u₀ hzu)
    have hlvPos : 0 < lv := by
      exact Real.sqrt_pos.2 (gExt.pos x₀ v₀ hzv)
    have hγu1 : γu 1 = y₀ := by
      rfl
    have hyvExp :
        y₀ =
          expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x₀ v₀ := by
      simpa only [y₀, F] using huvEnd
    have hγv1 : γv 1 = y₀ := by
      simpa only [γv, expMapIntrinsic_def] using hyvExp.symm
    have hvNot :
        ¬ IsConjVec
          (I := 𝓘(Real, E)) gExt hExt x₀ v₀ :=
      hshortNotConj x₀ v₀ hx₀ hvLe
    obtain ⟨Br, hvSrc⟩ :=
      branch_of_not_conj
        (I := 𝓘(Real, E)) gExt hExt hvNot
    have hyDom : y₀ ∈ Br.dom := by
      have hyHom : y₀ = Br.hom v₀ :=
        hyvExp.trans (Br.hom_eq hvSrc)
      rw [hyHom]
      exact Br.hom.map_source hvSrc
    have hInvY : Br.inv y₀ = v₀ := by
      rw [hyvExp]
      exact Br.left_inv hvSrc
    have hbrY :
        branchRadius (I := 𝓘(Real, E)) gExt Br y₀ = lv := by
      rw [hyvExp]
      simpa only [lv, ell] using
        branchRadius_exp (I := 𝓘(Real, E)) Br hvSrc
    have hvPos : 0 < gExt.inner x₀ v₀ v₀ :=
      gExt.pos x₀ v₀ hzv
    have hbrDiff :
        MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
          (branchRadius (I := 𝓘(Real, E)) gExt Br) y₀ := by
      rw [hyvExp]
      exact branchRadius_diff
        (I := 𝓘(Real, E)) Br hvSrc hvPos
    let η : Real → E := fun s => γu (1 - s)
    have hη0 : η 0 = y₀ := by
      simpa only [η, sub_zero] using hγu1
    have hηInf :
        ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ η := by
      simpa only [η] using
        (intrinsicGeodesic_contMDiff
          (I := 𝓘(Real, E)) gExt hExt x₀ u₀).comp
            (contMDiff_const.sub contMDiff_id)
    have hηDiff :
        MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) η 0 :=
      hηInf.contMDiffAt.mdifferentiableAt (by simp)
    have hηVel :
        mfderiv 𝓘(Real, Real) 𝓘(Real, E) η 0 (1 : Real) = -U := by
      have h :=
        curveVelocity_comp_affine
          (I := 𝓘(Real, E)) γu (-1) 1 0
            ((intrinsicGeodesic_contMDiff
              (I := 𝓘(Real, E)) gExt hExt x₀ u₀).contMDiffAt
                |>.mdifferentiableAt (by simp))
      have hfun :
          η = fun s : Real => γu ((-1 : Real) * s + 1) := by
        funext s
        dsimp only [η]
        congr 1
        ring
      rw [hfun]
      have harg : (-1 : Real) * 0 + 1 = 1 := by norm_num
      rw [harg] at h
      simpa only [curveVelocity, U,
        neg_smul, one_smul] using h
    have hgrad :
        gradientFun (I := 𝓘(Real, E)) gExt
            (branchRadius (I := 𝓘(Real, E)) gExt Br) y₀ =
          lv⁻¹ • V := by
      rw [hyvExp]
      simpa only [lv, ell, V, γv, intrinsicVelocityLift] using
        grad_branchRadius
          (I := 𝓘(Real, E)) Br hvSrc hvPos
    have hbrDeriv :
        HasDerivAt
          (fun s : Real =>
            branchRadius (I := 𝓘(Real, E)) gExt Br (η s))
          (gExt.inner y₀ (lv⁻¹ • V) (-U)) 0 := by
      have hbrDiffη :
          MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
            (branchRadius (I := 𝓘(Real, E)) gExt Br) (η 0) := by
        rw [hη0]
        exact hbrDiff
      have hcomp :=
        hbrDiffη.hasMFDerivAt.comp 0 hηDiff.hasMFDerivAt
      rw [hasMFDerivAt_iff_hasFDerivAt,
        hasFDerivAt_iff_hasDerivAt] at hcomp
      have hraw :
          HasDerivAt
            (fun s : Real =>
              branchRadius (I := 𝓘(Real, E)) gExt Br (η s))
            (mfderiv 𝓘(Real, E) 𝓘(Real, Real)
              (branchRadius (I := 𝓘(Real, E)) gExt Br) y₀
                (mfderiv 𝓘(Real, Real) 𝓘(Real, E) η 0
                  (1 : Real))) 0 := by
        have hraw₀ := hcomp
        rw [hη0] at hraw₀
        simpa only [Function.comp_apply] using hraw₀
      convert hraw using 1
      rw [hηVel, ← inner_gradientFun
        (I := 𝓘(Real, E)) gExt
          (branchRadius (I := 𝓘(Real, E)) gExt Br) y₀ (-U),
        hgrad]
    have hηCont : ContinuousAt η 0 := hηInf.continuous.continuousAt
    have hdomEv : ∀ᶠ s in 𝓝 (0 : Real), η s ∈ Br.dom := by
      exact hηCont (Br.hom.open_target.mem_nhds (by simpa only [hη0] using hyDom))
    have hbrCont :
        ContinuousAt
          (fun s : Real =>
            branchRadius (I := 𝓘(Real, E)) gExt Br (η s)) 0 :=
      (by
        have hbrDiffη :
            MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
              (branchRadius (I := 𝓘(Real, E)) gExt Br) (η 0) := by
          rw [hη0]
          exact hbrDiff
        exact hbrDiffη.continuousAt.comp hηCont)
    have hbrLtEv :
        ∀ᶠ s in 𝓝 (0 : Real),
          branchRadius (I := 𝓘(Real, E)) gExt Br (η s) < L := by
      exact hbrCont
        (Iio_mem_nhds (by simpa only [hη0, hbrY] using hzvLt))
    have hInvDiff :
        ContMDiffAt 𝓘(Real, E) 𝓘(Real, E) ∞ Br.inv y₀ :=
      Br.inv_inf.contMDiffAt (Br.hom.open_target.mem_nhds hyDom)
    have hleftCont :
        ContinuousAt (fun s : Real => (1 - s) • u₀) 0 :=
      (continuousAt_const.sub continuousAt_id).smul continuousAt_const
    have hrightCont :
        ContinuousAt (fun s : Real => Br.inv (η s)) 0 :=
      (by
        have hInvDiffη :
            ContMDiffAt 𝓘(Real, E) 𝓘(Real, E) ∞ Br.inv (η 0) := by
          rw [hη0]
          exact hInvDiff
        exact hInvDiffη.continuousAt.comp hηCont)
    have hneEv :
        ∀ᶠ s in 𝓝 (0 : Real),
          (1 - s) • u₀ ≠ Br.inv (η s) := by
      apply (hleftCont.ne_iff_eventually_ne hrightCont).1
      simpa only [sub_zero, one_smul, hη0, hInvY] using huv
    have huEnd :
        intrExtLaunch (I := I) g hEnorm p hR hloc x₀ u₀ 1 = y₀ := by
      rfl
    have hbadEv :
        ∀ᶠ s in 𝓝[>] (0 : Real),
          (x₀, (1 - s) • u₀, Br.inv (η s)) ∈
            shortBigons F ell a L := by
      filter_upwards [
        Filter.Eventually.filter_mono nhdsWithin_le_nhds hdomEv,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds hbrLtEv,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds hneEv,
        self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (eventually_lt_nhds (show (0 : Real) < 1 by norm_num))]
          with s hsDom hsBr hsNe hsPos hsOne
      change 0 < s at hsPos
      have hsIcc : 1 - s ∈ Set.Icc (0 : Real) 1 := by
        exact ⟨sub_nonneg.mpr hsOne.le, sub_le_self 1 hsPos.le⟩
      have hηCore : ‖η s‖ ≤ a := by
        simpa only [η, γu, gExt, hExt, intrExtLaunch] using
          intrExt_edge_core
            (I := I) g hEnorm p hR hloc hK hRm hsmall h2aL hbudget
              hx₀ hy₀ u₀
              (by simpa only [lu, ell, gExt] using huLe)
              huEnd (1 - s) hsIcc
      have hfirst : F (x₀, (1 - s) • u₀) = η s := by
        change
          intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt
            x₀ ((1 - s) • u₀) 1 = γu (1 - s)
        exact intrinsicGeodesic_smul
          (I := 𝓘(Real, E)) gExt hExt x₀ u₀ (1 - s)
      have hsecond : F (x₀, Br.inv (η s)) = η s := by
        exact Br.right_inv hsDom
      have hellFirst :
          ell (x₀, (1 - s) • u₀) = (1 - s) * lu := by
        exact sqrt_gInner_smul_self
          (I := 𝓘(Real, E)) gExt x₀
            (sub_nonneg.mpr hsOne.le) u₀
      have hfirstLe : ell (x₀, (1 - s) • u₀) ≤ L := by
        rw [hellFirst]
        have hluNonneg : 0 ≤ lu := Real.sqrt_nonneg _
        have hscaleLe : (1 - s) * lu ≤ lu := by
          have hsle : 1 - s ≤ 1 := sub_le_self 1 hsPos.le
          exact mul_le_of_le_one_left hluNonneg hsle
        exact hscaleLe.trans huLe
      have hsecondLt : ell (x₀, Br.inv (η s)) < L := by
        simpa only [ell, branchRadius] using hsBr
      change
        ‖x₀‖ ≤ a ∧
        ‖F (x₀, (1 - s) • u₀)‖ ≤ a ∧
        F (x₀, (1 - s) • u₀) = F (x₀, Br.inv (η s)) ∧
        ell (x₀, (1 - s) • u₀) ≤ L ∧
        ell (x₀, Br.inv (η s)) ≤ L ∧
        (1 - s) • u₀ ≠ Br.inv (η s)
      exact
        ⟨hx₀, by simpa only [hfirst] using hηCore,
          hfirst.trans hsecond.symm, hfirstLe, hsecondLt.le, hsNe⟩
    let φ : Real → Real := fun s =>
      (1 - s) * lu +
        branchRadius (I := 𝓘(Real, E)) gExt Br (η s)
    have hφ0 : φ 0 = total z := by
      dsimp only [φ, total, x₀, u₀, v₀, lu, lv]
      rw [hη0, hbrY]
      ring
    have hminEv : ∀ᶠ s in 𝓝[>] (0 : Real), φ 0 ≤ φ s := by
      filter_upwards [
        hbadEv,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (eventually_lt_nhds (show (0 : Real) < 1 by norm_num))]
          with s hsBad hsOne
      let zs : E × E × E :=
        (x₀, (1 - s) • u₀, Br.inv (η s))
      have hzsMin := (isMinOn_iff.mp hzmin) zs hsBad
      have hellFirst :
          ell (x₀, (1 - s) • u₀) = (1 - s) * lu := by
        exact sqrt_gInner_smul_self
          (I := 𝓘(Real, E)) gExt x₀
            (sub_nonneg.mpr hsOne.le) u₀
      calc
        φ 0 = total z := hφ0
        _ ≤ total zs := hzsMin
        _ = φ s := by
          dsimp only [total, zs, φ]
          rw [hellFirst]
          rfl
    have hlin :
        HasDerivAt (fun s : Real => (1 - s) * lu) (-lu) 0 := by
      convert
        ((hasDerivAt_const (x := (0 : Real)) (c := (1 : Real))).sub
          (hasDerivAt_id (x := (0 : Real)))).mul_const lu using 1
      all_goals simp
    have hφDeriv :
        HasDerivAt φ
          (-lu + gExt.inner y₀ (lv⁻¹ • V) (-U)) 0 := by
      simpa only [φ] using hlin.add hbrDeriv
    have hslope :
        ∀ᶠ s in 𝓝[>] (0 : Real),
          0 ≤ s⁻¹ • (φ (0 + s) - φ 0) := by
      filter_upwards [hminEv, self_mem_nhdsWithin] with s hsMin hsPos
      simpa only [zero_add, smul_eq_mul] using
        mul_nonneg (inv_nonneg.mpr hsPos.le) (sub_nonneg.mpr hsMin)
    have hderNonneg :
        0 ≤ -lu + gExt.inner y₀ (lv⁻¹ • V) (-U) :=
      ge_of_tendsto hφDeriv.tendsto_slope_zero_right hslope
    have hUSpeed : gExt.inner y₀ U U = gExt.inner x₀ u₀ u₀ := by
      simpa only [U, γu, hγu1] using
        intrinsicGeodesic_speedSq_eq
          (I := 𝓘(Real, E)) gExt hExt x₀ u₀ 1
    have hVSpeed : gExt.inner y₀ V V = gExt.inner x₀ v₀ v₀ := by
      have hspeed :=
        intrinsicGeodesic_speedSq_eq
          (I := 𝓘(Real, E)) gExt hExt x₀ v₀ 1
      change gExt.inner (γv 1) V V = gExt.inner x₀ v₀ v₀ at hspeed
      rw [hγv1] at hspeed
      exact hspeed
    have hluSq : lu ^ 2 = gExt.inner x₀ u₀ u₀ := by
      exact Real.sq_sqrt (gInner_self_nonneg
        (I := 𝓘(Real, E)) gExt x₀ u₀)
    have hlvSq : lv ^ 2 = gExt.inner x₀ v₀ v₀ := by
      exact Real.sq_sqrt (gInner_self_nonneg
        (I := 𝓘(Real, E)) gExt x₀ v₀)
    have hUunit :
        gExt.inner y₀ (lu⁻¹ • U) (lu⁻¹ • U) = 1 := by
      calc
        gExt.inner y₀ (lu⁻¹ • U) (lu⁻¹ • U) =
            lu⁻¹ ^ 2 * gExt.inner y₀ U U :=
          gInner_smul_self
            (I := 𝓘(Real, E)) gExt y₀ lu⁻¹ U
        _ = 1 := by
          rw [hUSpeed, ← hluSq, inv_pow]
          exact inv_mul_cancel₀ (pow_ne_zero 2 hluPos.ne')
    have hVunit :
        gExt.inner y₀ (lv⁻¹ • V) (lv⁻¹ • V) = 1 := by
      calc
        gExt.inner y₀ (lv⁻¹ • V) (lv⁻¹ • V) =
            lv⁻¹ ^ 2 * gExt.inner y₀ V V :=
          gInner_smul_self
            (I := 𝓘(Real, E)) gExt y₀ lv⁻¹ V
        _ = 1 := by
          rw [hVSpeed, ← hlvSq, inv_pow]
          exact inv_mul_cancel₀ (pow_ne_zero 2 hlvPos.ne')
    have hpair :
        gExt.inner y₀ (lv⁻¹ • V) (-U) =
          -(lv⁻¹ * gExt.inner y₀ U V) := by
      have hsmul :
          gExt.inner y₀ (lv⁻¹ • V) (-U) =
            lv⁻¹ * gExt.inner y₀ V (-U) := by
        have h :=
          congrArg (fun A : E →L[Real] Real => A (-U))
            ((gExt.inner y₀).map_smul lv⁻¹ V)
        simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using h
      have hneg :
          gExt.inner y₀ V (-U) = -gExt.inner y₀ V U :=
        (gExt.inner y₀ V).map_neg U
      rw [hsmul, hneg, gExt.symm y₀ V U]
      ring
    have hscaled : lv⁻¹ * gExt.inner y₀ U V ≤ -lu := by
      rw [hpair] at hderNonneg
      linarith only [hderNonneg]
    have hcrossForm :
        gExt.inner y₀ (lu⁻¹ • U) (lv⁻¹ • V) =
          lu⁻¹ * (lv⁻¹ * gExt.inner y₀ U V) := by
      have hout :
          gExt.inner y₀ (lu⁻¹ • U) (lv⁻¹ • V) =
            lu⁻¹ * gExt.inner y₀ U (lv⁻¹ • V) := by
        have h :=
          congrArg (fun A : E →L[Real] Real => A (lv⁻¹ • V))
            ((gExt.inner y₀).map_smul lu⁻¹ U)
        simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using h
      have hin :
          gExt.inner y₀ U (lv⁻¹ • V) =
            lv⁻¹ * gExt.inner y₀ U V := by
        simpa only [smul_eq_mul] using
          (gExt.inner y₀ U).map_smul lv⁻¹ V
      rw [hout, hin]
    have hcrossUpper :
        gExt.inner y₀ (lu⁻¹ • U) (lv⁻¹ • V) ≤ -1 := by
      calc
        gExt.inner y₀ (lu⁻¹ • U) (lv⁻¹ • V) =
            lu⁻¹ * (lv⁻¹ * gExt.inner y₀ U V) := hcrossForm
        _ ≤ lu⁻¹ * (-lu) :=
          mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hluPos.le)
        _ = -1 := by
          rw [mul_neg, inv_mul_cancel₀ hluPos.ne']
    have hcs :=
      abs_metric_inner_le_sqrt_metric_quadratic
        (I := 𝓘(Real, E)) (M := E) gExt y₀
          (lu⁻¹ • U) (lv⁻¹ • V)
    have hcrossLower :
        -1 ≤ gExt.inner y₀ (lu⁻¹ • U) (lv⁻¹ • V) := by
      rw [hUunit, hVunit, Real.sqrt_one, one_mul] at hcs
      have hneg :=
        neg_le_abs (gExt.inner y₀ (lu⁻¹ • U) (lv⁻¹ • V))
      linarith only [hneg, hcs]
    have hcross :
        gExt.inner y₀ (lu⁻¹ • U) (lv⁻¹ • V) = -1 :=
      le_antisymm hcrossUpper hcrossLower
    let W : E := lu⁻¹ • U + lv⁻¹ • V
    have hWInner : gExt.inner y₀ W W = 0 := by
      dsimp only [W]
      have hout :
          gExt.inner y₀ (lu⁻¹ • U + lv⁻¹ • V)
              (lu⁻¹ • U + lv⁻¹ • V) =
            gExt.inner y₀ (lu⁻¹ • U)
                (lu⁻¹ • U + lv⁻¹ • V) +
              gExt.inner y₀ (lv⁻¹ • V)
                (lu⁻¹ • U + lv⁻¹ • V) := by
        have h :=
          congrArg
            (fun A : E →L[Real] Real =>
              A (lu⁻¹ • U + lv⁻¹ • V))
            ((gExt.inner y₀).map_add
              (lu⁻¹ • U) (lv⁻¹ • V))
        simpa only [ContinuousLinearMap.add_apply] using h
      have hleft :
          gExt.inner y₀ (lu⁻¹ • U)
              (lu⁻¹ • U + lv⁻¹ • V) =
            gExt.inner y₀ (lu⁻¹ • U) (lu⁻¹ • U) +
              gExt.inner y₀ (lu⁻¹ • U) (lv⁻¹ • V) := by
        exact
          (gExt.inner y₀ (lu⁻¹ • U)).map_add
            (lu⁻¹ • U) (lv⁻¹ • V)
      have hright :
          gExt.inner y₀ (lv⁻¹ • V)
              (lu⁻¹ • U + lv⁻¹ • V) =
            gExt.inner y₀ (lv⁻¹ • V) (lu⁻¹ • U) +
              gExt.inner y₀ (lv⁻¹ • V) (lv⁻¹ • V) := by
        exact
          (gExt.inner y₀ (lv⁻¹ • V)).map_add
            (lu⁻¹ • U) (lv⁻¹ • V)
      rw [hout, hleft, hright,
        gExt.symm y₀ (lv⁻¹ • V) (lu⁻¹ • U),
        hUunit, hVunit, hcross]
      ring
    have hWzero : W = 0 := by
      by_contra hWne
      have hpos := gExt.pos y₀ W hWne
      exact hpos.ne' hWInner
    have hunitOpp : lu⁻¹ • U = -(lv⁻¹ • V) :=
      eq_neg_of_add_eq_zero_left hWzero
    simpa only [x₀, u₀, v₀, lu, lv, U, V, γu, γv] using hunitOpp
  have corner_opposite
      (z : E × E × E) (hz : z ∈ shortBigons F ell a L)
      (hzmin : IsMinOn total (shortBigons F ell a L) z)
      (hzu : z.2.1 ≠ 0) (hzv : z.2.2 ≠ 0)
      (hzslack :
        ell (z.1, z.2.1) < L ∨ ell (z.1, z.2.2) < L) :
      (ell (z.1, z.2.1))⁻¹ •
          mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (intrinsicGeodesic
              (I := 𝓘(Real, E)) gExt hExt z.1 z.2.1) 1 (1 : Real) =
        -((ell (z.1, z.2.2))⁻¹ •
          mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (intrinsicGeodesic
              (I := 𝓘(Real, E)) gExt hExt z.1 z.2.2) 1
              (1 : Real)) := by
    rcases hzslack with huLt | hvLt
    · let zs : E × E × E := (z.1, z.2.2, z.2.1)
      have hzs : zs ∈ shortBigons F ell a L := by
        dsimp only [zs]
        exact
          ⟨hz.1, by rw [← hz.2.2.1]; exact hz.2.1,
            hz.2.2.1.symm, hz.2.2.2.2.1, hz.2.2.2.1,
            hz.2.2.2.2.2.symm⟩
      have htotal : total zs = total z := by
        dsimp only [total, zs]
        rw [add_comm]
      have hzsmin : IsMinOn total (shortBigons F ell a L) zs := by
        apply isMinOn_iff.mpr
        intro w hw
        rw [htotal]
        exact (isMinOn_iff.mp hzmin) w hw
      have hs :=
        terminal_opposite zs hzs hzsmin hzv hzu
          (by simpa only [zs] using huLt)
      dsimp only [zs] at hs
      have hneg := congrArg Neg.neg hs
      exact (neg_neg _).symm.trans hneg.symm
    · exact terminal_opposite z hz hzmin hzu hzv hvLt
  have hterm :=
    corner_opposite z₁ hz₁ hmin₁ hu₁ hv₁ hslack₁
  let x₁ : E := z₁.1
  let u₁ : E := z₁.2.1
  let v₁ : E := z₁.2.2
  let γu : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x₁ u₁
  let γv : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x₁ v₁
  let y₁ : E := γu 1
  let U : E :=
    mfderiv 𝓘(Real, Real) 𝓘(Real, E) γu 1 (1 : Real)
  let V : E :=
    mfderiv 𝓘(Real, Real) 𝓘(Real, E) γv 1 (1 : Real)
  let lu : Real := ell (x₁, u₁)
  let lv : Real := ell (x₁, v₁)
  have hx₁ : ‖x₁‖ ≤ a := hz₁.1
  have hγu1 : γu 1 = y₁ := rfl
  have hγv1 : γv 1 = y₁ := by
    simpa only [γu, γv, y₁, F, expMapIntrinsic_def] using
      hz₁.2.2.1.symm
  have hy₁ : ‖y₁‖ ≤ a := by
    simpa only [γu, y₁, F, expMapIntrinsic_def] using hz₁.2.1
  have hluPos : 0 < lu := by
    exact Real.sqrt_pos.2 (gExt.pos x₁ u₁ hu₁)
  have hlvPos : 0 < lv := by
    exact Real.sqrt_pos.2 (gExt.pos x₁ v₁ hv₁)
  have hterm' : lu⁻¹ • U = -(lv⁻¹ • V) := by
    simpa only [x₁, u₁, v₁, γu, γv, U, V, lu, lv] using hterm
  have hUne : U ≠ 0 := by
    exact intrGeo_vel_ne
      (I := 𝓘(Real, E)) gExt hExt x₁ u₁ hu₁ 1
  have hVne : V ≠ 0 := by
    exact intrGeo_vel_ne
      (I := 𝓘(Real, E)) gExt hExt x₁ v₁ hv₁ 1
  have hUVne : U ≠ V := by
    intro hUV
    have hzero : (lu⁻¹ + lv⁻¹) • U = 0 := by
      rw [hUV] at hterm'
      rw [add_smul, hUV]
      rw [hterm']
      exact neg_add_cancel _
    have hcoef :
        lu⁻¹ + lv⁻¹ ≠ 0 :=
      (add_pos (inv_pos.mpr hluPos) (inv_pos.mpr hlvPos)).ne'
    exact hUne ((smul_eq_zero.mp hzero).resolve_left hcoef)
  have hUSpeed :
      gExt.inner y₁ U U = gExt.inner x₁ u₁ u₁ := by
    simpa only [U, γu, hγu1] using
      intrinsicGeodesic_speedSq_eq
        (I := 𝓘(Real, E)) gExt hExt x₁ u₁ 1
  have hVSpeed :
      gExt.inner y₁ V V = gExt.inner x₁ v₁ v₁ := by
    have hs :=
      intrinsicGeodesic_speedSq_eq
        (I := 𝓘(Real, E)) gExt hExt x₁ v₁ 1
    change gExt.inner (γv 1) V V = gExt.inner x₁ v₁ v₁ at hs
    rw [hγv1] at hs
    exact hs
  have hlenU : ell (y₁, -U) = lu := by
    have hneg :
        gExt.inner y₁ (-U) (-U) = gExt.inner y₁ U U := by
      simpa only [neg_one_smul, neg_one_sq, one_mul] using
        gInner_smul_self
          (I := 𝓘(Real, E)) gExt y₁ (-1 : Real) U
    dsimp only [ell, lu]
    rw [hneg, hUSpeed]
  have hlenV : ell (y₁, -V) = lv := by
    have hneg :
        gExt.inner y₁ (-V) (-V) = gExt.inner y₁ V V := by
      simpa only [neg_one_smul, neg_one_sq, one_mul] using
        gInner_smul_self
          (I := 𝓘(Real, E)) gExt y₁ (-1 : Real) V
    dsimp only [ell, lv]
    rw [hneg, hVSpeed]
  have hrevU :
      intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt y₁ (-U) =
        fun t => γu (1 - t) := by
    simpa only [y₁, U, γu, intrinsicVelocityLift] using
      intrGeo_reverse
        (I := 𝓘(Real, E)) gExt hExt x₁ u₁
  have hrevV :
      intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt y₁ (-V) =
        fun t => γv (1 - t) := by
    have hr :=
      intrGeo_reverse
        (I := 𝓘(Real, E)) gExt hExt x₁ v₁
    change
      intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt (γv 1) (-V) =
        fun t => γv (1 - t) at hr
    rw [hγv1] at hr
    exact hr
  have hrevUend :
      intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt y₁ (-U) 1 = x₁ := by
    rw [hrevU]
    simp only [sub_self, γu, intrinsicGeodesic_zero]
  have hrevVend :
      intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt y₁ (-V) 1 = x₁ := by
    rw [hrevV]
    simp only [sub_self, γv, intrinsicGeodesic_zero]
  let zr : E × E × E := (y₁, -U, -V)
  have hzr : zr ∈ shortBigons F ell a L := by
    have hFU : F (y₁, -U) = x₁ := by
      simpa only [F, expMapIntrinsic_def] using hrevUend
    have hFV : F (y₁, -V) = x₁ := by
      simpa only [F, expMapIntrinsic_def] using hrevVend
    dsimp only [zr]
    exact
      ⟨hy₁, by rw [hFU]; exact hx₁, hFU.trans hFV.symm,
        by rw [hlenU]; exact hz₁.2.2.2.1,
        by rw [hlenV]; exact hz₁.2.2.2.2.1,
        fun h => hUVne (neg_injective h)⟩
  have htotalr : total zr = total z₁ := by
    dsimp only [total, zr]
    rw [hlenU, hlenV]
  have hminr : IsMinOn total (shortBigons F ell a L) zr := by
    apply isMinOn_iff.mpr
    intro w hw
    rw [htotalr]
    exact (isMinOn_iff.mp hmin₁) w hw
  have hslackr :
      ell (zr.1, zr.2.1) < L ∨ ell (zr.1, zr.2.2) < L := by
    dsimp only [zr]
    simpa only [hlenU, hlenV] using hslack₁
  have hrevCorner :=
    corner_opposite zr hzr hminr
      (neg_ne_zero.mpr hUne) (neg_ne_zero.mpr hVne) hslackr
  dsimp only [zr] at hrevCorner
  have hrevVelU :
      mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt y₁ (-U)) 1 (1 : Real) =
        -u₁ := by
    simpa only [y₁, U, γu, intrinsicVelocityLift] using
      intrGeo_rev_vel
        (I := 𝓘(Real, E)) gExt hExt x₁ u₁
  have hrevVelV :
      mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt y₁ (-V)) 1 (1 : Real) =
        -v₁ := by
    have hv :=
      intrGeo_rev_vel
        (I := 𝓘(Real, E)) gExt hExt x₁ v₁
    change
      mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt (γv 1) (-V)) 1 (1 : Real) =
        -v₁ at hv
    rw [hγv1] at hv
    exact hv
  rw [hlenU, hlenV, hrevVelU, hrevVelV] at hrevCorner
  have hinit : lu⁻¹ • u₁ = -(lv⁻¹ • v₁) := by
    have hleft :
        lu⁻¹ • (-u₁) = -(lu⁻¹ • u₁) :=
      smul_neg lu⁻¹ u₁
    have hright :
        -(lv⁻¹ • (-v₁)) = lv⁻¹ • v₁ := by
      calc
        -(lv⁻¹ • (-v₁)) = -(-(lv⁻¹ • v₁)) :=
          congrArg Neg.neg (smul_neg lv⁻¹ v₁)
        _ = lv⁻¹ • v₁ := neg_neg _
    have hneg :
        -(lu⁻¹ • u₁) = lv⁻¹ • v₁ :=
      hleft.symm.trans (hrevCorner.trans hright)
    have hn := congrArg Neg.neg hneg
    exact (neg_neg _).symm.trans hn
  let c : Real := lu / lv
  let d : Real := lv / lu
  let T : Real := 1 + d
  have hcPos : 0 < c := div_pos hluPos hlvPos
  have hdPos : 0 < d := div_pos hlvPos hluPos
  have hcd : c * d = 1 := by
    dsimp only [c, d]
    field_simp [hluPos.ne', hlvPos.ne']
  have hTPos : 0 < T := by
    dsimp only [T]
    exact add_pos zero_lt_one hdPos
  have unnormalize (a₀ b₀ : Real) (ha₀ : a₀ ≠ 0)
      (A B : E) (h : a₀⁻¹ • A = -(b₀⁻¹ • B)) :
      A = (a₀ / b₀) • (-B) := by
    calc
      A = a₀ • (a₀⁻¹ • A) := by
        rw [smul_smul, mul_inv_cancel₀ ha₀, one_smul]
      _ = a₀ • (-(b₀⁻¹ • B)) := congrArg (fun q : E => a₀ • q) h
      _ = -(a₀ • (b₀⁻¹ • B)) := smul_neg a₀ _
      _ = -((a₀ * b₀⁻¹) • B) := by rw [smul_smul]
      _ = (a₀ / b₀) • (-B) := by
        rw [div_eq_mul_inv, smul_neg]
  have hUscale : U = c • (-V) := by
    exact unnormalize lu lv hluPos.ne' U V hterm'
  have huscale : u₁ = c • (-v₁) := by
    exact unnormalize lu lv hluPos.ne' u₁ v₁ hinit
  have hjoin (s : Real) :
      γu (s + 1) = γv (1 - c * s) := by
    have hcont :=
      congrFun
        (intrinsicGeodesic_continuation
          (I := 𝓘(Real, E)) gExt hExt x₁ u₁ 1) s
    change
      γu (s + 1) =
        intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt (γu 1) U s at hcont
    rw [hγu1] at hcont
    calc
      γu (s + 1) =
          intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt y₁ U s := hcont
      _ = intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt y₁ (c • (-V)) s := by
          rw [hUscale]
      _ = intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt y₁ (-V) (c * s) :=
          intrGeo_smul_apply
            (I := 𝓘(Real, E)) gExt hExt y₁ (-V) c s
      _ = γv (1 - c * s) := congrFun hrevV (c * s)
  have hbase (s : Real) : γu s = γv (-(c * s)) := by
    calc
      γu s =
          intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt x₁ (c • (-v₁)) s := by
        change
          intrinsicGeodesic
              (I := 𝓘(Real, E)) gExt hExt x₁ u₁ s =
            intrinsicGeodesic
              (I := 𝓘(Real, E)) gExt hExt x₁ (c • (-v₁)) s
        rw [huscale]
      _ = intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt x₁ (-v₁) (c * s) :=
          intrGeo_smul_apply
            (I := 𝓘(Real, E)) gExt hExt x₁ (-v₁) c s
      _ = γv (-(c * s)) := by
        have hs :=
          intrGeo_smul_apply
            (I := 𝓘(Real, E)) gExt hExt x₁ v₁ (-1) (c * s)
        simpa only [neg_one_smul, neg_one_mul, γv] using hs
  have hperiod (s : Real) : γu (s + T) = γu s := by
    calc
      γu (s + T) = γu ((s + d) + 1) := by
        congr 1
        dsimp only [T]
        ring
      _ = γv (1 - c * (s + d)) := hjoin (s + d)
      _ = γv (-(c * s)) := by
        congr 1
        rw [mul_add, hcd]
        ring
      _ = γu s := (hbase s).symm
  have huEnd₁ :
      intrExtLaunch (I := I) g hEnorm p hR hloc x₁ u₁ 1 = y₁ := by
    simpa only [γu, gExt, hExt, intrExtLaunch] using hγu1
  have hvEnd₁ :
      intrExtLaunch (I := I) g hEnorm p hR hloc x₁ v₁ 1 = y₁ := by
    simpa only [γv, gExt, hExt, intrExtLaunch] using hγv1
  have hcoreU :
      ∀ t ∈ Set.Icc (0 : Real) 1, ‖γu t‖ ≤ a := by
    intro t ht
    simpa only [γu, gExt, hExt, intrExtLaunch] using
      intrExt_edge_core
        (I := I) g hEnorm p hR hloc hK hRm hsmall h2aL hbudget
          hx₁ hy₁ u₁
          (by simpa only [lu, ell, gExt] using hz₁.2.2.2.1)
          huEnd₁ t ht
  have hcoreV :
      ∀ t ∈ Set.Icc (0 : Real) 1, ‖γv t‖ ≤ a := by
    intro t ht
    simpa only [γv, gExt, hExt, intrExtLaunch] using
      intrExt_edge_core
        (I := I) g hEnorm p hR hloc hK hRm hsmall h2aL hbudget
          hx₁ hy₁ v₁
          (by simpa only [lv, ell, gExt] using hz₁.2.2.2.2.1)
          hvEnd₁ t ht
  have hcore :
      ∀ t ∈ Set.Ioo (0 : Real) (2 * T), ‖γu t‖ ≤ a :=
    periodic_core_bound (E := E) (γu := γu) (γv := γv)
      (a := a) (c := c) (d := d) (T := T) rfl hcPos hcd
      hjoin hperiod hcoreU hcoreV
  have ha0 : 0 ≤ a := (norm_nonneg x).trans hx
  have haL : a ≤ L := by
    calc
      a ≤ a + a := le_add_of_nonneg_right ha0
      _ = 2 * a := by ring
      _ ≤ L := h2aL.le
  have haFence : a < 3 * R / 4 := by
    exact (le_add_of_nonneg_right hLpos.le).trans_lt hbudget
  have hgeo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc) γu
        (Set.Ioo (0 : Real) (2 * T)) := by
    change IsGeodesicOn (I := 𝓘(Real, E)) gExt γu _
    exact
      (intrinsicGeodesic_isGeodesic
        (I := 𝓘(Real, E)) gExt hExt x₁ u₁).isGeodesicOn _
  apply intrOrigin_no_return
    (I := I) g hEnorm p hR hloc hK hRm hsmall hTPos
    (γ := γu)
    (intrinsicGeodesic_contMDiff
      (I := 𝓘(Real, E)) gExt hExt x₁ u₁)
    hgeo
    (fun t ht => (hcore t ht).trans_lt haFence)
    (fun t ht => (hcore t ht).trans haL)
    (fun t _ =>
      intrGeo_vel_ne
        (I := 𝓘(Real, E)) gExt hExt x₁ u₁ hu₁ t)
  · have hp := hperiod 0
    simpa only [zero_add] using hp.symm
  · have hp := hperiod T
    have htwo : T + T = 2 * T := by ring
    rw [htwo] at hp
    exact hp.symm

end OriginEnergy

end CGT
end Riemannian
end Geometry
end DifferentialGeometry

end
