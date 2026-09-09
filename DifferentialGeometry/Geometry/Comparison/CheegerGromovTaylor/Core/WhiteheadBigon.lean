import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.RadialBump
import DifferentialGeometry.Analysis.Calculus.Derivative.Curve
import DifferentialGeometry.Analysis.Calculus.Inverse.MovingImplicit
import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.Pullback.CompleteMetricExtension
import DifferentialGeometry.Geometry.Comparison.Hessian.AlongGeodesic
import DifferentialGeometry.Geometry.Exponential.Injectivity
import DifferentialGeometry.Geometry.Exponential.MinimizingVector
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CheegerGromovTaylor

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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

noncomputable local instance {R : Real} :
    SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)

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

theorem intrinsicCore_min_regular
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
    {pt q : intrinsicPullBall (E := E) R}
    (hpt : pt ∈ intrinsicCore (E := E) R a)
    (hq : q ∈ intrinsicCore (E := E) R a) :
    let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
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
      (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
    let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
      fun z v =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z v
    let u :=
      minimizingVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
    ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (u : E) := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
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
    intrinsicExt_edist_le (I := I) g hEnorm p hR hloc hpt hq haInner
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
        ‖intrinsicExtLaunch (I := I) g hEnorm p hR hloc
          (pt : E) u t‖ < 3 * R / 4 :=
    intrinsicExt_shortLaunch_fenced
      (I := I) g hEnorm p hR hloc hpt u huL hbudget
  have hnot :=
    intrinsicExt_not_conj_of_shortLaunch
      (I := I) g hEnorm p hR hloc u hfence huL hK hRm hsmallL
  change
    ¬ IsConjVec
      (I := 𝓘(Real, E)) gExt hExt (pt : E) (u : E) at hnot
  exact hnot


theorem intrinsicExt_minVec_mem
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {pt q u : E} :
    let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
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
      (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
    let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
      fun z v =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z v
    ∀ (B : ExponentialInverseBranch (I := 𝓘(Real, E)) gExt hExt pt),
      u ∈ B.hom.source →
      (∀ v : E,
        expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt pt v = q →
        Real.sqrt (gExt.inner pt v v) =
          (riemannianEDist 𝓘(Real, E) pt q).toReal →
        v = u) →
      ∀ᶠ z in 𝓝 q,
        (minimizingVec (I := 𝓘(Real, E)) gExt hExt pt z : E) ∈
          B.hom.source := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  dsimp only
  intro B hu huniq
  exact tendsto_minimizingVec_of_unique gExt hExt huniq (B.hom.open_source.mem_nhds hu)

theorem branchEnergy_min_germ
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {pt q : M} (B : ExponentialInverseBranch (I := I) g hEnorm pt)
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

private theorem intrinsicExt_radial_geo
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
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc)
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
  let γ : Real → intrinsicPullBall (E := E) R := fun t =>
    ⟨φ t • z, by
      change φ t • z ∈ Metric.ball (0 : E) R
      rw [Metric.mem_ball, dist_zero_right]
      exact (hφ_bound t).trans hBR⟩
  have hγ_smooth :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    intro t
    exact codRestr_contMDiffAt
      (I := 𝓘(Real, Real)) (J := 𝓘(Real, E))
      (V := intrinsicPullBall (E := E) R)
      (f := fun s : Real => φ s • z)
      (fun s => (γ s).property)
      ((hφ_smooth.smul contDiff_const).contMDiff.contMDiffAt)
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let : RiemannianBundle
      (fun x : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) x) :=
    ⟨gPull.toRiemannianMetric⟩
  have hmap_geo :
      IsGeodesicOn (I := I) g
        (fun t => intrinsicExpOn (I := I) g hEnorm p R (γ t))
        (Set.Ioo (-c) c) := by
    intro t ht
    have heq :
        (fun s => intrinsicExpOn (I := I) g hEnorm p R (γ s)) =ᶠ[𝓝 t]
          intrinsicGeodesic (I := I) g hEnorm p
            (normalFrame (I := I) g p z) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      change intrinsicFramedExp (I := I) g hEnorm p (γ s : E) =
        intrinsicGeodesic (I := I) g hEnorm p
          (normalFrame (I := I) g p z) s
      rw [show (γ s : E) = s • z by
        change φ s • z = s • z
        rw [hφ_eq hs]]
      with_unfolding_all
        rw [intrinsicFrame_apply, map_smul]
        change intrinsicGeodesic (I := I) g hEnorm p
            (s • normalFrame (I := I) g p z) 1 =
          intrinsicGeodesic (I := I) g hEnorm p
            (normalFrame (I := I) g p z) s
        exact intrinsicGeodesic_smul (I := I) g hEnorm p
          (normalFrame (I := I) g p z) s
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
      (intrinsicExpOn_local (I := I) g hEnorm p hloc)
      (γ := γ) (t := t)
    · intro x v w
      change
        (intrinsicPullMetric (I := I) g hEnorm p hloc).inner x v w =
          g.inner (intrinsicExpOn (I := I) g hEnorm p R x)
            (mfderiv 𝓘(Real, E) I
              (intrinsicExpOn (I := I) g hEnorm p R) x v)
            (mfderiv 𝓘(Real, E) I
              (intrinsicExpOn (I := I) g hEnorm p R) x w)
      rw [intrinsicPullMetric, localPullMetric_inner]
    · exact hγ_smooth t
    · exact hmap_geo t ht
  have hext_geo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc)
        (fun t => ((γ t : intrinsicPullBall (E := E) R) : E))
        (Set.Ioo (-c) c) := by
    exact intrinsicExt_geo_of_pull (I := I) g hEnorm p hR hloc γ
      (Set.Ioo (-c) c)
      (fun t _ht => by
        change ‖φ t • z‖ < 3 * R / 4
        simpa only [B] using hφ_bound t)
      (by simpa only [gPull] using hpull_geo)
  refine ⟨c, hc, ?_⟩
  intro t ht
  have heq :
      (fun s => ((γ s : intrinsicPullBall (E := E) R) : E)) =ᶠ[𝓝 t]
        (fun s : Real => s • z) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    change φ s • z = s • z
    rw [hφ_eq hs]
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
    (I := 𝓘(Real, E))
    (g := intrinsicExtMetric (I := I) g hEnorm p hR hloc)
    heq.eq_of_nhds.symm heq.symm (hext_geo t ht)

theorem intrinsicExt_radial_eq
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
    intrinsicExtLaunch (I := I) g hEnorm p hR hloc (0 : E) z t =
      t • z := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let : RiemannianBundle
      (fun x : E ↦ TangentSpace 𝓘(Real, E) x) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) x) :=
    inferInstance
  let (x : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) x) :=
    inferInstance
  let : ∀ x : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E
      (fun x : E ↦ TangentSpace 𝓘(Real, E) x) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (x : E) (v : TangentSpace 𝓘(Real, E) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner x v v)) :=
    fun x v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt x v
  obtain ⟨c, hc, hline⟩ :=
    intrinsicExt_radial_geo (I := I) g hEnorm p hR hloc hz
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
        convert (hasFDerivAt_id (0 : Real)).smul_const z using 1
        all_goals rfl
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
    geo_eqOn_of_initial (I := 𝓘(Real, E)) gExt
      (O := O) isOpen_Ioo isPreconnected_Ioo h0O hΓ hline'
      hΓcont hlineCont
      (by
        dsimp only [Γ]
        simpa only [zero_smul] using
          intrinsicGeodesic_zero
            (I := modelWithCornersSelf Real E) gExt hExt (0 : E) z)
      hvel
  have htO : t ∈ O := by
    dsimp only [O]
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hΓt : Γ t = t • z := heq htO
  simpa only [Γ, gExt, hExt, intrinsicExtLaunch] using hΓt

theorem intrinsicExt_exp_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {z : E} (hz : ‖z‖ < 3 * R / 4) :
    intrinsicExtLaunch (I := I) g hEnorm p hR hloc (0 : E) z 1 = z := by
  simpa only [one_smul] using
    intrinsicExt_radial_eq (I := I) g hEnorm p hR hloc hz
      (t := (1 : Real)) ⟨zero_le_one, le_rfl⟩

private noncomputable def intrinsicOriginHom {R : Real} :
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

theorem intrinsicExt_inner_zero (v w : E) :
    (intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner (0 : E) v w =
      Inner.inner Real v w := by
  have hzero :
      (0 : E) ∈ Metric.closedBall (0 : E) (3 * R / 4) := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_zero]
    linarith
  rw [intrinsicExt_inner (I := I) g hEnorm p hR hloc hzero]
  have hinner := intrinsicPullMetric_inner (I := I) g hEnorm p hloc
    ⟨(0 : E), intrinsicClosed_subset (E := E) R hR hzero⟩ v w
  have hinner' :
      (intrinsicPullMetric (I := I) g hEnorm p hloc).inner
          ⟨(0 : E), intrinsicClosed_subset (E := E) R hR hzero⟩ v w =
        innerSL Real v w := by
    with_unfolding_all
      simpa only [intrinsicFrameMetric_zero,
        tangentSpaceModelContinuousLinearEquiv_symm_apply] using hinner
  exact hinner'.trans (innerSL_apply_apply Real v w)

theorem intrinsicOrigin_energy (z : E) :
    (1 / 2 : Real) *
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner (0 : E) z z =
      (1 / 2 : Real) * ‖z‖ ^ 2 := by
  rw [intrinsicExt_inner_zero (I := I) g hEnorm p hR hloc,
    real_inner_self_eq_norm_sq]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] in
private theorem model_line_mfderiv_apply (z : E) (t : Real) :
    tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(Real, E)) ((fun s : Real => s • z) t)
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (fun s : Real => s • z) t (1 : Real)) = z := by
  let scalar : Real → Real := id
  let constant : Real → E := fun _ => z
  have hid :
      mvfderiv 𝓘(Real, Real) scalar t =
        (1 : Real →L[Real] Real) := by
    dsimp only [scalar]
    simp only [mvfderiv, mfderiv_id]
    with_unfolding_all rfl
  have hmv := mvfderiv_smul
    (I := 𝓘(Real, Real)) (x := t)
    (a := scalar) (g := constant)
    mdifferentiableAt_id mdifferentiableAt_const
  rw [mvfderiv_const, hid] at hmv
  have hfun : scalar • constant = fun s : Real => s • z := by
    funext s
    rfl
  rw [hfun] at hmv
  dsimp only [scalar, constant] at hmv
  have happ := congrArg
    (fun A : TangentSpace 𝓘(Real, Real) t →L[Real] E =>
      A (1 : Real)) hmv
  simp only [id_eq, smul_zero, zero_add] at happ
  change NormedSpace.fromTangentSpace ((fun s : Real => s • z) t)
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
        (fun s : Real => s • z) t (1 : Real)) =
    (1 : Real) • z at happ
  have hfrom :
      NormedSpace.fromTangentSpace ((fun s : Real => s • z) t)
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (fun s : Real => s • z) t (1 : Real)) = z := by
    simpa only [one_smul] using happ
  with_unfolding_all exact hfrom

omit [NeZero (Module.finrank Real E)]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
omit [SigmaCompactSpace M] in
private theorem deriv2_geo_on_at_model_velocity
    (g : SmoothRiemannianMetric I M) {f : M → Real} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(Real, Real) ∞ f U)
    {γ : Real → M} (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    {t : Real} (hgeo : HasGeodesicEquationAt (I := I) g γ t)
    (ht : γ t ∈ U) (v : E)
    (hvel :
      tangentSpaceModelContinuousLinearEquiv (I := I) (γ t)
          ((mfderiv 𝓘(Real, Real) I γ t :
            Real →L[Real] TangentSpace I (γ t)) (1 : Real)) = v) :
    (deriv^[2] (f ∘ γ)) t =
      hessFun (I := I) g f (γ t)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) (γ t)).symm v)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) (γ t)).symm v) := by
  rw [deriv2_geo_on_at (I := I) g hU hf hγ hgeo ht]
  congr 2

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
    rw [deriv_mul_const_field, deriv_const_mul_field, deriv_pow_field]
    ring
  change
    deriv
        (deriv
          (fun s : Real => (1 / 2 : Real) * s ^ 2 * ‖z‖ ^ 2))
        t =
      ‖z‖ ^ 2
  rw [hfirst]
  rw [deriv_mul_const_field, deriv_id'']
  exact one_mul (‖z‖ ^ 2)

theorem intrinsicOrigin_hess_zero
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
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc)
        (fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) 0 Y Y =
      ‖Y‖ ^ 2 := by
  classical
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let : RiemannianBundle
      (fun y : E ↦ TangentSpace 𝓘(Real, E) y) :=
    ⟨gExt.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun y : E ↦ TangentSpace 𝓘(Real, E) y) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro y v w; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
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
    intrinsicExt_radial_geo (I := I) g hEnorm p hR hloc hz₀
  let line : Real → E := fun t => t • z₀
  have hlineSmooth :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ line := by
    exact (contDiff_id.smul contDiff_const).contMDiff
  have h0O : (0 : Real) ∈ Set.Ioo (-c) c := by
    constructor <;> linarith
  have hf :
      ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞ f :=
    (contDiff_const.mul (contDiff_norm_sq Real)).contMDiff
  have hmodel := model_line_mfderiv_apply (E := E) z₀ 0
  have hmodel' :
      tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E)) (line 0)
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            line 0 (1 : Real)) = z₀ := by
    simpa only [line] using hmodel
  have hd2 :=
    deriv2_geo_on_at_model_velocity (I := 𝓘(Real, E)) gExt
      (U := Set.univ) isOpen_univ hf.contMDiffOn hlineSmooth
      (hline 0 h0O) (Set.mem_univ (line 0)) z₀ hmodel'
  rw [halfSq_line_deriv2 z₀ 0] at hd2
  rw [tangentSpaceModelContinuousLinearEquiv_symm_apply] at hd2
  rw [show line 0 = 0 by simp only [line, zero_smul]] at hd2
  have hdiag :
      hessFun (I := 𝓘(Real, E)) gExt f 0 z₀ z₀ = ‖z₀‖ ^ 2 :=
    hd2.symm
  have hscale :
      hessFun (I := 𝓘(Real, E)) gExt f 0
          (ε • Y) (ε • Y) =
        ε ^ 2 * hessFun (I := 𝓘(Real, E)) gExt f 0 Y Y := by
    let YT : TangentSpace 𝓘(Real, E) (0 : E) :=
      (tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(Real, E)) (0 : E)).symm Y
    have hscaleT :
        hessFun (I := 𝓘(Real, E)) gExt f 0
            (ε • YT) (ε • YT) =
          ε ^ 2 * hessFun (I := 𝓘(Real, E)) gExt f 0 YT YT := by
      rw [LinearMap.map_smul₂, LinearMap.map_smul]
      simp only [smul_eq_mul]
      ring
    have hYT : YT = Y :=
      tangentSpaceModelContinuousLinearEquiv_symm_apply
        (I := 𝓘(Real, E)) (0 : E) Y
    have hεYT : ε • YT = (ε • Y : E) :=
      ((tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(Real, E)) (0 : E)).symm.map_smul ε Y).symm.trans
        (tangentSpaceModelContinuousLinearEquiv_symm_apply
          (I := 𝓘(Real, E)) (0 : E) (ε • Y))
    rw [hεYT, hYT] at hscaleT
    exact hscaleT
  have hnorm : ‖z₀‖ ^ 2 = ε ^ 2 * ‖Y‖ ^ 2 := by
    dsimp only [z₀]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    ring
  rw [show z₀ = ε • Y by rfl, hscale, hnorm] at hdiag
  nlinarith [sq_pos_of_pos hε]

theorem intrinsicOrigin_hess_pos
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
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc)
        (fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) z Y Y := by
  classical
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let : RiemannianBundle
      (fun y : E ↦ TangentSpace 𝓘(Real, E) y) :=
    ⟨gExt.toRiemannianMetric⟩
  let (y : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) y) :=
    inferInstance
  let (y : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) y) :=
    inferInstance
  let : ∀ y : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) y) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E
      (fun y : E ↦ TangentSpace 𝓘(Real, E) y) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro y v w; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (y : E) (v : TangentSpace 𝓘(Real, E) y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner y v v)) :=
    fun y v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt y v
  let hom : PartialDiffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞ :=
    intrinsicOriginHom (E := E) (R := R)
  let B : ExponentialInverseBranch (I := 𝓘(Real, E)) gExt hExt (0 : E) :=
    { hom := hom
      hom_eq := by
        intro y hy
        have hy' : ‖y‖ < 3 * R / 4 := by
          simpa only [hom, intrinsicOriginHom, PartialEquiv.ofSet_source,
            Metric.mem_ball, dist_zero_right] using hy
        change expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt
          (0 : E)
            ((tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(Real, E)) (0 : E)).symm y) = y
        rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
        with_unfolding_all
          change intrinsicGeodesic (I := 𝓘(Real, E))
            gExt hExt (0 : E) y 1 = y
          exact intrinsicExt_exp_zero (I := I) g hEnorm p hR hloc hy' }
  let f : E → Real := fun y => (1 / 2 : Real) * ‖y‖ ^ 2
  change
    0 < hessFun (I := 𝓘(Real, E)) gExt f z Y Y
  have hBsrc : (z : E) ∈ B.hom.source := by
    simpa only [B, hom, intrinsicOriginHom, PartialEquiv.ofSet_source,
      Metric.mem_ball, dist_zero_right] using hz
  have henergy :
      branchEnergy (I := 𝓘(Real, E)) gExt B = f := by
    funext y
    change
      (1 / 2 : Real) * gExt.inner (0 : E) y y =
        (1 / 2 : Real) * ‖y‖ ^ 2
    simpa only [gExt] using
      intrinsicOrigin_energy (I := I) g hEnorm p hR hloc y
  let expf : E → E := fun u =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt (0 : E) u
  have hzBall : z ∈ Metric.ball (0 : E) (3 * R / 4) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hexpid : expf =ᶠ[𝓝 z] id := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzBall] with y hy
    have hy' : ‖y‖ < 3 * R / 4 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hy
    change expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt
      (0 : E) y = y
    with_unfolding_all
      change intrinsicGeodesic (I := 𝓘(Real, E))
        gExt hExt (0 : E) y 1 = y
      exact intrinsicExt_exp_zero (I := I) g hEnorm p hR hloc hy'
  have hDexp (W : E) :
      mfderiv 𝓘(Real, E) 𝓘(Real, E) expf z W = W := by
    rw [hexpid.mfderiv_eq, mfderiv_id]
    rfl
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt (0 : E) z
  let J : E → Real → E := fun W =>
    intrinsicJacobi (I := 𝓘(Real, E)) gExt hExt (0 : E) z W
  have hγone : γ 1 = z := by
    simpa only [γ, gExt, hExt, intrinsicExtLaunch] using
      intrinsicExt_exp_zero (I := I) g hEnorm p hR hloc hz
  have hJone (W : E) : J W 1 = W := by
    have hraw :=
      congrArg (fun V => (V : E))
        (intrinsic_jacobi_one
          (I := 𝓘(Real, E)) gExt hExt (0 : E) z W)
    have hraw' :
        J W 1 =
          mfderiv 𝓘(Real, E) 𝓘(Real, E) expf z W := by
      convert hraw using 1
      all_goals rfl
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
    apply (tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(Real, E))
      (intrinsicGeodesic (I := 𝓘(Real, E))
        gExt hExt (0 : E) z 1)).injective
    with_unfolding_all
      convert hJone V using 1
      all_goals rfl
  have hfence :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        ‖intrinsicExtLaunch (I := I) g hEnorm p hR hloc
          (0 : E) z t‖ < 3 * R / 4 := by
    intro t ht
    have htAbs : |t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    calc
      ‖intrinsicExtLaunch (I := I) g hEnorm p hR hloc
          (0 : E) z t‖ =
          ‖t • z‖ := congrArg norm
            (intrinsicExt_radial_eq (I := I) g hEnorm p hR hloc hz ht)
      _ = |t| * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖z‖ := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right htAbs (norm_nonneg z)
      _ < 3 * R / 4 := hz
  have hspeedLe : Real.sqrt (gExt.inner (0 : E) z z) ≤ L := by
    rw [show gExt.inner (0 : E) z z = Inner.inner Real z z by
      simpa only [gExt] using
        intrinsicExt_inner_zero (I := I) g hEnorm p hR hloc z z,
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
        intrinsicExt_inner_zero (I := I) g hEnorm p hR hloc z W]
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
      intrinsicExt_radial_geo (I := I) g hEnorm p hR hloc hz
    let line : Real → E := fun t => t • z
    have hlineSmooth :
        ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ line := by
      exact (contDiff_id.smul contDiff_const).contMDiff
    have h1O : (1 : Real) ∈ Set.Ioo (-c) c := by
      constructor <;> linarith
    have hmodel := model_line_mfderiv_apply (E := E) z 1
    have hmodel' :
        tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) (line 1)
            (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
              line 1 (1 : Real)) = z := by
      simpa only [line] using hmodel
    have hd2 :=
      deriv2_geo_on_at_model_velocity (I := 𝓘(Real, E)) gExt
        (U := Set.univ) isOpen_univ hf.contMDiffOn hlineSmooth
        (hline 1 h1O) (Set.mem_univ (line 1)) z hmodel'
    rw [halfSq_line_deriv2 z 1] at hd2
    rw [tangentSpaceModelContinuousLinearEquiv_symm_apply] at hd2
    rw [show line 1 = z by simp only [line, one_smul]] at hd2
    exact hd2.symm
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
      have hselfT :=
        intrinsicJacobi_self
          (I := 𝓘(Real, E)) gExt hExt (0 : E) z
      have hselfE := congrArg
        (tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E))
          (intrinsicGeodesic (I := 𝓘(Real, E))
            gExt hExt (0 : E) z 1)) hselfT
      simpa only [γ, J,
        tangentSpaceModelContinuousLinearEquiv_apply] using hselfE
    have hdperp :=
      intrinsicJacobi_dperp
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
    let zT : TangentSpace 𝓘(Real, E) z :=
      (tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(Real, E)) z).symm z
    have hscaleT :
        hessFun (I := 𝓘(Real, E)) gExt f z
            (α • zT) (α • zT) =
          α ^ 2 * hessFun (I := 𝓘(Real, E)) gExt f z zT zT := by
      rw [LinearMap.map_smul₂, LinearMap.map_smul]
      simp only [smul_eq_mul]
      ring
    have hzT : zT = z :=
      tangentSpaceModelContinuousLinearEquiv_symm_apply
        (I := 𝓘(Real, E)) z z
    have hαzT : α • zT = (α • z : E) :=
      ((tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(Real, E)) z).symm.map_smul α z).symm.trans
        (tangentSpaceModelContinuousLinearEquiv_symm_apply
          (I := 𝓘(Real, E)) z (α • z))
    rw [hαzT, hzT] at hscaleT
    exact hscaleT
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
      intrinsicExt_pair_pos
        (I := I) g hEnorm p hR hloc z W hfence hspeedLe
          hW hK hRm hsmall
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
      let WT : TangentSpace 𝓘(Real, E) z :=
        (tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E)) z).symm W
      let zT : TangentSpace 𝓘(Real, E) z :=
        (tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E)) z).symm z
      have hs :=
        (hessFun (I := 𝓘(Real, E)) gExt f z WT).map_smul α zT
      have hcrossT : hessFun (I := 𝓘(Real, E))
          gExt f z WT zT = 0 := by
        with_unfolding_all
          simpa only [WT, zT,
            tangentSpaceModelContinuousLinearEquiv_symm_apply] using hcross
      have hresult : hessFun (I := 𝓘(Real, E))
          gExt f z WT (α • zT) = 0 := by
        calc
          _ = α * hessFun (I := 𝓘(Real, E)) gExt f z WT zT := by
            simpa only [smul_eq_mul] using hs
          _ = 0 := by rw [hcrossT, mul_zero]
      have hWT : WT = W :=
        tangentSpaceModelContinuousLinearEquiv_symm_apply
          (I := 𝓘(Real, E)) z W
      have hαzT : α • zT = (α • z : E) :=
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E)) z).symm.map_smul α z).symm.trans
          (tangentSpaceModelContinuousLinearEquiv_symm_apply
            (I := 𝓘(Real, E)) z (α • z))
      rw [hWT, hαzT] at hresult
      exact hresult
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

theorem intrinsicOrigin_hess_all
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
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc)
        (fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) z Y Y := by
  by_cases hz0 : z = 0
  · subst z
    rw [intrinsicOrigin_hess_zero (I := I) g hEnorm p hR hloc Y]
    exact sq_pos_of_pos (norm_pos_iff.mpr hY)
  · exact
      intrinsicOrigin_hess_pos (I := I) g hEnorm p hR hloc
        hK hRm hsmall hz hzL hz0 hY

theorem intrinsicOrigin_strict
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
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc) γ
        (interior D))
    (hD : Convex Real D)
    (hfence : ∀ t ∈ interior D, ‖γ t‖ < 3 * R / 4)
    (hbound : ∀ t ∈ interior D, ‖γ t‖ ≤ L)
    (hvel : ∀ t ∈ interior D,
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real) : E) ≠ 0) :
    StrictConvexOn Real D
      ((fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) ∘ γ) := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
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
  with_unfolding_all
    exact intrinsicOrigin_hess_all (I := I) g hEnorm p hR hloc
      hK hRm hsmall (hfence t ht) (hbound t ht) (hvel t ht)

theorem intrinsicExtendedGeodesic_stays_in_ball
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
          ((intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner x v v) ≤
        L)
    (hend : intrinsicExtLaunch (I := I) g hEnorm p hR hloc x v 1 = y) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖intrinsicExtLaunch (I := I) g hEnorm p hR hloc x v t‖ ≤ a := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
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
    simpa only [γ, gExt, hExt, intrinsicExtLaunch] using hend
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
    simpa only [γ, gExt, hExt, intrinsicExtLaunch, ← heq] using hx
  · have hfence :
        ∀ s ∈ Set.Icc (0 : Real) 1, ‖γ s‖ < 3 * R / 4 := by
      simpa only [γ, gExt, hExt, intrinsicExtLaunch] using
        intrinsicExt_shortLaunch_fenced
          (I := I) g hEnorm p hR hloc hx v hv hbudget
    have hscale :
        ∀ s ∈ Set.Icc (0 : Real) 1, ‖γ s‖ ≤ a + L / 2 := by
      simpa only [γ, gExt, hExt, intrinsicExtLaunch] using
        intrinsicExt_scale_bound
          (I := I) g hEnorm p hR hloc hx hy v hv hbudget hend
    have hstrict :
        StrictConvexOn Real (Set.Icc (0 : Real) 1)
          ((fun z : E => (1 / 2 : Real) * ‖z‖ ^ 2) ∘ γ) :=
      intrinsicOrigin_strict (I := I) g hEnorm p hR hloc
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
          intrinsicGeo_velocity_ne
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
    simpa only [γ, gExt, hExt, intrinsicExtLaunch] using hnorm

theorem intrinsicOrigin_no_return
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
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc) γ
        (Set.Ioo (0 : Real) (2 * T)))
    (hfence :
      ∀ t ∈ Set.Ioo (0 : Real) (2 * T), ‖γ t‖ < 3 * R / 4)
    (hbound : ∀ t ∈ Set.Ioo (0 : Real) (2 * T), ‖γ t‖ ≤ L)
    (hvel : ∀ t ∈ Set.Ioo (0 : Real) (2 * T),
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real) : E) ≠ 0)
    (h0T : γ 0 = γ T) (hT2 : γ T = γ (2 * T)) :
    False := by
  have hstrict :=
    intrinsicOrigin_strict (I := I) g hEnorm p hR hloc hK hRm hsmall
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

theorem intrinsicCore_short_inj
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
          ((intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner x u u) <
        L)
    (hvL :
      Real.sqrt
          ((intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner x v v) <
        L)
    (huEnd : intrinsicExtLaunch (I := I) g hEnorm p hR hloc x u 1 = y)
    (hvEnd : intrinsicExtLaunch (I := I) g hEnorm p hR hloc x v 1 = y) :
    u = v := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  have hcore : ∀ x₀ y₀ q : E, ‖x₀‖ ≤ a → ‖y₀‖ ≤ a →
      Real.sqrt (gExt.inner x₀ q q) ≤ L →
      intrinsicGeodesic gExt hExt x₀ q 1 = y₀ →
      ∀ t ∈ Icc (0 : ℝ) 1, ‖intrinsicGeodesic gExt hExt x₀ q t‖ ≤ a := by
    intro x₀ y₀ q hx₀ hy₀ hq hend
    exact intrinsicExtendedGeodesic_stays_in_ball
      (I := I) g hEnorm p hR hloc hK hRm hsmall h2aL hbudget hx₀ hy₀ q hq hend
  have hnot : ∀ x₀ q : E, ‖x₀‖ ≤ a → Real.sqrt (gExt.inner x₀ q q) ≤ L →
      ¬ IsConjVec gExt hExt x₀ q := by
    intro x₀ q hx₀ hq
    have hfence := intrinsicExt_shortLaunch_fenced
      (I := I) g hEnorm p hR hloc hx₀ q hq hbudget
    exact intrinsicExt_not_conj_of_shortLaunch
      (I := I) g hEnorm p hR hloc q hfence hq hK hRm hsmall
  by_contra huv
  have hloop : ∃ x₁ u₁ : E, ‖x₁‖ ≤ a ∧ u₁ ≠ 0 ∧
      Real.sqrt (gExt.inner x₁ u₁ u₁) ≤ L ∧
      ∃ T : ℝ, 0 < T ∧
        (∀ s : ℝ, intrinsicGeodesic gExt hExt x₁ u₁ (s + T) =
          intrinsicGeodesic gExt hExt x₁ u₁ s) ∧
        ∀ t ∈ Ioo (0 : ℝ) (2 * T), ‖intrinsicGeodesic gExt hExt x₁ u₁ t‖ ≤ a := by
    with_unfolding_all
      exact Exponential.exists_periodic_geodesic_of_expMapIntrinsic_eq
        gExt (intrinsicExt_complete (I := I) g hEnorm p hR hloc) hcore hnot x y u v
        hx hy huL hvL huEnd hvEnd huv
  obtain ⟨x₁, u₁, _, hu₁, _, T, hT, hperiod, hstay⟩ := hloop
  let γ : ℝ → E := intrinsicGeodesic gExt hExt x₁ u₁
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  have hLpos : 0 < L := (Real.sqrt_nonneg _).trans_lt huL
  have haL : a ≤ L := by linarith only [ha, h2aL]
  have haFence : a < 3 * R / 4 := by linarith only [hLpos, hbudget]
  apply intrinsicOrigin_no_return (I := I) g hEnorm p hR hloc hK hRm hsmall hT
    (γ := γ) (intrinsicGeodesic_contMDiff gExt hExt x₁ u₁)
    ((intrinsicGeodesic_isGeodesic gExt hExt x₁ u₁).isGeodesicOn _)
    (fun t ht => (hstay t ht).trans_lt haFence)
    (fun t ht => (hstay t ht).trans haL)
    (fun t _ => intrinsicGeo_velocity_ne gExt hExt x₁ u₁ hu₁ t)
  · simpa only [zero_add] using (hperiod 0).symm
  · have h := hperiod T
    rw [show T + T = 2 * T by ring] at h
    exact h.symm

end OriginEnergy

end CheegerGromovTaylor
end Riemannian
end Geometry
end DifferentialGeometry

end
