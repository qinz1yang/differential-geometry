import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphOpens
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Framed
import DifferentialGeometry.Geometry.Metric.TensorInner.MetricKoszul

set_option autoImplicit false

noncomputable section

universe u uE uH

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

structure NormalBallChart (p : M) where
  radius : Real
  radius_pos : 0 < radius
  hom : PartialDiffeomorph (modelWithCornersSelf Real E) I E M 1
  ball_subset : Metric.ball (0 : E) radius ⊆ hom.source
  map_zero : hom 0 = p
  smooth_to :
    ContMDiffOn (modelWithCornersSelf Real E) I ∞ hom
      (Metric.ball (0 : E) radius)
  smooth_inv :
    ContMDiffOn I (modelWithCornersSelf Real E) ∞ hom.symm
      (hom '' Metric.ball (0 : E) radius)

namespace NormalBallChart

def ofHigher {p : M} {r : Real} (hr : 0 < r)
    (Φ : PartialDiffeomorph (modelWithCornersSelf Real E) I E M ∞)
    (hsub : Metric.ball (0 : E) r ⊆ Φ.source)
    (hzero : Φ 0 = p) :
    NormalBallChart (I := I) p where
  radius := r
  radius_pos := hr
  hom :=
    { toPartialEquiv := Φ.toPartialEquiv
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by simp)
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by simp) }
  ball_subset := hsub
  map_zero := hzero
  smooth_to := Φ.contMDiffOn_toFun.mono hsub
  smooth_inv := Φ.symm.contMDiffOn_toFun.mono fun y hy => by
    obtain ⟨z, hz, rfl⟩ := hy
    exact Φ.map_source (hsub hz)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space (TangentBundle I M)] in
@[simp] theorem of_higher_radius {p : M} {r : Real} (hr : 0 < r)
    (Φ : PartialDiffeomorph (modelWithCornersSelf Real E) I E M ∞)
    (hsub : Metric.ball (0 : E) r ⊆ Φ.source)
    (hzero : Φ 0 = p) :
    (ofHigher (I := I) hr Φ hsub hzero).radius = r :=
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space (TangentBundle I M)] in
@[simp] theorem of_higher_apply {p : M} {r : Real} (hr : 0 < r)
    (Φ : PartialDiffeomorph (modelWithCornersSelf Real E) I E M ∞)
    (hsub : Metric.ball (0 : E) r ⊆ Φ.source)
    (hzero : Φ 0 = p) (z : E) :
    (ofHigher (I := I) hr Φ hsub hzero).hom z = Φ z :=
  rfl

noncomputable def restrictBall {p : M}
    (c : NormalBallChart (I := I) p) :
    PartialDiffeomorph (modelWithCornersSelf Real E) I E M ∞ := by
  let Φ := c.hom
  let U : Opens E := ⟨Metric.ball (0 : E) c.radius, Metric.isOpen_ball⟩
  have hU : (U : Set E) ⊆ Φ.source := c.ball_subset
  exact
    { toPartialEquiv :=
        { toFun := Φ
          invFun := Φ.symm
          source := U
          target := (Φ : E → M) '' (U : Set E)
          map_source' := fun z hz => ⟨z, hz, rfl⟩
          map_target' := by
            rintro y ⟨z, hz, rfl⟩
            have hleft : Φ.symm (Φ z) = z := Φ.left_inv' (hU hz)
            rw [hleft]
            exact hz
          left_inv' := fun z hz => Φ.left_inv' (hU hz)
          right_inv' := by
            rintro y ⟨z, hz, rfl⟩
            have hleft : Φ.symm (Φ z) = z := Φ.left_inv' (hU hz)
            rw [hleft] }
      open_source := U.2
      open_target := image_opens_isOpen Φ hU
      contMDiffOn_toFun := by
        change ContMDiffOn (modelWithCornersSelf Real E) I ∞ Φ
          (Metric.ball (0 : E) c.radius)
        exact c.smooth_to
      contMDiffOn_invFun := by
        change ContMDiffOn I (modelWithCornersSelf Real E) ∞ Φ.symm
          (Φ '' Metric.ball (0 : E) c.radius)
        exact c.smooth_inv }

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space (TangentBundle I M)] in
@[simp] theorem restrict_ball_source {p : M}
    (c : NormalBallChart (I := I) p) :
    (c.restrictBall : PartialDiffeomorph
      (modelWithCornersSelf Real E) I E M ∞).source =
        Metric.ball (0 : E) c.radius :=
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space (TangentBundle I M)] in
@[simp] theorem restrict_ball_apply {p : M}
    (c : NormalBallChart (I := I) p) (z : E) :
    c.restrictBall z = c.hom z :=
  rfl

def inv {p : M} (c : NormalBallChart (I := I) p) : M → E :=
  c.hom.symm

def transition {p q : M}
    (c : NormalBallChart (I := I) p)
    (d : NormalBallChart (I := I) q) : E → E :=
  fun z => d.inv (c.hom z)

def OverlapOn {p q : M}
    (c : NormalBallChart (I := I) p)
    (d : NormalBallChart (I := I) q) (U : Set E) : Prop :=
  ∀ z ∈ U, z ∈ Metric.ball (0 : E) c.radius ∧
    c.hom z ∈ d.hom '' Metric.ball (0 : E) d.radius

namespace OverlapOn

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space (TangentBundle I M)] in
theorem source {p q : M}
    {c : NormalBallChart (I := I) p}
    {d : NormalBallChart (I := I) q} {U : Set E}
    (h : c.OverlapOn d U) {z : E} (hz : z ∈ U) :
    z ∈ c.hom.source :=
  c.ball_subset (h z hz).1

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space (TangentBundle I M)] in
theorem target {p q : M}
    {c : NormalBallChart (I := I) p}
    {d : NormalBallChart (I := I) q} {U : Set E}
    (h : c.OverlapOn d U) {z : E} (hz : z ∈ U) :
    c.hom z ∈ d.hom.target := by
  obtain ⟨w, hw, heq⟩ := (h z hz).2
  rw [← heq]
  exact d.hom.map_source (d.ball_subset hw)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space (TangentBundle I M)] in
theorem coord_mem {p q : M}
    {c : NormalBallChart (I := I) p}
    {d : NormalBallChart (I := I) q} {U : Set E}
    (h : c.OverlapOn d U) {z : E} (hz : z ∈ U) :
    c.transition d z ∈ Metric.ball (0 : E) d.radius := by
  obtain ⟨w, hw, heq⟩ := (h z hz).2
  have hcoord : c.transition d z = w := by
    change d.hom.symm (c.hom z) = w
    rw [← heq]
    exact d.hom.left_inv (d.ball_subset hw)
  rw [hcoord]
  exact hw

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space (TangentBundle I M)] in
theorem map_eq {p q : M}
    {c : NormalBallChart (I := I) p}
    {d : NormalBallChart (I := I) q} {U : Set E}
    (h : c.OverlapOn d U) {z : E} (hz : z ∈ U) :
    d.hom (c.transition d z) = c.hom z := by
  change d.hom (d.hom.symm (c.hom z)) = c.hom z
  exact d.hom.right_inv (h.target hz)

end OverlapOn

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space (TangentBundle I M)] in
theorem transition_smooth {p q : M}
    (c : NormalBallChart (I := I) p)
    (d : NormalBallChart (I := I) q) {U : Set E}
    (hovl : c.OverlapOn d U) :
    ContDiffOn Real (⊤ : ℕ∞) (c.transition d) U := by
  rw [← contMDiffOn_iff_contDiffOn]
  have hc : ContMDiffOn (modelWithCornersSelf Real E) I ∞ c.hom U :=
    c.smooth_to.mono fun z hz => (hovl z hz).1
  have hmap : MapsTo c.hom U
      (d.hom '' Metric.ball (0 : E) d.radius) :=
    fun z hz => (hovl z hz).2
  have hcomp := d.smooth_inv.comp hc hmap
  change ContMDiffOn (modelWithCornersSelf Real E)
    (modelWithCornersSelf Real E) ∞ (c.transition d) U at hcomp
  exact hcomp

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space (TangentBundle I M)] in
theorem transition_cancel {p q : M}
    (c : NormalBallChart (I := I) p)
    (d : NormalBallChart (I := I) q) {U : Set E}
    (hovl : c.OverlapOn d U) {z : E} (hz : z ∈ U) :
    d.transition c (c.transition d z) = z := by
  change c.hom.symm (d.hom (c.transition d z)) = z
  rw [hovl.map_eq hz]
  exact c.hom.left_inv (hovl.source hz)

noncomputable def tangent {p : M}
    (c : NormalBallChart (I := I) p) (z : E × E) :
    TangentBundle I M :=
  ⟨c.hom z.1,
    mfderiv (modelWithCornersSelf Real E) I
      (fun u : E => c.hom u) z.1 z.2⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space (TangentBundle I M)] in
@[simp] theorem tangent_zero {p : M}
    (c : NormalBallChart (I := I) p) :
    c.tangent 0 = (⟨p, (0 : E)⟩ : TangentBundle I M) := by
  simp only [tangent, Prod.fst_zero, Prod.snd_zero]
  rw [c.map_zero]
  apply TotalSpace.mk_inj.mpr
  change (mfderiv (modelWithCornersSelf Real E) I
    (fun u : E => c.hom u) 0) 0 = (0 : E)
  exact ContinuousLinearMap.map_zero _

def pair {p : M}
    (c : NormalBallChart (I := I) p) (z : E × E) : M × M :=
  (c.hom z.1, c.hom z.2)

def metric (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) :
    E → E →L[Real] E →L[Real] Real :=
  fun z =>
    let D : E →L[Real] TangentSpace I (c.hom z) :=
      mfderiv (modelWithCornersSelf Real E) I c.hom z
    (ContinuousLinearMap.precomp Real D).comp
      ((g.inner (c.hom z)).comp D)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem metric_apply (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z v w : E) :
    c.metric g z v w =
      g.inner (c.hom z)
        (mfderiv (modelWithCornersSelf Real E) I c.hom z v)
        (mfderiv (modelWithCornersSelf Real E) I c.hom z w) := by
  simp only [metric, ContinuousLinearMap.comp_apply,
    ]
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem transition_isom (g : SmoothRiemannianMetric I M) {p q : M}
    (c : NormalBallChart (I := I) p)
    (d : NormalBallChart (I := I) q) {U : Set E}
    (hovl : c.OverlapOn d U) {z : E} (hz : z ∈ U) (u v : E) :
    d.metric g (c.transition d z)
        (fderiv Real (c.transition d) z u)
        (fderiv Real (c.transition d) z v) =
      c.metric g z u v := by
  have hcz : z ∈ c.hom.source := hovl.source hz
  have htarget : c.hom z ∈ d.hom.target := hovl.target hz
  have hdz : c.transition d z ∈ d.hom.source :=
    d.ball_subset (hovl.coord_mem hz)
  have hcDiff : MDifferentiableAt (modelWithCornersSelf Real E) I c.hom z :=
    ((c.hom.contMDiffOn_toFun.mdifferentiableOn one_ne_zero z hcz).mdifferentiableAt
      (c.hom.open_source.mem_nhds hcz))
  have hdInvDiff : MDifferentiableAt I (modelWithCornersSelf Real E)
      d.hom.symm (c.hom z) :=
    ((d.hom.symm.contMDiffOn_toFun.mdifferentiableOn one_ne_zero
      (c.hom z) htarget).mdifferentiableAt
        (d.hom.open_target.mem_nhds htarget))
  have htransDiff : MDifferentiableAt (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real E) (c.transition d) z := by
    have hcomp := hdInvDiff.comp z hcDiff
    change MDifferentiableAt (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real E) (c.transition d) z at hcomp
    exact hcomp
  have hdDiff : MDifferentiableAt (modelWithCornersSelf Real E) I
      d.hom (c.transition d z) :=
    ((d.hom.contMDiffOn_toFun.mdifferentiableOn one_ne_zero
      (c.transition d z) hdz).mdifferentiableAt
        (d.hom.open_source.mem_nhds hdz))
  have hnear : ∀ᶠ w in nhds z, c.hom w ∈ d.hom.target :=
    hcDiff.continuousAt.eventually (d.hom.open_target.mem_nhds htarget)
  have heq : d.hom ∘ c.transition d =ᶠ[nhds z] c.hom := by
    filter_upwards [hnear] with w hw
    change d.hom (d.hom.symm (c.hom w)) = c.hom w
    exact d.hom.right_inv hw
  have hcomp :
      (mfderiv (modelWithCornersSelf Real E) I d.hom
        (c.transition d z)).comp
          (mfderiv (modelWithCornersSelf Real E)
            (modelWithCornersSelf Real E) (c.transition d) z) =
        mfderiv (modelWithCornersSelf Real E) I c.hom z := by
    have hderiv := Filter.EventuallyEq.mfderiv_eq
      (I := modelWithCornersSelf Real E) (I' := I) heq
    rw [mfderiv_comp z hdDiff htransDiff] at hderiv
    simpa only using hderiv
  rw [d.metric_apply g, c.metric_apply g, hovl.map_eq hz]
  have hu := DFunLike.congr_fun hcomp u
  have hv := DFunLike.congr_fun hcomp v
  rw [mfderiv_eq_fderiv (𝕜 := Real) (E := E) (E' := E)
    (f := c.transition d) (x := z)] at hu hv
  change (mfderiv (modelWithCornersSelf Real E) I d.hom
      (c.transition d z))
        (fderiv Real (c.transition d) z u) =
      mfderiv (modelWithCornersSelf Real E) I c.hom z u at hu
  change (mfderiv (modelWithCornersSelf Real E) I d.hom
      (c.transition d z))
        (fderiv Real (c.transition d) z v) =
      mfderiv (modelWithCornersSelf Real E) I c.hom z v at hv
  exact congrArg₂
    (fun a b => g.inner (c.hom z) a b) hu hv

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space (TangentBundle I M)] in
private theorem push_smooth {p : M}
    (c : NormalBallChart (I := I) p) {U : Set E}
    (hU : IsOpen U)
    (hf : ContMDiffOn (modelWithCornersSelf Real E) I ∞ c.hom U)
    (v : E) :
    ContMDiffOn (modelWithCornersSelf Real E)
      (I.prod (modelWithCornersSelf Real E)) ∞
      (fun z => TotalSpace.mk' E
        (E := fun b : M => TangentSpace I b)
        (c.hom z)
        (mfderiv (modelWithCornersSelf Real E) I c.hom z v)) U := by
  have htm :=
    hf.contMDiffOn_tangentMapWithin (m := ∞) le_rfl hU.uniqueMDiffOn
  have hσ : ContMDiff (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real E).tangent ∞
      (fun z : E =>
        (TotalSpace.mk' E z v :
          TangentBundle (modelWithCornersSelf Real E) E)) :=
    (contMDiff_vectorSpace_iff_contDiff
      (V := fun _ : E => v)).mpr contDiff_const
  have hcomp : ContMDiffOn (modelWithCornersSelf Real E) I.tangent ∞
      (fun z => tangentMapWithin (modelWithCornersSelf Real E) I
        c.hom U (TotalSpace.mk' E z v)) U :=
    htm.comp (hσ.contMDiffOn (s := U)) (fun z hz => hz)
  refine hcomp.congr ?_
  intro z hz
  have hmf : mfderivWithin (modelWithCornersSelf Real E) I
      c.hom U z =
      mfderiv (modelWithCornersSelf Real E) I c.hom z :=
    mfderivWithin_of_isOpen hU hz
  change TotalSpace.mk' E (E := fun b : M => TangentSpace I b)
      (c.hom z)
      (mfderiv (modelWithCornersSelf Real E) I c.hom z v) =
    tangentMapWithin (modelWithCornersSelf Real E) I c.hom U
      (TotalSpace.mk' E z v)
  dsimp only [tangentMapWithin]
  rw [hmf]

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem metric_cont_diff_on (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) {U : Set E}
    (hU : IsOpen U)
    (hf : ContMDiffOn (modelWithCornersSelf Real E) I ∞ c.hom U) :
    ContDiffOn Real (⊤ : ℕ∞) (c.metric g) U := by
  have hscalar : ∀ v w : E,
      ContMDiffOn (modelWithCornersSelf Real E)
        (modelWithCornersSelf Real Real) ∞
        (fun z => g.inner (c.hom z)
          (mfderiv (modelWithCornersSelf Real E) I c.hom z v)
          (mfderiv (modelWithCornersSelf Real E) I c.hom z w)) U := by
    intro v w
    have hg : ContMDiffOn (modelWithCornersSelf Real E)
        (I.prod (modelWithCornersSelf Real
          (E →L[Real] E →L[Real] Real))) ∞
        (fun z => TotalSpace.mk'
          (E →L[Real] E →L[Real] Real)
          (E := fun b : M =>
            TangentSpace I b →L[Real] TangentSpace I b →L[Real] Real)
          (c.hom z) (g.inner (c.hom z))) U :=
      g.contMDiff.comp_contMDiffOn hf
    have hv := c.push_smooth hU hf v
    have hw := c.push_smooth hU hf w
    have htotal : ContMDiffOn (modelWithCornersSelf Real E)
        (I.prod (modelWithCornersSelf Real Real)) ∞
        (fun z => TotalSpace.mk' Real
          (E := Bundle.Trivial M Real)
          (c.hom z)
          (g.inner (c.hom z)
            (mfderiv (modelWithCornersSelf Real E) I c.hom z v)
            (mfderiv (modelWithCornersSelf Real E) I c.hom z w))) U :=
      ContMDiffOn.clm_bundle_apply₂
        (E₁ := fun b : M => TangentSpace I b)
        (E₂ := fun b : M => TangentSpace I b)
        (E₃ := fun _ : M => Real)
        (b := fun z => c.hom z)
        (ψ := fun z => g.inner (c.hom z))
        (v := fun z =>
          mfderiv (modelWithCornersSelf Real E) I c.hom z v)
        (w := fun z =>
          mfderiv (modelWithCornersSelf Real E) I c.hom z w)
        hg hv hw
    intro z hz
    have h_at := htotal z hz
    rw [contMDiffWithinAt_totalSpace] at h_at
    exact h_at.2
  rw [contDiffOn_clm_apply]
  intro v
  rw [contDiffOn_clm_apply]
  intro w
  rw [← contMDiffOn_iff_contDiffOn]
  exact (hscalar v w).congr fun z _ => c.metric_apply g z v w

def MetricEquivOn (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (U : Set E) : Prop :=
  ∀ z ∈ U, ∀ v : E,
    (1 / 2 : Real) * ‖v‖ ^ 2 ≤ c.metric g z v v ∧
      c.metric g z v v ≤ 2 * ‖v‖ ^ 2

def MetricDerivBound (g : SmoothRiemannianMetric I M) {p₀ : M}
    (c : NormalBallChart (I := I) p₀) (U : Set E)
    (p : Nat) (C : Real) : Prop :=
  ∀ z ∈ U, ‖iteratedFDeriv Real p (c.metric g) z‖ ≤ C

namespace MetricDerivBound

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem of_eq_on (g : SmoothRiemannianMetric I M) {p₀ : M}
    {c : NormalBallChart (I := I) p₀} {U : Set E} (hU : IsOpen U)
    {f : E → E →L[Real] E →L[Real] Real} {p : Nat} {C : Real}
    (heq : Set.EqOn (c.metric g) f U)
    (hf : ∀ z ∈ U, ‖iteratedFDeriv Real p f z‖ ≤ C) :
    c.MetricDerivBound g U p C := by
  intro z hz
  have hev : c.metric g =ᶠ[nhds z] f :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hz) fun q hq => heq hq
  rw [(Filter.EventuallyEq.iteratedFDeriv Real hev p).eq_of_nhds]
  exact hf z hz

end MetricDerivBound

structure MetricBounds (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) where
  C : Nat → Real
  C_nonneg : ∀ q, 0 ≤ C q
  radius : Real
  radius_pos : 0 < radius
  equiv : c.MetricEquivOn g (Metric.ball (0 : E) radius)
  deriv :
    ∀ q, c.MetricDerivBound g (Metric.ball (0 : E) radius) q (C q)

namespace MetricEquivOn

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem coercive (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} {U : Set E}
    (h : c.MetricEquivOn g U) {z : E} (hz : z ∈ U) :
    IsCoercive (c.metric g z) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro v
  simpa [pow_two, mul_assoc] using (h z hz v).1

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem sharp_norm_le (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} {U : Set E}
    (h : c.MetricEquivOn g U) {z : E} (hz : z ∈ U)
    (eta : E →L[Real] Real) :
    ‖(h.coercive g hz).sharp eta‖ ≤ 2 * ‖eta‖ := by
  have hbound := IsCoercive.sharp_norm_le (h.coercive g hz)
    (c := (1 / 2 : Real)) (by norm_num)
    (fun v => by simpa [pow_two, mul_assoc] using (h z hz v).1) eta
  norm_num at hbound ⊢
  exact hbound

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem abs_apply_le (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} {U : Set E}
    (h : c.MetricEquivOn g U) {z : E} (hz : z ∈ U) (v w : E) :
    |c.metric g z v w| ≤ 2 * ‖v‖ * ‖w‖ := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  let dHom : E →L[Real] TangentSpace I (c.hom z) :=
    mfderiv (modelWithCornersSelf Real E) I c.hom z
  have hcs : |c.metric g z v w| ≤ ‖dHom v‖ * ‖dHom w‖ := by
    rw [c.metric_apply]
    exact abs_real_inner_le_norm (dHom v) (dHom w)
  have hvSq : ‖dHom v‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    have hv := (h z hz v).2
    change inner Real (dHom v) (dHom v) ≤ 2 * ‖v‖ ^ 2 at hv
    exact hv
  have hwSq : ‖dHom w‖ ^ 2 ≤ 2 * ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    have hw := (h z hz w).2
    change inner Real (dHom w) (dHom w) ≤ 2 * ‖w‖ ^ 2 at hw
    exact hw
  have hprodSq :
      (‖dHom v‖ * ‖dHom w‖) ^ 2 ≤ (2 * ‖v‖ * ‖w‖) ^ 2 := by
    have hmul := mul_le_mul hvSq hwSq (sq_nonneg ‖dHom w‖)
      (mul_nonneg (by norm_num) (sq_nonneg ‖v‖))
    nlinarith [sq_nonneg ‖v‖, sq_nonneg ‖w‖]
  exact hcs.trans <| le_of_sq_le_sq hprodSq
    (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg v)) (norm_nonneg w))

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem deriv_zero (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} {U : Set E}
    (h : c.MetricEquivOn g U) :
    c.MetricDerivBound g U 0 2 := by
  intro z hz
  rw [norm_iteratedFDeriv_zero]
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by norm_num) fun v w ↦ ?_
  simpa only [Real.norm_eq_abs] using h.abs_apply_le g hz v w

end MetricEquivOn

namespace MetricBounds

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem fderiv_apply_le (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (h : c.MetricBounds g)
    {z : E} (hz : z ∈ Metric.ball (0 : E) h.radius) (u v w : E) :
    ‖fderiv Real (c.metric g) z u v w‖ ≤
      h.C 1 * ‖u‖ * ‖v‖ * ‖w‖ := by
  let D := fderiv Real (c.metric g) z
  let T := iteratedFDeriv Real 1 (c.metric g) z
  have hT : ‖T‖ ≤ h.C 1 := h.deriv 1 z hz
  have hDu : ‖D u‖ ≤ h.C 1 * ‖u‖ := by
    calc
      ‖D u‖ = ‖T (fun _ : Fin 1 ↦ u)‖ := by
        simp only [D, T, iteratedFDeriv_one_apply]
      _ ≤ ‖T‖ * ∏ _ : Fin 1, ‖u‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖T‖ * ‖u‖ := by simp
      _ ≤ h.C 1 * ‖u‖ :=
        mul_le_mul_of_nonneg_right hT (norm_nonneg u)
  calc
    ‖D u v w‖ ≤ ‖D u‖ * ‖v‖ * ‖w‖ :=
      ContinuousLinearMap.le_opNorm₂ (D u) v w
    _ ≤ (h.C 1 * ‖u‖) * ‖v‖ * ‖w‖ := by gcongr
    _ = h.C 1 * ‖u‖ * ‖v‖ * ‖w‖ := rfl

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem koszul_vec_norm_le (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (h : c.MetricBounds g)
    {z : E} (hz : z ∈ Metric.ball (0 : E) h.radius) (v w : E) :
    ‖MetricKoszul.koszulVec (h.equiv.coercive g hz)
        (fderiv Real (c.metric g) z) v w‖ ≤
      3 * h.C 1 * ‖v‖ * ‖w‖ := by
  have hraw := MetricKoszul.koszul_vec_norm_le
    (h.equiv.coercive g hz)
    (c := (1 / 2 : Real)) (by norm_num)
    (fun u ↦ by
      simpa [pow_two, mul_assoc] using (h.equiv z hz u).1)
    (fderiv Real (c.metric g) z)
    (C := h.C 1) (h.C_nonneg 1)
    (h.fderiv_apply_le g hz) v w
  norm_num at hraw ⊢
  ring_nf at hraw ⊢
  exact hraw

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem koszul_vec_pair_le (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (h : c.MetricBounds g)
    {z y : E}
    (hz : z ∈ Metric.ball (0 : E) h.radius)
    (hy : y ∈ Metric.ball (0 : E) h.radius)
    (hmetric : ‖c.metric g y - c.metric g z‖ ≤ h.C 1 * ‖z - y‖)
    (hjet : ∀ u v w : E,
      ‖(fderiv Real (c.metric g) z -
          fderiv Real (c.metric g) y) u v w‖ ≤
        (h.C 2 * ‖z - y‖) * ‖u‖ * ‖v‖ * ‖w‖)
    (v w : E) :
    ‖MetricKoszul.koszulVec (h.equiv.coercive g hz)
          (fderiv Real (c.metric g) z) v w -
        MetricKoszul.koszulVec (h.equiv.coercive g hy)
          (fderiv Real (c.metric g) y) v w‖ ≤
      (6 * (h.C 1) ^ 2 + 3 * h.C 2) *
        ‖z - y‖ * ‖v‖ * ‖w‖ := by
  have hraw := MetricKoszul.koszul_vec_sub_le
    (h.equiv.coercive g hz) (h.equiv.coercive g hy)
    (cB := (1 / 2 : Real)) (cC := (1 / 2 : Real))
    (by norm_num) (by norm_num)
    (fun u ↦ by
      simpa [pow_two, mul_assoc] using (h.equiv z hz u).1)
    (fun u ↦ by
      simpa [pow_two, mul_assoc] using (h.equiv y hy u).1)
    (fderiv Real (c.metric g) z) (fderiv Real (c.metric g) y)
    (Csub := h.C 2 * ‖z - y‖) (CF := h.C 1)
    (mul_nonneg (h.C_nonneg 2) (norm_nonneg _))
    (h.C_nonneg 1) hjet (h.fderiv_apply_le g hy) v w
  norm_num at hraw
  have hC1 : 0 ≤ h.C 1 := h.C_nonneg 1
  calc
    ‖MetricKoszul.koszulVec (h.equiv.coercive g hz)
          (fderiv Real (c.metric g) z) v w -
        MetricKoszul.koszulVec (h.equiv.coercive g hy)
          (fderiv Real (c.metric g) y) v w‖
        ≤ 2 * ((3 / 2 : Real) * (h.C 2 * ‖z - y‖) * ‖v‖ * ‖w‖) +
          2 * (‖c.metric g y - c.metric g z‖ *
            (2 * ((3 / 2 : Real) * h.C 1 * ‖v‖ * ‖w‖))) := hraw
    _ ≤ 2 * ((3 / 2 : Real) * (h.C 2 * ‖z - y‖) * ‖v‖ * ‖w‖) +
          2 * ((h.C 1 * ‖z - y‖) *
            (2 * ((3 / 2 : Real) * h.C 1 * ‖v‖ * ‖w‖))) := by
      gcongr
    _ = (6 * (h.C 1) ^ 2 + 3 * h.C 2) *
          ‖z - y‖ * ‖v‖ * ‖w‖ := by ring

omit [FiniteDimensional ℝ E] in
private theorem fderiv_eval3
    {G : E → E →L[Real] E →L[Real] Real} {q : E}
    (hG : DifferentiableAt Real (fderiv Real G) q)
    (d u v w : E) :
    fderiv Real (fun x ↦ fderiv Real G x u v w) q d =
      fderiv Real (fderiv Real G) q d u v w := by
  let : NormedAddCommGroup (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace Real (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[Real] (E →L[Real] Real)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace Real (E →L[Real] (E →L[Real] Real)) :=
    ContinuousLinearMap.toNormedSpace
  have hu : HasFDerivAt (fun _ : E ↦ u) 0 q :=
    hasFDerivAt_const (𝕜 := Real) (x := q) u
  have hv : HasFDerivAt (fun _ : E ↦ v) 0 q :=
    hasFDerivAt_const (𝕜 := Real) (x := q) v
  have hw : HasFDerivAt (fun _ : E ↦ w) 0 q :=
    hasFDerivAt_const (𝕜 := Real) (x := q) w
  have hfirst := hG.hasFDerivAt.clm_apply hu
  have hsecond := hfirst.clm_apply hv
  have hthird := hsecond.clm_apply hw
  have happ := DFunLike.congr_fun hthird.fderiv d
  simpa using happ

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem koszul_vec_lip_on (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (h : c.MetricBounds g)
    {r : Real}
    (hr : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) h.radius)
    (hrChart : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) c.radius)
    {z y : E} (hz : z ∈ Metric.ball (0 : E) r)
    (hy : y ∈ Metric.ball (0 : E) r) (v w : E) :
    ‖MetricKoszul.koszulVec (h.equiv.coercive g (hr hz))
          (fderiv Real (c.metric g) z) v w -
        MetricKoszul.koszulVec (h.equiv.coercive g (hr hy))
          (fderiv Real (c.metric g) y) v w‖ ≤
      (6 * (h.C 1) ^ 2 + 3 * h.C 2) *
        ‖z - y‖ * ‖v‖ * ‖w‖ := by
  let : NormedAddCommGroup (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace Real (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[Real] (E →L[Real] Real)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace Real (E →L[Real] (E →L[Real] Real)) :=
    ContinuousLinearMap.toNormedSpace
  let G := c.metric g
  let U := Metric.ball (0 : E) r
  have hsm : ContDiffOn Real (⊤ : ℕ∞) G U :=
    (c.metric_cont_diff_on g Metric.isOpen_ball c.smooth_to).mono hrChart
  have hdiff : ∀ q ∈ U, DifferentiableAt Real G q := by
    intro q hq
    exact (hsm q hq).contDiffAt (Metric.isOpen_ball.mem_nhds hq)
      |>.differentiableAt (by simp)
  have hmetric : ‖G y - G z‖ ≤ h.C 1 * ‖z - y‖ := by
    have hmean := (convex_ball (0 : E) r).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := Real) (C := h.C 1) hdiff (fun q hq ↦ by
        rw [← norm_iteratedFDeriv_one (f := G)]
        exact h.deriv 1 q (hr hq)) hz hy
    calc
      ‖G y - G z‖ ≤ h.C 1 * ‖y - z‖ := hmean
      _ = h.C 1 * ‖z - y‖ := by rw [norm_sub_rev]
  have hdiffD : ∀ q ∈ U, DifferentiableAt Real (fderiv Real G) q := by
    intro q hq
    have hqsm := (hsm q hq).contDiffAt (Metric.isOpen_ball.mem_nhds hq)
    have hfdsm : ContDiffAt Real 1 (fderiv Real G) q :=
      hqsm.fderiv_right (m := 1) (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
    exact hfdsm.differentiableAt_one
  have hjet : ∀ u a b : E,
      ‖(fderiv Real G z - fderiv Real G y) u a b‖ ≤
        (h.C 2 * ‖z - y‖) * ‖u‖ * ‖a‖ * ‖b‖ := by
    intro u a b
    let F : E → Real := fun q ↦ fderiv Real G q u a b
    let C : Real := h.C 2 * ‖u‖ * ‖a‖ * ‖b‖
    have hC : 0 ≤ C := by
      dsimp only [C]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (h.C_nonneg 2) (norm_nonneg u))
          (norm_nonneg a)) (norm_nonneg b)
    have hFdiff : ∀ q ∈ U, DifferentiableAt Real F q := by
      intro q hq
      have hu : HasFDerivAt (fun _ : E ↦ u) 0 q :=
        hasFDerivAt_const (𝕜 := Real) (x := q) u
      have ha : HasFDerivAt (fun _ : E ↦ a) 0 q :=
        hasFDerivAt_const (𝕜 := Real) (x := q) a
      have hb : HasFDerivAt (fun _ : E ↦ b) 0 q :=
        hasFDerivAt_const (𝕜 := Real) (x := q) b
      exact ((((hdiffD q hq).hasFDerivAt.clm_apply hu).clm_apply ha).clm_apply hb)
        |>.differentiableAt
    have hFbound : ∀ q ∈ U, ‖fderiv Real F q‖ ≤ C := by
      intro q hq
      refine ContinuousLinearMap.opNorm_le_bound _ hC fun d ↦ ?_
      rw [fderiv_eval3 (hdiffD q hq) d u a b]
      have hdu :
          iteratedFDeriv Real 2 G q (![d, u] : Fin 2 → E) =
            fderiv Real (fderiv Real G) q d u := by
        rw [iteratedFDeriv_two_apply]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← hdu]
      calc
        ‖iteratedFDeriv Real 2 G q (![d, u] : Fin 2 → E) a b‖ ≤
            ‖iteratedFDeriv Real 2 G q (![d, u] : Fin 2 → E)‖ *
              ‖a‖ * ‖b‖ :=
          ContinuousLinearMap.le_opNorm₂ _ a b
        _ ≤ (‖iteratedFDeriv Real 2 G q‖ *
              ∏ i : Fin 2, ‖(![d, u] : Fin 2 → E) i‖) * ‖a‖ * ‖b‖ := by
          gcongr
          exact (iteratedFDeriv Real 2 G q).le_opNorm _
        _ = (‖iteratedFDeriv Real 2 G q‖ * (‖d‖ * ‖u‖)) *
              ‖a‖ * ‖b‖ := by
          rw [Fin.prod_univ_two]
          simp [Matrix.cons_val_zero, Matrix.cons_val_one]
        _ ≤ (h.C 2 * (‖d‖ * ‖u‖)) * ‖a‖ * ‖b‖ := by
          gcongr
          exact h.deriv 2 q (hr hq)
        _ = C * ‖d‖ := by
          dsimp only [C]
          ring
    have hmean := (convex_ball (0 : E) r).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := Real) (C := C) hFdiff hFbound hz hy
    calc
      ‖(fderiv Real G z - fderiv Real G y) u a b‖ =
          ‖F z - F y‖ := by
        simp only [F, sub_apply]
      _ = ‖F y - F z‖ := norm_sub_rev _ _
      _ ≤ C * ‖y - z‖ := hmean
      _ = (h.C 2 * ‖z - y‖) * ‖u‖ * ‖a‖ * ‖b‖ := by
        dsimp only [C]
        rw [norm_sub_rev y z]
        ring
  exact h.koszul_vec_pair_le g (hr hz) (hr hy)
    (by simpa only [G] using hmetric)
    (by simpa only [G] using hjet) v w

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem koszul_accel_lip_on (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (h : c.MetricBounds g)
    {r : Real}
    (hr : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) h.radius)
    (hrChart : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) c.radius)
    {z y : E × E} {R : Real} (hR : 0 ≤ R)
    (hz : z.1 ∈ Metric.ball (0 : E) r)
    (hy : y.1 ∈ Metric.ball (0 : E) r)
    (hzv : ‖z.2‖ ≤ R) (hyv : ‖y.2‖ ≤ R) :
    ‖MetricKoszul.koszulVec (h.equiv.coercive g (hr hz))
          (fderiv Real (c.metric g) z.1) z.2 z.2 -
        MetricKoszul.koszulVec (h.equiv.coercive g (hr hy))
          (fderiv Real (c.metric g) y.1) y.2 y.2‖ ≤
      ((6 * (h.C 1) ^ 2 + 3 * h.C 2) * R ^ 2 +
          6 * h.C 1 * R) * ‖z - y‖ := by
  let Kz := MetricKoszul.koszulVec (h.equiv.coercive g (hr hz))
    (fderiv Real (c.metric g) z.1)
  let Ky := MetricKoszul.koszulVec (h.equiv.coercive g (hr hy))
    (fderiv Real (c.metric g) y.1)
  let A : Real := 6 * (h.C 1) ^ 2 + 3 * h.C 2
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact add_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg (h.C 1)))
      (mul_nonneg (by norm_num) (h.C_nonneg 2))
  have hC1 : 0 ≤ h.C 1 := h.C_nonneg 1
  have hposNorm : ‖z.1 - y.1‖ ≤ ‖z - y‖ := by
    simpa only [Prod.fst_sub] using norm_fst_le (z - y)
  have hvelNorm : ‖z.2 - y.2‖ ≤ ‖z - y‖ := by
    simpa only [Prod.snd_sub] using norm_snd_le (z - y)
  have hpos : ‖Kz z.2 z.2 - Ky z.2 z.2‖ ≤
      A * R ^ 2 * ‖z - y‖ := by
    have hraw := h.koszul_vec_lip_on g hr hrChart hz hy z.2 z.2
    calc
      ‖Kz z.2 z.2 - Ky z.2 z.2‖ ≤
          A * ‖z.1 - y.1‖ * ‖z.2‖ * ‖z.2‖ := by
        simpa only [Kz, Ky, A] using hraw
      _ ≤ A * ‖z - y‖ * R * R := by gcongr
      _ = A * R ^ 2 * ‖z - y‖ := by ring
  have hvel : ‖Ky z.2 z.2 - Ky y.2 y.2‖ ≤
      6 * h.C 1 * R * ‖z - y‖ := by
    have hraw := MetricKoszul.koszul_vec_diag_le
      (h.equiv.coercive g (hr hy))
      (c := (1 / 2 : Real)) (by norm_num)
      (fun u ↦ by
        simpa [pow_two, mul_assoc] using (h.equiv y.1 (hr hy) u).1)
      (fderiv Real (c.metric g) y.1)
      (C := h.C 1) hC1 (h.fderiv_apply_le g (hr hy)) z.2 y.2
    norm_num at hraw
    calc
      ‖Ky z.2 z.2 - Ky y.2 y.2‖ ≤
          2 * ((3 / 2 : Real) * h.C 1 *
            (‖z.2‖ + ‖y.2‖) * ‖z.2 - y.2‖) := by
        simpa only [Ky] using hraw
      _ = 3 * h.C 1 * (‖z.2‖ + ‖y.2‖) * ‖z.2 - y.2‖ := by ring
      _ ≤ 3 * h.C 1 * (R + R) * ‖z - y‖ := by gcongr
      _ = 6 * h.C 1 * R * ‖z - y‖ := by ring
  have hsplit : Kz z.2 z.2 - Ky y.2 y.2 =
      (Kz z.2 z.2 - Ky z.2 z.2) +
        (Ky z.2 z.2 - Ky y.2 y.2) := by
    abel
  rw [hsplit]
  calc
    ‖(Kz z.2 z.2 - Ky z.2 z.2) +
        (Ky z.2 z.2 - Ky y.2 y.2)‖ ≤
      ‖Kz z.2 z.2 - Ky z.2 z.2‖ +
        ‖Ky z.2 z.2 - Ky y.2 y.2‖ :=
      norm_add_le _ _
    _ ≤ A * R ^ 2 * ‖z - y‖ +
          6 * h.C 1 * R * ‖z - y‖ := add_le_add hpos hvel
    _ = (A * R ^ 2 + 6 * h.C 1 * R) * ‖z - y‖ := by ring
    _ = ((6 * (h.C 1) ^ 2 + 3 * h.C 2) * R ^ 2 +
          6 * h.C 1 * R) * ‖z - y‖ := by rfl

end MetricBounds
end NormalBallChart
end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
