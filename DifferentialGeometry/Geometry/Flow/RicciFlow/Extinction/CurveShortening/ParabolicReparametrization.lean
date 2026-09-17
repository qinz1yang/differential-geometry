import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Reparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistenceDimensionOne
import DifferentialGeometry.Geometry.Metric.AddCircle

noncomputable section

open Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem reparametrization_lift_slices {J : Set ℝ}
    (P : CircleReparametrization J) {x t : ℝ} (ht : t ∈ J)
    {l : ℝ × ℝ → ℝ} (hl : ContDiffWithinAt ℝ ∞ l (univ ×ˢ J) (x, t))
    (heq : ∀ᶠ p in 𝓝[univ ×ˢ J] (x, t),
      (l p : AddCircle (1 : ℝ)) = P.map p.2 (p.1 : AddCircle (1 : ℝ))) :
    ContDiffAt ℝ ∞ (fun y => l (y, t)) x ∧
      DifferentiableWithinAt ℝ (fun s => l (x, s)) J t ∧
      (∀ᶠ y in 𝓝 x, (l (y, t) : AddCircle (1 : ℝ)) =
        P.map t (y : AddCircle (1 : ℝ))) ∧
      (∀ᶠ s in 𝓝[J] t, (l (x, s) : AddCircle (1 : ℝ)) =
        P.map s (x : AddCircle (1 : ℝ))) := by
  have hs : MapsTo (fun y : ℝ => (y, t)) univ (univ ×ˢ J) :=
    fun _ _ => ⟨mem_univ _, ht⟩
  have htime : MapsTo (fun s : ℝ => (x, s)) J (univ ×ˢ J) :=
    fun _ h => ⟨mem_univ _, h⟩
  refine ⟨contDiffWithinAt_univ.mp
    (hl.comp x (contDiff_id.prodMk contDiff_const).contDiffWithinAt hs),
    (hl.comp t (contDiff_const.prodMk contDiff_id).contDiffWithinAt htime).differentiableWithinAt
      (by simp), ?_, ?_⟩
  · exact (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (continuous_id.prodMk continuous_const).continuousAt
      (Filter.Eventually.of_forall (fun _ => hs trivial))).eventually heq
  · have hi : Continuous (fun s : ℝ => (x, s)) := continuous_const.prodMk continuous_id
    exact (hi.continuousWithinAt.tendsto_nhdsWithin htime).eventually heq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem speed_reparam_eq_of_induced_metric
    {c : CurveMap M} {g : ℝ → SmoothRiemannianMetric I M} {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (P : CircleReparametrization J)
    (h : ℝ → SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (hmetric : ∀ (y t : ℝ), t ∈ J →
      (h t).inner (y : AddCircle (1 : ℝ))
          (AddCircle.parameterTangent (y : AddCircle (1 : ℝ)))
          (AddCircle.parameterTangent (y : AddCircle (1 : ℝ))) =
        (g t).inner (c.lift y t) (c.X (I := I) y t) (c.X (I := I) y t))
    {x t : ℝ} (ht : t ∈ J) :
    CurveMap.speed (fun z s => P.map s z) h x t =
      CurveMap.speed (fun z s => c (P.map s z) s) g x t := by
  let q : CurveMap (AddCircle (1 : ℝ)) := fun z _ => z
  obtain ⟨l, hl, heq⟩ := P.smooth x t ht
  obtain ⟨hls, -, hspace, -⟩ := reparametrization_lift_slices P ht hl heq
  have hqd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun y => q.lift y t) (l (x, t)) :=
    AddCircle.contMDiff_coe.mdifferentiableAt (by simp)
  have hcd := (c.smooth_slice hc ht).mdifferentiableAt (x := l (x, t)) (by simp)
  have hqeq : (fun y : ℝ => (P.map t (y : AddCircle (1 : ℝ)))) =ᶠ[𝓝 x]
      (fun y => q.lift (l (y, t)) t) := Filter.EventuallyEq.symm hspace
  have hceq : (fun y : ℝ => c (P.map t (y : AddCircle (1 : ℝ))) t) =ᶠ[𝓝 x]
      (fun y => c.lift (l (y, t)) t) := by
    filter_upwards [hspace] with y hy
    exact congrArg (fun z => c z t) hy.symm
  rw [CurveMap.speed_reparam q (fun z s => P.map s z) h hqeq hqd
      (hls.differentiableAt (by simp)),
    CurveMap.speed_reparam c (fun z s => c (P.map s z) s) g hceq hcd
      (hls.differentiableAt (by simp))]
  congr 1
  change Real.sqrt ((h t).inner (l (x, t) : AddCircle (1 : ℝ))
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun y : ℝ => (y : AddCircle (1 : ℝ))) (l (x, t)) 1)
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun y : ℝ => (y : AddCircle (1 : ℝ))) (l (x, t)) 1)) = _
  erw [← AddCircle.parameterTangent_coe, hmetric _ _ ht]
  rfl

variable [FiniteDimensional ℝ E] [I.Boundaryless]

theorem CurveMap.IsSolutionOn.parabolic_equation_reparam
    {c : CurveMap M} {g : ℝ → SmoothRiemannianMetric I M} {J : Set ℝ}
    (hc : c.IsSolutionOn g J) (P : CircleReparametrization J)
    (h : ℝ → SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (hJ : UniqueDiffOn ℝ J)
    (hmetric : ∀ (y t : ℝ), t ∈ J →
      (h t).inner (y : AddCircle (1 : ℝ))
          (AddCircle.parameterTangent (y : AddCircle (1 : ℝ)))
          (AddCircle.parameterTangent (y : AddCircle (1 : ℝ))) =
        (g t).inner (c.lift y t) (c.X (I := I) y t) (c.X (I := I) y t))
    (hparametric : ∀ x t, t ∈ J →
      CurveMap.velocity (I := 𝓘(ℝ, ℝ)) (fun z s => P.map s z) J x t =
        CurveMap.speed (fun z s => P.map s z) h x t ^ (-2 : ℤ) •
          CurveMap.Dx (fun z s => P.map s z) h (CurveMap.X (fun z s => P.map s z)) x t) :
    let d : CurveMap M := fun z t => c (P.map t z) t
    d.SmoothOn (I := I) J ∧ d.ImmersedOn (I := I) J ∧
      ∀ x t, t ∈ J → d.velocity (I := I) J x t =
        d.speed g x t ^ (-2 : ℤ) • d.Dx g d.X x t := by
  let d : CurveMap M := fun z t => c (P.map t z) t
  let ψ : CurveMap (AddCircle (1 : ℝ)) := fun z t => P.map t z
  let q : CurveMap (AddCircle (1 : ℝ)) := fun z _ => z
  have hq : q.SmoothOn (I := 𝓘(ℝ, ℝ)) J :=
    staticCurve_smoothOn id AddCircle.contMDiff_coe J
  have hqi : q.ImmersedOn (I := 𝓘(ℝ, ℝ)) J := by
    intro y t ht
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun y : ℝ => (y : AddCircle (1 : ℝ))) y 1 ≠ 0
    erw [← AddCircle.parameterTangent_coe]
    exact AddCircle.parameterTangent_ne_zero _
  have hψ : ψ.SmoothOn (I := 𝓘(ℝ, ℝ)) J := hq.reparam P
  have hψi : ψ.ImmersedOn (I := 𝓘(ℝ, ℝ)) J := hqi.reparam hq P
  have hd : d.SmoothOn (I := I) J := hc.smooth.reparam P
  have hdi : d.ImmersedOn (I := I) J := hc.immersed.reparam hc.smooth P
  refine ⟨hd, hdi, ?_⟩
  intro x t ht
  obtain ⟨l, hl, heq⟩ := P.smooth x t ht
  obtain ⟨hls, hlt, hspace, htime⟩ := reparametrization_lift_slices P ht hl heq
  have hnonzero := P.deriv_localLift_ne_zero ht hl heq
  have hcd := (c.smooth_slice hc.smooth ht).mdifferentiableAt (x := l (x, t)) (by simp)
  have hqd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun y => q.lift y t) (l (x, t)) :=
    AddCircle.contMDiff_coe.mdifferentiableAt (by simp)
  have hqeq : (fun y : ℝ => ψ.lift y t) =ᶠ[𝓝 x]
      (fun y => q.lift (l (y, t)) t) := Filter.EventuallyEq.symm hspace
  have hceq : (fun y : ℝ => d.lift y t) =ᶠ[𝓝 x]
      (fun y => c.lift (l (y, t)) t) := by
    filter_upwards [hspace] with y hy
    exact congrArg (fun z => c z t) hy.symm
  have hdX := CurveMap.X_reparam c d hceq hcd (hls.differentiableAt (by simp))
  have hψX := CurveMap.X_reparam q ψ hqeq hqd (hls.differentiableAt (by simp))
  have hspeed : (fun y => ψ.speed h y t) = (fun y => d.speed g y t) :=
    funext fun y => speed_reparam_eq_of_induced_metric hc.smooth P h hmetric ht
  have hψvel := hparametric x t ht
  have hzero := curvatureVector_eq_zero_of_finrank_eq_one (I := 𝓘(ℝ, ℝ))
    (Module.finrank_self ℝ) h hψ hψi (x := x) ht
  rw [(parabolic_gauge_velocity h ψ hψ hψi x t ht).2, hzero, zero_add] at hψvel
  have hspeedat : ψ.speed h x t = d.speed g x t := congrFun hspeed x
  rw [hspeed, hspeedat, hψX] at hψvel
  erw [smul_smul] at hψvel
  have hqtime : (fun s : ℝ => ψ.lift x s) =ᶠ[𝓝[J] t]
      (fun s => q.lift (l (x, s)) s) := Filter.EventuallyEq.symm htime
  have hψderiv := congrArg (fun A : ℝ →L[ℝ] ℝ => A 1)
    (hqtime.mfderivWithin_eq_of_mem (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) ht)
  have hqchain := CurveMap.mfderivWithin_lift_comp_time hq ht (hJ t ht) hlt
  have hqvelocity : q.velocity (I := 𝓘(ℝ, ℝ)) J (l (x, t)) t = 0 :=
    staticCurve_velocity id J _ _
  rw [hqvelocity, add_zero] at hqchain
  have hscalar : derivWithin (fun s => l (x, s)) J t =
      (deriv (fun y => d.speed g y t) x / d.speed g x t ^ 3) *
        deriv (fun y => l (y, t)) x := by
    apply smul_left_injective ℝ (hqi (l (x, t)) t ht)
    exact (hψderiv.trans hqchain).symm.trans hψvel
  have hdtime : (fun s : ℝ => d.lift x s) =ᶠ[𝓝[J] t]
      (fun s => c.lift (l (x, s)) s) := by
    filter_upwards [htime] with s hs
    exact congrArg (fun z => c z s) hs.symm
  have hdderiv := congrArg (fun A : ℝ →L[ℝ] E => A 1)
    (hdtime.mfderivWithin_eq_of_mem (I := 𝓘(ℝ, ℝ)) (I' := I) ht)
  have hdchain := CurveMap.mfderivWithin_lift_comp_time hc.smooth ht (hJ t ht) hlt
  have hcurvature := CurveMap.curvatureVector_reparam c d g hceq hc.smooth hc.immersed ht
    (hls.of_le (by simp)) hnonzero
  have hvelocity : (d.velocity (I := I) J x t : E) =
      derivWithin (fun s => l (x, s)) J t • (c.X (I := I) (l (x, t)) t : E) +
        (c.velocity (I := I) J (l (x, t)) t : E) := hdderiv.trans hdchain
  rw [hscalar, hc.equation _ _ ht] at hvelocity
  change (d.velocity (I := I) J x t : E) =
    d.speed g x t ^ (-2 : ℤ) • (d.Dx g d.X x t : E)
  rw [(parabolic_gauge_velocity g d hd hdi x t ht).2]
  rw [hcurvature, hdX]
  erw [smul_smul]
  erw [add_comm]
  exact hvelocity

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
