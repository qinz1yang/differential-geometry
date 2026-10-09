import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Connection.ProductAlongCurve
import DifferentialGeometry.Geometry.Connection.LeviCivita.AddCircle
import DifferentialGeometry.Topology.Manifold.AddCircle.AffinePeriodicLift
import DifferentialGeometry.Analysis.Parabolic.Euclidean.Uniqueness

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
private theorem velocity_fst (c : CurveMap (AddCircle (1 : ℝ) × M))
    {J : Set ℝ} {x t : ℝ} (hJ : UniqueDiffWithinAt ℝ J t)
    (hc : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (c.lift x) J t) :
    (c.velocity (I := 𝓘(ℝ, ℝ).prod I) J x t).1 =
      velocity (I := 𝓘(ℝ, ℝ)) (fun z τ => (c z τ).1) J x t := by
  unfold velocity lift
  have h := mfderiv_comp_mfderivWithin t mdifferentiableAt_fst hc hJ.uniqueMDiffWithinAt
  rw [mfderiv_fst] at h
  exact (congrArg (fun L => L (1 : ℝ)) h).symm

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Connection
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M]

private theorem Dx_X_fst (c : CurveMap (AddCircle (1 : ℝ) × M))
    (g : SmoothRiemannianMetric I M) {x t : ℝ}
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) 2
      (fun y => c.lift y t) x) :
    (c.Dx (fun _ => AddCircle.flatMetric.prod g) c.X x t).1 =
      Dx (fun z τ => (c z τ).1) (fun _ => AddCircle.flatMetric)
        (X (I := 𝓘(ℝ, ℝ)) (fun z τ => (c z τ).1)) x t := by
  let γ₁ : ℝ → AddCircle (1 : ℝ) := fun y => (c.lift y t).1
  let γ₂ : ℝ → M := fun y => (c.lift y t).2
  let V₁ := fun y => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ₁ y (1 : ℝ)
  let V₂ := fun y => mfderiv 𝓘(ℝ, ℝ) I γ₂ y (1 : ℝ)
  have h₁ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 γ₁ x := hc.fst
  have h₂ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ₂ x := hc.snd
  have hV₁ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent
      (fun y => (⟨γ₁ y, V₁ y⟩ : TangentBundle 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))) x :=
    (h₁.velocityLift (m := 1) (by norm_num)).mdifferentiableAt (by decide)
  have hV₂ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun y => (⟨γ₂ y, V₂ y⟩ : TangentBundle I M)) x :=
    (h₂.velocityLift (m := 1) (by norm_num)).mdifferentiableAt (by decide)
  have hX : ∀ᶠ y in 𝓝 x, (c.X (I := 𝓘(ℝ, ℝ).prod I) y t : ℝ × E) =
      (V₁ y, V₂ y) := by
    filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by decide)).mp hc] with y hy
    change mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I)
      (fun z => (γ₁ z, γ₂ z)) y 1 = _
    rw [mfderiv_prodMk (hy.fst.mdifferentiableAt (by decide))
      (hy.snd.mdifferentiableAt (by decide))]
    rfl
  have hcongr := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
    (AddCircle.flatMetric.prod g)
    (fun y => c.X (I := 𝓘(ℝ, ℝ).prod I) y t)
    (fun y => (V₁ y, V₂ y)) (Filter.EventuallyEq.refl _ _) hX
  unfold Dx
  rw [hcongr, covDerivAlong_prod AddCircle.flatMetric g
    γ₁ γ₂ V₁ V₂ x hV₁ hV₂]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M]

theorem hasDerivWithinAt_fst_local_lift_of_parabolic_equation
    (c : CurveMap (AddCircle (1 : ℝ) × M)) (g : SmoothRiemannianMetric I M)
    {J : Set ℝ} {x t a : ℝ}
    {φ ψ : ℝ → ℝ} (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (hc : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (c.lift x) J t)
    (hcx : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) 2
      (fun y => c.lift y t) x)
    (hφ : DifferentiableWithinAt ℝ φ J t)
    (hψ : ContDiffAt ℝ 2 ψ x)
    (hφeq : (fun τ => (φ τ : AddCircle (1 : ℝ))) =ᶠ[𝓝[J] t]
      (fun τ => (c.lift x τ).1))
    (hψeq : (fun y => (ψ y : AddCircle (1 : ℝ))) =ᶠ[𝓝 x]
      (fun y => (c.lift y t).1))
    (heq : c.velocity (I := 𝓘(ℝ, ℝ).prod I) J x t =
      a • c.Dx (fun _ => AddCircle.flatMetric.prod g) c.X x t) :
    HasDerivWithinAt φ (a * deriv (deriv ψ) x) J t := by
  have hvel := congrArg Prod.fst heq
  change (c.velocity (I := 𝓘(ℝ, ℝ).prod I) J x t).1 =
    a • (c.Dx (fun _ => AddCircle.flatMetric.prod g) c.X x t).1 at hvel
  rw [velocity_fst c hJ hc, Dx_X_fst c g hcx] at hvel
  have hacc := AddCircle.covDerivAlong_curveVelocity_of_local_lift hψ hψeq
  change Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong AddCircle.flatMetric
    (fun y => (c.lift y t).1)
    (fun y => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => (c.lift z t).1) y (1 : ℝ)) x = _ at hacc
  change mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun τ => (c.lift x τ).1) J t 1 =
    a • Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong AddCircle.flatMetric
      (fun y => (c.lift y t).1)
      (fun y => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => (c.lift z t).1) y (1 : ℝ)) x at hvel
  rw [hacc, smul_smul] at hvel
  have hmf : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun τ => (c.lift x τ).1) J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        ((a * deriv (deriv ψ) x) • AddCircle.parameterTangent (c.lift x t).1)) := by
    have hd : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun τ => (c.lift x τ).1) J t :=
      mdifferentiableAt_fst.comp_mdifferentiableWithinAt t hc
    have hL : (1 : ℝ →L[ℝ] ℝ).smulRight
        ((a * deriv (deriv ψ) x) • AddCircle.parameterTangent (c.lift x t).1) =
          mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun τ => (c.lift x τ).1) J t := by
      apply ContinuousLinearMap.ext
      intro r
      change r • ((a * deriv (deriv ψ) x) • AddCircle.parameterTangent (c.lift x t).1) = _
      rw [← hvel, ← map_smul]
      change (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun τ => (c.lift x τ).1) J t) (r * 1) =
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun τ => (c.lift x τ).1) J t) r
      exact congrArg
        (fun b : ℝ => (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
          (fun τ => (c.lift x τ).1) J t) b) (mul_one r)
    rw [hL]
    exact hd.hasMFDerivWithinAt
  exact AddCircle.hasDerivWithinAt_of_local_lift ht hJ hφ hφeq hmf

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

open Set Filter

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]

theorem fst_eq_id_of_parabolic_equation
    (c : CurveMap (AddCircle (1 : ℝ) × M))
    (g : ℝ → SmoothRiemannianMetric I M) {s T : ℝ}
    (hc : c.SmoothOn (I := 𝓘(ℝ, ℝ).prod I) (Icc s T))
    (hinit : ∀ z, (c z s).1 = z)
    (a : ℝ → ℝ → ℝ) (ha : ∀ x t, t ∈ Ioo s T → 0 ≤ a x t)
    (heq : ∀ x t, t ∈ Ioo s T →
      c.velocity (I := 𝓘(ℝ, ℝ).prod I) (Icc s T) x t =
        a x t • c.Dx (fun τ => AddCircle.flatMetric.prod (g τ)) c.X x t) :
    ∀ z t, t ∈ Icc s T → (c z t).1 = z := by
  by_cases hsT : s ≤ T
  · obtain ⟨θ, hθ, hθlift, hθperiod, hθinitial⟩ :=
      AddCircle.exists_contDiffOn_affine_periodic_lift_of_initial_identity hsT
        (contMDiff_fst.comp_contMDiffOn hc)
        (fun p => by
          change (c ((p.1 + 1 : ℝ) : AddCircle (1 : ℝ)) p.2).1 = (c (p.1 : AddCircle (1 : ℝ)) p.2).1
          rw [AddCircle.coe_add_period])
        (fun x => hinit (x : AddCircle (1 : ℝ)))
    have hθspace (x t : ℝ) (ht : t ∈ Icc s T) :
        ContDiffAt ℝ ∞ (fun y => θ (y, t)) x := by
      have hs : ContDiffOn ℝ ∞ (fun y => θ (y, t)) univ :=
        hθ.comp (contDiffOn_id.prodMk contDiffOn_const)
          (fun y _ => ⟨mem_univ y, ht⟩)
      exact (contDiffOn_univ.mp hs).contDiffAt
    have hθtime (x t : ℝ) (ht : t ∈ Icc s T) :
        ContDiffWithinAt ℝ ∞ (fun r => θ (x, r)) (Icc s T) t := by
      exact (hθ.comp (contDiffOn_const.prodMk contDiffOn_id)
        (fun r hr => ⟨mem_univ x, hr⟩)) t ht
    have hθheat (x t : ℝ) (ht : t ∈ Ioo s T) : HasDerivAt (fun r => θ (x, r))
        (a x t * deriv (deriv (fun y => θ (y, t))) x) t := by
      have ht' : t ∈ Icc s T := ⟨ht.1.le, ht.2.le⟩
      have hJ : UniqueDiffWithinAt ℝ (Icc s T) t :=
        uniqueDiffOn_Icc (ht.1.trans ht.2) t ht'
      apply (hasDerivWithinAt_fst_local_lift_of_parabolic_equation c (g t) ht' hJ
        ((c.time_slice_contMDiffWithinAt (Icc s T) hc x t ht').mdifferentiableWithinAt (by simp))
        (((contMDiffOn_univ.mp (c.space_slice_contMDiffOn (Icc s T) hc t ht')).contMDiffAt).of_le
          (by exact WithTop.coe_le_coe.mpr le_top))
        ((hθtime x t ht').differentiableWithinAt (by simp))
        ((hθspace x t ht').of_le (by exact WithTop.coe_le_coe.mpr le_top))
        (Filter.eventually_of_mem self_mem_nhdsWithin (fun r hr => hθlift (x, r) ⟨mem_univ x, hr⟩))
        (Filter.Eventually.of_forall (fun y => hθlift (y, t) ⟨mem_univ y, ht'⟩))
        (heq x t ht)).hasDerivAt
      exact Icc_mem_nhds ht.1 ht.2
    have hidentity := DifferentialGeometry.Analysis.Parabolic.affine_periodic_eq_id_of_homogeneous_parabolic_equation
      (u := fun x t => θ (x, t)) (a := a)
      (fun x t ht => hθperiod (x, t) ⟨mem_univ x, ht⟩)
      (hθ.continuousOn.mono (prod_mono (subset_univ _) Subset.rfl)) hθinitial
      (fun x t ht => (hθspace x t ⟨ht.1.le, ht.2.le⟩).of_le (by exact WithTop.coe_le_coe.mpr le_top)) hθheat ha
    intro z t ht
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact (hθlift (x, t) ⟨mem_univ x, ht⟩).symm.trans
      (congrArg (fun r : ℝ => (r : AddCircle (1 : ℝ))) (hidentity x t ht))
  · intro z t ht
    exact (hsT (ht.1.trans ht.2)).elim

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
