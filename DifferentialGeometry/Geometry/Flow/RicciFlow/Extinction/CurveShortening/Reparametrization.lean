import DifferentialGeometry.Topology.Maps.LocallyInjective
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistence
import DifferentialGeometry.Topology.Manifold.AddCircle.LocalLift
import Mathlib.Topology.Covering.AddCircle
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CalculusGeometry
import DifferentialGeometry.Geometry.Metric.SourceTangent
import DifferentialGeometry.Topology.Manifold.MFDeriv.TimeComposition

noncomputable section

open Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

def CircleReparametrization.ofContMDiffOn {J : Set ℝ}
    (F : ℝ → (AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)))
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × AddCircle (1 : ℝ) => F p.1 p.2) (J ×ˢ univ))
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × AddCircle (1 : ℝ) => (F p.1).symm p.2) (J ×ˢ univ)) :
    CircleReparametrization J where
  map := F
  smooth := by
    intro x t ht
    apply DifferentialGeometry.Topology.exists_contDiffWithinAt_addCircle_lift
    have hp : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × ℝ => (p.2, (p.1 : AddCircle (1 : ℝ)))) :=
      contDiff_snd.contMDiff.prodMk (AddCircle.contMDiff_coe.comp contDiff_fst.contMDiff)
    exact hF.comp hp.contMDiffOn (fun p hp => ⟨hp.2, mem_univ _⟩) (x, t)
      ⟨mem_univ _, ht⟩
  smooth_inverse := by
    intro x t ht
    apply DifferentialGeometry.Topology.exists_contDiffWithinAt_addCircle_lift
    have hp : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × ℝ => (p.2, (p.1 : AddCircle (1 : ℝ)))) :=
      contDiff_snd.contMDiff.prodMk (AddCircle.contMDiff_coe.comp contDiff_fst.contMDiff)
    exact hG.comp hp.contMDiffOn (fun p hp => ⟨hp.2, mem_univ _⟩) (x, t)
      ⟨mem_univ _, ht⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section

open Filter Set
open scoped Topology ContDiff


namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

theorem SmoothCircleMap.deriv_localLift_ne_zero
    {φ : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)}
    (hφinv : SmoothCircleMap φ.symm) {ψ : ℝ → ℝ} {x : ℝ}
    (hψ : DifferentiableAt ℝ ψ x)
    (hψeq : ∀ᶠ y in 𝓝 x, (ψ y : AddCircle (1 : ℝ)) = φ (y : AddCircle (1 : ℝ))) :
    deriv ψ x ≠ 0 := by
  obtain ⟨χ, hχ, hχeq⟩ := hφinv (ψ x)
  have hcomp : ∀ᶠ y in 𝓝 x,
      (χ (ψ y) : AddCircle (1 : ℝ)) = (y : AddCircle (1 : ℝ)) := by
    filter_upwards [hψ.continuousAt.eventually hχeq, hψeq] with y hyχ hyψ
    rw [hyχ, hyψ, φ.symm_apply_apply]
  have hcompx : (χ (ψ x) : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) :=
    hcomp.self_of_nhds
  have heq : (fun y => χ (ψ y)) =ᶠ[𝓝 x] (fun y => y + (χ (ψ x) - x)) := by
    refine (AddCircle.isLocalHomeomorph_coe (1 : ℝ)).isLocallyInjective
      |>.eventuallyEq_of_comp_eventuallyEq
      (hχ.continuousAt.comp hψ.continuousAt)
      (continuousAt_id.add continuousAt_const) (by simp) ?_
    filter_upwards [hcomp] with y hy
    simpa [hcompx] using hy
  have hcompderiv :=
    (hχ.differentiableAt (by simp)).hasDerivAt.comp x
      hψ.hasDerivAt
  have htranslation : HasDerivAt (fun y : ℝ => y + (χ (ψ x) - x)) 1 x :=
    (hasDerivAt_id x).add_const _
  have hprod : deriv χ (ψ x) * deriv ψ x = 1 :=
    hcompderiv.unique (htranslation.congr_of_eventuallyEq heq)
  intro hz
  simp [hz] at hprod

theorem CircleReparametrization.smooth_slice {J : Set ℝ}
    (φ : CircleReparametrization J) {t : ℝ} (ht : t ∈ J) :
    SmoothCircleMap (φ.map t) := by
  intro x
  obtain ⟨ψ, hψ, hψeq⟩ := φ.smooth x t ht
  have hi : ContDiff ℝ ∞ (fun y : ℝ => (y, t)) :=
    contDiff_id.prodMk contDiff_const
  have hmaps : MapsTo (fun y : ℝ => (y, t)) univ (univ ×ˢ J) :=
    fun _ _ => ⟨mem_univ _, ht⟩
  have hs : ContDiffAt ℝ ∞ (fun y => ψ (y, t)) x :=
    contDiffWithinAt_univ.mp (hψ.comp x hi.contDiffAt.contDiffWithinAt hmaps)
  refine ⟨fun y => ψ (y, t), hs, ?_⟩
  exact (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    hi.continuous.continuousAt
    (Filter.Eventually.of_forall (fun _ => hmaps trivial))).eventually hψeq

theorem CircleReparametrization.smooth_inverse_slice {J : Set ℝ}
    (φ : CircleReparametrization J) {t : ℝ} (ht : t ∈ J) :
    SmoothCircleMap (φ.map t).symm := by
  intro x
  obtain ⟨ψ, hψ, hψeq⟩ := φ.smooth_inverse x t ht
  have hi : ContDiff ℝ ∞ (fun y : ℝ => (y, t)) :=
    contDiff_id.prodMk contDiff_const
  have hmaps : MapsTo (fun y : ℝ => (y, t)) univ (univ ×ˢ J) :=
    fun _ _ => ⟨mem_univ _, ht⟩
  have hs : ContDiffAt ℝ ∞ (fun y => ψ (y, t)) x :=
    contDiffWithinAt_univ.mp (hψ.comp x hi.contDiffAt.contDiffWithinAt hmaps)
  refine ⟨fun y => ψ (y, t), hs, ?_⟩
  exact (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    hi.continuous.continuousAt
    (Filter.Eventually.of_forall (fun _ => hmaps trivial))).eventually hψeq

theorem CircleReparametrization.deriv_localLift_ne_zero {J : Set ℝ}
    (φ : CircleReparametrization J) {x t : ℝ} (ht : t ∈ J)
    {ψ : ℝ × ℝ → ℝ} (hψ : ContDiffWithinAt ℝ ∞ ψ (univ ×ˢ J) (x, t))
    (hψeq : ∀ᶠ p in 𝓝[univ ×ˢ J] (x, t),
      (ψ p : AddCircle (1 : ℝ)) = φ.map p.2 (p.1 : AddCircle (1 : ℝ))) :
    deriv (fun y => ψ (y, t)) x ≠ 0 := by
  have hi : ContDiff ℝ ∞ (fun y : ℝ => (y, t)) :=
    contDiff_id.prodMk contDiff_const
  have hmaps : MapsTo (fun y : ℝ => (y, t)) univ (univ ×ˢ J) :=
    fun _ _ => ⟨mem_univ _, ht⟩
  have hs : ContDiffAt ℝ ∞ (fun y => ψ (y, t)) x :=
    contDiffWithinAt_univ.mp (hψ.comp x hi.contDiffAt.contDiffWithinAt hmaps)
  apply (φ.smooth_inverse_slice ht).deriv_localLift_ne_zero (hs.differentiableAt (by simp))
  exact (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    hi.continuous.continuousAt
    (Filter.Eventually.of_forall (fun _ => hmaps trivial))).eventually hψeq

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
theorem X_reparam (c d : CurveMap M) {φ : ℝ → ℝ} {x t : ℝ}
    (heq : (fun y : ℝ => d.lift y t) =ᶠ[𝓝 x] (fun y => c.lift (φ y) t))
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) (φ x))
    (hφ : DifferentiableAt ℝ φ x) :
    d.X (I := I) x t = deriv φ x • c.X (I := I) (φ x) t := by
  unfold X
  rw [heq.mfderiv_eq]
  have h := congrArg (fun p : TangentBundle I M => (p.2 : E))
    (DifferentialGeometry.Geometry.tangent_velocity_comp hc hφ)
  change mfderiv 𝓘(ℝ, ℝ) I (fun y => c.lift (φ y) t) x 1 =
    mfderiv 𝓘(ℝ, ℝ) I (fun y => c.lift y t) (φ x) (deriv φ x) at h
  apply h.trans
  erw [← map_smul]
  congr 1
  change deriv φ x = deriv φ x * (1 : ℝ)
  exact (mul_one _).symm

theorem speed_reparam (c d : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {φ : ℝ → ℝ} {x t : ℝ}
    (heq : (fun y : ℝ => d.lift y t) =ᶠ[𝓝 x] (fun y => c.lift (φ y) t))
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) (φ x))
    (hφ : DifferentiableAt ℝ φ x) :
    d.speed g x t = |deriv φ x| * c.speed g (φ x) t := by
  unfold speed
  rw [heq.eq_of_nhds, X_reparam c d heq hc hφ]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem unitTangent_reparam_pos (c d : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) {φ : ℝ → ℝ} {x t : ℝ}
    (heq : (fun y : ℝ => d.lift y t) =ᶠ[𝓝 x] (fun y => c.lift (φ y) t))
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) (φ x))
    (hφ : DifferentiableAt ℝ φ x) (hpos : 0 < deriv φ x) :
    d.unitTangent g x t = c.unitTangent g (φ x) t := by
  change (d.speed g x t)⁻¹ • (d.X (I := I) x t : E) =
    (c.speed g (φ x) t)⁻¹ • (c.X (I := I) (φ x) t : E)
  rw [speed_reparam c d g heq hc hφ, abs_of_pos hpos, X_reparam c d heq hc hφ]
  erw [smul_smul]
  congr 1
  field_simp

theorem unitTangent_reparam_neg (c d : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) {φ : ℝ → ℝ} {x t : ℝ}
    (heq : (fun y : ℝ => d.lift y t) =ᶠ[𝓝 x] (fun y => c.lift (φ y) t))
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) (φ x))
    (hφ : DifferentiableAt ℝ φ x) (hneg : deriv φ x < 0) :
    d.unitTangent g x t = (-1 : ℝ) • c.unitTangent g (φ x) t := by
  change (d.speed g x t)⁻¹ • (d.X (I := I) x t : E) =
    (-1 : ℝ) • ((c.speed g (φ x) t)⁻¹ • (c.X (I := I) (φ x) t : E))
  rw [speed_reparam c d g heq hc hφ, abs_of_neg hneg, X_reparam c d heq hc hφ]
  erw [smul_smul, smul_smul]
  congr 1
  field_simp [ne_of_lt hneg]

variable [FiniteDimensional ℝ E]

theorem curvatureVector_reparam_pos (c d : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) {φ : ℝ → ℝ} {x t : ℝ} {J : Set ℝ}
    (heq : (fun y : ℝ => d.lift y t) =ᶠ[𝓝 x] (fun y => c.lift (φ y) t))
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J) (ht : t ∈ J)
    (hφ : ContDiffAt ℝ 1 φ x) (hpos : 0 < deriv φ x) :
    d.curvatureVector g x t = c.curvatureVector g (φ x) t := by
  have hcs : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t) :=
    contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc t ht)
  have hcd (s : ℝ) := hcs.mdifferentiable (by simp) s
  have hpd := hφ.differentiableAt one_ne_zero
  have hevent : ∀ᶠ s in 𝓝 x, 0 < deriv φ s :=
    (hφ.derivWithin (m := 0) (by simp)).continuousAt.eventually (lt_mem_nhds hpos)
  have hT : ∀ᶠ s in 𝓝 x, d.unitTangent g s t = c.unitTangent g (φ s) t := by
    filter_upwards [hevent, heq.eventuallyEq_nhds, hφ.eventually (by norm_num)] with s hs heqs hφs
    exact unitTangent_reparam_pos c d g heqs (hcd _) (hφs.differentiableAt one_ne_zero) hs
  have hrep := differentiableAt_chartRepAt_of_contMDiff_two
    ((c.unitTangent_contMDiff g J hc hi t ht).of_le (by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)) (φ x)
  have hcov := covDerivAlong_congr_curve (g t) (fun y => d.unitTangent g y t)
    (fun y => c.unitTangent g (φ y) t) heq hT
  have hcomp := covDerivAlong_comp (g t) (fun y => c.lift y t)
    (fun y => c.unitTangent g y t) φ x (hcd _) hrep hpd
  change (d.speed g x t)⁻¹ •
      (covDerivAlong (g t) (fun y => d.lift y t) (fun y => d.unitTangent g y t) x : E) =
    (c.speed g (φ x) t)⁻¹ •
      (covDerivAlong (g t) (fun y => c.lift y t) (fun y => c.unitTangent g y t) (φ x) : E)
  rw [speed_reparam c d g heq (hcd _) hpd, abs_of_pos hpos]
  rw [hcov]
  erw [hcomp]
  erw [smul_smul]
  congr 1
  field_simp

theorem curvatureVector_reparam_neg (c d : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) {φ : ℝ → ℝ} {x t : ℝ} {J : Set ℝ}
    (heq : (fun y : ℝ => d.lift y t) =ᶠ[𝓝 x] (fun y => c.lift (φ y) t))
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J) (ht : t ∈ J)
    (hφ : ContDiffAt ℝ 1 φ x) (hneg : deriv φ x < 0) :
    d.curvatureVector g x t = c.curvatureVector g (φ x) t := by
  have hcs : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t) :=
    contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc t ht)
  have hcd (s : ℝ) := hcs.mdifferentiable (by simp) s
  have hpd := hφ.differentiableAt one_ne_zero
  have hevent : ∀ᶠ s in 𝓝 x, deriv φ s < 0 :=
    (hφ.derivWithin (m := 0) (by simp)).continuousAt.eventually (gt_mem_nhds hneg)
  have hT : ∀ᶠ s in 𝓝 x, d.unitTangent g s t = (-1 : ℝ) • c.unitTangent g (φ s) t := by
    filter_upwards [hevent, heq.eventuallyEq_nhds, hφ.eventually (by norm_num)] with s hs heqs hφs
    exact unitTangent_reparam_neg c d g heqs (hcd _) (hφs.differentiableAt one_ne_zero) hs
  have hrep := differentiableAt_chartRepAt_of_contMDiff_two
    ((c.unitTangent_contMDiff g J hc hi t ht).of_le (by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)) (φ x)
  have hcov := covDerivAlong_congr_curve (g t) (fun y => d.unitTangent g y t)
    (fun y => (-1 : ℝ) • c.unitTangent g (φ y) t) heq hT
  have hcomp := covDerivAlong_comp (g t) (fun y => c.lift y t)
    (fun y => c.unitTangent g y t) φ x (hcd _) hrep hpd
  change (d.speed g x t)⁻¹ •
      (covDerivAlong (g t) (fun y => d.lift y t) (fun y => d.unitTangent g y t) x : E) =
    (c.speed g (φ x) t)⁻¹ •
      (covDerivAlong (g t) (fun y => c.lift y t) (fun y => c.unitTangent g y t) (φ x) : E)
  rw [speed_reparam c d g heq (hcd _) hpd, abs_of_neg hneg]
  rw [hcov]
  rw [covDerivAlong_smul]
  erw [hcomp]
  erw [smul_smul, smul_smul]
  congr 1
  field_simp [ne_of_lt hneg, ne_of_gt (c.speed_pos g hi (φ x) t ht)]

theorem curvatureVector_reparam (c d : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) {φ : ℝ → ℝ} {x t : ℝ} {J : Set ℝ}
    (heq : (fun y : ℝ => d.lift y t) =ᶠ[𝓝 x] (fun y => c.lift (φ y) t))
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J) (ht : t ∈ J)
    (hφ : ContDiffAt ℝ 1 φ x) (hne : deriv φ x ≠ 0) :
    d.curvatureVector g x t = c.curvatureVector g (φ x) t := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact curvatureVector_reparam_neg c d g heq hc hi ht hφ hneg
  · exact curvatureVector_reparam_pos c d g heq hc hi ht hφ hpos

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section

open Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem CurveMap.SmoothOn.reparam {c : CurveMap M} {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (φ : CircleReparametrization J) :
    CurveMap.SmoothOn (I := I) (fun z t => c (φ.map t z) t) J := by
  intro p hp
  obtain ⟨l, hl, heq⟩ := φ.smooth p.1 p.2 hp.2
  have hmap : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun q : ℝ × ℝ => (l q, q.2)) (univ ×ˢ J) p :=
    (hl.prodMk contDiffWithinAt_snd).contMDiffWithinAt
  have hm : MapsTo (fun q : ℝ × ℝ => (l q, q.2)) (univ ×ˢ J) (univ ×ˢ J) :=
    fun q hq => ⟨mem_univ _, hq.2⟩
  have hcomp := (hc (l p, p.2) ⟨mem_univ _, hp.2⟩).comp p hmap hm
  apply hcomp.congr_of_eventuallyEq_of_mem _ hp
  filter_upwards [heq] with q hq
  exact congrArg (fun z => c z q.2) hq.symm

theorem CurveMap.SmoothOn.reparam_inverse {c : CurveMap M} {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (φ : CircleReparametrization J) :
    CurveMap.SmoothOn (I := I) (fun z t => c ((φ.map t).symm z) t) J := by
  intro p hp
  obtain ⟨l, hl, heq⟩ := φ.smooth_inverse p.1 p.2 hp.2
  have hmap : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun q : ℝ × ℝ => (l q, q.2)) (univ ×ˢ J) p :=
    (hl.prodMk contDiffWithinAt_snd).contMDiffWithinAt
  have hm : MapsTo (fun q : ℝ × ℝ => (l q, q.2)) (univ ×ˢ J) (univ ×ˢ J) :=
    fun q hq => ⟨mem_univ _, hq.2⟩
  have hcomp := (hc (l p, p.2) ⟨mem_univ _, hp.2⟩).comp p hmap hm
  apply hcomp.congr_of_eventuallyEq_of_mem _ hp
  filter_upwards [heq] with q hq
  exact congrArg (fun z => c z q.2) hq.symm

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section

open Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem mfderivWithin_lift_comp_time {c : CurveMap M} {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) {φ : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (hφ : DifferentiableWithinAt ℝ φ J t) :
    mfderivWithin 𝓘(ℝ, ℝ) I (fun s => c.lift (φ s) s) J t (1 : ℝ) =
      (derivWithin φ J t) • c.X (I := I) (φ t) t + c.velocity J (φ t) t :=
  DifferentialGeometry.mfderivWithin_comp_prod_id ht hJ
    ((hc (φ t, t) ⟨mem_univ _, ht⟩).mdifferentiableWithinAt (by simp)) hφ

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

theorem IsGeometricSolutionOn.mfderivWithin_lift_comp_time
    {c : CurveMap M} {g : ℝ → SmoothRiemannianMetric I M} {J : Set ℝ}
    {α : ℝ → ℝ → ℝ} (hc : c.IsGeometricSolutionOn g J α)
    {φ : ℝ → ℝ} {t : ℝ} (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (hφ : HasDerivWithinAt φ (-(α (φ t) t) / c.speed g (φ t) t) J t) :
    mfderivWithin 𝓘(ℝ, ℝ) I (fun s => c.lift (φ s) s) J t (1 : ℝ) =
      c.curvatureVector g (φ t) t := by
  rw [CurveMap.mfderivWithin_lift_comp_time hc.smooth ht hJ hφ.differentiableWithinAt,
    hφ.derivWithin hJ, hc.equation (φ t) t ht]
  simp only [unitTangent, smul_smul, div_eq_mul_inv, neg_mul, neg_smul]
  abel

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section
open Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private theorem space_lift_smooth {J : Set ℝ} {x t : ℝ} (ht : t ∈ J)
    {l : ℝ × ℝ → ℝ} (hl : ContDiffWithinAt ℝ ∞ l (univ ×ˢ J) (x, t)) :
    ContDiffAt ℝ ∞ (fun y => l (y, t)) x := by
  have hi : ContDiff ℝ ∞ (fun y : ℝ => (y, t)) :=
    contDiff_id.prodMk contDiff_const
  have hmaps : MapsTo (fun y : ℝ => (y, t)) univ (univ ×ˢ J) :=
    fun _ _ => ⟨mem_univ _, ht⟩
  exact contDiffWithinAt_univ.mp (hl.comp x hi.contDiffAt.contDiffWithinAt hmaps)

private theorem space_lift_eq {J : Set ℝ} {x t : ℝ} (ht : t ∈ J)
    {l : ℝ × ℝ → ℝ} {φ : CircleReparametrization J}
    (heq : ∀ᶠ p in 𝓝[univ ×ˢ J] (x, t),
      (l p : AddCircle (1 : ℝ)) = φ.map p.2 (p.1 : AddCircle (1 : ℝ))) :
    ∀ᶠ y in 𝓝 x, (l (y, t) : AddCircle (1 : ℝ)) = φ.map t (y : AddCircle (1 : ℝ)) := by
  have hi : Continuous (fun y : ℝ => (y, t)) := continuous_id.prodMk continuous_const
  have hmaps : MapsTo (fun y : ℝ => (y, t)) univ (univ ×ˢ J) :=
    fun _ _ => ⟨mem_univ _, ht⟩
  exact (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    hi.continuousAt (Filter.Eventually.of_forall (fun _ => hmaps trivial))).eventually heq

theorem CurveMap.ImmersedOn.reparam {c : CurveMap M} {J : Set ℝ}
    (hi : c.ImmersedOn (I := I) J) (hc : c.SmoothOn (I := I) J)
    (φ : CircleReparametrization J) :
    CurveMap.ImmersedOn (I := I) (fun z t => c (φ.map t z) t) J := by
  let d : CurveMap M := fun z t => c (φ.map t z) t
  intro x t ht
  obtain ⟨l, hl, hleq⟩ := φ.smooth x t ht
  have hsp := φ.deriv_localLift_ne_zero ht hl hleq
  have hls := space_lift_smooth ht hl
  have hspace := space_lift_eq ht hleq
  have heq : (fun y : ℝ => d.lift y t) =ᶠ[𝓝 x]
      (fun y => c.lift (l (y, t)) t) := by
    filter_upwards [hspace] with y hy
    exact congrArg (fun z => c z t) hy.symm
  have hcd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) (l (x, t)) :=
    (c.smooth_slice hc ht).mdifferentiable (by simp) _
  change d.X (I := I) x t ≠ 0
  rw [CurveMap.X_reparam c d heq hcd (hls.differentiableAt (by simp))]
  exact smul_ne_zero hsp (hi _ _ ht)

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

theorem CurveMap.IsGeometricSolutionOn.isSolutionOn_reparam_of_local_lifts
    {c : CurveMap M} {g : ℝ → SmoothRiemannianMetric I M} {J : Set ℝ}
    {α : ℝ → ℝ → ℝ} (hc : c.IsGeometricSolutionOn g J α)
    (φ : CircleReparametrization J) (hJ : UniqueDiffOn ℝ J)
    (hdata : ∀ x t, t ∈ J → ∃ l : ℝ × ℝ → ℝ,
      ContDiffWithinAt ℝ ∞ l (univ ×ˢ J) (x, t) ∧
      (∀ᶠ p in 𝓝[univ ×ˢ J] (x, t),
        (l p : AddCircle (1 : ℝ)) = φ.map p.2 (p.1 : AddCircle (1 : ℝ))) ∧
      HasDerivWithinAt (fun s => l (x, s))
        (-(α (l (x, t)) t) / c.speed g (l (x, t)) t) J t) :
    CurveMap.IsSolutionOn (I := I) (fun z t => c (φ.map t z) t) g J := by
  let d : CurveMap M := fun z t => c (φ.map t z) t
  refine ⟨hc.smooth.reparam φ, hc.immersed.reparam hc.smooth φ, ?_⟩
  intro x t ht
  obtain ⟨l, hl, hleq, hderiv⟩ := hdata x t ht
  have hsp := φ.deriv_localLift_ne_zero ht hl hleq
  have hls := space_lift_smooth ht hl
  have hspace := space_lift_eq ht hleq
  have htime : ∀ᶠ s in 𝓝[J] t,
      (l (x, s) : AddCircle (1 : ℝ)) = φ.map s (x : AddCircle (1 : ℝ)) := by
    have hi : Continuous (fun s : ℝ => (x, s)) := continuous_const.prodMk continuous_id
    have hmaps : MapsTo (fun s : ℝ => (x, s)) J (univ ×ˢ J) :=
      fun _ hs => ⟨mem_univ _, hs⟩
    exact (hi.continuousWithinAt.tendsto_nhdsWithin hmaps).eventually hleq
  have heq : (fun s : ℝ => d.lift x s) =ᶠ[𝓝[J] t]
      (fun s => c.lift (l (x, s)) s) := by
    filter_upwards [htime] with s hs
    exact congrArg (fun z => c z s) hs.symm
  have heqspace : (fun y : ℝ => d.lift y t) =ᶠ[𝓝 x]
      (fun y => c.lift (l (y, t)) t) := by
    filter_upwards [hspace] with y hy
    exact congrArg (fun z => c z t) hy.symm
  change d.velocity (I := I) J x t = d.curvatureVector g x t
  have hv := hc.mfderivWithin_lift_comp_time ht (hJ t ht) hderiv
  have hcurv := CurveMap.curvatureVector_reparam c d g heqspace hc.smooth hc.immersed ht
    (hls.of_le (by simp)) hsp
  change mfderivWithin 𝓘(ℝ, ℝ) I (fun s => d.lift x s) J t (1 : ℝ) = _
  have hdv := congrArg (fun A : ℝ →L[ℝ] E => A 1)
    (heq.mfderivWithin_eq_of_mem (I := 𝓘(ℝ, ℝ)) (I' := I) ht)
  exact hdv.trans (hv.trans hcurv.symm)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
