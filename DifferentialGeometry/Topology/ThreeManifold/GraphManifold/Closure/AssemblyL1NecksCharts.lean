import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksProfilesApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksBallChart
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.InteriorChart
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.Immersion

/-!
# Chapter-14 assembly, item L1, G3b / T1′: local charts of the master bicollar

Lane ASM-L1e, group C. The master bicollar of a rim (`AssemblyL1NecksMaster.lean`) is, near each
point, one of three local diffeomorphisms; this file provides them.

* `isLocalDiffeomorphAt_of_contDiffOn_of_bijective`: the inverse function theorem between finite
  dimensional spaces in the form `IsLocalDiffeomorphAt`.
* `isLocalDiffeomorphAt_of_bijective_of_isInteriorPoint`: a smooth map from a vector space into a
  manifold with corners, of bijective differential at a point sent to an interior point, is a
  local diffeomorphism there (read in the interior chart `interiorChart`).
* `planePolar`: polar coordinates `(z, s) ↦ (planeUnit z, (‖z‖, s))` of `ℝ² × ℝ` off the axis, as a
  partial diffeomorphism onto `Circle × (0, ∞) × ℝ`.
* `isLocalDiffeomorphAt_rimCoord`: `(θ, (r, s)) ↦ (θ, (f (8 (r - 1)), s))` for a compression `f`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASML1eC : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASML1eC : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

local instance diskChartsSucc_ASML1eC :
    ChartedSpace (EuclideanHalfSpace (1 + 1)) (ClosedCell (1 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

/-! ## Inverse function theorems -/

/-- The inverse function theorem between finite-dimensional spaces. -/
theorem isLocalDiffeomorphAt_of_contDiffOn_of_bijective {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hbij : Bijective (fderiv ℝ f x)) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x := by
  apply DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
    hU hx (contMDiffOn_iff_contDiffOn.mpr hf)
  rw [mfderiv_eq_fderiv]
  exact ⟨((LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap hbij).toContinuousLinearEquiv),
    rfl⟩

/-- The inverse function theorem into a manifold with corners, at a point sent to an interior
point. -/
theorem isLocalDiffeomorphAt_of_bijective_of_isInteriorPoint {E E' H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E' H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {f : E → M} {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I ∞ f U) (hbij : Bijective (mfderiv 𝓘(ℝ, E) I f x))
    (hint : I.IsInteriorPoint (f x)) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ f x := by
  let c := DifferentialGeometry.Manifold.interiorChart I ∞ (f x)
  have hfx : f x ∈ c.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ (f x)).mpr hint
  set V : Set E := U ∩ f ⁻¹' c.source with hV
  have hVo : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU c.open_source
  have hxV : x ∈ V := ⟨hx, hfx⟩
  have hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ (c ∘ f) V :=
    c.contMDiffOn_toFun.comp (hf.mono inter_subset_left) (fun y hy => hy.2)
  have hcd : MDifferentiableAt I 𝓘(ℝ, E') c (f x) :=
    (c.isLocalDiffeomorphAt I 𝓘(ℝ, E') ∞ hfx).mdifferentiableAt (by simp)
  have hfd : MDifferentiableAt 𝓘(ℝ, E) I f x :=
    (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') (c ∘ f) x).IsInvertible := by
    rw [mfderiv_comp x hcd hfd]
    have hc : Bijective (mfderiv I 𝓘(ℝ, E') c (f x)) :=
      ((c.isLocalDiffeomorphAt I 𝓘(ℝ, E') ∞ hfx).mfderivToContinuousLinearEquiv (by simp)).bijective
    exact ⟨(LinearEquiv.ofBijective ((mfderiv I 𝓘(ℝ, E') c (f x)).comp
      (mfderiv 𝓘(ℝ, E) I f x)).toLinearMap (hc.comp hbij)).toContinuousLinearEquiv, rfl⟩
  have hgl : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ (c ∘ f) x :=
    DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
      hVo hxV hg hinv
  have hcs : IsLocalDiffeomorphAt 𝓘(ℝ, E') I ∞ c.symm ((c ∘ f) x) :=
    c.symm.isLocalDiffeomorphAt 𝓘(ℝ, E') I ∞ (c.map_source hfx)
  have hcomp := hgl.comp I M hcs
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _ hcomp
  filter_upwards [hVo.mem_nhds hxV] with y hy
  exact (c.left_inv hy.2).symm

/-! ## Polar coordinates of `ℝ² × ℝ` -/

/-- Polar coordinates `(z, s) ↦ (planeUnit z, (‖z‖, s))` off the axis `z = 0`. -/
def planePolar : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
    ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) (EuclideanSpace ℝ (Fin 2) × ℝ) (Circle × (ℝ × ℝ)) ∞ where
  toFun q := (planeUnit q.1, (‖q.1‖, q.2))
  invFun p := (p.2.1 • planeOfCircle p.1, p.2.2)
  source := {q | q.1 ≠ 0}
  target := {p | 0 < p.2.1}
  map_source' q hq := by
    change 0 < ‖q.1‖
    exact norm_pos_iff.mpr hq
  map_target' p hp := by
    change p.2.1 • planeOfCircle p.1 ≠ 0
    exact smul_ne_zero (ne_of_gt hp) (by
      intro h0
      have := norm_planeOfCircle_eq_one p.1
      rw [h0, norm_zero] at this
      exact zero_ne_one this)
  left_inv' q hq := by
    change (‖q.1‖ • planeOfCircle (planeUnit q.1), q.2) = q
    rw [norm_smul_planeOfCircle_planeUnit hq]
  right_inv' p hp := by
    have hp' : 0 < p.2.1 := hp
    change (planeUnit (p.2.1 • planeOfCircle p.1), (‖p.2.1 • planeOfCircle p.1‖, p.2.2)) = p
    rw [planeUnit_smul_planeOfCircle hp', norm_smul, norm_planeOfCircle_eq_one, mul_one,
      Real.norm_of_nonneg hp'.le]
  open_source := isOpen_ne.preimage continuous_fst
  open_target := isOpen_lt continuous_const (continuous_fst.comp continuous_snd)
  contMDiffOn_toFun := by
    have h1 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡 1) ∞
        (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => planeUnit q.1) {q | q.1 ≠ 0} :=
      contMDiffOn_planeUnit.comp contDiff_fst.contMDiff.contMDiffOn (fun q hq => hq)
    have h2 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
        (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => (‖q.1‖, q.2)) {q | q.1 ≠ 0} := by
      intro q hq
      exact (((contDiffAt_norm ℝ hq).comp q contDiffAt_fst).prodMk
        contDiffAt_snd).contMDiffAt.contMDiffWithinAt
    exact h1.prodMk h2
  contMDiffOn_invFun := by
    have hpl : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun p : Circle × (ℝ × ℝ) => planeOfCircle p.1) :=
      Complex.orthonormalBasisOneI.repr.contDiff.contMDiff.comp
        (contMDiff_circle_coe.comp contMDiff_fst)
    exact ((contDiff_fst.contMDiff.comp contMDiff_snd).smul hpl).prodMk_space
      (contDiff_snd.contMDiff.comp contMDiff_snd) |>.contMDiffOn

theorem planePolar_apply (q : EuclideanSpace ℝ (Fin 2) × ℝ) :
    planePolar q = (planeUnit q.1, (‖q.1‖, q.2)) :=
  rfl

theorem planePolar_source : planePolar.source = {q | q.1 ≠ 0} :=
  rfl

/-! ## The compressed rim coordinate -/

/-- `(r, s) ↦ (f (8 (r - 1)), s)` is a local diffeomorphism for `f' > 0`. -/
theorem isLocalDiffeomorphAt_rimRadial {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfd : ∀ x, 0 < deriv f x) (p : ℝ × ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (Prod.map (fun r : ℝ => f (8 * (r - 1))) id) p := by
  have hF : ContDiff ℝ ∞ (fun r : ℝ => f (8 * (r - 1))) :=
    hf.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have hc : ContDiff ℝ ∞ (Prod.map (fun r : ℝ => f (8 * (r - 1))) (id : ℝ → ℝ)) :=
    hF.prodMap contDiff_id
  apply isLocalDiffeomorphAt_of_contDiffOn_of_bijective isOpen_univ (mem_univ p) hc.contDiffOn
  have hd1 : HasDerivAt (fun r : ℝ => f (8 * (r - 1))) (deriv f (8 * (p.1 - 1)) * 8) p.1 := by
    have hd : HasDerivAt f (deriv f (8 * (p.1 - 1))) (8 * (p.1 - 1)) :=
      ((hf.differentiable (by simp)) _).hasDerivAt
    have hlin : HasDerivAt (fun r : ℝ => 8 * (r - 1)) 8 p.1 := by
      simpa using ((hasDerivAt_id p.1).sub_const 1).const_mul 8
    exact hd.comp p.1 hlin
  have hD := hd1.hasFDerivAt.prodMap p (hasFDerivAt_id p.2)
  rw [hD.fderiv]
  have hne : deriv f (8 * (p.1 - 1)) * 8 ≠ 0 := by
    have := hfd (8 * (p.1 - 1))
    positivity
  refine (Prod.map_bijective (f := ⇑((1 : ℝ →L[ℝ] ℝ).smulRight (deriv f (8 * (p.1 - 1)) * 8)))
    (g := ⇑(ContinuousLinearMap.id ℝ ℝ))).mpr ⟨⟨fun v w hvw => ?_, fun w => ?_⟩,
      Function.bijective_id⟩
  · have h1 : v * (deriv f (8 * (p.1 - 1)) * 8) = w * (deriv f (8 * (p.1 - 1)) * 8) := by
      simpa using hvw
    exact mul_right_cancel₀ hne h1
  · refine ⟨w / (deriv f (8 * (p.1 - 1)) * 8), ?_⟩
    have h2 : w / (deriv f (8 * (p.1 - 1)) * 8) * (deriv f (8 * (p.1 - 1)) * 8) = w :=
      div_mul_cancel₀ w hne
    simpa using h2

/-- The rim coordinate change `(θ, (r, s)) ↦ (θ, (f (8 (r - 1)), s))` is a local
diffeomorphism. -/
theorem isLocalDiffeomorphAt_rimCoord {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfd : ∀ x, 0 < deriv f x) (p : Circle × (ℝ × ℝ)) :
    IsLocalDiffeomorphAt ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ∞
      (Prod.map id (Prod.map (fun r : ℝ => f (8 * (r - 1))) id)) p :=
  ((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph p.1).prodMap
    (isLocalDiffeomorphAt_rimRadial hf hfd p.2)

end GC.GraphManifold.Assembly
