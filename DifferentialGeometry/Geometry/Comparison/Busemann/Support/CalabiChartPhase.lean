import DifferentialGeometry.Geometry.Comparison.Busemann.Support.CalabiPhase
import DifferentialGeometry.Geometry.Comparison.Busemann.Support.CalabiExponential
import DifferentialGeometry.Geometry.Comparison.Busemann.Support.CompactSmoothExtension
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem gradient_calabiPhase_chart_ne_zero
    (g : SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞)
    (v : F) (hv : ‖v‖ = 1) (a : ℝ) (ha : a ≠ 0)
    {x : M} (hx : x ∈ Φ.source) :
    gradientFun (I := I) g (fun y => calabiPhase v a (Φ y)) x ≠ 0 := by
  have hlocal : IsLocalDiffeomorphAt I 𝓘(ℝ, F) ∞ Φ x :=
    ⟨Φ, hx, Set.eqOn_refl _ _⟩
  let L := hlocal.mfderivToContinuousLinearEquiv (by simp)
  have hpre : mfderiv I 𝓘(ℝ, F) Φ x (L.symm v) = v := L.apply_symm_apply v
  intro hzero
  have hpair := inner_gradientFun (I := I) g
    (fun y => calabiPhase v a (Φ y)) x (L.symm v)
  have hdiff : mfderiv I 𝓘(ℝ, ℝ) (fun y => calabiPhase v a (Φ y)) x (L.symm v) = 0 := by
    apply (NormedSpace.fromTangentSpace (calabiPhase v a (Φ x))).injective
    rw [map_zero]
    change mvfderiv (I := I) (fun y => calabiPhase v a (Φ y)) x (L.symm v) = 0
    simpa only [hzero, map_zero, zero_apply] using hpair.symm
  have hchain := mfderiv_comp x
    ((calabiPhase_contDiff v a).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    (Φ.mdifferentiableAt (by simp) hx)
  change mfderiv I 𝓘(ℝ, ℝ) (fun y => calabiPhase v a (Φ y)) x = _ at hchain
  rw [hchain, mfderiv_eq_fderiv] at hdiff
  change fderiv ℝ (calabiPhase v a) (Φ x)
    (mfderiv I 𝓘(ℝ, F) Φ x (L.symm v)) = 0 at hdiff
  rw [hpre, calabiPhase_fderiv_unit v hv a (Φ x)] at hdiff
  exact ha hdiff

theorem exists_calabi_boundary_perturbation_of_chart
    [I.Boundaryless] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
    [FiniteDimensional ℝ F]
    (g : SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞)
    (p : M) (hp : p ∈ Φ.source) (hcenter : Φ p = 0)
    (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall (0 : F) r ⊆ Φ.target)
    (v : F) (hv : ‖v‖ = 1) (f : M → ℝ) (hf : Continuous f)
    (hbelow : f (Φ.symm (r • v)) < f p) :
    ∃ K : Set M, IsCompact K ∧ p ∈ interior K ∧
      ∃ h : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ h ∧ h p = 0 ∧
        (∀ x ∈ K \ interior K, f x = f p → h x < 0) ∧
        ∀ x ∈ K, 0 < laplacian (I := I) (LeviCivita (I := I) g) g h x := by
  let K : Set M := Φ.symm '' Metric.closedBall (0 : F) r
  let B : Set M := Φ.symm '' Metric.ball (0 : F) r
  have hK : IsCompact K := (isCompact_closedBall (0 : F) r).image_of_continuousOn
    (Φ.contMDiffOn_invFun.continuousOn.mono hball)
  have hKsource : K ⊆ Φ.source := by
    rintro x ⟨y, hy, rfl⟩
    exact Φ.toPartialEquiv.map_target (hball hy)
  have hcoords (x : M) (hx : x ∈ K) : Φ x ∈ Metric.closedBall (0 : F) r := by
    obtain ⟨y, hy, hxy⟩ := hx
    have hright : Φ (Φ.symm y) = y := Φ.toPartialEquiv.right_inv (hball hy)
    rw [← hxy, hright]
    exact hy
  have hBopen : IsOpen B := Φ.toOpenPartialHomeomorph.isOpen_image_symm_of_subset_target
    Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hball)
  have hBK : B ⊆ K := image_mono Metric.ball_subset_closedBall
  have hBint : B ⊆ interior K := by
    intro x hx
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hBopen.mem_nhds hx) hBK)
  have hpB : p ∈ B := by
    refine ⟨0, ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_self] using hr
    · rw [← hcenter]
      exact Φ.toPartialEquiv.left_inv hp
  have hpK : p ∈ K := hBK hpB
  let S : Set M := (K \ interior K) ∩ {x | f x = f p}
  have hS : IsCompact S :=
    (hK.diff isOpen_interior).inter_right (isClosed_eq hf continuous_const)
  have hSsource : S ⊆ Φ.source := fun _ hx => hKsource hx.1.1
  let V : Set F := Φ '' S
  have hV : IsCompact V := hS.image_of_continuousOn
    (Φ.contMDiffOn_toFun.continuousOn.mono hSsource)
  have hsphere : V ⊆ Metric.sphere (0 : F) r := by
    rintro _ ⟨x, hx, rfl⟩
    have hle := hcoords x hx.1.1
    have hnot : Φ x ∉ Metric.ball (0 : F) r := by
      intro hlt
      have hxB : x ∈ B := ⟨Φ x, hlt, Φ.toPartialEquiv.left_inv (hSsource hx)⟩
      exact hx.1.2 (hBint hxB)
    exact Metric.mem_sphere.mpr (le_antisymm hle (not_lt.mp hnot))
  have hmissing : r • v ∉ V := by
    rintro ⟨x, hx, hcoord⟩
    have heq : x = Φ.symm (r • v) := by
      rw [← hcoord]
      exact (Φ.toPartialEquiv.left_inv (hSsource hx)).symm
    have hfx : f x = f p := hx.2
    rw [heq] at hfx
    exact (ne_of_lt hbelow) hfx
  obtain ⟨a, ha, hnegative⟩ := exists_calabiPhase_negative_on_sphere v hv r hr hV hsphere hmissing
  let ρ : M → ℝ := fun x => calabiPhase v a (Φ x)
  have hρ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ρ Φ.source :=
    (calabiPhase_contDiff v a).contMDiff.comp_contMDiffOn Φ.contMDiffOn_toFun
  obtain ⟨R, hR, hgerm⟩ := exists_contMDiff_extension_near_compact
    hK Φ.open_source hKsource hρ
  have hRzero : R p = 0 := by
    rw [(hgerm p hpK).eq_of_nhds]
    change calabiPhase v a (Φ p) = 0
    rw [hcenter, calabiPhase_zero]
  have hRgrad : ∀ x ∈ K, gradientFun (I := I) g R x ≠ 0 := by
    intro x hx
    have heq : gradientFun (I := I) g R x = gradientFun (I := I) g ρ x := by
      unfold gradientFun metricSharp mvfderiv
      rw [(hgerm x hx).mfderiv_eq, (hgerm x hx).eq_of_nhds]
    rw [heq]
    exact gradient_calabiPhase_chart_ne_zero (I := I) g Φ v hv a ha.ne' (hKsource hx)
  obtain ⟨lam, hlam, hsmooth, hlap⟩ := exists_positive_laplacian_exponential (I := I) g hR hK hRgrad
  refine ⟨K, hK, hBint hpB, fun x => Real.exp (lam * R x) - 1, hsmooth, ?_, ?_, hlap⟩
  · change Real.exp (lam * R p) - 1 = 0
    rw [hRzero, mul_zero, Real.exp_zero, sub_self]
  · intro x hx hfx
    have hneg : R x < 0 := by
      rw [(hgerm x hx.1).eq_of_nhds]
      exact hnegative (Φ x) (mem_image_of_mem Φ ⟨hx, hfx⟩)
    exact sub_neg.mpr (Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg hlam hneg))

end DifferentialGeometry.Geometry.Topology

end
