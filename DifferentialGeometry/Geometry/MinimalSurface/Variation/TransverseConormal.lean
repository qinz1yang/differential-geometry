import DifferentialGeometry.Geometry.MinimalSurface.Variation.ImmersedDiskDivergence
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

set_option autoImplicit false
noncomputable section
open Set Filter _root_.Manifold DifferentialGeometry
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem uniqueMDiffOn_conormal_halfdisk {r : ℝ} (hr : 0 < r) :
    UniqueMDiffOn 𝓘(ℝ, ℂ) (closedHalfDisk 0 r) := by
  apply UniqueDiffOn.uniqueMDiffOn
  apply uniqueDiffOn_convex
    ((convex_halfSpace_im_ge 0).inter (convex_closedBall (0 : ℂ) r))
  have hinside : (openHalfDisk 0 r : Set ℂ) ⊆ interior (closedHalfDisk 0 r) := by
    intro z hz
    apply mem_interior_iff_mem_nhds.mpr
    exact mem_of_superset ((openHalfDisk 0 r).isOpen.mem_nhds hz)
      (fun q hq => ⟨(show 0 < q.im from hq.1).le, Metric.ball_subset_closedBall hq.2⟩)
  refine ⟨(r / 2 : ℂ) * Complex.I, hinside ?_⟩
  constructor
  · change 0 < ((r / 2 : ℂ) * Complex.I).im
    simp only [Complex.mul_I_im, Complex.div_ofNat_re, Complex.ofReal_re]
    positivity
  · rw [Metric.mem_ball, dist_eq_norm, Complex.ofReal_zero, sub_zero]
    simp only [norm_mul, Complex.norm_I, mul_one, norm_div,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
    rw [abs_of_pos hr]
    linarith

omit [FiniteDimensional ℝ E] in
/-- For the already chosen paired charts, original transversality prevents
cancellation of the actual inward conormals at their common seam center.
The closed-half differentials and their common tangent are derived from the
smooth chart buffer and the literal common real parameter. -/
theorem paired_halfdisk_inward_conormals_ne_zero_of_transverse
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {S : Set ℂ} {a b : ℂ}
    (hS : IsOpen S)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U S)
    (heq : U a = U b)
    (hia : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U a))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U b))
    (htrans : Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U a).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U b))))
    (hdim : Module.finrank ℝ E = 3)
    {r : ℝ} (hr : 0 < r) (ψ₁ ψ₂ : OpenPartialHomeomorph ℂ ℂ)
    (hcenter₁ : ψ₁ 0 = a) (hcenter₂ : ψ₂ 0 = b)
    (hbuffer : Metric.closedBall (0 : ℂ) (2 * r) ⊆ ψ₁.source ∩ ψ₂.source)
    (htarget₁ : ψ₁.target ⊆ S) (htarget₂ : ψ₂.target ⊆ S)
    (hψ₁sm : ContDiffOn ℝ ∞ ψ₁ ψ₁.source)
    (hψ₂sm : ContDiffOn ℝ ∞ ψ₂ ψ₂.source)
    (hψ₁bij : ∀ z ∈ ψ₁.source, Function.Bijective (fderiv ℝ ψ₁ z))
    (hψ₂bij : ∀ z ∈ ψ₂.source, Function.Bijective (fderiv ℝ ψ₂ z))
    (hseam : ∀ t ∈ Icc (-2 * r) (2 * r), U (ψ₁ (t : ℂ)) = U (ψ₂ (t : ℂ))) :
    let F₁ : ℂ → M := U ∘ ψ₁
    let F₂ : ℂ → M := U ∘ ψ₂
    let H : Set ℂ := closedHalfDisk 0 r
    let D₁ : ℂ →L[ℝ] E := mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ H 0
    let D₂ : ℂ →L[ℝ] E := mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ H 0
    let ν₁ : TangentSpace 𝓘(ℝ, E) (F₁ 0) := inwardConormalWithin g F₁ H 0
    let ν₂ : TangentSpace 𝓘(ℝ, E) (F₁ 0) :=
      tangentSpaceCast 𝓘(ℝ, E) (F₂ 0) (F₁ 0) (inwardConormalWithin g F₂ H 0)
    F₁ 0 = F₂ 0 ∧
      D₁ 1 = D₂ 1 ∧ D₁ 1 ≠ 0 ∧
      Function.Injective D₁ ∧ Function.Injective D₂ ∧
      Function.Surjective (D₁.coprod (-D₂)) ∧
      ν₁ + ν₂ ≠ 0 ∧ 0 < g.inner (F₁ 0) (ν₁ + ν₂) (ν₁ + ν₂) := by
  have : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite
  let F₁ : ℂ → M := U ∘ ψ₁
  let F₂ : ℂ → M := U ∘ ψ₂
  let H : Set ℂ := closedHalfDisk 0 r
  let D₁ : ℂ →L[ℝ] E := mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ H 0
  let D₂ : ℂ →L[ℝ] E := mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ H 0
  let ν₁ : TangentSpace 𝓘(ℝ, E) (F₁ 0) := inwardConormalWithin g F₁ H 0
  let ν₂ : TangentSpace 𝓘(ℝ, E) (F₁ 0) :=
    tangentSpaceCast 𝓘(ℝ, E) (F₂ 0) (F₁ 0) (inwardConormalWithin g F₂ H 0)
  change F₁ 0 = F₂ 0 ∧ D₁ 1 = D₂ 1 ∧ D₁ 1 ≠ 0 ∧
    Function.Injective D₁ ∧ Function.Injective D₂ ∧
    Function.Surjective (D₁.coprod (-D₂)) ∧
    ν₁ + ν₂ ≠ 0 ∧ 0 < g.inner (F₁ 0) (ν₁ + ν₂) (ν₁ + ν₂)
  have hbase : F₁ 0 = F₂ 0 := by
    dsimp only [F₁, F₂, Function.comp_apply]
    rw [hcenter₁, hcenter₂]
    exact heq
  have hzero : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (2 * r) := by
    rw [Metric.mem_closedBall, dist_self]
    linarith only [hr]
  have hz₁ : (0 : ℂ) ∈ ψ₁.source := (hbuffer hzero).1
  have hz₂ : (0 : ℂ) ∈ ψ₂.source := (hbuffer hzero).2
  have hH0 : (0 : ℂ) ∈ H := by
    constructor
    · exact (le_rfl : (0 : ℝ) ≤ 0)
    · simpa only [Metric.mem_closedBall, Complex.ofReal_zero, dist_self] using hr.le
  have huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℂ) H 0 :=
    uniqueMDiffOn_conormal_halfdisk hr 0 hH0
  have hdψ₁ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₁ 0 :=
    (hψ₁sm.contMDiffOn.contMDiffAt (ψ₁.open_source.mem_nhds hz₁)).mdifferentiableAt
      (by simp)
  have hdψ₂ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₂ 0 :=
    (hψ₂sm.contMDiffOn.contMDiffAt (ψ₂.open_source.mem_nhds hz₂)).mdifferentiableAt
      (by simp)
  have hdU₁ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (ψ₁ 0) :=
    (hU.contMDiffAt (hS.mem_nhds (htarget₁ (ψ₁.map_source hz₁)))).mdifferentiableAt
      (by simp)
  have hdU₂ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (ψ₂ 0) :=
    (hU.contMDiffAt (hS.mem_nhds (htarget₂ (ψ₂.map_source hz₂)))).mdifferentiableAt
      (by simp)
  have hdF₁ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ 0 := hdU₁.comp 0 hdψ₁
  have hdF₂ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ 0 := hdU₂.comp 0 hdψ₂
  have hwithin₁ : D₁ = (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ 0) :=
    mfderivWithin_eq_mfderiv huniq hdF₁
  have hwithin₂ : D₂ = (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ 0) :=
    mfderivWithin_eq_mfderiv huniq hdF₂
  let A : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U a
  let B : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U b
  let P : ℂ →L[ℝ] ℂ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₁ 0
  let Q : ℂ →L[ℝ] ℂ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₂ 0
  have hP : Function.Bijective P := by
    dsimp only [P]
    rw [mfderiv_eq_fderiv]
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (ψ₁ 0)).symm.bijective.comp
      ((hψ₁bij 0 hz₁).comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℂ)).bijective)
  have hQ : Function.Bijective Q := by
    dsimp only [Q]
    rw [mfderiv_eq_fderiv]
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (ψ₂ 0)).symm.bijective.comp
      ((hψ₂bij 0 hz₂).comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℂ)).bijective)
  have hchain₁ : D₁ = A.comp P := by
    refine hwithin₁.trans ((mfderiv_comp 0 hdU₁ hdψ₁).trans ?_)
    exact congrArg (fun L : ℂ →L[ℝ] E => L.comp P)
      (mfderiv_congr_point (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) (f := U) hcenter₁)
  have hchain₂ : D₂ = B.comp Q := by
    refine hwithin₂.trans ((mfderiv_comp 0 hdU₂ hdψ₂).trans ?_)
    exact congrArg (fun L : ℂ →L[ℝ] E => L.comp Q)
      (mfderiv_congr_point (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) (f := U) hcenter₂)
  have hi₁ : Function.Injective D₁ := by
    rw [hchain₁]
    exact hia.comp hP.1
  have hi₂ : Function.Injective D₂ := by
    rw [hchain₂]
    exact hib.comp hQ.1
  have hsurj : Function.Surjective (D₁.coprod (-D₂)) := by
    intro v
    obtain ⟨⟨s, t⟩, hst⟩ := htrans v
    obtain ⟨x, hx⟩ := hP.2 s
    obtain ⟨y, hy⟩ := hQ.2 t
    refine ⟨(x, y), ?_⟩
    change D₁ x + -(D₂ y) = v
    change A s + -(B t) = v at hst
    rw [hchain₁, hchain₂]
    change A (P x) + -(B (Q y)) = v
    rw [hx, hy]
    exact hst
  have hsame : D₁ 1 = D₂ 1 := by
    have hevent : (fun t : ℝ => F₁ (t : ℂ)) =ᶠ[𝓝 (0 : ℝ)]
        (fun t : ℝ => F₂ (t : ℂ)) := by
      filter_upwards [Icc_mem_nhds (by linarith only [hr] : -2 * r < 0)
        (by linarith only [hr] : 0 < 2 * r)] with t ht
      exact hseam t ht
    have hline : HasFDerivAt (fun t : ℝ => (t : ℂ)) Complex.ofRealCLM 0 :=
      Complex.ofRealCLM.hasFDerivAt
    have hdl := hline.hasMFDerivAt
    have he := hevent.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))
    have hc₁ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₁ (t : ℂ)) 0
        ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ 0).comp Complex.ofRealCLM) :=
      HasMFDerivAt.comp (f := fun t : ℝ => (t : ℂ)) (g := F₁)
        0 hdF₁.hasMFDerivAt hdl
    have hc₂ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₂ (t : ℂ)) 0
        ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ 0).comp Complex.ofRealCLM) :=
      HasMFDerivAt.comp (f := fun t : ℝ => (t : ℂ)) (g := F₂)
        0 hdF₂.hasMFDerivAt hdl
    have hv := congrArg (fun L : ℝ →L[ℝ] E => L 1) he
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₁ (t : ℂ)) 0) 1 =
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₂ (t : ℂ)) 0) 1 at hv
    have hv₁ := congrArg (fun L : ℝ →L[ℝ] E => L 1) hc₁.mfderiv
    have hv₂ := congrArg (fun L : ℝ →L[ℝ] E => L 1) hc₂.mfderiv
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₁ (t : ℂ)) 0) 1 =
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ 0) (1 : ℂ) at hv₁
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => F₂ (t : ℂ)) 0) 1 =
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ 0) (1 : ℂ) at hv₂
    have hfull := hv₁.symm.trans (hv.trans hv₂)
    change @Eq E
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₁ 0) (1 : ℂ))
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F₂ 0) (1 : ℂ)) at hfull
    exact (congrArg (fun L : ℂ →L[ℝ] E => L (1 : ℂ)) hwithin₁).trans
      (hfull.trans (congrArg (fun L : ℂ →L[ℝ] E => L (1 : ℂ)) hwithin₂).symm)
  have hT₁ : D₁ 1 ≠ 0 := by
    intro h
    exact one_ne_zero (hi₁ (h.trans D₁.map_zero.symm))
  have hT₂ : D₂ 1 ≠ 0 := by
    rw [← hsame]
    exact hT₁
  have hunit₂ := (inwardConormalWithin_geometry g (U := F₂) (S := H) (z := 0) hi₂).1
  have hν₂ : (ν₂ : E) ≠ 0 := by
    intro h
    change (inwardConormalWithin g F₂ H 0 : E) = 0 at h
    rw [h, map_zero] at hunit₂
    exact zero_ne_one hunit₂
  have hsum : ν₁ + ν₂ ≠ 0 := by
    intro hcancel
    let R : Submodule ℝ E := LinearMap.range D₁.toLinearMap
    have hR₁ (z : ℂ) : D₁ z ∈ R := ⟨z, rfl⟩
    have hν₁R : (ν₁ : E) ∈ R := by
      change (Real.sqrt (gramWithin g F₁ H 0 1 1) * densityWithin g F₁ H 0)⁻¹ •
        (gramWithin g F₁ H 0 1 1 • D₁ Complex.I -
          gramWithin g F₁ H 0 1 Complex.I • D₁ 1) ∈ R
      exact R.smul_mem _ (R.sub_mem (R.smul_mem _ (hR₁ Complex.I))
        (R.smul_mem _ (hR₁ 1)))
    have hν₂R : (ν₂ : E) ∈ R := by
      have hc : (ν₁ : E) + ν₂ ∈ R := hcancel.symm ▸ R.zero_mem
      have hcancelE : (ν₁ : E) + (ν₂ : E) - (ν₁ : E) = (ν₂ : E) :=
        add_sub_cancel_left (ν₁ : E) (ν₂ : E)
      exact hcancelE ▸ R.sub_mem hc hν₁R
    let a₂ : ℝ := gramWithin g F₂ H 0 1 1
    let b₂ : ℝ := gramWithin g F₂ H 0 1 Complex.I
    let c₂ : ℝ := (Real.sqrt a₂ * densityWithin g F₂ H 0)⁻¹
    have ha₂ : 0 < a₂ := g.pos (F₂ 0) (D₂ 1) hT₂
    have hform : (ν₂ : E) = c₂ • (a₂ • D₂ Complex.I - b₂ • D₂ 1) := rfl
    -- Unit length rules out a zero normalization coefficient; no private
    -- density-positivity theorem or extra positivity premise is used.
    have hc₂ : c₂ ≠ 0 := by
      intro h
      have hz : c₂ • (a₂ • D₂ Complex.I - b₂ • D₂ 1 : E) = (0 : E) := by
        rw [h]
        exact zero_smul ℝ _
      exact hν₂ (hform.trans hz)
    have hT₂R : D₂ 1 ∈ R := hsame ▸ hR₁ 1
    have hN₂R : D₂ Complex.I ∈ R := by
      apply (R.smul_mem_iff ha₂.ne').mp
      rw [hform] at hν₂R
      have hdiff := (R.smul_mem_iff hc₂).mp hν₂R
      simpa only [sub_add_cancel] using R.add_mem hdiff (R.smul_mem b₂ hT₂R)
    have hR₂ (z : ℂ) : D₂ z ∈ R := by
      have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
        simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
      rw [hz, map_add, map_smul, map_smul]
      exact R.add_mem (R.smul_mem _ hT₂R) (R.smul_mem _ hN₂R)
    have honto : Function.Surjective D₁ := by
      intro v
      obtain ⟨⟨x, y⟩, hxy⟩ := hsurj v
      change D₁ x + -(D₂ y) = v at hxy
      have hmem : v ∈ R := hxy ▸ R.add_mem (hR₁ x) (R.neg_mem (hR₂ y))
      exact hmem
    have hdimle := LinearMap.finrank_le_finrank_of_surjective
      (f := D₁.toLinearMap) honto
    have hcomplex : Module.finrank ℝ ℂ = 2 := by
      rw [Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin]
    rw [hdim, hcomplex] at hdimle
    norm_num at hdimle
  exact ⟨hbase, hsame, hT₁, hi₁, hi₂, hsurj, hsum, g.pos (F₁ 0) (ν₁ + ν₂) hsum⟩

end DifferentialGeometry.Geometry
