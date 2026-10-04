import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspBoundaryApplications
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspMetricEquivalence

/-!
# Two-sided bound for the differential of the actual collar height (BSA01 (i), `|dz|` part)

For a cusp embedding `e : CuspEmbedding W g K δ X`, let `ζ = z ∘ e⁻¹` be the actual height on the
open collar `e(T² × [0, 100))` (`ζ y = (invFunOn e.toFun cuspDomain y).2.val 0`, which is `C¹` up
to the boundary by `CuspEmbedding.contMDiffOn_height_invFunOn`). At every collar point, boundary
included:

* `CuspEmbedding.mfderiv_height_invFunOn_mfderiv`: `dζ (De v) = dz(v)`;
* `CuspEmbedding.abs_mfderiv_height_invFunOn_le`: `|dζ(u)| ≤ (1 - δ)^{-1/2} |u|_g` for every `u`;
* `CuspEmbedding.exists_mfderiv_height_invFunOn_eq_one`: `dζ(u) = 1` for some `u` with
  `|u|_g² ≤ 1 + δ` (the image of the vertical unit vector).

Together: `(1 + δ)^{-1/2} ≤ ‖dζ‖_g ≤ (1 - δ)^{-1/2}` as a dual norm (blueprint 207B, BSA01.a,
`B:7600–7604`; review of the boundary-geometry design, §6). The `1.01` form for `δ ≤ 1/100` is
`CuspEmbedding.height_invFunOn_differential_bounds_of_le_hundredth`. Only the order-zero part of the
metric error is used.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {δ : ℝ} {X : Set W.Carrier}

/-- The height of the cusp half space has differential `v ↦ v.2 0`. -/
theorem hasMFDerivAt_cusp_height (p : CuspHalfSpace) :
    HasMFDerivAt halfCollarModel 𝓘(ℝ, ℝ) (fun q : CuspHalfSpace => q.2.val 0) p
      ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toContinuousLinearMap.comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
          (EuclideanSpace ℝ (Fin 1)))) :=
  (hasMFDerivAt_halfSpaceOneCoordinate p.2).comp p (hasMFDerivAt_snd p)

/-- The actual collar height `ζ = z ∘ e⁻¹` satisfies `dζ (De v) = dz(v)` on the cusp domain. -/
theorem CuspEmbedding.mfderiv_height_invFunOn_mfderiv (e : CuspEmbedding W g K δ X)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (v : TangentSpace halfCollarModel p) :
    mfderiv W.model 𝓘(ℝ, ℝ) (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
      (mfderiv halfCollarModel W.model e.toFun p v) = v.2 0 := by
  set ζ : W.Carrier → ℝ := fun y => (invFunOn e.toFun cuspDomain y).2.val 0 with hζ
  have hep : e.toFun p ∈ e.toFun '' cuspDomain := mem_image_of_mem _ hp
  have hζd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) ζ (e.toFun p) :=
    (e.contMDiffOn_height_invFunOn.contMDiffAt
      (e.isOpen_image_cuspDomain.mem_nhds hep)).mdifferentiableAt one_ne_zero
  have hed : MDifferentiableAt halfCollarModel W.model e.toFun p :=
    (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hp)).mdifferentiableAt (by simp)
  have heq : (ζ ∘ e.toFun) =ᶠ[𝓝 p] (fun q : CuspHalfSpace => q.2.val 0) := by
    filter_upwards [isOpen_cuspDomain.mem_nhds hp] with q hq
    simp only [comp_apply, hζ]
    rw [e.injOn_cuspDomain.leftInvOn_invFunOn hq]
  have hL : (mfderiv W.model 𝓘(ℝ, ℝ) ζ (e.toFun p)).comp
      (mfderiv halfCollarModel W.model e.toFun p) =
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toContinuousLinearMap.comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
          (EuclideanSpace ℝ (Fin 1))) := by
    rw [← mfderiv_comp p hζd hed, heq.mfderiv_eq]
    exact (hasMFDerivAt_cusp_height p).mfderiv
  have h := congrArg (fun L : TangentSpace halfCollarModel p →L[ℝ] ℝ => L v) hL
  exact h

/-- Upper half of BSA01.a's height-differential bound: `|dζ(u)| ≤ (1 - δ)^{-1/2} |u|_g` at every
point of the open collar (boundary included). -/
theorem CuspEmbedding.abs_mfderiv_height_invFunOn_le (e : CuspEmbedding W g K δ X) (hδ : δ < 1)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (u : TangentSpace W.model (e.toFun p)) :
    |(show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) (fun y => (invFunOn e.toFun cuspDomain y).2.val 0)
        (e.toFun p) u)| ≤
      (Real.sqrt (1 - δ))⁻¹ * Real.sqrt (g.inner (e.toFun p) u u) := by
  obtain ⟨M, hM⟩ := e.isInvertible_mfderiv hp
  have hu : mfderiv halfCollarModel W.model e.toFun p (M.symm u) = u := by
    rw [← hM]
    exact M.apply_symm_apply u
  rw [← hu, e.mfderiv_height_invFunOn_mfderiv hp]
  exact e.abs_height_deriv_le hδ hp _

/-- Lower half of BSA01.a's height-differential bound: the image `u` of the vertical unit vector
has `dζ(u) = 1` and `|u|_g² ≤ 1 + δ`, so `‖dζ‖_g ≥ (1 + δ)^{-1/2}`. -/
theorem CuspEmbedding.exists_mfderiv_height_invFunOn_eq_one (e : CuspEmbedding W g K δ X)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) :
    ∃ u : TangentSpace W.model (e.toFun p),
      (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) (fun y => (invFunOn e.toFun cuspDomain y).2.val 0)
        (e.toFun p) u) = 1 ∧ g.inner (e.toFun p) u u ≤ 1 + δ := by
  let v : TangentSpace halfCollarModel p := ((0, 0), EuclideanSpace.single 0 1)
  have hv1 : v.1 = 0 := rfl
  have hv2 : v.2 0 = 1 := by simp [v]
  refine ⟨mfderiv halfCollarModel W.model e.toFun p v, ?_, ?_⟩
  · rw [e.mfderiv_height_invFunOn_mfderiv hp, hv2]
  · have h := e.pullback_inner_vertical_le hp v hv1
    rwa [hv2, one_pow, mul_one] at h

/-- BSA01.a, height-differential part, with the blueprint's numbers: for `δ ≤ 1/100`,
`1/1.01 ≤ ‖dζ‖_g ≤ 1.01` on the whole open collar. -/
theorem CuspEmbedding.height_invFunOn_differential_bounds_of_le_hundredth
    (e : CuspEmbedding W g K δ X) (hδ : δ ≤ 1 / 100) {p : CuspHalfSpace} (hp : p ∈ cuspDomain) :
    (∀ u : TangentSpace W.model (e.toFun p),
      |(show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) (fun y => (invFunOn e.toFun cuspDomain y).2.val 0)
        (e.toFun p) u)| ≤
        1.01 * Real.sqrt (g.inner (e.toFun p) u u)) ∧
    ∃ u : TangentSpace W.model (e.toFun p),
      (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) (fun y => (invFunOn e.toFun cuspDomain y).2.val 0)
        (e.toFun p) u) = 1 ∧ Real.sqrt (g.inner (e.toFun p) u u) ≤ 1.01 := by
  refine ⟨fun u => ?_, ?_⟩
  · obtain ⟨M, hM⟩ := e.isInvertible_mfderiv hp
    have hu : mfderiv halfCollarModel W.model e.toFun p (M.symm u) = u := by
      rw [← hM]
      exact M.apply_symm_apply u
    rw [← hu, e.mfderiv_height_invFunOn_mfderiv hp]
    exact e.abs_height_deriv_le_of_le_hundredth hδ hp _
  · obtain ⟨u, hu1, hu2⟩ := e.exists_mfderiv_height_invFunOn_eq_one hp
    refine ⟨u, hu1, ?_⟩
    calc Real.sqrt (g.inner (e.toFun p) u u) ≤ Real.sqrt ((1.01 : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (hu2.trans (by nlinarith))
      _ = 1.01 := Real.sqrt_sq (by norm_num)

end DifferentialGeometry.Geometry.Collapse
