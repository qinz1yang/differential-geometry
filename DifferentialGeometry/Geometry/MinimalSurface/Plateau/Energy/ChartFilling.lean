import DifferentialGeometry.Geometry.MinimalSurface.Plateau.HomogeneousRegularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Replacement.DiskFilling
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz
import DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.HomogeneousChart
import DifferentialGeometry.Topology.MetricSpace.LipschitzExtension
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Trace.CircleAnchor

section

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem diskMapEnergyDensity_comp_le_of_mfderiv_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {ψ : V → M} {f : ℂ → V} {z : ℂ}
    {A : ℝ} (hψ : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) ψ (f z))
    (hf : DifferentiableAt ℝ f z)
    (hA : ∀ ξ : V, g.inner (ψ (f z))
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ψ (f z) ξ)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ψ (f z) ξ) ≤ A * ‖ξ‖ ^ 2) :
    diskMapEnergyDensity g (ψ ∘ f) z ≤
      A * ((‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2) := by
  have hchain : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (ψ ∘ f) z =
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ψ (f z)).comp (fderiv ℝ f z) := by
    rw [mfderiv_comp z hψ hf.mdifferentiableAt, mfderiv_eq_fderiv]
    rfl
  have hdir (ξ : ℂ) : diskMapPartial (ψ ∘ f) z ξ =
      mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ψ (f z) (fderiv ℝ f z ξ) := by
    unfold diskMapPartial
    rw [hchain]
    rfl
  have h1 := hA (fderiv ℝ f z 1)
  have hI := hA (fderiv ℝ f z Complex.I)
  unfold diskMapEnergyDensity
  simp only [Function.comp_apply, hdir]
  nlinarith

theorem diskMapEnergyDensity_comp_chart_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ψ : OpenPartialHomeomorph plateauCoordinateSpace M)
    (hsource : plateauClosedCube ⊆ ψ.source)
    (hψ : ContMDiffOn 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ∞ ψ ψ.source)
    {A : ℝ} (hA : ∀ y ∈ plateauOpenCube, ∀ ξ : plateauCoordinateSpace,
      g.inner (ψ y)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y ξ)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y ξ) ≤ A * ‖ξ‖ ^ 2)
    {f : ℂ → plateauCoordinateSpace} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hz : f z ∈ plateauOpenCube) :
    diskMapEnergyDensity g (ψ ∘ f) z ≤
      A * ((‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2) := by
  have hzsource : f z ∈ ψ.source := hsource (fun i => (hz i).le)
  apply diskMapEnergyDensity_comp_le_of_mfderiv_bound g
    ((hψ.contMDiffAt (ψ.open_source.mem_nhds hzsource)).mdifferentiableAt (by simp)) hf
  exact hA (f z) hz

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

private theorem closedBall_half_subset_plateauOpenCube :
    closedBall (0 : plateauCoordinateSpace) (1 / 2) ⊆ plateauOpenCube := by
  intro x hx i
  have hn : ‖x‖ ≤ (1 / 2 : ℝ) := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  exact hi.trans_lt (hn.trans_lt (by norm_num))

private theorem integrable_plane_column_energy_of_lipschitz
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : ℂ → F} {C : ℝ≥0} (hf : LipschitzWith C f) :
    IntegrableOn (fun z => (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2)
      (closedBall (0 : ℂ) 1) := by
  borelize F
  let : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  have hm (ξ : ℂ) : MemLp (fun z => fderiv ℝ f z ξ) 2
      (volume.restrict (closedBall (0 : ℂ) 1)) :=
    MemLp.of_bound (measurable_fderiv_apply_const ℝ f ξ).aestronglyMeasurable
      ((C : ℝ) * ‖ξ‖) (Eventually.of_forall fun z =>
        ((fderiv ℝ f z).le_opNorm ξ).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg ξ)))
  exact ((hm 1).norm.integrable_sq.add (hm Complex.I).norm.integrable_sq).div_const 2

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_disk_filling_in_chart_of_boundary_norm_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ψ : OpenPartialHomeomorph plateauCoordinateSpace M)
    (hsource : plateauClosedCube ⊆ ψ.source)
    (hψ : ContMDiffOn 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ∞ ψ ψ.source)
    {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ y ∈ plateauOpenCube, ∀ ξ : plateauCoordinateSpace,
      g.inner (ψ y)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y ξ)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y ξ) ≤ A * ‖ξ‖ ^ 2)
    {u : ℂ → plateauCoordinateSpace} {K : ℝ≥0} (hu : LipschitzWith K u)
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → ‖u z‖ ≤ 1 / 2) :
    ∃ w : C(closedDisk, M),
      (∃ C : ℝ≥0, ∀ z z', riemannianEDistOf g (w z) (w z') ≤ (C : ℝ≥0∞) * edist z z') ∧
      (∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → w z = ψ (u z)) ∧
      (∀ z : closedDisk, ‖(z : ℂ)‖ ≤ 1 / 2 → w z = ψ 0) ∧
      IsCompact (ψ '' closedBall (0 : plateauCoordinateSpace) (1 / 2)) ∧
      MapsTo w univ (ψ '' closedBall (0 : plateauCoordinateSpace) (1 / 2)) ∧
      (∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension w) z) ≤
        (2 * Real.pi) * A * ((∫ t in Icc (0 : ℝ) 1,
          ‖u (circleMap 0 1 (2 * Real.pi * t - Real.pi))‖ ^ 2) +
          (1 / 4) * ∫ t in Icc (0 : ℝ) 1,
            ‖deriv (fun s => u (circleMap 0 1 (2 * Real.pi * s - Real.pi))) t‖ ^ 2) := by
  have huK : ∀ z : ℂ, ‖z‖ = 1 → u z ∈ closedBall (0 : plateauCoordinateSpace) (1 / 2) := by
    intro z hz
    simpa only [mem_closedBall, dist_zero_right] using hboundary z hz
  have hp : (0 : plateauCoordinateSpace) ∈ closedBall 0 (1 / 2) :=
    mem_closedBall_self (by norm_num)
  have hseg : ∀ z : ℂ, ‖z‖ = 1 → segment ℝ (0 : plateauCoordinateSpace) (u z) ⊆
      closedBall 0 (1 / 2) :=
    fun z hz => (convex_closedBall 0 (1 / 2)).segment_subset hp (huK z hz)
  obtain ⟨f, ⟨Cf, hf⟩, houter, hinner, htarget, henergy⟩ :=
    Analysis.exists_lipschitz_retracted_disk_filling_energy_le hu 0 hp huK hseg
      (id : plateauCoordinateSpace → plateauCoordinateSpace)
      differentiable_id (L := 1) (by intro x; simp) (fun x hx => hx) (fun _ _ => rfl)
  have hmax : max (1 : ℝ) (((2 * Real.pi) ^ 2 * (1 / 2))⁻¹) = 1 := by
    apply max_eq_left
    apply inv_le_one_of_one_le₀
    nlinarith [Real.pi_gt_three]
  simp only [hmax, one_pow, mul_one, sub_zero] at henergy
  have hsub : closedBall (0 : plateauCoordinateSpace) (1 / 2) ⊆ ψ.source :=
    fun x hx => hsource (fun i => (closedBall_half_subset_plateauOpenCube hx i).le)
  have hψLip (x) (hx : x ∈ closedBall (0 : plateauCoordinateSpace) (1 / 2))
      (y) (hy : y ∈ closedBall (0 : plateauCoordinateSpace) (1 / 2)) :
      riemannianEDistOf g (ψ x) (ψ y) ≤ (Real.nnabs (Real.sqrt A) : ℝ≥0∞) * edist x y := by
    apply riemannian_edist_le_on_convex_source g ψ.open_source (hψ.of_le (by simp)) hsub
      (convex_closedBall 0 (1 / 2)) ?_ hx hy
    intro q hq ξ
    have hbound := hA q (closedBall_half_subset_plateauOpenCube hq) ξ
    have hs := Real.sqrt_le_sqrt hbound
    simpa only [Real.sqrt_mul hA0, Real.sqrt_sq_eq_abs, abs_norm,
      Real.coe_nnabs, abs_of_nonneg (Real.sqrt_nonneg A)] using hs
  let w : C(closedDisk, M) := ⟨fun z => ψ (f z),
    (hψ.continuousOn.comp_continuous (hf.continuous.comp continuous_subtype_val)
      (fun z => hsub (htarget z.property)))⟩
  have hwLip : ∀ z z' : closedDisk,
      riemannianEDistOf g (w z) (w z') ≤
        ((Real.nnabs (Real.sqrt A) * Cf : ℝ≥0) : ℝ≥0∞) * edist z z' := by
    intro z z'
    exact (hψLip (f z) (htarget z.property) (f z') (htarget z'.property)).trans
      ((mul_le_mul_right (hf z z') (Real.nnabs (Real.sqrt A) : ℝ≥0∞)).trans_eq (by
        rw [ENNReal.coe_mul, mul_assoc]
        rfl))
  have hE (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      diskExtension w =ᶠ[𝓝 z] (ψ ∘ f) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    change diskExtension w y = ψ (f y)
    exact diskExtension_coe w ⟨y, ball_subset_closedBall hy⟩
  refine ⟨w, ⟨_, hwLip⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    change ψ (f z) = ψ (u z)
    rw [houter z hz.ge]
  · intro z hz
    change ψ (f z) = ψ 0
    rw [hinner z hz]
  · exact (isCompact_closedBall (0 : plateauCoordinateSpace) (1 / 2)).image_of_continuousOn
      (hψ.continuousOn.mono hsub)
  · intro z _
    exact mem_image_of_mem ψ (htarget z.property)
  · have hi := integrable_diskMapEnergyDensity g hwLip
    have hiE := integrable_plane_column_energy_of_lipschitz hf
    have hle : (∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension w) z) ≤
        A * ∫ z in closedBall (0 : ℂ) 1,
          (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2 := by
      rw [← integral_const_mul]
      apply integral_mono_ae hi (hiE.const_mul A)
      filter_upwards [ae_disk_interior, ae_restrict_of_ae hf.ae_differentiableAt] with z hz hd
      have heq := hE z hz
      have hed : diskMapEnergyDensity g (diskExtension w) z =
          diskMapEnergyDensity g (ψ ∘ f) z := by
        unfold diskMapEnergyDensity diskMapPartial
        rw [heq.mfderiv_eq, heq.eq_of_nhds]
        rfl
      rw [hed]
      exact diskMapEnergyDensity_comp_chart_le g ψ hsource hψ hA hd
        (closedBall_half_subset_plateauOpenCube (htarget (ball_subset_closedBall hz)))
    exact hle.trans ((mul_le_mul_of_nonneg_left henergy hA0).trans_eq (by ring))

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Filter Set MeasureTheory Metric Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_disk_filling_in_chart_of_intrinsic_boundary_energy_lt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ψ : OpenPartialHomeomorph plateauCoordinateSpace M)
    (hsource : plateauClosedCube ⊆ ψ.source)
    (hψ : ContMDiffOn 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ∞ ψ ψ.source)
    (hψinv : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, plateauCoordinateSpace) ∞ ψ.symm ψ.target)
    {m A : ℝ} (hm : 0 < m) (hA : 0 ≤ A)
    (hlower : ∀ y ∈ plateauOpenCube, ∀ ξ : plateauCoordinateSpace,
      m * ‖ξ‖ ^ 2 ≤ g.inner (ψ y)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y ξ)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y ξ))
    (hupper : ∀ y ∈ plateauOpenCube, ∀ ξ : plateauCoordinateSpace,
      g.inner (ψ y)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y ξ)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y ξ) ≤ A * ‖ξ‖ ^ 2)
    {u : ℂ → M} {K : ℝ≥0}
    (hu : ∀ z z', riemannianEDistOf g (u z) (u z') ≤ (K : ℝ≥0∞) * edist z z')
    (hanchor : u (circleMap 0 1 (-Real.pi)) = ψ 0)
    (henergy : IntegrableOn (fun t => (riemannianCurveSpeed g
      (fun s => u (circleMap 0 1 (2 * Real.pi * s - Real.pi))) t) ^ 2) (Icc 0 1))
    (hsmall : (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g
      (fun s => u (circleMap 0 1 (2 * Real.pi * s - Real.pi))) t) ^ 2) < m / 4) :
    ∃ w : C(closedDisk, M),
      (∃ C : ℝ≥0, ∀ z z', riemannianEDistOf g (w z) (w z') ≤ (C : ℝ≥0∞) * edist z z') ∧
      (∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → w z = u z) ∧
      (∀ z : closedDisk, ‖(z : ℂ)‖ ≤ 1 / 2 → w z = ψ 0) ∧
      IsCompact (ψ '' closedBall (0 : plateauCoordinateSpace) (1 / 2)) ∧
      MapsTo w univ (ψ '' closedBall (0 : plateauCoordinateSpace) (1 / 2)) ∧
      (∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension w) z) ≤
        (5 * Real.pi / 2) * (A / m) * ∫ t in Icc (0 : ℝ) 1,
          (riemannianCurveSpeed g
            (fun s => u (circleMap 0 1 (2 * Real.pi * s - Real.pi))) t) ^ 2 := by
  let c : ℝ → ℂ := fun t => circleMap 0 1 (2 * Real.pi * t - Real.pi)
  let γ : ℝ → M := u ∘ c
  let P : ℝ≥0 := ⟨2 * Real.pi, by positivity⟩
  have hc : LipschitzWith P c := by
    have hd (t : ℝ) : HasDerivAt c
        ((2 * Real.pi) • (circleMap 0 1 (2 * Real.pi * t - Real.pi) * Complex.I)) t := by
      have ht : HasDerivAt (fun t : ℝ => 2 * Real.pi * t - Real.pi) (2 * Real.pi) t := by
        simpa using ((hasDerivAt_id t).const_mul (2 * Real.pi)).sub_const Real.pi
      exact (hasDerivAt_circleMap 0 1 (2 * Real.pi * t - Real.pi)).scomp t ht
    apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hd t).differentiableAt)
    intro t
    change ‖deriv c t‖ ≤ 2 * Real.pi
    rw [(hd t).deriv]
    simp [abs_of_pos Real.pi_pos]
  have hγ : ∀ s t, riemannianEDistOf g (γ s) (γ t) ≤
      ((K * P : ℝ≥0) : ℝ≥0∞) * edist s t := by
    intro s t
    exact (hu (c s) (c t)).trans ((mul_le_mul_right (hc s t) (K : ℝ≥0∞)).trans_eq (by
      rw [ENNReal.coe_mul, mul_assoc]))
  have hstart : γ 0 = ψ 0 := by
    simpa only [γ, c, Function.comp_apply, mul_zero, zero_sub] using hanchor
  obtain ⟨hmaps, _, _, hcoordenergy⟩ := chart_curve_energy_le_of_intrinsic_energy_lt
    g ψ hsource hψ hψinv hm (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      hlower hγ hstart henergy (by
        norm_num only [show ((1 / 2 : ℝ) ^ 2) = 1 / 4 by norm_num]
        change (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g γ t) ^ 2) < m * (1 / 4)
        simpa only [γ, c, Function.comp_def, div_eq_mul_inv, one_mul] using hsmall)
  have hcover (z : ℂ) (hz : ‖z‖ = 1) : ∃ t ∈ Icc (0 : ℝ) 1, c t = z := by
    have hmem : z ∈ range (circleMap 0 1) := by
      rw [range_circleMap, mem_sphere, dist_zero_right]
      simpa using hz
    rw [← (periodic_circleMap 0 1).image_Ioc Real.two_pi_pos (-Real.pi)] at hmem
    obtain ⟨θ, hθ, hθz⟩ := hmem
    refine ⟨(θ + Real.pi) / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith [hθ.1]) (by positivity)
    · exact (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr (by linarith [hθ.2])
    · have heq : 2 * Real.pi * ((θ + Real.pi) / (2 * Real.pi)) - Real.pi = θ := by
        field_simp
        ring
      simpa only [c, heq] using hθz
  have hboundary : MapsTo u (sphere (0 : ℂ) 1) ψ.target := by
    intro z hz
    obtain ⟨t, ht, htz⟩ := hcover z (by simpa only [mem_sphere, dist_zero_right] using hz)
    obtain ⟨y, hy, hyt⟩ := hmaps ht
    have hs : y ∈ ψ.source := hsource (fun i => by
      have hi : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
      have hn : ‖y‖ < (1 / 2 : ℝ) := by simpa only [mem_ball, dist_zero_right] using hy
      exact hi.trans (by linarith))
    have htarg : γ t ∈ ψ.target := hyt ▸ ψ.map_source hs
    simpa only [γ, Function.comp_apply, htz] using htarg
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_comp_of_contMDiffOn_of_isCompact
    g ψ.open_target (hψinv.of_le (by simp)) hu (isCompact_sphere (0 : ℂ) 1) hboundary
  obtain ⟨v, Kv, hv, hveq⟩ := hL.exists_lipschitz_extension
  have hvc : (fun t => v (c t)) = ψ.symm ∘ γ := by
    funext t
    exact (hveq (by simp only [mem_sphere, dist_zero_right, c, norm_circleMap_zero,
      abs_one])).symm
  have hvanchor : v (circleMap 0 1 (-Real.pi)) = 0 := by
    have he := congrFun hvc 0
    have h0 : (0 : plateauCoordinateSpace) ∈ ψ.source := hsource (fun _ => by simp)
    simpa only [c, mul_zero, zero_sub, Function.comp_apply, hstart, ψ.left_inv h0] using he
  have hvsmall : (∫ t in Icc (0 : ℝ) 1, ‖deriv (fun s => v (c s)) t‖ ^ 2) < 1 / 4 := by
    rw [hvc]
    have hlt := hcoordenergy.trans_lt hsmall
    nlinarith
  have hvnorm (z : ℂ) (hz : ‖z‖ = 1) : ‖v z‖ ≤ 1 / 2 := by
    have h := Analysis.norm_sq_le_boundary_energy_of_circle_anchor hv 0 hvanchor hz
    simp only [sub_zero] at h
    nlinarith [norm_nonneg (v z)]
  obtain ⟨w, hwLip, hwtrace, hwinner, hwcompact, hwtarget, hwenergy⟩ :=
    exists_disk_filling_in_chart_of_boundary_norm_le g ψ hsource hψ hA hupper hv hvnorm
  refine ⟨w, hwLip, ?_, hwinner, hwcompact, hwtarget, ?_⟩
  · intro z hz
    rw [hwtrace z hz, ← hveq (by simpa only [mem_sphere, dist_zero_right] using hz)]
    exact ψ.right_inv (hboundary (by simpa only [mem_sphere, dist_zero_right] using hz))
  · have hgap := Analysis.integral_norm_sq_le_boundary_energy_of_circle_anchor hv 0 hvanchor
    simp only [sub_zero] at hgap
    have hscaled : (5 * Real.pi / 2) * A *
        (∫ t in Icc (0 : ℝ) 1, ‖deriv (fun s => v (c s)) t‖ ^ 2) ≤
          (5 * Real.pi / 2) * (A / m) *
            ∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g γ t) ^ 2 := by
      have hcoord : (∫ t in Icc (0 : ℝ) 1, ‖deriv (fun s => v (c s)) t‖ ^ 2) ≤
          (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g γ t) ^ 2) / m := by
        rw [hvc]
        exact (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using hcoordenergy)
      apply (mul_le_mul_of_nonneg_left hcoord (mul_nonneg (by positivity) hA)).trans_eq
      ring
    apply (hwenergy.trans ?_).trans hscaled
    calc
      _ ≤ (2 * Real.pi) * A *
          ((∫ t in Icc (0 : ℝ) 1, ‖deriv (fun s => v (c s)) t‖ ^ 2) +
            (1 / 4) * ∫ t in Icc (0 : ℝ) 1, ‖deriv (fun s => v (c s)) t‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hgap le_rfl)
          (mul_nonneg (by positivity) hA)
      _ = _ := by ring

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Set MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_uniform_disk_filling_of_intrinsic_boundary_energy_lt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ (u : ℂ → M) (K : ℝ≥0),
        (∀ z z', riemannianEDistOf g (u z) (u z') ≤ (K : ℝ≥0∞) * edist z z') →
        IntegrableOn (fun t => (riemannianCurveSpeed g
          (fun s => u (circleMap 0 1 (2 * Real.pi * s - Real.pi))) t) ^ 2) (Icc 0 1) →
        (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g
          (fun s => u (circleMap 0 1 (2 * Real.pi * s - Real.pi))) t) ^ 2) < ε →
        ∃ w : C(closedDisk, M),
          (∃ L : ℝ≥0, ∀ z z',
            riemannianEDistOf g (w z) (w z') ≤ (L : ℝ≥0∞) * edist z z') ∧
          (∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → w z = u z) ∧
          (∀ z : closedDisk, ‖(z : ℂ)‖ ≤ 1 / 2 → w z = u (circleMap 0 1 (-Real.pi))) ∧
          ∃ S : Set M, IsCompact S ∧ MapsTo w univ S ∧
            (∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension w) z) ≤
              C * ∫ t in Icc (0 : ℝ) 1,
                (riemannianCurveSpeed g
                  (fun s => u (circleMap 0 1 (2 * Real.pi * s - Real.pi))) t) ^ 2 := by
  obtain ⟨m, A, hm, hmA, ψ, hψ, _⟩ := hregular
  have hA : 0 < A := hm.trans_le hmA
  refine ⟨m / 4, (5 * Real.pi / 2) * (A / m), by positivity, by positivity, ?_⟩
  intro u K hu henergy hsmall
  let p := u (circleMap 0 1 (-Real.pi))
  obtain ⟨w, hLip, htrace, hinner, hcompact, htarget, hbound⟩ :=
    exists_disk_filling_in_chart_of_intrinsic_boundary_energy_lt g (ψ p)
      (hψ p).1 (hψ p).2.2.1 (hψ p).2.2.2.1 hm hA.le
      (fun y hy ξ => ((hψ p).2.2.2.2 y hy ξ).1)
      (fun y hy ξ => ((hψ p).2.2.2.2 y hy ξ).2) hu (hψ p).2.1.symm henergy hsmall
  refine ⟨w, hLip, htrace, ?_, _, hcompact, htarget, hbound⟩
  intro z hz
  exact (hinner z hz).trans (hψ p).2.1

end DifferentialGeometry.Geometry

end

end
