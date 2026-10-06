import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.SeparatedMap

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

-- This is the local part of the singleton-fiber openness proof in
-- Topology.Maps.CoincidentGerms; no global local-injectivity premise is needed.
private theorem eventually_singleton_fiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] {f : X → Y} (hf : Continuous f)
    {x : X} {U : Set X} (hU : IsOpen U) (hxU : x ∈ U)
    (hinj : Set.InjOn f U) (hsingle : ∀ y, f y = f x → y = x) :
    ∀ᶠ z in 𝓝 x, ∀ y, f y = f z → y = z := by
  let V : Set Y := (f '' Uᶜ)ᶜ
  have hV : IsOpen V := (hf.isClosedMap _ hU.isClosed_compl).isOpen_compl
  have hxV : f x ∈ V := by
    rintro ⟨y, hy, hfy⟩
    exact hy ((hsingle y hfy).symm ▸ hxU)
  apply Filter.mem_of_superset ((hV.preimage hf).mem_nhds hxV)
  intro z hz y hfy
  have hzU : z ∈ U := by
    by_contra h
    exact hz ⟨z, h, rfl⟩
  have hyU : y ∈ U := by
    by_contra h
    exact hz ⟨y, h, hfy⟩
  exact hinj hyU hzU hfy

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

-- Reuses the open-subtype normal-form argument of EmbeddedSubdisk, with the
-- arbitrary open neighborhood supplied by the actual smooth extension.
private theorem exists_injective_regular_neighborhood
    {Q : ℂ → M} {N : Set ℂ} (hN : IsOpen N)
    (hQ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Q N)
    {a : ℂ} (ha : a ∈ N)
    (hrank : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q a)) :
    ∃ V : Set ℂ, IsOpen V ∧ a ∈ V ∧ V ⊆ N ∧
      Set.InjOn Q V ∧ ∀ z ∈ V, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) := by
  let S : TopologicalSpace.Opens ℂ := ⟨N, hN⟩
  let F : S → M := fun z => Q z
  let aS : S := ⟨a, ha⟩
  have hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F :=
    hQ.comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  have hDF : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F aS) := by
    change Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z : S => Q z) aS : ℂ →L[ℝ] E)
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact hrank
  have hImm := DifferentialGeometry.Topology.Manifold.isImmersionAt_of_injective_mfderiv
    (by simp : (∞ : ℕ∞ω) ≠ 0) hF aS hDF
  have hnormal (z : S) (hz : z ∈ hImm.domChart.source) :
      (hImm.codChart.extend 𝓘(ℝ, E)) (F z) =
        hImm.equiv ((hImm.domChart.extend 𝓘(ℝ, ℂ)) z, 0) := by
    have hz' : z ∈ (hImm.domChart.extend 𝓘(ℝ, ℂ)).source := by
      rwa [OpenPartialHomeomorph.extend_source]
    have hh := hImm.writtenInCharts ((hImm.domChart.extend 𝓘(ℝ, ℂ)).map_source hz')
    simpa only [Function.comp_apply,
      (hImm.domChart.extend 𝓘(ℝ, ℂ)).left_inv hz'] using hh
  have hinj : Set.InjOn F hImm.domChart.source := by
    intro z hz w hw hzw
    have hh := (hnormal z hz).symm.trans
      ((congrArg (hImm.codChart.extend 𝓘(ℝ, E)) hzw).trans (hnormal w hw))
    apply (hImm.domChart.extend 𝓘(ℝ, ℂ)).injOn
    · rwa [OpenPartialHomeomorph.extend_source]
    · rwa [OpenPartialHomeomorph.extend_source]
    · exact congrArg Prod.fst (hImm.equiv.injective hh)
  let T : Set S := hImm.domChart.source ∩ {z | IsImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F z}
  have hT : IsOpen T := hImm.domChart.open_source.inter IsOpen.isImmersionAt
  let V : Set ℂ := Subtype.val '' T
  have hV : IsOpen V := hN.isOpenMap_subtype_val T hT
  refine ⟨V, hV, ⟨aS, ⟨hImm.mem_domChart_source, hImm⟩, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨z, _, rfl⟩
    exact z.property
  · rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩ hzw
    exact congrArg (fun t : S => (t : ℂ)) (hinj hz.1 hw.1 hzw)
  · rintro _ ⟨z, hz, rfl⟩
    have hd := hz.2.mfderiv_injective (by simp : (∞ : ℕ∞ω) ≠ 0)
    change Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z : S => Q z) z : ℂ →L[ℝ] E) at hd
    rw [DifferentialGeometry.mfderiv_restrict_open] at hd
    exact hd

/-- Singleton boundary fibers and boundary rank persist on one collar of the
same closed disk. Nothing is asserted about collisions deeper in the disk. -/
theorem SmoothDiskExtension.exists_singleton_regular_collar [T2Space M]
    {q : C(closedDisk, M)} {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q)
    (hsingle : ∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → ∀ w, q w = q z → w = z)
    (hrank : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) :
    ∃ r₀ : ℝ, 0 ≤ r₀ ∧ r₀ < 1 ∧ ∀ z : closedDisk, r₀ < ‖(z : ℂ)‖ →
      (∀ w, q w = q z → w = z) ∧
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) := by
  obtain ⟨N, hN, hDN, hQN⟩ := hQ.2
  let P : Set closedDisk := {z | (∀ w, q w = q z → w = z) ∧
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)}
  let S : Set closedDisk := interior P
  have hb (x : closedDisk) (hx : ‖(x : ℂ)‖ = 1) : x ∈ S := by
    have hxrank := hrank x (by simpa only [Metric.mem_sphere, dist_zero_right] using hx)
    obtain ⟨V, hV, hxV, _, hQV, hVr⟩ :=
      exists_injective_regular_neighborhood hN hQN (hDN x.property) hxrank
    let U : Set closedDisk := (Subtype.val : closedDisk → ℂ) ⁻¹' V
    have hU : IsOpen U := hV.preimage continuous_subtype_val
    have hqU : Set.InjOn q U := by
      intro z hz w hw hzw
      apply Subtype.ext
      apply hQV hz hw
      exact (hQ.1 z).trans (hzw.trans (hQ.1 w).symm)
    have hsing := eventually_singleton_fiber q.continuous hU hxV hqU (hsingle x hx)
    have hmem : P ∈ 𝓝 x := by
      filter_upwards [hsing, hU.mem_nhds hxV] with z hz hzU
      exact ⟨hz, hVr z hzU⟩
    exact mem_interior_iff_mem_nhds.mpr hmem
  have hK : IsCompact Sᶜ := isOpen_interior.isClosed_compl.isCompact
  by_cases hne : (Sᶜ).Nonempty
  · obtain ⟨m, hm, hmax⟩ := hK.exists_isMaxOn hne
      (continuous_subtype_val.norm.continuousOn : ContinuousOn (fun z : closedDisk => ‖(z : ℂ)‖) Sᶜ)
    have hmle : ‖(m : ℂ)‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using m.property
    have hmlt : ‖(m : ℂ)‖ < 1 := lt_of_le_of_ne hmle (fun heq => hm (hb m heq))
    refine ⟨‖(m : ℂ)‖, norm_nonneg _, hmlt, ?_⟩
    intro z hz
    have hzS : z ∈ S := by
      by_contra h
      exact (not_lt_of_ge (hmax h)) hz
    exact (interior_subset : interior P ⊆ P) hzS
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    intro z _
    have hzS : z ∈ S := by
      by_contra h
      exact hne ⟨z, h⟩
    exact (interior_subset : interior P ⊆ P) hzS

/-- Every sufficiently large proper concentric restriction has a smooth
embedded boundary, retains the original metric and Morrey minimality, and
its entire boundary has singleton fibers in the original disk. The restricted
disk itself is not asserted to be embedded. -/
theorem IsMorreyDisk.exists_regular_concentric_restrictions [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hsingle : ∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → ∀ w, q w = q z → w = z)
    (hrank : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) :
    ∃ r₀ : ℝ, 0 ≤ r₀ ∧ r₀ < 1 ∧
      (∀ z : closedDisk, r₀ < ‖(z : ℂ)‖ →
        (∀ w, q w = q z → w = z) ∧
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) ∧
      ∀ r : ℝ, r₀ < r → r < 1 →
        IsSmoothEmbeddedLoop (E := E) (diskTrace (DifferentialGeometry.Geometry.affineSubdisk q 0 r)) ∧
        IsMorreyDisk g (diskTrace (DifferentialGeometry.Geometry.affineSubdisk q 0 r)) (DifferentialGeometry.Geometry.affineSubdisk q 0 r) ∧
        ∀ (θ : loopCircle) (w : closedDisk),
          q w = diskTrace (DifferentialGeometry.Geometry.affineSubdisk q 0 r) θ →
            (w : ℂ) = r • (diskBoundary θ : ℂ) := by
  obtain ⟨r₀, hr₀, hr₀1, hcollar⟩ := hQ.exists_singleton_regular_collar hsingle hrank
  obtain ⟨L, hLip⟩ := hQ.lipschitz g
  refine ⟨r₀, hr₀, hr₀1, hcollar, ?_⟩
  intro r hr₀r hr1
  have hr : 0 < r := hr₀.trans_lt hr₀r
  have hinside : ‖(0 : ℂ)‖ + r < 1 := by simpa using hr1
  let d : C(closedDisk, M) := DifferentialGeometry.Geometry.affineSubdisk q 0 r
  have hφ (z : ℂ) (hz : ‖z‖ ≤ 1) : r • z ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_of_le_one_right hr.le hz).trans hr1.le
  let p : loopCircle → closedDisk := fun θ =>
    ⟨r • (diskBoundary θ : ℂ), hφ _ (by exact (Circle.norm_coe _).le)⟩
  have hp (θ : loopCircle) : ‖(p θ : ℂ)‖ = r := by
    change ‖r • (diskBoundary θ : ℂ)‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      (show ‖(diskBoundary θ : ℂ)‖ = 1 from Circle.norm_coe _), mul_one]
  have htrace (θ : loopCircle) : diskTrace d θ = q (p θ) := by
    change diskExtension q (0 + r • (diskBoundary θ : ℂ)) = q (p θ)
    rw [zero_add]
    exact diskExtension_coe q (p θ)
  have hsingle' (θ : loopCircle) (w : closedDisk)
      (hw : q w = diskTrace d θ) : w = p θ :=
    (hcollar (p θ) (by rw [hp]; exact hr₀r)).1 w (hw.trans (htrace θ))
  have hbInj : Function.Injective (diskTrace d) := by
    intro θ η hθη
    have heq : p θ = p η := hsingle' η (p θ) ((htrace θ).symm.trans hθη)
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    have hh := congrArg (fun z : closedDisk => r⁻¹ • (z : ℂ)) heq
    change (diskBoundary θ : ℂ) = (diskBoundary η : ℂ)
    simpa only [p, inv_smul_smul₀ hr.ne'] using hh
  have hExt := hq.smoothDiskExtension_affineSubdisk 0 r hr.le hinside
  have hloop : IsSmoothEmbeddedLoop (E := E) (diskTrace d) := by
    refine ⟨hExt.smoothUpToBoundary.trace,
      ((diskTrace d).continuous.isClosedEmbedding hbInj).isEmbedding, ?_⟩
    intro t
    let β : ℝ → ℂ := fun s => circleMap 0 r (2 * Real.pi * s)
    have hβnorm (s : ℝ) : ‖β s‖ = r := by
      have heq : β s = r • (diskBoundary (s : loopCircle) : ℂ) := by
        rw [diskBoundary_coe]
        simp only [β, circleMap, zero_add, Complex.real_smul]
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
        (show ‖(diskBoundary (s : loopCircle) : ℂ)‖ = 1 from Circle.norm_coe _), mul_one]
    have hβin (s : ℝ) : β s ∈ Metric.ball (0 : ℂ) 1 := by
      simpa only [Metric.mem_ball, dist_zero_right, hβnorm] using hr1
    have hβ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β :=
      ((contDiff_circleMap 0 r).comp (contDiff_const.mul contDiff_id)).contMDiff
    have hθ : HasDerivAt (fun s : ℝ => 2 * Real.pi * s) (2 * Real.pi) t := by
      simpa only [mul_one, id_eq] using! (hasDerivAt_id t).const_mul (2 * Real.pi)
    have hβder : HasDerivAt β
        ((2 * Real.pi) • (circleMap 0 r (2 * Real.pi * t) * Complex.I)) t := by
      simpa only [Function.comp_def, β] using
        (hasDerivAt_circleMap 0 r (2 * Real.pi * t)).scomp t hθ
    have hβnonzero : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β t 1 ≠ 0 := by
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ β t 1 ≠ 0
      rw [fderiv_eq_smul_deriv, one_smul, hβder.deriv]
      apply smul_ne_zero (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      apply mul_ne_zero _ Complex.I_ne_zero
      simp only [circleMap, zero_add]
      exact mul_ne_zero (by exact_mod_cast hr.ne') (Complex.exp_ne_zero _)
    have htrace' : (fun s : ℝ => diskTrace d (s : loopCircle)) = diskExtension q ∘ β := by
      funext s
      change diskExtension q (0 + r • (diskBoundary (s : loopCircle) : ℂ)) = _
      rw [diskBoundary_coe]
      simp only [Function.comp_apply, β, circleMap, Complex.real_smul]
    have hUdiff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (β t) :=
      (hq.smoothInterior.contMDiffAt
        (Metric.isOpen_ball.mem_nhds (hβin t))).mdifferentiableAt (by simp)
    have hβdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β t :=
      hβ.mdifferentiable (by simp) t
    have hβcollar : r₀ < ‖β t‖ := by
      rw [hβnorm]
      exact hr₀r
    have hQr : Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q (β t) : ℂ →L[ℝ] E) :=
      (hcollar (⟨β t, Metric.ball_subset_closedBall (hβin t)⟩ : closedDisk) hβcollar).2
    have hUr : Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (β t) : ℂ →L[ℝ] E) := by
      have hder :
          (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q (β t)) =
            (show ℂ →L[ℝ] E from
              mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (β t)) := by
        ext v
        exact congrArg (fun L => L v)
          ((hQ.eventuallyEq_diskExtension (hβin t)).mfderiv_eq
            (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)))
      intro v w hvw
      apply hQr
      exact (congrArg (fun L : ℂ →L[ℝ] E => L v) hder).trans
        (hvw.trans (congrArg (fun L : ℂ →L[ℝ] E => L w) hder).symm)
    rw [htrace', mfderiv_comp t hUdiff hβdiff]
    intro hzero
    apply hβnonzero
    apply hUr
    let DQ : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (β t)
    let Dβ : ℝ →L[ℝ] ℂ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β t
    change DQ (Dβ 1) = DQ 0
    rw [map_zero]
    have hzeroE := congrArg
      (fun v : TangentSpace 𝓘(ℝ, E) (diskTrace d (t : loopCircle)) => (show E from v)) hzero
    change DQ (Dβ 1) = 0 at hzeroE
    exact hzeroE
  refine ⟨hloop, hq.affineSubdisk hLip 0 r hr hinside hloop.immersed, ?_⟩
  intro θ w hw
  exact congrArg (fun z : closedDisk => (z : ℂ)) (hsingle' θ w hw)

end DifferentialGeometry.Geometry
