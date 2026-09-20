import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.LocalComparison
import DifferentialGeometry.Topology.LoopSpace.AffineLift
import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import DifferentialGeometry.Analysis.Sobolev.Interpolation.BoundaryRecovery
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BoundedDerivative
import DifferentialGeometry.Geometry.Metric.Pullback.Continuity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Integrability
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WitnessCongruence

noncomputable section

open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_disk_competitors_of_eventually_target_valued_recovery
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F} (hΦ : Continuous Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    (γ : freeLoop M) (f : ℕ → ℂ → F) (K : ℕ → ℝ≥0)
    (hf : ∀ n, LipschitzWith (K n) (f n))
    (hfK : ∀ᶠ n in atTop, MapsTo (f n) (Metric.closedBall (0 : ℂ) 1) (range Φ))
    (ψ : ℕ → CircleDeg1Lift) (hψ : ∀ n, Continuous (ψ n))
    (htrace : ∀ n t, f n (circleMap 0 1 (2 * Real.pi * t)) =
      Φ (γ ((ψ n t : ℝ) : loopCircle)))
    {I : ℝ} (henergy : Tendsto (fun n => ∫ z in Metric.closedBall (0 : ℂ) 1,
      (pullbackMetricCoefficients g r (f n z) (fderiv ℝ (f n) z 1) (fderiv ℝ (f n) z 1) +
        pullbackMetricCoefficients g r (f n z)
          (fderiv ℝ (f n) z Complex.I) (fderiv ℝ (f n) z Complex.I)) / 2) atTop (𝓝 I)) :
    ∃ (N : ℕ) (w : ℕ → C(closedDisk, M)) (τ : ℕ → C(loopCircle, loopCircle)),
      (∀ k, τ k = affineCircleMap (ψ (k + N)) (hψ (k + N)) (ψ (k + N)).map_add_one) ∧
      (∀ k (t : ℝ), τ k (t : loopCircle) = ((ψ (k + N) t : ℝ) : loopCircle)) ∧
      (∀ k z, w k z = r (f (k + N) z)) ∧
      (∀ k z, Φ (w k z) = f (k + N) z) ∧
      (∀ k, IsWeaklyMonotoneOnce (τ k)) ∧
      (∀ k, diskTrace (w k) = γ.comp (τ k)) ∧
      (∀ k, w k ∈ weaklyMonotoneDiskCompetitors g γ) ∧
      Tendsto (fun k => riemannianDiskEnergy g (w k)) atTop (𝓝 I) ∧
      sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ) ≤ I := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfK
  let τ (k : ℕ) := affineCircleMap (ψ (k + N)) (hψ (k + N)) (ψ (k + N)).map_add_one
  have hτ (k : ℕ) : IsWeaklyMonotoneOnce (τ k) :=
    ⟨ψ (k + N), hψ (k + N), fun _ => rfl,
      Or.inl ⟨(ψ (k + N)).monotone, (ψ (k + N)).map_add_one⟩⟩
  have htr (k : ℕ) (θ : loopCircle) : f (k + N) (diskBoundary θ) = Φ (γ (τ k θ)) := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    simpa only [τ, affineCircleMap_coe, diskBoundary_coe, circleMap_zero,
      Complex.ofReal_one, one_mul] using htrace (k + N) t
  obtain ⟨C, hC⟩ := exists_riemannian_lipschitz_disk_of_lipschitz_retraction
    g hΦ hU hr hΦU hleft
  have hproduce (k : ℕ) := hC (f (k + N)) (K (k + N)) (hf (k + N))
    (hN (k + N) (Nat.le_add_left _ _)) γ (τ k) (htr k)
  choose w hwr hΦw hwLip hwTrace hwInt hfInt hwEnergy using hproduce
  have hwmem (k : ℕ) : w k ∈ weaklyMonotoneDiskCompetitors g γ :=
    ⟨⟨τ k, hτ k, hwTrace k⟩, C * K (k + N), hwLip k⟩
  have hlim : Tendsto (fun k => riemannianDiskEnergy g (w k)) atTop (𝓝 I) := by
    have h := henergy.comp (tendsto_add_atTop_nat N)
    have heq (k : ℕ) : riemannianDiskEnergy g (w k) =
        ∫ z in Metric.closedBall (0 : ℂ) 1,
          (pullbackMetricCoefficients g r (f (k + N) z)
              (fderiv ℝ (f (k + N)) z 1) (fderiv ℝ (f (k + N)) z 1) +
            pullbackMetricCoefficients g r (f (k + N) z)
              (fderiv ℝ (f (k + N)) z Complex.I) (fderiv ℝ (f (k + N)) z Complex.I)) / 2 :=
      hwEnergy k
    apply h.congr'
    exact Eventually.of_forall fun k => (heq k).symm
  have hbound : BddBelow ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
      weaklyMonotoneDiskCompetitors g γ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨v, _, rfl⟩
    exact riemannianDiskEnergy_nonneg g v
  have hInf (k : ℕ) : sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
      weaklyMonotoneDiskCompetitors g γ) ≤ riemannianDiskEnergy g (w k) :=
    csInf_le hbound (mem_image_of_mem _ (hwmem k))
  exact ⟨N, w, τ, fun _ => rfl, fun _ _ => rfl, hwr, hΦw, hτ, hwTrace, hwmem, hlim,
    ge_of_tendsto hlim (Eventually.of_forall hInf)⟩

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Metric Filter MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_weakly_monotone_disks_tendsto_energy_of_continuous_disk
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    (γ : freeLoop M) {KΓ : ℝ≥0}
    (hΓ : LipschitzWith KΓ (fun t : ℝ => Φ (γ (t : loopCircle))))
    (q : C(closedDisk, M))
    (hq : ContDiffOn ℝ 1 (Φ ∘ diskExtension q) (ball (0 : ℂ) 1))
    (hE : IntegrableOn (fun z => ‖fderiv ℝ (Φ ∘ diskExtension q) z‖ ^ 2) (ball (0 : ℂ) 1))
    (τ : C(loopCircle, loopCircle)) (hτ : IsWeaklyMonotoneOnce τ)
    (hτ0 : τ 0 = 0) (hτ1 : τ ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle))
    (hτ2 : τ ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle))
    (htrace : diskTrace q = γ.comp τ) :
    ∃ (qn : ℕ → C(closedDisk, M)) (τn : ℕ → C(loopCircle, loopCircle)),
      (∀ n, qn n ∈ weaklyMonotoneDiskCompetitors g γ) ∧
      (∀ n, IsWeaklyMonotoneOnce (τn n) ∧ τn n 0 = 0 ∧
        τn n ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle) ∧
        τn n ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle)) ∧
      (∀ n, diskTrace (qn n) = γ.comp (τn n)) ∧
      TendstoUniformly (fun n (z : closedDisk) => Φ (qn n z)) (fun z => Φ (q z)) atTop ∧
      TendstoUniformly (fun n t => τn n t) τ atTop ∧
      Tendsto (fun n => riemannianDiskEnergy g (qn n)) atTop (𝓝 (riemannianDiskEnergy g q)) ∧
      sInf ((fun u : C(closedDisk, M) => riemannianDiskEnergy g u) ''
        weaklyMonotoneDiskCompetitors g γ) ≤ riemannianDiskEnergy g q := by
  let f : ℂ → F := Φ ∘ diskExtension q
  have hfc : Continuous f :=
    hΦ.continuous.comp (q.continuous.comp diskRetraction_lipschitz.continuous)
  have hfK : MapsTo f (closedBall (0 : ℂ) 1) (range Φ) := fun z _ => mem_range_self _
  have hK : IsCompact (range Φ) := isCompact_range hΦ.continuous
  have hret : ContDiffOn ℝ ∞ (Φ ∘ r) U := (hΦ.comp_contMDiffOn hr).contDiffOn
  have hretK : MapsTo (Φ ∘ r) U (range Φ) := fun y _ => mem_range_self _
  have hretfix : ∀ y ∈ range Φ, (Φ ∘ r) y = y := by
    rintro y ⟨x, rfl⟩
    exact congrArg Φ (hleft x)
  obtain ⟨V, T, L, hV, hKV, _, _, hT, _, hL0, hL, hTK, hfix⟩ :=
    exists_contDiff_retraction_extension_fderiv_bound hK hU hΦU (Φ ∘ r) hret hretK hretfix
  obtain ⟨ψ₀, hψc, hψlift, hψmono, hψper, hψ0, hψ1, hψ2⟩ :=
    hτ.exists_monotone_lift_of_three_fixed_points (by norm_num : (0 : ℝ) < 1 / 3)
      (by norm_num : (1 / 3 : ℝ) < 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1)
      hτ0 hτ1 hτ2
  let ψ : CircleDeg1Lift := ⟨⟨ψ₀, hψmono⟩, hψper⟩
  let Γ : ℝ → F := fun t => Φ (γ (t : loopCircle))
  have hΓper : Function.Periodic Γ 1 := by
    intro t
    dsimp only [Γ]
    rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]
  have htr (s : ℝ) : f (circleMap 0 1 (2 * Real.pi * s)) = Γ (ψ s) := by
    have hc : circleMap 0 1 (2 * Real.pi * s) = (diskBoundary (s : loopCircle) : ℂ) := by
      simp only [circleMap_zero, diskBoundary_coe, Complex.ofReal_one, one_mul]
    change Φ (diskExtension q _) = Φ (γ (ψ s : loopCircle))
    rw [hc, diskExtension_coe]
    change Φ (q (diskBoundary (s : loopCircle))) = Φ (γ (ψ₀ s : loopCircle))
    rw [hψlift]
    exact congrArg Φ (congrArg (fun u : C(loopCircle, M) => u (s : loopCircle)) htrace)
  obtain ⟨fn, ψn, a, hfnLip, hψnLip, _, hmarks, hψnconv, hfnTrace, _, _, _,
      hfnK, hfnUniform, hfnEnergy⟩ :=
    exists_periodic_boundary_energy_recovery hK hV hKV f hfc.continuousOn hq hfK hE
      Γ hΓ hΓper ψ hψc htr T
      (hT.differentiable (by simp)) (LT := Real.toNNReal L)
      (fun y => (hL y).trans (Real.le_coe_toNNReal L)) hfix hTK
  let A := pullbackMetricCoefficients g r
  have hA : ContinuousOn A (range Φ) :=
    (continuousOn_pullback_metric_coefficients_of_contMDiffOn_one g hU
      (hr.of_le (by simp))).mono hΦU
  have hvalue : (∫ z in closedBall (0 : ℂ) 1,
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2) =
        riemannianDiskEnergy g q := by
    apply integral_congr_ae
    filter_upwards [ae_disk_interior] with z hz
    have hd : DifferentiableAt ℝ f z :=
      (hq.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt one_ne_zero
    have hdr : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) r (f z) :=
      (hr.contMDiffAt (hU.mem_nhds (hΦU (mem_range_self (diskExtension q z))))).mdifferentiableAt
        (by simp)
    have heq : r ∘ f = diskExtension q := by
      funext x
      exact hleft (diskExtension q x)
    have hchain := mfderiv_comp (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, F))
      (I'' := 𝓘(ℝ, E)) z hdr hd.mdifferentiableAt
    rw [mfderiv_eq_fderiv, heq] at hchain
    dsimp only [A, diskMapEnergyDensity, diskMapPartial, pullbackMetricCoefficients_apply]
    rw [hchain]
    have hp : r (f z) = diskExtension q z := hleft (diskExtension q z)
    rw [hp]
    rfl
  have henergy := hfnEnergy A hA
  rw [hvalue] at henergy
  choose Kn hKn using hfnLip
  obtain ⟨N, qn, τn, _, hτnLift, _, hΦqn, hτn, hqnTrace, hqn, hqnEnergy, hInf⟩ :=
    exists_disk_competitors_of_eventually_target_valued_recovery g hΦ.continuous hU
      (hr.of_le (by simp)) hΦU hleft γ fn Kn hKn hfnK ψn
      (fun n => (hψnLip n).continuous) hfnTrace henergy
  have hqUniform : TendstoUniformly (fun n (z : closedDisk) => Φ (qn n z))
      (fun z => Φ (q z)) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have he := (Metric.tendstoUniformlyOn_iff.mp hfnUniform) ε hε
    filter_upwards [(tendsto_add_atTop_nat N).eventually he] with n hn z
    have h := hn z z.property
    simpa only [hΦqn, f, Function.comp_apply, diskExtension_coe] using h
  have hτUniform : TendstoUniformly (fun n t => τn n t) τ atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have he := (Metric.tendstoUniformly_iff.mp hψnconv) ε hε
    filter_upwards [(tendsto_add_atTop_nat N).eventually he] with n hn θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    rw [hτnLift, ← hψlift]
    have hdist := loopCircle_projection_lipschitz.dist_le_mul (ψ t) (ψn (n + N) t)
    have hdist' : dist (ψ t : loopCircle) (ψn (n + N) t : loopCircle) ≤
        dist (ψ t) (ψn (n + N) t) := by
      simpa only [NNReal.coe_one, one_mul] using hdist
    exact hdist'.trans_lt (hn t)
  refine ⟨qn, τn, hqn, ?_, hqnTrace, hqUniform, hτUniform, hqnEnergy, hInf⟩
  intro n
  refine ⟨hτn n, ?_, ?_, ?_⟩
  · have h := hτnLift n 0
    rw [(hmarks (n + N)).1] at h
    change τn n ((0 : ℝ) : loopCircle) = (ψ₀ 0 : loopCircle) at h
    simpa only [hψ0, AddCircle.coe_zero] using h
  · rw [hτnLift n (1 / 3), (hmarks (n + N)).2.1]
    change (ψ₀ (1 / 3) : loopCircle) = ((1 / 3 : ℝ) : loopCircle)
    rw [hψ1]
  · rw [hτnLift n (2 / 3), (hmarks (n + N)).2.2]
    change (ψ₀ (2 / 3) : loopCircle) = ((2 / 3 : ℝ) : loopCircle)
    rw [hψ2]

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Metric Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_weakly_monotone_disks_tendsto_energy_of_weak_representative
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    (γ : freeLoop M) {KΓ : ℝ≥0}
    (hΓ : LipschitzWith KΓ (fun t : ℝ => Φ (γ (t : loopCircle))))
    (w : V → F) (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (ball (0 : V) 1))
    (v : V → F) (hvc : ContDiffOn ℝ 1 v (ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (ball (0 : V) 1)] w)
    (hvK : MapsTo v (ball (0 : V) 1) (range Φ))
    (q : C(closedDisk, M))
    (hq : ∀ z ∈ ball (0 : ℂ) 1, diskExtension q z = r (v (Complex.orthonormalBasisOneI.repr z)))
    (τ : C(loopCircle, loopCircle)) (hτ : IsWeaklyMonotoneOnce τ)
    (hτ0 : τ 0 = 0) (hτ1 : τ ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle))
    (hτ2 : τ ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle))
    (htrace : diskTrace q = γ.comp τ) :
    ∃ (qn : ℕ → C(closedDisk, M)) (τn : ℕ → C(loopCircle, loopCircle)),
      (∀ n, qn n ∈ weaklyMonotoneDiskCompetitors g γ) ∧
      (∀ n, IsWeaklyMonotoneOnce (τn n) ∧ τn n 0 = 0 ∧
        τn n ((1 / 3 : ℝ) : loopCircle) = ((1 / 3 : ℝ) : loopCircle) ∧
        τn n ((2 / 3 : ℝ) : loopCircle) = ((2 / 3 : ℝ) : loopCircle)) ∧
      (∀ n, diskTrace (qn n) = γ.comp (τn n)) ∧
      TendstoUniformly (fun n (z : closedDisk) => Φ (qn n z)) (fun z => Φ (q z)) atTop ∧
      TendstoUniformly (fun n t => τn n t) τ atTop ∧
      Tendsto (fun n => riemannianDiskEnergy g (qn n)) atTop (𝓝 (riemannianDiskEnergy g q)) ∧
      sInf ((fun u : C(closedDisk, M) => riemannianDiskEnergy g u) ''
        weaklyMonotoneDiskCompetitors g γ) ≤ riemannianDiskEnergy g q := by
  let e := Complex.orthonormalBasisOneI.repr
  let f : ℂ → F := Φ ∘ diskExtension q
  have hemap : MapsTo e (ball (0 : ℂ) 1) (ball (0 : V) 1) := by
    intro z hz
    simpa only [mem_ball, dist_zero_right, e.norm_map] using hz
  have heq : EqOn f (v ∘ e) (ball (0 : ℂ) 1) := by
    intro z hz
    change Φ (diskExtension q z) = v (e z)
    rw [hq z hz]
    obtain ⟨p, hp⟩ := hvK (hemap hz)
    rw [← hp, hleft]
  have hvce : ContDiffOn ℝ 1 (v ∘ e) (ball (0 : ℂ) 1) :=
    hvc.comp e.contDiff.contDiffOn hemap
  have hfc : ContDiffOn ℝ 1 f (ball (0 : ℂ) 1) := hvce.congr heq
  let hv (i : ι) : DeGiorgi.MemW1pWitness 2 (fun x => v x i) (ball (0 : V) 1) :=
    (hw i).congr (hvw.symm.mono fun x hx => congrArg (fun z : F => z i) hx)
  have hi :=
    Analysis.Sobolev.Euclidean.integrableOn_norm_fderiv_comp_complex_repr_sq_of_contDiffOn_of_memW12
    hv hvc
  have hfi : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) (ball (0 : ℂ) 1) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
    have hgerm : f =ᶠ[𝓝 z] v ∘ e := by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      exact heq hy
    rw [hgerm.fderiv_eq]
  exact exists_weakly_monotone_disks_tendsto_energy_of_continuous_disk
    g hΦ hU hr hΦU hleft γ hΓ q hfc hfi τ hτ hτ0 hτ1 hτ2 htrace

end DifferentialGeometry.Geometry

end
