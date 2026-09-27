import DifferentialGeometry.Analysis.Sobolev.Euclidean.Poincare.Lipschitz
import DifferentialGeometry.Topology.EMetricSpace.FiniteDistanceLipschitz
import DifferentialGeometry.Geometry.Measure.Area.DiskExtensionSupport
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.ScalarProbe
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz
import Mathlib.Analysis.InnerProductSpace.Dual
import DifferentialGeometry.Geometry.Metric.Distance.CompactImage

section

set_option autoImplicit false
noncomputable section

open Bundle MeasureTheory Set Filter Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

private theorem norm_sq_complex_dual (L : ℂ →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = (L 1) ^ 2 + (L Complex.I) ^ 2 := by
  simpa [Complex.coe_orthonormalBasisOneI, Fin.sum_univ_two] using
    Complex.orthonormalBasisOneI.norm_dual L

private theorem ball_integral_eq_closedBall (f : ℂ → ℝ) :
    (∫ z in ball (0 : ℂ) 1, f z) = ∫ z in closedBall (0 : ℂ) 1, f z := by
  have hrestrict : (volume.restrict (closedBall (0 : ℂ) 1)).restrict (ball 0 1) =
      volume.restrict (closedBall (0 : ℂ) 1) :=
    Measure.restrict_eq_self_of_ae_mem ae_disk_interior
  rw [Measure.restrict_restrict measurableSet_ball,
    inter_eq_left.mpr ball_subset_closedBall] at hrestrict
  rw [hrestrict]

private theorem excess_sq_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 ≤ 2 * (max (a - b) 0) ^ 2 + 2 * b ^ 2 := by
  have hq : 0 ≤ max (a - b) 0 := le_max_right _ _
  have hsum : a ≤ max (a - b) 0 + b := by linarith [le_max_left (a - b) 0]
  have hsq := sq_le_sq₀ ha (add_nonneg hq hb) |>.mpr hsum
  nlinarith [sq_nonneg (max (a - b) 0 - b)]

private theorem scalar_disk_moment_bound
    {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ {f : ℂ → ℝ} {K : ℝ≥0}, LipschitzWith K f →
      HasCompactSupport f → tsupport f ⊆ ball 0 1 →
      (∫ z in ball (0 : ℂ) 1, f z ^ 2) ≤ C * ∫ z in ball (0 : ℂ) 1,
        ‖fderiv ℝ f z‖ ^ 2)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (d : C(closedDisk, ℝ)) {L : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (hd : ∀ z w, edist (d z) (d w) ≤ riemannianEDistOf g (u z) (u w))
    (hd0 : ∀ z, 0 ≤ d z) {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ θ : loopCircle, d (diskBoundary θ) ≤ R) :
    (∫ z in closedBall (0 : ℂ) 1, diskExtension d z ^ 2) ≤
      4 * C * (∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z) +
      2 * (R + 1) ^ 2 * volume.real (closedBall (0 : ℂ) 1) := by
  let q : ℂ → ℝ := fun z => max (diskExtension d z - (R + 1)) 0
  have hdLip : LipschitzWith L d := fun z w => (hd z w).trans (hu z w)
  have hde : LipschitzWith L (diskExtension d) := diskExtension_lipschitz hdLip
  have hqeq : q = fun z => max (dist (diskExtension d z) 0 - (R + 1)) 0 := by
    funext z
    change max (d (diskRetraction z) - (R + 1)) 0 =
      max (dist (d (diskRetraction z)) 0 - (R + 1)) 0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hd0 (diskRetraction z))]
  have hb : ∀ θ : loopCircle, dist (d (diskBoundary θ)) 0 ≤ R := by
    intro θ
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hd0 _)]
    exact hboundary θ
  have hqLip : LipschitzWith L q := by
    rw [hqeq]
    exact lipschitzWith_diskExtension_dist_excess d 0 hdLip (R + 1)
  have hqcomp : HasCompactSupport q := by
    rw [hqeq]
    exact hasCompactSupport_diskExtension_dist_excess d 0 (by linarith : R < R + 1) hb
  have hqsupport : tsupport q ⊆ ball (0 : ℂ) 1 := by
    rw [hqeq]
    exact tsupport_diskExtension_dist_excess_subset_ball d 0 (by linarith : R < R + 1) hb
  have hqc : ∀ z w, edist (q z) (q w) ≤
      riemannianEDistOf g (diskExtension u z) (diskExtension u w) := by
    intro z w
    have hmax : LipschitzWith 1 (fun s : ℝ => max (s - (R + 1)) 0) := by
      simpa using ((LipschitzWith.id.sub (LipschitzWith.const (R + 1))).max_const 0)
    exact (hmax (diskExtension d z) (diskExtension d w)).trans (by
      simp only [ENNReal.coe_one, one_mul]
      exact hd (diskRetraction z) (diskRetraction w))
  have hae := ae_fderiv_partials_sq_le_two_mul_diskMapEnergyDensity g
    (diskExtension_riemannian_lipschitz g hu) hqc
  have henergy : IntegrableOn (diskMapEnergyDensity g (diskExtension u))
      (closedBall (0 : ℂ) 1) := integrable_diskMapEnergyDensity g hu
  let : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  have hqm : MemLp (fderiv ℝ q) 2 (volume.restrict (closedBall (0 : ℂ) 1)) :=
    MemLp.of_bound
      ((measurable_fderiv ℝ q).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
      L (Eventually.of_forall fun z => norm_fderiv_le_of_lipschitz ℝ hqLip)
  have hgrad : (∫ z in closedBall (0 : ℂ) 1, ‖fderiv ℝ q z‖ ^ 2) ≤
      2 * ∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hqm.norm.integrable_sq) (henergy.const_mul 2)
    filter_upwards [ae_restrict_of_ae (s := closedBall (0 : ℂ) 1) hae] with z hz
    rwa [norm_sq_complex_dual]
  have hqp := hP hqLip hqcomp hqsupport
  rw [ball_integral_eq_closedBall, ball_integral_eq_closedBall] at hqp
  have hqintegrable : IntegrableOn (fun z => q z ^ 2) (closedBall (0 : ℂ) 1) :=
    ((hqLip.continuous.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1))
  have hdintegrable : IntegrableOn (fun z => diskExtension d z ^ 2)
      (closedBall (0 : ℂ) 1) :=
    ((hde.continuous.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1))
  have hp := integral_mono_ae hdintegrable
    ((hqintegrable.const_mul 2).add (integrable_const (2 * (R + 1) ^ 2)))
    (Eventually.of_forall fun z => excess_sq_bound (hd0 _) (by linarith : 0 ≤ R + 1))
  simp only [Pi.add_apply] at hp
  rw [integral_add (hqintegrable.const_mul 2) (integrable_const _),
    integral_const_mul, integral_const] at hp
  have hqp' := hqp.trans (mul_le_mul_of_nonneg_left hgrad hC)
  change _ ≤ 2 * (∫ z in closedBall (0 : ℂ) 1, q z ^ 2) +
    (volume.restrict (closedBall (0 : ℂ) 1)).real univ * (2 * (R + 1) ^ 2) at hp
  simp only [Measure.restrict_apply_univ, Measure.real] at hp ⊢
  nlinarith [hqp']

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_disk_distance_moment_constant :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
        (p : M) {R : ℝ} {L : ℝ≥0}, 0 ≤ R →
        (∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w) →
        (∀ θ : loopCircle, riemannianEDistOf g (u (diskBoundary θ)) p ≤ ENNReal.ofReal R) →
        (∫ z in closedBall (0 : ℂ) 1,
          (riemannianEDistOf g (diskExtension u z) p).toReal ^ 2) ≤
        C * ((∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z) +
          (R + 1) ^ 2) := by
  obtain ⟨C, hC, hP⟩ :=
    Analysis.Sobolev.exists_integral_sq_le_mul_integral_norm_fderiv_sq_complex_ball_of_lipschitz
  let V : ℝ := volume.real (closedBall (0 : ℂ) 1)
  refine ⟨4 * C + 2 * V, by dsimp [V]; positivity, ?_⟩
  intro g u p R L hR hu hb
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hedist (x y : M) : edist x y = riemannianEDistOf g x y := rfl
  have hfin : ∀ z : closedDisk, edist (u z) p ≠ ⊤ := by
    intro z
    have hpfin : edist (u (diskBoundary 0)) p ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb 0)
    have hpair : edist (u z) (u (diskBoundary 0)) ≠ ⊤ :=
      ne_top_of_le_ne_top
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) (hu z (diskBoundary 0))
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hpair, hpfin⟩)
      (edist_triangle (u z) (u (diskBoundary 0)) p)
  have hLip : LipschitzWith L (fun z : closedDisk => (edist (u z) p).toReal) :=
    EMetric.lipschitzWith_toReal_edist_comp (U := u) (L := L)
      (fun z w => hu z w) p hfin
  let d : C(closedDisk, ℝ) := ⟨fun z => (edist (u z) p).toReal, hLip.continuous⟩
  have hd : ∀ z w, edist (d z) (d w) ≤ riemannianEDistOf g (u z) (u w) := by
    intro z w
    rw [edist_dist, Real.dist_eq]
    exact EMetric.ofReal_abs_toReal_edist_sub_le_of_edist_ne_top (hfin z) (hfin w)
  have hdb : ∀ θ : loopCircle, d (diskBoundary θ) ≤ R := by
    intro θ
    change (riemannianEDistOf g (u (diskBoundary θ)) p).toReal ≤ R
    exact (ENNReal.toReal_le_toReal (hfin _) ENNReal.ofReal_ne_top).mpr (hb θ) |>.trans_eq
      (ENNReal.toReal_ofReal hR)
  have hm := scalar_disk_moment_bound hC hP g u d hu hd
    (fun _ => ENNReal.toReal_nonneg) hR hdb
  have henergy : 0 ≤ ∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension u) z := by
    apply integral_nonneg
    intro z
    exact div_nonneg (add_nonneg (metric_inner_self_nonneg _ _ _)
      (metric_inner_self_nonneg _ _ _)) (by norm_num)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  change (∫ z in closedBall (0 : ℂ) 1,
      (riemannianEDistOf g (diskExtension u z) p).toReal ^ 2) ≤
    4 * C * (∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z) +
      2 * (R + 1) ^ 2 * V at hm
  have hmul1 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hV) henergy
  have hmul2 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC) (sq_nonneg (R + 1))
  nlinarith

theorem exists_disk_distance_moment_constant_of_trace :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
        (u : C(closedDisk, M)) (σ : C(loopCircle, loopCircle))
        (p : M) {R : ℝ} {L : ℝ≥0}, 0 ≤ R →
        (∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w) →
        diskTrace u = γ.comp σ →
        (∀ θ : loopCircle, riemannianEDistOf g (γ θ) p ≤ ENNReal.ofReal R) →
        (∫ z in closedBall (0 : ℂ) 1,
          (riemannianEDistOf g (diskExtension u z) p).toReal ^ 2) ≤
        C * ((∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z) +
          (R + 1) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_disk_distance_moment_constant (E := E) (M := M)
  refine ⟨C, hC, ?_⟩
  intro g γ u σ p R L hR hu htrace hγ
  apply hbound g u p hR hu
  intro θ
  have hpoint : u (diskBoundary θ) = γ (σ θ) :=
    congrArg (fun v : freeLoop M => v θ) htrace
  rw [hpoint]
  exact hγ (σ θ)

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle MeasureTheory Set Filter Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem integrable_disk_distance_sq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (p : M) {L : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (hfinite : ∃ z : closedDisk, riemannianEDistOf g (u z) p ≠ ⊤) :
    IntegrableOn (fun z : ℂ =>
      (riemannianEDistOf g (diskExtension u z) p).toReal ^ 2)
      (closedBall (0 : ℂ) 1) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  obtain ⟨z₀, hz₀⟩ := hfinite
  have hf : ∀ z : closedDisk, edist (u z) p ≠ ⊤ := by
    intro z
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨ne_top_of_le_ne_top
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) (hu z z₀), hz₀⟩)
      (edist_triangle (u z) (u z₀) p)
  have hd : LipschitzWith L (fun z : closedDisk => (edist (u z) p).toReal) :=
    EMetric.lipschitzWith_toReal_edist_comp (U := u) (L := L) (fun z w => hu z w) p hf
  exact ((diskExtension_lipschitz hd).continuous.pow 2).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) 1)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem lintegral_disk_distance_sq_eq_integral
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (p : M) {L : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (hfinite : ∃ z : closedDisk, riemannianEDistOf g (u z) p ≠ ⊤) :
    (∫⁻ z in closedBall (0 : ℂ) 1,
      riemannianEDistOf g (diskExtension u z) p ^ 2) =
      ENNReal.ofReal (∫ z in closedBall (0 : ℂ) 1,
        (riemannianEDistOf g (diskExtension u z) p).toReal ^ 2) := by
  obtain ⟨z₀, hz₀⟩ := hfinite
  have hf : ∀ z : closedDisk, riemannianEDistOf g (u z) p ≠ ⊤ := by
    intro z
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨ne_top_of_le_ne_top
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) (hu z z₀), hz₀⟩)
      (riemannianEDistOf_triangle g (u z) (u z₀) p)
  calc
    _ = ∫⁻ z in closedBall (0 : ℂ) 1,
        ENNReal.ofReal ((riemannianEDistOf g (diskExtension u z) p).toReal ^ 2) := by
      apply lintegral_congr
      intro z
      have hfin : riemannianEDistOf g (diskExtension u z) p ≠ ⊤ := hf (diskRetraction z)
      rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin]
    _ = _ := (ofReal_integral_eq_lintegral_ofReal
      (integrable_disk_distance_sq g u p hu ⟨z₀, hz₀⟩)
      (Eventually.of_forall fun _ => sq_nonneg _)).symm

theorem exists_uniform_disk_distance_moment_bound_of_energy_le
    {ι : Type*} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (u : ι → C(closedDisk, M)) (p : M) {R A : ℝ}
    (hR : 0 ≤ R)
    (hγ : ∀ θ : loopCircle, riemannianEDistOf g (γ θ) p ≤ ENNReal.ofReal R)
    (hu : ∀ i, ∃ L : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u i z) (u i w) ≤ (L : ℝ≥0∞) * edist z w)
    (ht : ∀ i, ∃ σ : C(loopCircle, loopCircle), diskTrace (u i) = γ.comp σ)
    (he : ∀ i, (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u i)) z) ≤ A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i,
      (∫ z in closedBall (0 : ℂ) 1,
        (riemannianEDistOf g (diskExtension (u i) z) p).toReal ^ 2) ≤ B := by
  obtain ⟨C, hC, hc⟩ := exists_disk_distance_moment_constant_of_trace (E := E) (M := M)
  refine ⟨C * (max A 0 + (R + 1) ^ 2),
    mul_nonneg hC (add_nonneg (le_max_right A 0) (sq_nonneg _)), ?_⟩
  intro i
  obtain ⟨L, hL⟩ := hu i
  obtain ⟨σ, hσ⟩ := ht i
  exact (hc g γ (u i) σ p hR hL hσ hγ).trans
    (mul_le_mul_of_nonneg_left (add_le_add ((he i).trans (le_max_left A 0)) le_rfl) hC)

theorem exists_uniform_disk_distance_sq_lintegral_bound_of_energy_le
    {ι : Type*} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (u : ι → C(closedDisk, M)) (p : M) {R A : ℝ}
    (hR : 0 ≤ R)
    (hγ : ∀ θ : loopCircle, riemannianEDistOf g (γ θ) p ≤ ENNReal.ofReal R)
    (hu : ∀ i, ∃ L : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u i z) (u i w) ≤ (L : ℝ≥0∞) * edist z w)
    (ht : ∀ i, ∃ σ : C(loopCircle, loopCircle), diskTrace (u i) = γ.comp σ)
    (he : ∀ i, (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u i)) z) ≤ A) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ i,
      (∫⁻ z in closedBall (0 : ℂ) 1,
        riemannianEDistOf g (diskExtension (u i) z) p ^ 2) ≤ B := by
  obtain ⟨B, -, hB⟩ :=
    exists_uniform_disk_distance_moment_bound_of_energy_le g γ u p hR hγ hu ht he
  refine ⟨ENNReal.ofReal B, ENNReal.ofReal_ne_top, ?_⟩
  intro i
  obtain ⟨L, hL⟩ := hu i
  obtain ⟨σ, hσ⟩ := ht i
  have hpoint : u i (diskBoundary 0) = γ (σ 0) :=
    congrArg (fun v : freeLoop M => v 0) hσ
  have hfin : riemannianEDistOf g (u i (diskBoundary 0)) p ≠ ⊤ := by
    rw [hpoint]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hγ (σ 0))
  rw [lintegral_disk_distance_sq_eq_integral g (u i) p hL ⟨diskBoundary 0, hfin⟩]
  exact ENNReal.ofReal_le_ofReal (hB i)

theorem exists_uniform_disk_distance_sq_lintegral_bound_of_trace
    {ι : Type*} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (u : ι → C(closedDisk, M)) {A : ℝ}
    (hu : ∀ i, ∃ L : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u i z) (u i w) ≤ (L : ℝ≥0∞) * edist z w)
    (ht : ∀ i, ∃ σ : C(loopCircle, loopCircle), diskTrace (u i) = γ.comp σ)
    (he : ∀ i, (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u i)) z) ≤ A) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ i,
      (∫⁻ z in closedBall (0 : ℂ) 1,
        riemannianEDistOf g (diskExtension (u i) z) (γ 0) ^ 2) ≤ B := by
  obtain ⟨R, hR, hγ⟩ := exists_uniform_riemannianEDistOf_bound_on_loop g γ
  exact exists_uniform_disk_distance_sq_lintegral_bound_of_energy_le
    g γ u (γ 0) hR hγ hu ht he

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle MeasureTheory Set Filter Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

omit [T3Space M] in
private theorem disk_distance_ne_top
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (p : M) {L : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (hfinite : ∃ z : closedDisk, riemannianEDistOf g (u z) p ≠ ⊤) :
    ∀ z : closedDisk, riemannianEDistOf g (u z) p ≠ ⊤ := by
  obtain ⟨z₀, hz₀⟩ := hfinite
  intro z
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) (hu z z₀), hz₀⟩)
    (riemannianEDistOf_triangle g (u z) (u z₀) p)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lipschitzWith_disk_distance
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (p : M) {L : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (hfinite : ∃ z : closedDisk, riemannianEDistOf g (u z) p ≠ ⊤) :
    LipschitzWith L (fun z : ℂ => (riemannianEDistOf g (diskExtension u z) p).toReal) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hf := disk_distance_ne_top g u p hu hfinite
  have hd : LipschitzWith L (fun z : closedDisk => (edist (u z) p).toReal) :=
    EMetric.lipschitzWith_toReal_edist_comp (U := u) (L := L) (fun z w => hu z w) p hf
  exact diskExtension_lipschitz hd

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integral_norm_fderiv_disk_distance_sq_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (p : M) {L : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (hfinite : ∃ z : closedDisk, riemannianEDistOf g (u z) p ≠ ⊤) :
    (∫ z in closedBall (0 : ℂ) 1,
      ‖fderiv ℝ (fun w : ℂ => (riemannianEDistOf g (diskExtension u w) p).toReal) z‖ ^ 2) ≤
      2 * ∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let f : ℂ → ℝ := fun z => (riemannianEDistOf g (diskExtension u z) p).toReal
  have hfin := disk_distance_ne_top g u p hu hfinite
  have hcontract : ∀ z w, edist (f z) (f w) ≤
      riemannianEDistOf g (diskExtension u z) (diskExtension u w) := by
    intro z w
    rw [edist_dist, Real.dist_eq]
    change ENNReal.ofReal |(edist (u (diskRetraction z)) p).toReal -
      (edist (u (diskRetraction w)) p).toReal| ≤
        edist (u (diskRetraction z)) (u (diskRetraction w))
    exact EMetric.ofReal_abs_toReal_edist_sub_le_of_edist_ne_top
      (x := u (diskRetraction z)) (y := u (diskRetraction w)) (p := p)
      (hfin (diskRetraction z)) (hfin (diskRetraction w))
  have hae := ae_fderiv_partials_sq_le_two_mul_diskMapEnergyDensity g
    (diskExtension_riemannian_lipschitz g hu) hcontract
  have hLip := lipschitzWith_disk_distance g u p hu hfinite
  let : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  have hfm : MemLp (fderiv ℝ f) 2 (volume.restrict (closedBall (0 : ℂ) 1)) :=
    MemLp.of_bound
      ((measurable_fderiv ℝ f).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
      L (Eventually.of_forall fun z => norm_fderiv_le_of_lipschitz ℝ hLip)
  have he := integrable_diskMapEnergyDensity g hu
  rw [← integral_const_mul]
  apply integral_mono_ae hfm.norm.integrable_sq (he.const_mul 2)
  filter_upwards [ae_restrict_of_ae (s := closedBall (0 : ℂ) 1) hae] with z hz
  have hnorm : ‖fderiv ℝ f z‖ ^ 2 =
      (fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2 := by
    simpa [Complex.coe_orthonormalBasisOneI, Fin.sum_univ_two] using
      Complex.orthonormalBasisOneI.norm_dual (fderiv ℝ f z)
  rwa [hnorm]

theorem exists_uniform_disk_distance_moment_bound_at_point
    {ι : Type*} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (u : ι → C(closedDisk, M)) (p : M)
    (hp : riemannianEDistOf g (γ 0) p ≠ ⊤) {A : ℝ}
    (hu : ∀ i, ∃ L : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u i z) (u i w) ≤ (L : ℝ≥0∞) * edist z w)
    (ht : ∀ i, ∃ σ : C(loopCircle, loopCircle), diskTrace (u i) = γ.comp σ)
    (he : ∀ i, (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u i)) z) ≤ A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i,
      (∫ z in closedBall (0 : ℂ) 1,
        (riemannianEDistOf g (diskExtension (u i) z) p).toReal ^ 2) ≤ B := by
  obtain ⟨R, hR, hγ⟩ := exists_uniform_riemannianEDistOf_bound_on_loop g γ
  let S : ℝ := R + (riemannianEDistOf g (γ 0) p).toReal
  have hS : 0 ≤ S := add_nonneg hR ENNReal.toReal_nonneg
  have hγp : ∀ θ : loopCircle, riemannianEDistOf g (γ θ) p ≤ ENNReal.ofReal S := by
    intro θ
    calc
      riemannianEDistOf g (γ θ) p ≤
          riemannianEDistOf g (γ θ) (γ 0) + riemannianEDistOf g (γ 0) p :=
        riemannianEDistOf_triangle g (γ θ) (γ 0) p
      _ ≤ ENNReal.ofReal R + riemannianEDistOf g (γ 0) p := add_le_add (hγ θ) le_rfl
      _ = ENNReal.ofReal S := by
        rw [show S = R + (riemannianEDistOf g (γ 0) p).toReal from rfl,
          ENNReal.ofReal_add hR ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hp]
  exact exists_uniform_disk_distance_moment_bound_of_energy_le g γ u p hS hγp hu ht he

end DifferentialGeometry.Geometry

end

end
