import DifferentialGeometry.Topology.MetricSpace.BallPasting
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Affine
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.ChartFilling

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric Bundle Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_disk_replacement_of_eq_on_sphere
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u : C(closedDisk, M)) {v : ℂ → M} {K L : ℝ≥0}
    (hu : ∀ z z', riemannianEDistOf g (u z) (u z') ≤ (K : ℝ≥0∞) * edist z z')
    (hv : ∀ z z', riemannianEDistOf g (v z) (v z') ≤ (L : ℝ≥0∞) * edist z z')
    {b : ℂ} {r : ℝ} (hbr : ‖b‖ + r < 1)
    (heq : ∀ z ∈ sphere b r, v z = diskExtension u z) :
    ∃ w : C(closedDisk, M),
      (∀ z z', riemannianEDistOf g (w z) (w z') ≤ ((L + K : ℝ≥0) : ℝ≥0∞) * edist z z') ∧
      (∀ z : closedDisk, dist (z : ℂ) b ≤ r → w z = v z) ∧
      (∀ z : closedDisk, r ≤ dist (z : ℂ) b → w z = u z) ∧
      diskTrace w = diskTrace u ∧
      (∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension w) z) =
        (∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z) -
          (∫ z in closedBall b r, diskMapEnergyDensity g (diskExtension u) z) +
            ∫ z in closedBall b r, diskMapEnergyDensity g v z := by
  classical
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let U : ℂ → M := diskExtension u
  let f : ℂ → M := (closedBall b r).piecewise v U
  have hULip : LipschitzWith K U := diskExtension_riemannian_lipschitz g hu
  have hvLip : LipschitzWith L v := hv
  have hfLip : LipschitzWith (L + K) f :=
    Analysis.lipschitzWith_piecewise_closedBall_of_eqOn_sphere
      hvLip.lipschitzOnWith hULip.lipschitzOnWith heq
  let w : C(closedDisk, M) := ⟨fun z => f z, hfLip.continuous.comp continuous_subtype_val⟩
  have hball : closedBall b r ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    rw [mem_ball, dist_zero_right]
    have hn : ‖z‖ ≤ dist z b + ‖b‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - b) b
    exact hn.trans_lt (by have hd := mem_closedBall.mp hz; linarith)
  have hinner (z : closedDisk) (hz : dist (z : ℂ) b ≤ r) : w z = v z := by
    change (closedBall b r).piecewise v U z = v z
    exact piecewise_eq_of_mem _ _ _ (mem_closedBall.mpr hz)
  have houter (z : closedDisk) (hz : r ≤ dist (z : ℂ) b) : w z = u z := by
    by_cases hzr : dist (z : ℂ) b = r
    · rw [hinner z hzr.le, heq z (mem_sphere.mpr hzr)]
      exact diskExtension_coe u z
    · have hn : (z : ℂ) ∉ closedBall b r := not_le.mpr (lt_of_le_of_ne hz (Ne.symm hzr))
      change (closedBall b r).piecewise v U z = u z
      rw [piecewise_eq_of_notMem _ _ _ hn]
      exact diskExtension_coe u z
  have hext (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : diskExtension w =ᶠ[𝓝 z] f := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact diskExtension_coe w ⟨y, ball_subset_closedBall hy⟩
  have hgin (z : ℂ) (hz : z ∈ ball b r) : f =ᶠ[𝓝 z] v := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact piecewise_eq_of_mem _ _ _ (ball_subset_closedBall hy)
  have hgout (z : ℂ) (hz : z ∉ closedBall b r) : f =ᶠ[𝓝 z] U := by
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hz] with y hy
    exact piecewise_eq_of_notMem _ _ _ hy
  have hcongr {F G : ℂ → M} {z : ℂ} (h : F =ᶠ[𝓝 z] G) :
      diskMapEnergyDensity g F z = diskMapEnergyDensity g G z := by
    unfold diskMapEnergyDensity diskMapPartial
    rw [h.mfderiv_eq, h.eq_of_nhds]
    have hcast :
        (tangentSpaceCast 𝓘(ℝ, E) (G z) (G z) :
          TangentSpace 𝓘(ℝ, E) (G z) →L[ℝ] TangentSpace 𝓘(ℝ, E) (G z)) =
        ContinuousLinearMap.id ℝ _ := by
      ext w
      rfl
    rw [hcast]
    simp
  let : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  have hif : IntegrableOn (diskMapEnergyDensity g f) (closedBall (0 : ℂ) 1) :=
    integrableOn_diskMapEnergyDensity_of_lipschitz g hfLip _
  have hiU : IntegrableOn (diskMapEnergyDensity g U) (closedBall (0 : ℂ) 1) :=
    integrableOn_diskMapEnergyDensity_of_lipschitz g hULip _
  have htotal : (∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension w) z) =
      ∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g f z := by
    apply integral_congr_ae
    filter_upwards [ae_disk_interior] with z hz
    exact hcongr (hext z hz)
  have hinside : (∫ z in closedBall b r, diskMapEnergyDensity g f z) =
      ∫ z in closedBall b r, diskMapEnergyDensity g v z := by
    apply integral_congr_ae
    filter_upwards [ae_mem_ball_of_measure_sphere_eq_zero
      (Measure.addHaar_sphere volume b r)] with z hz
    exact hcongr (hgin z hz)
  have houtside : (∫ z in closedBall (0 : ℂ) 1 \ closedBall b r, diskMapEnergyDensity g f z) =
      ∫ z in closedBall (0 : ℂ) 1 \ closedBall b r, diskMapEnergyDensity g U z := by
    apply setIntegral_congr_fun (measurableSet_closedBall.diff measurableSet_closedBall)
    intro z hz
    exact hcongr (hgout z hz.2)
  refine ⟨w, fun z z' => hfLip z z', hinner, houter, ?_, ?_⟩
  · ext θ
    change w (diskBoundary θ) = u (diskBoundary θ)
    apply houter
    have hnorm : ‖((diskBoundary θ : closedDisk) : ℂ)‖ = 1 := by
      change ‖(AddCircle.toCircle θ : ℂ)‖ = 1
      exact Circle.norm_coe _
    by_contra hnot
    have hin := hball (show (diskBoundary θ : ℂ) ∈ closedBall b r from (not_le.mp hnot).le)
    have hn : ‖(diskBoundary θ : ℂ)‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hin
    exact (not_lt_of_ge hnorm.ge) hn
  · have hsubset : closedBall b r ⊆ closedBall (0 : ℂ) 1 := hball.trans ball_subset_closedBall
    have hsf := setIntegral_sdiff measurableSet_closedBall hif hsubset
    have hsU := setIntegral_sdiff measurableSet_closedBall hiU hsubset
    rw [hinside, houtside, hsU] at hsf
    rw [htotal]
    linarith

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_weaklyMonotoneDiskCompetitor_replacement_of_eq_on_sphere
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : u ∈ weaklyMonotoneDiskCompetitors g γ)
    {v : ℂ → M} {L : ℝ≥0}
    (hv : ∀ z z', riemannianEDistOf g (v z) (v z') ≤ (L : ℝ≥0∞) * edist z z')
    {b : ℂ} {r : ℝ} (hbr : ‖b‖ + r < 1)
    (heq : ∀ z ∈ sphere b r, v z = diskExtension u z) :
    ∃ w : C(closedDisk, M), w ∈ weaklyMonotoneDiskCompetitors g γ ∧
      diskTrace w = diskTrace u ∧
      (∀ z : closedDisk, dist (z : ℂ) b ≤ r → w z = v z) ∧
      (∀ z : closedDisk, r ≤ dist (z : ℂ) b → w z = u z) ∧
      riemannianDiskEnergy g w = riemannianDiskEnergy g u -
        (∫ z in closedBall b r, diskMapEnergyDensity g (diskExtension u) z) +
          ∫ z in closedBall b r, diskMapEnergyDensity g v z := by
  obtain ⟨huTrace, K, hK⟩ := hu
  obtain ⟨w, hLip, hinner, houter, htrace, henergy⟩ :=
    exists_disk_replacement_of_eq_on_sphere g u hK hv hbr heq
  have hwTrace : DiskWeakJordanTrace γ w := by
    obtain ⟨τ, hτ, ht⟩ := huTrace
    exact ⟨τ, hτ, htrace.trans ht⟩
  exact ⟨w, ⟨hwTrace, L + K, hLip⟩, htrace, hinner, houter, henergy⟩

theorem disk_energy_on_ball_le_replacement_add_minimizing_defect
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : u ∈ weaklyMonotoneDiskCompetitors g γ)
    {v : ℂ → M} {L : ℝ≥0}
    (hv : ∀ z z', riemannianEDistOf g (v z) (v z') ≤ (L : ℝ≥0∞) * edist z z')
    {b : ℂ} {r : ℝ} (hbr : ‖b‖ + r < 1)
    (heq : ∀ z ∈ sphere b r, v z = diskExtension u z) :
    (∫ z in closedBall b r, diskMapEnergyDensity g (diskExtension u) z) ≤
      (∫ z in closedBall b r, diskMapEnergyDensity g v z) +
        (riemannianDiskEnergy g u -
          sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
            weaklyMonotoneDiskCompetitors g γ)) := by
  obtain ⟨w, hw, _, _, _, he⟩ :=
    exists_weaklyMonotoneDiskCompetitor_replacement_of_eq_on_sphere g hu hv hbr heq
  have hbounded : BddBelow ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
      weaklyMonotoneDiskCompetitors g γ) := by
    refine ⟨0, ?_⟩
    rintro e ⟨v, _, rfl⟩
    exact riemannianDiskEnergy_nonneg g v
  have hle := csInf_le hbounded (mem_image_of_mem (fun w : C(closedDisk, M) =>
    riemannianDiskEnergy g w) hw)
  linarith

omit [FiniteDimensional ℝ E] [T3Space M] in
theorem tendsto_disk_energy_of_energy_nonincreasing_replacements
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (u w : ℕ → C(closedDisk, M))
    (hw : ∀ n, w n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hdecrease : ∀ n, riemannianDiskEnergy g (w n) ≤ riemannianDiskEnergy g (u n))
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ)))) :
    Tendsto (fun n => riemannianDiskEnergy g (w n)) atTop
      (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))) := by
  have hbounded : BddBelow ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
      weaklyMonotoneDiskCompetitors g γ) := by
    refine ⟨0, ?_⟩
    rintro e ⟨v, _, rfl⟩
    exact riemannianDiskEnergy_nonneg g v
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmin
  · intro n
    exact csInf_le hbounded (mem_image_of_mem (fun v : C(closedDisk, M) =>
      riemannianDiskEnergy g v) (hw n))
  · exact hdecrease

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_disk_replacement_from_unit_filling
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : u ∈ weaklyMonotoneDiskCompetitors g γ)
    (w : C(closedDisk, M)) {L : ℝ≥0}
    (hw : ∀ z z', riemannianEDistOf g (w z) (w z') ≤ (L : ℝ≥0∞) * edist z z')
    {b : ℂ} {r : ℝ} (hr : 0 < r) (hbr : ‖b‖ + r < 1)
    (htrace : ∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → w z = diskExtension u (b + r • (z : ℂ))) :
    ∃ v : C(closedDisk, M), v ∈ weaklyMonotoneDiskCompetitors g γ ∧
      diskTrace v = diskTrace u ∧
      (∀ z : closedDisk, r ≤ dist (z : ℂ) b → v z = u z) ∧
      (∀ z : closedDisk, dist (z : ℂ) b ≤ r →
        v z = diskExtension w (r⁻¹ • ((z : ℂ) - b))) ∧
      riemannianDiskEnergy g v = riemannianDiskEnergy g u -
        (∫ z in closedBall b r, diskMapEnergyDensity g (diskExtension u) z) +
          riemannianDiskEnergy g w := by
  let a : ℂ → ℂ := fun z => r⁻¹ • (z - b)
  let W : ℂ → M := diskExtension w ∘ a
  have ha : LipschitzWith (Real.nnabs r⁻¹) a := by
    apply LipschitzWith.of_dist_le_mul
    intro z z'
    simp only [a, dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right,
      norm_smul, Real.norm_eq_abs, Real.coe_nnabs, le_refl]
  have hW : ∀ z z', riemannianEDistOf g (W z) (W z') ≤
      ((L * Real.nnabs r⁻¹ : ℝ≥0) : ℝ≥0∞) * edist z z' := by
    intro z z'
    exact (diskExtension_riemannian_lipschitz g hw (a z) (a z')).trans
      ((mul_le_mul_right (ha z z') (L : ℝ≥0∞)).trans_eq (by rw [ENNReal.coe_mul, mul_assoc]))
  have hnorm {z : ℂ} (hz : z ∈ sphere b r) : ‖a z‖ = 1 := by
    rw [show a z = r⁻¹ • (z - b) from rfl, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    rw [show ‖z - b‖ = r by simpa only [mem_sphere, dist_eq_norm] using hz]
    exact inv_mul_cancel₀ hr.ne'
  have hinv (z : ℂ) : b + r • a z = z := by
    rw [show a z = r⁻¹ • (z - b) from rfl, smul_inv_smul₀ hr.ne', add_sub_cancel]
  have hboundary : ∀ z ∈ sphere b r, W z = diskExtension u z := by
    intro z hz
    let q : closedDisk := ⟨a z, by simp only [mem_closedBall, dist_zero_right, hnorm hz, le_refl]⟩
    have hqnorm : ‖(q : ℂ)‖ = 1 := hnorm hz
    have ht := htrace q hqnorm
    rw [show b + r • (q : ℂ) = z from hinv z] at ht
    exact (diskExtension_coe w q).trans ht
  obtain ⟨v, hv, ht, hi, ho, he⟩ :=
    exists_weaklyMonotoneDiskCompetitor_replacement_of_eq_on_sphere g hu hW hbr hboundary
  have hcomp : (fun z => W (b + r • z)) = diskExtension w := by
    funext z
    change diskExtension w (r⁻¹ • (b + r • z - b)) = diskExtension w z
    rw [add_sub_cancel_left, inv_smul_smul₀ hr.ne']
  have henergy : (∫ z in closedBall b r, diskMapEnergyDensity g W z) =
      riemannianDiskEnergy g w := by
    rw [← integral_diskMapEnergyDensity_comp_affine_closedBall g W b hr, hcomp]
    rfl
  exact ⟨v, hv, ht, ho, hi, by rwa [henergy] at he⟩

end DifferentialGeometry.Geometry

end

end
