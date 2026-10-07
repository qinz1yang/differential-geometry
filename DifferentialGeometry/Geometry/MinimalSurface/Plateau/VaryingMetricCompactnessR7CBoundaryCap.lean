import DifferentialGeometry.Geometry.MinimalSurface.Plateau.VaryingMetricCompactnessR7CHoleFilling
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.IntrinsicBoundaryCap
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.IntrinsicCrosscut

/-!
# R7C L5（一）：quasi-minimal 盘的边界 cap 能量界（competitor 形，无 defect）

树内 `exists_local_reconstructed_disk_cap_energy_bound` 与
`exists_uniform_intrinsic_boundary_cap_energy_bound`（`Energy/IntrinsicBoundaryCap.lean`）的结论
带全局 minimizing defect `E(u) − inf`；这里把最后一步
`disk_cap_energy_le_add_minimizing_defect` 换成**局部 quasi-minimality 前提**（对一切在 `B̄_s(c)` 外与 `u`
相同、trace 类为 `γ` 的 Lipschitz competitor `w`：`E(u, D ∩ B̄_s(c)) ≤ Λ E(w, D ∩ B̄_s(c))`），得
`E(u, lens ρ) ≤ Λ · C · ∫ speed²(crosscut)`，常数 `ε, C` 只依赖 `(g, γ)`。证明其余部分逐字照搬树内
（cap 构造：`exists_boundary_cap_in_ball_of_short_lift_increment` + 管状邻域 retraction）。
R7C 中 `(g, γ) = (Ĝ, Γ')` 取 completion buffer，quasi-minimality 由
`local_quasi_minimality_R7C`（`Λ = 4`）给出。
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

section Local

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ E] [T3Space M]

/-- 局部 reconstructed cap 的 quasi-minimal 版（R7C）：见文件头。 -/
theorem local_reconstructed_disk_cap_energy_bound_qm_R7C
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {r : F → M} {U K : Set F}
    (hU : IsOpen U) (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (η : ℝ) (C : ℝ≥0), 0 < η ∧ ∀ p ∈ K,
      ∀ (u : C(closedDisk, M)) (q : ℂ → F) (L Lq : ℝ≥0) (c : ℂ) (s : ℝ),
      (∀ z w : closedDisk, riemannianEDistOf g (u z) (u w) ≤
        (L : ℝ≥0∞) * edist z w) → LipschitzWith Lq q →
      MapsTo q (closedBall (0 : ℂ) 1 ∩ closedBall c s) (closedBall p η) →
      EqOn (r ∘ q) (diskExtension u) (closedBall (0 : ℂ) 1 ∩ sphere c s) →
      ∀ (γ : freeLoop M) (τ : C(loopCircle, loopCircle)), IsWeaklyMonotoneOnce τ →
      (∀ θ, dist (diskBoundary θ : ℂ) c ≤ s → r (q (diskBoundary θ)) = γ (τ θ)) →
      (∀ θ, s ≤ dist (diskBoundary θ : ℂ) c → u (diskBoundary θ) = γ (τ θ)) →
      ∀ Λ : ℝ, 0 ≤ Λ →
      (∀ (w : C(closedDisk, M)) (Lw : ℝ≥0),
        (∀ z z', riemannianEDistOf g (w z) (w z') ≤ (Lw : ℝ≥0∞) * edist z z') →
        DiskWeakJordanTrace γ w → (∀ z : closedDisk, s ≤ dist (z : ℂ) c → w z = u z) →
        (∫ z in closedBall (0 : ℂ) 1 ∩ closedBall c s,
          diskMapEnergyDensity g (diskExtension u) z) ≤
          Λ * ∫ z in closedBall (0 : ℂ) 1 ∩ closedBall c s,
            diskMapEnergyDensity g (diskExtension w) z) →
      (∫ z in closedBall (0 : ℂ) 1 ∩ closedBall c s,
        diskMapEnergyDensity g (diskExtension u) z) ≤
        Λ * ((C : ℝ) ^ 2 *
          (∫ z in closedBall (0 : ℂ) 1 ∩ closedBall c s,
            (‖fderiv ℝ q z 1‖ ^ 2 + ‖fderiv ℝ q z Complex.I‖ ^ 2) / 2)) := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  obtain ⟨η, C, hη, hlocal⟩ := exists_uniform_local_source_metric_bound_near_compact g hU hr hK hKU
  refine ⟨η, C, hη, ?_⟩
  intro p hp u q L Lq c s hu hq hqrange hseam γ τ hτ htraceIn htraceOut Λ hΛ hqm
  obtain ⟨hballU, hrlip, hrbound⟩ := hlocal p hp
  let A : Set ℂ := closedBall (0 : ℂ) 1 ∩ closedBall c s
  have hv : ∀ z ∈ A, ∀ w ∈ A, riemannianEDistOf g ((r ∘ q) z) ((r ∘ q) w) ≤
      ((C * Lq : ℝ≥0) : ℝ≥0∞) * edist z w := by
    intro z hz w hw
    apply (hrlip (q z) (hqrange hz) (q w) (hqrange hw)).trans
    rw [ENNReal.coe_mul, mul_assoc]
    exact mul_le_mul' le_rfl (hq z w)
  obtain ⟨w, hwLip, hwin, hwout, hvint, hwE⟩ :=
    exists_disk_cap_replacement_of_eqOn_sphere g u hu hv hseam
  have hwtrace : diskTrace w = γ.comp τ := by
    ext θ
    change w (diskBoundary θ) = γ (τ θ)
    by_cases hθ : dist (diskBoundary θ : ℂ) c ≤ s
    · rw [hwin (diskBoundary θ) hθ]
      exact htraceIn θ hθ
    · rw [hwout (diskBoundary θ) (not_le.mp hθ).le]
      exact htraceOut θ (not_le.mp hθ).le
  have hAc : IsClosed (closedBall c s) := isClosed_closedBall
  have hqmw := hqm w _ hwLip ⟨τ, hτ, hwtrace⟩ hwout
  have hiu := integrable_diskMapEnergyDensity g hu
  have hiw := integrable_diskMapEnergyDensity g hwLip
  have hAD : A ⊆ closedBall (0 : ℂ) 1 := inter_subset_left
  have hAm : MeasurableSet A := measurableSet_closedBall.inter measurableSet_closedBall
  have hsu := setIntegral_sdiff hAm hiu hAD
  have hsw := setIntegral_sdiff hAm hiw hAD
  have hdA : closedBall (0 : ℂ) 1 \ A = closedBall (0 : ℂ) 1 \ closedBall c s :=
    sdiff_self_inter
  rw [hdA] at hsu hsw
  have hdiff := setIntegral_diskMapEnergyDensity_diff_eq_R7C g hAc
    (fun z hz => hwout z (le_of_lt (not_le.mp hz)))
  have hwA : (∫ z in A, diskMapEnergyDensity g (diskExtension w) z) =
      ∫ z in A, diskMapEnergyDensity g (r ∘ q) z := by
    change riemannianDiskEnergy g w = riemannianDiskEnergy g u -
      (∫ z in A, diskMapEnergyDensity g (diskExtension u) z) +
        ∫ z in A, diskMapEnergyDensity g (r ∘ q) z at hwE
    unfold riemannianDiskEnergy at hwE
    linarith
  have hc : (∫ z in A, diskMapEnergyDensity g (diskExtension u) z) ≤
      Λ * ∫ z in A, diskMapEnergyDensity g (r ∘ q) z := by
    rw [← hwA]
    exact hqmw
  have hdirint (v : ℂ) : IntegrableOn (fun z => ‖fderiv ℝ q z v‖ ^ 2) A := by
    apply (integrableOn_const (C := ((Lq : ℝ) * ‖v‖) ^ 2)
      ((isCompact_closedBall (0 : ℂ) 1).inter_right isClosed_closedBall).measure_ne_top).mono'
    · have heval : Continuous (fun A : ℂ →L[ℝ] F => A v) := by fun_prop
      exact ((heval.measurable.comp (measurable_fderiv ℝ q)).norm.pow_const 2).aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) ((fderiv ℝ q z).le_opNorm v |>.trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hq) (norm_nonneg v))) 2
  have hJint := ((hdirint 1).add (hdirint Complex.I)).div_const 2
  have hpoint : ∀ᵐ z ∂volume.restrict A,
      diskMapEnergyDensity g (r ∘ q) z ≤ (C : ℝ) ^ 2 *
        ((‖fderiv ℝ q z 1‖ ^ 2 + ‖fderiv ℝ q z Complex.I‖ ^ 2) / 2) := by
    filter_upwards [ae_restrict_of_ae (hq.ae_differentiableAt (μ := volume)),
      ae_restrict_mem (measurableSet_closedBall.inter measurableSet_closedBall)] with z hz hzA
    have hrz : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) r (q z) :=
      (hr.contMDiffAt (hU.mem_nhds (hballU (hqrange hzA)))).mdifferentiableAt one_ne_zero
    have hd := mfderiv_comp z hrz hz.mdifferentiableAt
    rw [mfderiv_eq_fderiv] at hd
    have hbound (v : ℂ) : g.inner (r (q z))
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (q z) (fderiv ℝ q z v))
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (q z) (fderiv ℝ q z v)) ≤
          (C : ℝ) ^ 2 * ‖fderiv ℝ q z v‖ ^ 2 := by
      have h := hrbound (q z) (hqrange hzA) (fderiv ℝ q z v)
      have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
      rwa [Real.sq_sqrt (metric_inner_self_nonneg g _ _), mul_pow] at hs
    unfold diskMapEnergyDensity diskMapPartial
    rw [hd]
    have h1 := hbound 1
    have hI := hbound Complex.I
    change (g.inner (r (q z))
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (q z) (fderiv ℝ q z 1))
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (q z) (fderiv ℝ q z 1)) +
      g.inner (r (q z))
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (q z) (fderiv ℝ q z Complex.I))
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r (q z) (fderiv ℝ q z Complex.I))) / 2 ≤ _
    nlinarith
  have hb := integral_mono_ae hvint (hJint.const_mul ((C : ℝ) ^ 2)) hpoint
  rw [integral_const_mul] at hb
  exact hc.trans (mul_le_mul_of_nonneg_left (by simpa only [Pi.add_apply] using hb) hΛ)

end Local

section Main

open Function DifferentialGeometry.Analysis

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- 边界 cap 能量界的 quasi-minimal 版（R7C）：`ε, C` 只依赖 `(g, γ)`；对一切 Lipschitz、trace 由单调 lift
`ψ`（`ψ` 的 lens 增量 `≤ 2/3`）给出、在 `lens ρ` 上局部 `Λ`-quasi-minimal 的盘 `u`：
`E(u, lens ρ) ≤ Λ · C · ∫ speed²`。 -/
theorem boundary_cap_energy_bound_qm_R7C
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ (u : C(closedDisk, M)) (L : ℝ≥0),
      (∀ z w : closedDisk, riemannianEDistOf g (u z) (u w) ≤
        (L : ℝ≥0∞) * edist z w) →
      ∀ ψ : CircleDeg1Lift, Continuous ψ →
      (∀ t : ℝ, u (diskBoundary (t : loopCircle)) = γ ((ψ t : ℝ) : loopCircle)) →
      ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ψ (1 - Real.arccos (ρ / 2) / Real.pi) - ψ (Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3 →
      let α : ℝ → M := fun s => diskExtension u
        (circleMap (-1) ρ (-Real.arccos (ρ / 2) + 2 * Real.arccos (ρ / 2) * s))
      IntegrableOn (fun t => (riemannianCurveSpeed g α t) ^ 2) (Icc (0 : ℝ) 1) →
      (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g α t) ^ 2) ≤ ε →
      ∀ Λ : ℝ, 0 ≤ Λ →
      (∀ (w : C(closedDisk, M)) (Lw : ℝ≥0),
        (∀ z z', riemannianEDistOf g (w z) (w z') ≤ (Lw : ℝ≥0∞) * edist z z') →
        DiskWeakJordanTrace γ w → (∀ z : closedDisk, ρ ≤ dist (z : ℂ) (-1) → w z = u z) →
        (∫ z in closedBall (0 : ℂ) 1 ∩ closedBall (-1) ρ,
          diskMapEnergyDensity g (diskExtension u) z) ≤
          Λ * ∫ z in closedBall (0 : ℂ) 1 ∩ closedBall (-1) ρ,
            diskMapEnergyDensity g (diskExtension w) z) →
      (∫ z in boundaryLens ρ, diskMapEnergyDensity g (diskExtension u) z) ≤
        Λ * (C * (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g α t) ^ 2)) := by
  obtain ⟨N, n, e, r, U, _, Cγ, J, hγN, he, hesupp, hU, heU, hr, hleft, _, hCγ, hJ⟩ :=
    exists_loop_neighborhood_embedding_retraction g γ hγ
  obtain ⟨Ce, hCe, heLip, hcurve⟩ := exists_curve_energy_bound_of_hasCompactSupport g
    (he.of_le (by simp)) hesupp
  let K := range (fun θ : loopCircle => e (γ θ))
  have hK : IsCompact K := isCompact_range (he.continuous.comp γ.continuous)
  have hKU : K ⊆ U := by
    rintro _ ⟨θ, rfl⟩
    exact heU (mem_image_of_mem e (hγN (mem_range_self θ)))
  obtain ⟨η, Cr, hη, hlocal⟩ := local_reconstructed_disk_cap_energy_bound_qm_R7C g hU
    (hr.of_le (by simp)) hK hKU
  obtain ⟨ε₀, hε₀, htube⟩ := exists_energy_bound_curve_range_subset_of_isCompact g
    (isCompact_range γ.continuous) N.isOpen hγN
  let D : ℝ := 1 + 2 * (Cγ : ℝ) * (J : ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  let ε := min ε₀ ((η / (D * Ce)) ^ 2)
  have hε : 0 < ε := lt_min hε₀ (sq_pos_of_pos (div_pos hη (by positivity)))
  let Q : ℝ := 2 * (144 * (16 * Real.pi + 1) * (18 * Real.pi ^ 2 + 1)) ^ 2 *
    ((Real.pi / 2) * D ^ 2 + (2 + 8 * (Cγ : ℝ) ^ 2 * (J : ℝ) ^ 2) / (8 * Real.pi))
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨ε, (Cr : ℝ) ^ 2 * Q * (Ce : ℝ) ^ 2, hε, by positivity, ?_⟩
  intro u L hu ψ hψ htrace ρ hρ hρ1 hshort α hαI hαE Λ hΛ hqm
  let a := Real.arccos (ρ / 2)
  let arc : ℝ → ℂ := fun s => circleMap (-1) ρ (-a + 2 * a * s)
  let f : ℂ → EuclideanSpace ℝ (Fin n) := e ∘ diskExtension u
  let Γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => e (γ (t : loopCircle))
  have hUlip := diskExtension_riemannian_lipschitz g hu
  have hf : LipschitzWith (Ce * L) f := by
    intro z w
    apply (heLip _ _).trans
    rw [ENNReal.coe_mul, mul_assoc]
    exact mul_le_mul' le_rfl (hUlip z w)
  have hparam : LipschitzWith (Real.nnabs (2 * a)) (fun s : ℝ => -a + 2 * a * s) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [Real.dist_eq, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, Real.coe_nnabs]
    exact le_rfl
  have harc := (lipschitzWith_circleMap (-1) ρ).comp hparam
  have hαlip (s t : ℝ) : riemannianEDistOf g (α s) (α t) ≤
      ((L * (Real.nnabs ρ * Real.nnabs (2 * a)) : ℝ≥0) : ℝ≥0∞) * edist s t := by
    apply (hUlip (arc s) (arc t)).trans
    rw [ENNReal.coe_mul, mul_assoc]
    exact mul_le_mul' le_rfl (harc s t)
  have hper : Periodic Γ 1 := by
    intro t
    simp only [Γ, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  have hInv : AntilipschitzWith J (hper.lift : loopCircle → EuclideanSpace ℝ (Fin n)) := by
    intro x y
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact hJ (s : loopCircle) (t : loopCircle)
  have hftrace (t : ℝ) : f (circleMap 0 1 (2 * Real.pi * t)) = Γ (ψ t) := by
    have hz : circleMap 0 1 (2 * Real.pi * t) = (diskBoundary (t : loopCircle) : ℂ) := by
      simp only [diskBoundary_coe, circleMap, Complex.ofReal_one, one_mul, zero_add]
    change e (diskExtension u _) = e (γ _)
    rw [hz, diskExtension_coe, htrace]
  have hα0 : α 0 = γ ((ψ (1 - a / Real.pi) : ℝ) : loopCircle) := by
    have hArc : arc 0 = circleMap 0 1 (2 * Real.pi * (1 - a / Real.pi)) := by
      simp only [arc, mul_zero, add_zero]
      rw [circleMap_neg_one_neg_arccos (by linarith : -2 ≤ ρ) (by linarith : ρ ≤ 2)]
      congr 1
      dsimp [a]
      field_simp
    change diskExtension u (arc 0) = _
    rw [hArc]
    have hz : circleMap 0 1 (2 * Real.pi * (1 - a / Real.pi)) =
        (diskBoundary ((1 - a / Real.pi : ℝ) : loopCircle) : ℂ) := by
      simp only [diskBoundary_coe, circleMap, Complex.ofReal_one, one_mul, zero_add]
    rw [hz, diskExtension_coe, htrace]
  have hαrange : MapsTo α (Icc (0 : ℝ) 1) N :=
    htube α _ hαlip (hα0 ▸ mem_range_self _) hαI (hαE.trans (min_le_left _ _))
  obtain ⟨_, hEa⟩ := hcurve α _ hαlip 0 1 hαI
  let Ea := ∫ t in Icc (0 : ℝ) 1, ‖deriv (f ∘ arc) t‖ ^ 2
  have hEa' : Ea ≤ (Ce : ℝ) ^ 2 *
      ∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g α t) ^ 2 := hEa
  have hEsq : Ea ≤ (η / D) ^ 2 := by
    apply (hEa'.trans (mul_le_mul_of_nonneg_left
      (hαE.trans (min_le_right _ _)) (sq_nonneg (Ce : ℝ)))).trans_eq
    field_simp
  have hsmall : D * Real.sqrt Ea ≤ η := by
    have hs := Real.sqrt_le_sqrt hEsq
    rw [Real.sqrt_sq (div_nonneg hη.le hD.le)] at hs
    exact (mul_le_mul_of_nonneg_left hs hD.le).trans_eq (mul_div_cancel₀ η hD.ne')
  obtain ⟨ψbar, h, q, hψbar, _, _, _, _, _, hqLip, hqrange, hseamF, hcaptrace, hqEnergy⟩ :=
    exists_boundary_cap_in_ball_of_short_lift_increment Γ hCγ hper hInv f hf ψ hψ hftrace
      hρ hρ1 hshort hsmall
  obtain ⟨Lq, hLq⟩ := hqLip
  have hseam : EqOn (r ∘ q) (diskExtension u) (closedBall (0 : ℂ) 1 ∩ sphere (-1) ρ) := by
    intro z hz
    rw [Function.comp_apply, hseamF hz]
    apply hleft
    have hzArc : z ∈ circleMap (-1) ρ '' Icc (-a) a := by
      rw [← sphere_inter_closedDisk_eq_inner_arc_image hρ (hρ1.le.trans (by norm_num))]
      exact ⟨hz.2, hz.1⟩
    obtain ⟨θ, hθ, rfl⟩ := hzArc
    have ha : 0 < a := Real.arccos_pos.mpr (by linarith)
    let t := (θ + a) / (2 * a)
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith [hθ.1]) (by positivity)
      · apply (div_le_one (by positivity : 0 < 2 * a)).mpr
        linarith [hθ.2]
    have heq : -a + 2 * a * t = θ := by dsimp [t]; field_simp; ring
    have hh := hαrange ht
    change diskExtension u (circleMap (-1) ρ (-a + 2 * a * t)) ∈ N at hh
    rwa [heq] at hh
  let τ := affineCircleMap ψbar hψbar ψbar.map_add_one
  have hτ : IsWeaklyMonotoneOnce τ :=
    ⟨ψbar, hψbar, fun _ => rfl, Or.inl ⟨ψbar.monotone, ψbar.map_add_one⟩⟩
  have hcap (θ : loopCircle) : attachBoundaryCap f q ρ (diskBoundary θ) = e (γ (τ θ)) := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    simpa only [τ, affineCircleMap_coe, diskBoundary_coe, circleMap_zero,
      Complex.ofReal_one, one_mul, Γ] using hcaptrace t
  have hIn (θ : loopCircle) (hθ : dist (diskBoundary θ : ℂ) (-1) ≤ ρ) :
      r (q (diskBoundary θ)) = γ (τ θ) := by
    have heq := attachBoundaryCap_inner f q ρ
      (by simpa only [dist_eq_norm, sub_neg_eq_add] using hθ)
    rw [← heq, hcap]
    exact hleft _ (hγN (mem_range_self _))
  have hOut (θ : loopCircle) (hθ : ρ ≤ dist (diskBoundary θ : ℂ) (-1)) :
      u (diskBoundary θ) = γ (τ θ) := by
    have heq := attachBoundaryCap_outer f q ρ hseamF (diskBoundary θ).property
      (by simpa only [dist_eq_norm, sub_neg_eq_add] using hθ)
    have hfval : r (f (diskBoundary θ)) = u (diskBoundary θ) := by
      change r (e (diskExtension u (diskBoundary θ))) = _
      rw [diskExtension_coe]
      obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
      rw [htrace]
      exact hleft _ (hγN (mem_range_self _))
    rw [← hfval, ← heq, hcap]
    exact hleft _ (hγN (mem_range_self _))
  have hpK : f (arc 0) ∈ K := by
    change e (α 0) ∈ range (fun θ : loopCircle => e (γ θ))
    rw [hα0]
    exact mem_range_self _
  have hqRange : MapsTo q (closedBall (0 : ℂ) 1 ∩ closedBall (-1) ρ)
      (closedBall (f (arc 0)) η) := fun z hz => hqrange ⟨hz.2, hz.1⟩
  have hbound := hlocal (f (arc 0)) hpK u q L Lq (-1) ρ hu hLq hqRange hseam γ τ hτ hIn hOut
    Λ hΛ hqm
  rw [inter_comm] at hbound
  have hqE : (∫ z in boundaryLens ρ,
      (‖fderiv ℝ q z 1‖ ^ 2 + ‖fderiv ℝ q z Complex.I‖ ^ 2) / 2) ≤ Q * Ea := hqEnergy
  have hb := mul_le_mul_of_nonneg_left hqE (sq_nonneg (Cr : ℝ))
  have hc := mul_le_mul_of_nonneg_left hEa' (mul_nonneg (sq_nonneg (Cr : ℝ)) hQ)
  have hfin : (Cr : ℝ) ^ 2 * (Q * Ea) ≤
      (Cr : ℝ) ^ 2 * Q * (Ce : ℝ) ^ 2 * ∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g α t) ^ 2 := by
    nlinarith only [hc]
  calc
    _ ≤ _ := hbound
    _ ≤ Λ * ((Cr : ℝ) ^ 2 * (Q * Ea)) := mul_le_mul_of_nonneg_left hb hΛ
    _ ≤ _ := mul_le_mul_of_nonneg_left hfin hΛ

theorem integral_annulus_closedDisk_eq_boundaryLens_sdiff_R7C (f : ℂ → ℝ) (a b : ℝ) :
    (∫ z in {z : ℂ | dist z (-1) ∈ Icc a b} ∩ closedBall (0 : ℂ) 1, f z) =
      ∫ z in boundaryLens b \ boundaryLens a, f z := by
  have hzero : ∀ᵐ z : ℂ ∂volume, z ∉ sphere (-1 : ℂ) a := by
    rw [ae_iff]
    convert Measure.addHaar_sphere volume (-1 : ℂ) a using 1
    congr 1
    ext z
    simp only [mem_ofPred_eq, not_not]
  apply setIntegral_congr_set
  filter_upwards [hzero] with z hz
  have hne : dist z (-1) ≠ a := hz
  apply propext
  change ((a ≤ dist z (-1) ∧ dist z (-1) ≤ b) ∧ dist z 0 ≤ 1) ↔
    ((dist z (-1) ≤ b ∧ dist z 0 ≤ 1) ∧ ¬ (dist z (-1) ≤ a ∧ dist z 0 ≤ 1))
  constructor
  · rintro ⟨⟨ha, hb⟩, hD⟩
    refine ⟨⟨hb, hD⟩, ?_⟩
    intro h
    exact hne (le_antisymm h.1 ha)
  · rintro ⟨⟨hb, hD⟩, hn⟩
    exact ⟨⟨le_of_not_ge (fun h => hn ⟨h, hD⟩), hb⟩, hD⟩


/-- 边界 lens hole-filling 的 quasi-minimal 版（R7C）：`ε₀, C` 只依赖 `(g, γ)`；若环形 lens 能量
`≤ ε₀`、lift 增量条件对 `ρ ∈ (s, 2s)` 成立、且 `u` 在每个 `B̄_ρ(−1)`（`ρ ∈ (s, 2s)`）上局部 `Λ`-quasi-minimal，
则 `E(u, lens s) ≤ Λ C (E(u, lens 2s) − E(u, lens s))`。证明照搬树内
`exists_uniform_intrinsic_boundary_energy_contraction`，cap 一步换
`boundary_cap_energy_bound_qm_R7C`。 -/
theorem boundary_lens_hole_filling_qm_R7C
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ (u : C(closedDisk, M)) (L : ℝ≥0),
      (∀ z w : closedDisk, riemannianEDistOf g (u z) (u w) ≤
        (L : ℝ≥0∞) * edist z w) →
      ∀ ψ : CircleDeg1Lift, Continuous ψ →
      (∀ t : ℝ, u (diskBoundary (t : loopCircle)) = γ ((ψ t : ℝ) : loopCircle)) →
      ∀ s : ℝ, 0 < s → s < 1 / 4 →
      (∀ ρ ∈ Ioo s (2 * s), ψ (1 - Real.arccos (ρ / 2) / Real.pi) -
        ψ (Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3) →
      (∫ z in {z : ℂ | dist z (-1) ∈ Icc s (2 * s)} ∩ closedBall (0 : ℂ) 1,
        diskMapEnergyDensity g (diskExtension u) z) ≤ ε₀ →
      ∀ Λ : ℝ, 0 ≤ Λ →
      (∀ ρ ∈ Ioo s (2 * s), ∀ (w : C(closedDisk, M)) (Lw : ℝ≥0),
        (∀ z z', riemannianEDistOf g (w z) (w z') ≤ (Lw : ℝ≥0∞) * edist z z') →
        DiskWeakJordanTrace γ w → (∀ z : closedDisk, ρ ≤ dist (z : ℂ) (-1) → w z = u z) →
        (∫ z in closedBall (0 : ℂ) 1 ∩ closedBall (-1) ρ,
          diskMapEnergyDensity g (diskExtension u) z) ≤
          Λ * ∫ z in closedBall (0 : ℂ) 1 ∩ closedBall (-1) ρ,
            diskMapEnergyDensity g (diskExtension w) z) →
      (∫ z in boundaryLens s, diskMapEnergyDensity g (diskExtension u) z) ≤
        Λ * C * ((∫ z in boundaryLens (2 * s), diskMapEnergyDensity g (diskExtension u) z) -
          ∫ z in boundaryLens s, diskMapEnergyDensity g (diskExtension u) z) := by
  obtain ⟨ε, Ccap, hε, hCcap, hcap⟩ := boundary_cap_energy_bound_qm_R7C g γ hγ
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwoπ : 0 < 2 * Real.pi := by positivity
  let ε₀ := ε * Real.log 2 / (2 * Real.pi)
  let C := Ccap * (2 * Real.pi) / Real.log 2
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hCcap htwoπ.le) hlog.le
  refine ⟨ε₀, C, div_pos (mul_pos hε hlog) htwoπ, hC, ?_⟩
  intro u L hu ψ hψ htrace s hs hsquarter hshort hsmall Λ hΛ hqm
  let d : ℂ → ℝ := diskMapEnergyDensity g (diskExtension u)
  let S := {z : ℂ | dist z (-1) ∈ Icc s (2 * s)} ∩ closedBall (0 : ℂ) 1
  let B := ∫ z in S, d z
  have hdi : IntegrableOn d (closedBall (0 : ℂ) 1) := integrable_diskMapEnergyDensity g hu
  have hd0 (z : ℂ) : 0 ≤ d z :=
    div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
      (metric_inner_self_nonneg g _ _)) (by norm_num)
  obtain ⟨ρ, hρ, hαI, hαE⟩ := exists_radius_normalized_crosscut_riemannian_energy_le g
    (diskExtension_riemannian_lipschitz g hu) hs (by linarith : s < 2 * s)
    (by linarith : 2 * s < 2) (le_refl B)
  let α : ℝ → M := fun t => diskExtension u
    (circleMap (-1) ρ (-Real.arccos (ρ / 2) + 2 * Real.arccos (ρ / 2) * t))
  let Ea := ∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g α t) ^ 2
  have hratio : (2 * s) / s = 2 := by field_simp [hs.ne']
  have hEa : Ea ≤ 2 * Real.pi * B / Real.log 2 := by
    simpa only [hratio] using hαE
  have hEasmall : Ea ≤ ε := by
    apply hEa.trans
    apply (div_le_iff₀ hlog).mpr
    have hBsmall : B ≤ ε₀ := hsmall
    have h := mul_le_mul_of_nonneg_left hBsmall htwoπ.le
    have heq : (2 * Real.pi) * ε₀ = ε * Real.log 2 := by
      dsimp only [ε₀]
      field_simp
    exact h.trans_eq heq
  have hlocal := hcap u L hu ψ hψ htrace ρ (hs.trans hρ.1)
    (by linarith [hρ.2] : ρ < 1) (hshort ρ hρ) hαI hEasmall Λ hΛ (hqm ρ hρ)
  have hsmallρ : boundaryLens s ⊆ boundaryLens ρ := fun z hz =>
    ⟨closedBall_subset_closedBall hρ.1.le hz.1, hz.2⟩
  have hmono : (∫ z in boundaryLens s, d z) ≤ ∫ z in boundaryLens ρ, d z :=
    setIntegral_mono_set (hdi.mono_set inter_subset_right) (Eventually.of_forall hd0)
      (Eventually.of_forall hsmallρ)
  have hcoeff : Ccap * (2 * Real.pi * B / Real.log 2) = C * B := by
    dsimp only [C]
    ring
  have hestimate : (∫ z in boundaryLens s, d z) ≤ Λ * (C * B) := by
    have hb := mul_le_mul_of_nonneg_left hEa hCcap
    rw [hcoeff] at hb
    exact hmono.trans (hlocal.trans (mul_le_mul_of_nonneg_left hb hΛ))
  have hsub : boundaryLens s ⊆ boundaryLens (2 * s) := fun z hz =>
    ⟨closedBall_subset_closedBall (by linarith : s ≤ 2 * s) hz.1, hz.2⟩
  have hAnn : B = (∫ z in boundaryLens (2 * s), d z) - ∫ z in boundaryLens s, d z := by
    rw [show B = ∫ z in {z : ℂ | dist z (-1) ∈ Icc s (2 * s)} ∩
      closedBall (0 : ℂ) 1, d z from rfl,
      integral_annulus_closedDisk_eq_boundaryLens_sdiff_R7C]
    exact setIntegral_sdiff (isClosed_closedBall.inter isClosed_closedBall).measurableSet
      (hdi.mono_set inter_subset_right) hsub
  rw [hAnn] at hestimate
  change (∫ z in boundaryLens s, d z) ≤
    Λ * C * ((∫ z in boundaryLens (2 * s), d z) - ∫ z in boundaryLens s, d z)
  linarith

end Main

end DifferentialGeometry.Geometry
