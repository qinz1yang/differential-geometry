import DifferentialGeometry.Geometry.MinimalSurface.Plateau.VaryingMetricCompactnessR7CQuasiMin
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.LocalDefect
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BoundarySmoothness
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.OpenTargetAdaptersADP
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ExistenceReduction

/-!
# R7C L4：内部 hole-filling（每个 Morrey 盘、常数只依赖 completion buffer）

`(W, Ĝ)` 为 `C` 的 completion buffer（HR，`Ĝ = G` 于 `O ⊆ W`）。对任何度量 `g` 满足 `g ≤ 2Ĝ` 于 `W`、
`G ≤ 2g` 于 `O`，以及任何像在 `O` 里、trace 为 smooth embedded loop `Γ` 的 `(M, g)`-Morrey 盘 `u`：
若环形区域 `{r ≤ |z − b| ≤ 2r}` 上 `G`-能量 `< ε₀`，则 `E_G(u, B̄_r(b)) ≤ K · E_G(u, 环)`，
`ε₀, K` 只依赖 `(W, Ĝ)`（树内 `exists_uniform_local_replacement_energy_comparison` 的常数）。
证明：树内半径选取 + HR 替换得 `Ĝ`-competitor `v`（`B̄_ρ(b)` 外 = `u`），再用 R7C 局部
quasi-minimality（`local_quasi_minimality_R7C`）比较——**无 defect 项**，所以对一切尺度、一切 `n` 成立。
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Bundle Manifold TopologicalSpace
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- 在闭集 `R` 外相同的两盘，`D \ R` 上的能量积分相同（R7C 辅助）。 -/
theorem setIntegral_diskMapEnergyDensity_diff_eq_R7C {N : Type*} [TopologicalSpace N]
    [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] (g : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {u v : C(closedDisk, N)}
    {R : Set ℂ} (hR : IsClosed R) (hout : ∀ z : closedDisk, (z : ℂ) ∉ R → v z = u z) :
    (∫ z in closedBall (0 : ℂ) 1 \ R, diskMapEnergyDensity g (diskExtension v) z) =
      ∫ z in closedBall (0 : ℂ) 1 \ R, diskMapEnergyDensity g (diskExtension u) z := by
  have hzin : ∀ᵐ z ∂volume.restrict (closedBall (0 : ℂ) 1 \ R), z ∈ ball (0 : ℂ) 1 :=
    ae_restrict_of_ae_restrict_of_subset sdiff_subset ae_disk_interior
  apply integral_congr_ae
  filter_upwards [hzin, ae_restrict_mem (measurableSet_closedBall.diff hR.measurableSet)]
    with z hz hzd
  have heq : diskExtension v =ᶠ[𝓝 z] diskExtension u := by
    filter_upwards [(isOpen_ball.inter hR.isOpen_compl).mem_nhds ⟨hz, hzd.2⟩] with y hy
    let q : closedDisk := ⟨y, ball_subset_closedBall hy.1⟩
    rw [diskExtension_coe v q, diskExtension_coe u q]
    exact hout q hy.2
  unfold diskMapEnergyDensity diskMapPartial
  rw [heq.mfderiv_eq, heq.eq_of_nhds]
  rfl

/-- lift 到 completion buffer 后能量密度不变（R7C）：`u` 像在 `O`、`Ĝ = G` 于 `O` ⇒
`e_Ĝ(u') = e_G(u)` 逐点（`u'` 为 `u` 的 `W`-lift）。 -/
theorem diskMapEnergyDensity_lift_eq_R7C [T2Space M] {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (W : Opens M) (Ghat : SmoothRiemannianMetric 𝓘(ℝ, E) W) {O : Set M}
    (hagree : ∀ x : W, (x : M) ∈ O → Ghat.inner x = G.inner x)
    {u : C(closedDisk, M)} (huO : range u ⊆ O) (u' : C(closedDisk, W))
    (hu' : ∀ z, (u' z : M) = u z) (z : ℂ) :
    diskMapEnergyDensity Ghat (diskExtension u') z =
      diskMapEnergyDensity G (diskExtension u) z := by
  have hzO : ((diskExtension u' z : W) : M) ∈ O := by
    have hq : diskExtension u' z = u' (diskRetraction z) := rfl
    rw [hq, hu']
    exact huO ⟨_, rfl⟩
  rw [show diskExtension u = Subtype.val ∘ diskExtension u' from
    funext fun y => (hu' _).symm, ← diskMapEnergyDensity_restrictOpen G W]
  unfold diskMapEnergyDensity
  rw [hagree _ hzO]
  rfl

/-- **L4 内部 hole-filling**（R7C）：见文件头。常数 `ε₀, K` 只依赖 `(W, Ĝ)`。 -/
theorem interior_hole_filling_R7C [T3Space M] {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (W : Opens M) (Ghat : SmoothRiemannianMetric 𝓘(ℝ, E) W) {O : Set M}
    (hHR : HomogeneouslyRegularMetric Ghat) (hOW : O ⊆ (W : Set M))
    (hagree : ∀ x : W, (x : M) ∈ O → Ghat.inner x = G.inner x) :
    ∃ ε₀ K : ℝ, 0 < ε₀ ∧ 0 < K ∧ ∀ g : SmoothRiemannianMetric 𝓘(ℝ, E) M,
      (∀ (x : W) (v : TangentSpace 𝓘(ℝ, E) x), g.inner x v v ≤ 2 * Ghat.inner x v v) →
      (∀ x ∈ O, ∀ v : TangentSpace 𝓘(ℝ, E) x, G.inner x v v ≤ 2 * g.inner x v v) →
      ∀ (Γ : freeLoop M) (u : C(closedDisk, M)), IsSmoothEmbeddedLoop (E := E) Γ →
      IsMorreyDisk g Γ u → range u ⊆ O →
      ∀ (b : ℂ) (r : ℝ), 0 < r → ‖b‖ + 2 * r < 1 →
      (∫ z in {z : ℂ | dist z b ∈ Icc r (2 * r)},
        diskMapEnergyDensity G (diskExtension u) z) < ε₀ →
      (∫ z in closedBall b r, diskMapEnergyDensity G (diskExtension u) z) ≤
        K * ∫ z in {z : ℂ | dist z b ∈ Icc r (2 * r)},
          diskMapEnergyDensity G (diskExtension u) z := by
  obtain ⟨εt, Ct, hεt, hCt, hrep⟩ := exists_uniform_local_replacement_energy_comparison Ghat hHR
  refine ⟨εt / (8 * Real.pi), 32 * Real.pi * Ct, by positivity, by positivity, ?_⟩
  intro g hup hlo Γ u hΓ hu huO b r hr hbr hsmall
  set Ann : Set ℂ := {z : ℂ | dist z b ∈ Icc r (2 * r)} with hAnn
  have huW : range u ⊆ (W : Set M) := huO.trans hOW
  set u' : C(closedDisk, W) := liftToOpen_AT u huW with hu'def
  have hu' : ∀ z, (u' z : M) = u z := fun _ => rfl
  have hval : (ContinuousMap.mk Subtype.val continuous_subtype_val).comp u' = u := by
    ext z
    rfl
  obtain ⟨σ, hσ, htr⟩ := hu.trace
  obtain ⟨Q, hQ⟩ := exists_smooth_extension_of_conformal_harmonic_disk g hΓ u hu.smoothInterior
    hu.conformal hu.harmonic σ htr
  obtain ⟨V, hV, _⟩ := smoothDiskExtension_liftToOpen_ADP hQ huW
  obtain ⟨L, hL⟩ := hV.lipschitz Ghat
  -- `Γ` 的 `W`-lift
  have hΓW : ∀ θ, Γ θ ∈ (W : Set M) := by
    intro θ
    obtain ⟨θ', hθ'⟩ := IsWeaklyMonotoneOnce.surjective hσ θ
    have h := congrArg (fun f : freeLoop M => f θ') htr
    change u (diskBoundary θ') = Γ (σ θ') at h
    rw [← hθ', ← h]
    exact huW ⟨_, rfl⟩
  let Γ' : freeLoop W := ⟨fun θ => ⟨Γ θ, hΓW θ⟩, Γ.continuous.subtype_mk _⟩
  have hu'tr : DiskWeakJordanTrace Γ' u' :=
    diskWeakJordanTrace_of_comp_val_ADP (Γ := Γ') (γ := Γ) (fun _ => rfl)
      (by rw [hval]; exact hu.trace)
  have hu'mem : u' ∈ weaklyMonotoneDiskCompetitors Ghat Γ' := ⟨hu'tr, L, hL⟩
  have hdens : ∀ z, diskMapEnergyDensity Ghat (diskExtension u') z =
      diskMapEnergyDensity G (diskExtension u) z :=
    diskMapEnergyDensity_lift_eq_R7C W Ghat hagree huO u' hu'
  -- 半径选取
  obtain ⟨ρ, hρ, hint, hS⟩ := exists_radius_circle_energy_le_annular_disk_energy_at Ghat
    (diskExtension_riemannian_lipschitz Ghat hL) b hr (by linarith : r < 2 * r)
  have hρ0 : 0 < ρ := hr.trans_le hρ.1
  have hρb : ‖b‖ + ρ < 1 := by linarith [hρ.2]
  set S := ∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed Ghat
    (fun s => diskExtension u' (b + ρ • circleMap 0 1 (2 * Real.pi * s - Real.pi))) t) ^ 2
    with hSdef
  have hcoef : 4 * Real.pi * (2 * r) / (2 * r - r) = 8 * Real.pi := by
    field_simp
    ring
  have hAnnEq : (∫ z in Ann, diskMapEnergyDensity Ghat (diskExtension u') z) =
      ∫ z in Ann, diskMapEnergyDensity G (diskExtension u) z :=
    integral_congr_ae (Eventually.of_forall hdens)
  rw [hcoef, hAnnEq] at hS
  have hS8 : S < εt := by
    have h8 : 8 * Real.pi * (∫ z in Ann, diskMapEnergyDensity G (diskExtension u) z) <
        8 * Real.pi * (εt / (8 * Real.pi)) := mul_lt_mul_of_pos_left hsmall (by positivity)
    rw [mul_div_cancel₀ _ (by positivity)] at h8
    exact hS.trans_lt h8
  obtain ⟨v, hv, hvtr, hvout, _, hvE⟩ := hrep Γ' u' hu'mem b ρ hρ0 hρb hint hS8
  -- `v` 的 `M`-trace 类仍是 `Γ`
  have hvΓ : DiskWeakJordanTrace Γ
      ((ContinuousMap.mk Subtype.val continuous_subtype_val).comp v) := by
    refine ⟨σ, hσ, ?_⟩
    ext θ
    have h1 := congrArg (fun f : freeLoop W => (f θ : M)) hvtr
    have h2 := congrArg (fun f : freeLoop M => f θ) htr
    change ((v (diskBoundary θ) : W) : M) = ((u' (diskBoundary θ) : W) : M) at h1
    change u (diskBoundary θ) = Γ (σ θ) at h2
    change ((v (diskBoundary θ) : W) : M) = Γ (σ θ)
    rw [h1, hu', h2]
  obtain ⟨_, Lv, hvL⟩ := hv
  set R : Set ℂ := closedBall b ρ with hRdef
  have hR : IsClosed R := isClosed_closedBall
  have hRD : R ⊆ closedBall (0 : ℂ) 1 := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    have := norm_le_norm_add_norm_sub' z b
    rw [mem_closedBall, dist_eq_norm] at hz
    linarith
  have hout : ∀ z : closedDisk, (z : ℂ) ∉ R → v z = u' z := fun z hz =>
    hvout z (le_of_lt (not_le.mp hz))
  have hqm := local_quasi_minimality_R7C W Ghat hup hlo (fun x hx => hagree x hx) hu huO u' hu'
    v hvΓ hvL hR hout
  rw [inter_eq_right.mpr hRD] at hqm
  -- `∫_R e_Ĝ(v) ≤ Ct · S`
  have hiu' : IntegrableOn (diskMapEnergyDensity Ghat (diskExtension u')) (closedBall (0 : ℂ) 1) :=
    integrable_diskMapEnergyDensity Ghat hL
  have hiv : IntegrableOn (diskMapEnergyDensity Ghat (diskExtension v)) (closedBall (0 : ℂ) 1) :=
    integrable_diskMapEnergyDensity Ghat hvL
  have hsplit_u := setIntegral_sdiff hR.measurableSet hiu' hRD
  have hsplit_v := setIntegral_sdiff hR.measurableSet hiv hRD
  have hdiff := setIntegral_diskMapEnergyDensity_diff_eq_R7C Ghat hR hout
  have hvR : (∫ z in R, diskMapEnergyDensity Ghat (diskExtension v) z) ≤ Ct * S := by
    change riemannianDiskEnergy Ghat v ≤ riemannianDiskEnergy Ghat u' -
      (∫ z in R, diskMapEnergyDensity Ghat (diskExtension u') z) + Ct * S at hvE
    unfold riemannianDiskEnergy at hvE
    linarith
  -- 汇总
  have hmono : (∫ z in closedBall b r, diskMapEnergyDensity G (diskExtension u) z) ≤
      ∫ z in R, diskMapEnergyDensity G (diskExtension u) z := by
    have hiG : IntegrableOn (diskMapEnergyDensity G (diskExtension u)) R :=
      (hiu'.mono_set hRD).congr_fun (fun z _ => hdens z) hR.measurableSet
    exact setIntegral_mono_set hiG
      (Eventually.of_forall fun z => div_nonneg (add_nonneg (metric_inner_self_nonneg _ _ _)
        (metric_inner_self_nonneg _ _ _)) (by norm_num))
      (Eventually.of_forall (closedBall_subset_closedBall hρ.1))
  have hRG : (∫ z in R, diskMapEnergyDensity G (diskExtension u) z) =
      ∫ z in R, diskMapEnergyDensity Ghat (diskExtension u') z :=
    integral_congr_ae (Eventually.of_forall fun z => (hdens z).symm)
  have hCtS : Ct * S ≤ Ct * (8 * Real.pi *
      ∫ z in Ann, diskMapEnergyDensity G (diskExtension u) z) :=
    mul_le_mul_of_nonneg_left hS hCt.le
  nlinarith [hmono, hRG, hqm, hvR, hCtS]

end DifferentialGeometry.Geometry
