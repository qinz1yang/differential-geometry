import DifferentialGeometry.Geometry.MinimalSurface.Plateau.VaryingMetricCompactnessR7CBoundaryDecay
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.VaryingMetricCompactnessR7CLift
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CourantLebesgueR7A
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CoveringLift
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

/-!
# R7C L5（五）：R7 设定下的边界一致 Morrey decay（序列版，G3 consumer）

R7 设定（`[SecondCountableTopology M]`、`finrank E = 3`、`C ⊆ int B`、S-MY-R7A 形相对度量收敛 `hrel` 于 `B`、
smooth embedded `Γ`、三点归一 `huθ`（`θ` 单射）、`Gₙ`-Morrey `uₙ` 像在 `C`、面积一致界 `Λ`）下：
**终将**对每个边界点 `c` 有 `E_G(uₙ, B̄_{s₀/2^{K+k}}(c) ∩ D) ≤ θ^k ε₀`，常数与 `n, c` 无关。
组装：completion buffer（`exists_completion_buffer_R7C`）上 lift `uₙ' , Γ'`；局部 quasi-minimality
（`local_quasi_minimality_R7C`，`Λ = 4`）；三点不动 ⇒ 单调 lift（`exists_monotone_lift_of_three_fixed_R7C`）；
S-MY-R7A `courant_lebesgue_equicontinuity_varying_R7A`（`ε = 1/2`）+ 介值 ⇒ lift 增量模；
`boundary_dyadic_decay_R7C`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Bundle Manifold TopologicalSpace
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **G3 consumer**（R7C）：见文件头。 -/
theorem eventually_boundary_dyadic_decay_R7C [T3Space M] [SecondCountableTopology M]
    (hdim : Module.finrank ℝ E = 3) {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {B C : Set M} (hC : IsCompact C)
    (hCB : C ⊆ interior B)
    (hrel : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ B, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      |(Gn n).inner x v v - G.inner x v v| ≤ ε * G.inner x v v)
    {Γ : freeLoop M} (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) (θ : Fin 3 → loopCircle)
    (hθ : Function.Injective θ)
    {u : ℕ → C(closedDisk, M)} (hu : ∀ n, IsMorreyDisk (Gn n) Γ (u n))
    (huC : ∀ n, range (u n) ⊆ C) (huθ : ∀ n j, diskTrace (u n) (θ j) = Γ (θ j))
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hA : ∀ n, riemannianDiskArea (Gn n) (u n) ≤ Λ) :
    ∃ (K : ℕ) (θd ε₀ s₀ : ℝ), 0 ≤ θd ∧ θd < 1 ∧ 0 < ε₀ ∧ 0 < s₀ ∧ s₀ ≤ 1 / 8 ∧
      ∀ᶠ n in atTop, ∀ c ∈ sphere (0 : ℂ) 1, ∀ k : ℕ,
        (∫ z in closedBall c (s₀ / 2 ^ (K + k)) ∩ closedBall (0 : ℂ) 1,
          diskMapEnergyDensity G (diskExtension (u n)) z) ≤ θd ^ k * ε₀ := by
  obtain ⟨W, Ghat, O, _, hCO, hOW, hWB, _, _, hGle, hgerm⟩ :=
    exists_completion_buffer_R7C hdim G hC hCB
  have hagree : ∀ x : W, (x : M) ∈ O → Ghat.inner x = G.inner x := by
    intro x hx
    have h := (hgerm x hx).self_of_nhds
    rw [h]
    ext v w
    exact SmoothRiemannianMetric.restrictOpen_inner G W x v w
  have hWB' : (W : Set M) ⊆ B := subset_closure.trans (hWB.trans interior_subset)
  have huB : ∀ n, range (u n) ⊆ B := fun n =>
    (huC n).trans (hCO.trans (hOW.trans hWB'))
  -- `Γ` 落在 `W` 里，其 lift `Γ'` 是 smooth embedded loop
  have hΓW : ∀ t, Γ t ∈ (W : Set M) := by
    intro t
    obtain ⟨σ, hσ, htr⟩ := (hu 0).trace
    obtain ⟨t', ht'⟩ := IsWeaklyMonotoneOnce.surjective hσ t
    have h := congrArg (fun f : freeLoop M => f t') htr
    change u 0 (diskBoundary t') = Γ (σ t') at h
    rw [← ht', ← h]
    exact hOW (hCO (huC 0 ⟨_, rfl⟩))
  let Γ' : freeLoop W := ⟨fun t => ⟨Γ t, hΓW t⟩, Γ.continuous.subtype_mk _⟩
  have hΓ' : IsSmoothEmbeddedLoop (E := E) Γ' :=
    hΓ.of_lift_through_localDiffeomorph (DifferentialGeometry.isLocalDiffeomorph_subtype_val W)
      Γ' (fun _ => rfl)
  obtain ⟨η, hη, hev⟩ := courant_lebesgue_equicontinuity_varying_R7A hrel hΓ θ hθ hu huB huθ
    hΛ0 hA (ε := 1 / 2) (by norm_num)
  obtain ⟨K, θd, ε₀, s₀, hθ0, hθ1, hε₀, hs₀, hs₀8, hdec⟩ :=
    boundary_dyadic_decay_R7C Ghat Γ' hΓ' (Λ := 4) (E₀ := 2 * Λ) (η := η / 2) (by norm_num)
      (by linarith) (half_pos hη)
  refine ⟨K, θd, ε₀, s₀, hθ0, hθ1, hε₀, hs₀, hs₀8, ?_⟩
  filter_upwards [hev, hrel (1 / 2) (by norm_num)] with n hn hrn
  have hup : ∀ (x : W) (v : TangentSpace 𝓘(ℝ, E) x),
      (Gn n).inner x v v ≤ 2 * Ghat.inner x v v := by
    intro x v
    have h1 := (abs_le.mp (hrn x (hWB' x.property) v)).2
    have h2 := hGle x v
    rw [SmoothRiemannianMetric.restrictOpen_inner] at h2
    have h3 := metric_inner_self_nonneg G (x : M) v
    linarith
  have hlo : ∀ x ∈ O, ∀ v : TangentSpace 𝓘(ℝ, E) x, G.inner x v v ≤ 2 * (Gn n).inner x v v := by
    intro x hx v
    have h1 := (abs_le.mp (hrn x (hWB' (hOW hx)) v)).1
    linarith
  have huO : range (u n) ⊆ O := (huC n).trans hCO
  have huW : range (u n) ⊆ (W : Set M) := huO.trans hOW
  set u' : C(closedDisk, W) := liftToOpen_AT (u n) huW with hu'def
  have hu' : ∀ z, (u' z : M) = u n z := fun _ => rfl
  obtain ⟨σ, hσ, htr⟩ := (hu n).trace
  obtain ⟨Q, hQ⟩ := exists_smooth_extension_of_conformal_harmonic_disk (Gn n) hΓ (u n)
    (hu n).smoothInterior (hu n).conformal (hu n).harmonic σ htr
  obtain ⟨V, hV, _⟩ := smoothDiskExtension_liftToOpen_ADP hQ huW
  obtain ⟨L, hL⟩ := hV.lipschitz Ghat
  -- 单调 lift
  have hfix : ∀ j, σ (θ j) = θ j := by
    intro j
    apply hΓ.embedding.injective
    have h := congrArg (fun f : freeLoop M => f (θ j)) htr
    change diskTrace (u n) (θ j) = Γ (σ (θ j)) at h
    rw [← h, huθ n j]
  obtain ⟨ψ, hψc, hψl, hψm, hψp⟩ := exists_monotone_lift_of_three_fixed_R7C hσ θ hθ hfix
  let ψL : CircleDeg1Lift := ⟨⟨ψ, hψm⟩, hψp⟩
  have hψLc : Continuous ψL := hψc
  have htr' : ∀ t : ℝ, u' (diskBoundary (t : loopCircle)) = Γ' ((ψL t : ℝ) : loopCircle) := by
    intro t
    apply Subtype.ext
    change u n (diskBoundary (t : loopCircle)) = Γ ((ψ t : ℝ) : loopCircle)
    have h := congrArg (fun f : freeLoop M => f (t : loopCircle)) htr
    change u n (diskBoundary (t : loopCircle)) = Γ (σ (t : loopCircle)) at h
    rw [h, hψl]
  have hinc := lift_increment_lt_of_circle_modulus_R7C hψc hψl (by norm_num)
    (hn σ hσ htr)
  have hmod : ∀ a b : ℝ, a ≤ b → b - a ≤ η / 2 → ψL b - ψL a ≤ 2 / 3 := by
    intro a b hab hba
    have := hinc a b hab (by linarith)
    change ψ b - ψ a ≤ 2 / 3
    linarith
  -- 能量界
  have hdens : ∀ z, diskMapEnergyDensity Ghat (diskExtension u') z =
      diskMapEnergyDensity G (diskExtension (u n)) z :=
    diskMapEnergyDensity_lift_eq_R7C W Ghat hagree huO u' hu'
  have hpt : ∀ z, diskMapEnergyDensity G (diskExtension (u n)) z ≤
      2 * diskMapEnergyDensity (Gn n) (diskExtension (u n)) z := by
    intro z
    have hx := hrn (diskExtension (u n) z) (huB n ⟨diskRetraction z, rfl⟩)
    have h1 := (abs_le.mp (hx (diskMapPartial (diskExtension (u n)) z 1))).1
    have h2 := (abs_le.mp (hx (diskMapPartial (diskExtension (u n)) z Complex.I))).1
    unfold diskMapEnergyDensity
    linarith
  have hEn : (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity (Gn n) (diskExtension (u n)) z) = riemannianDiskArea (Gn n) (u n) := by
    unfold riemannianDiskArea riemannianArea
    apply integral_congr_ae
    filter_upwards [ae_disk_interior] with z hz
    exact diskMapEnergyDensity_eq_areaDensity_of_conformal_R7A (Gn n) ((hu n).conformal z hz)
  have hE' : (∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity Ghat (diskExtension u') z) ≤
      2 * Λ := by
    rw [integral_congr_ae (Eventually.of_forall hdens)]
    calc (∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity G (diskExtension (u n)) z)
        ≤ ∫ z in closedBall (0 : ℂ) 1,
            2 * diskMapEnergyDensity (Gn n) (diskExtension (u n)) z :=
          integral_mono_of_nonneg (Eventually.of_forall fun z => div_nonneg
            (add_nonneg (metric_inner_self_nonneg G _ _) (metric_inner_self_nonneg G _ _))
            (by norm_num)) ((hu n).finiteEnergy.const_mul 2) (Eventually.of_forall hpt)
      _ = 2 * riemannianDiskArea (Gn n) (u n) := by rw [integral_const_mul, hEn]
      _ ≤ 2 * Λ := by linarith [hA n]
  -- 局部 quasi-minimality（一切中心）
  have hqm : ∀ (c : ℂ) (s : ℝ) (w : C(closedDisk, W)) (Lw : ℝ≥0),
      (∀ z z', riemannianEDistOf Ghat (w z) (w z') ≤ (Lw : ℝ≥0∞) * edist z z') →
      DiskWeakJordanTrace Γ' w → (∀ z : closedDisk, s ≤ dist (z : ℂ) c → w z = u' z) →
      (∫ z in closedBall (0 : ℂ) 1 ∩ closedBall c s,
        diskMapEnergyDensity Ghat (diskExtension u') z) ≤
        4 * ∫ z in closedBall (0 : ℂ) 1 ∩ closedBall c s,
          diskMapEnergyDensity Ghat (diskExtension w) z := by
    intro c s w Lw hwL hwΓ hwout
    have hwΓ' : DiskWeakJordanTrace Γ
        ((ContinuousMap.mk Subtype.val continuous_subtype_val).comp w) := by
      obtain ⟨σw, hσw, htrw⟩ := hwΓ
      refine ⟨σw, hσw, ?_⟩
      ext t
      have h := congrArg (fun f : freeLoop W => (f t : M)) htrw
      exact h
    exact local_quasi_minimality_R7C W Ghat hup hlo hagree (hu n) huO u' hu' w hwΓ' hwL
      isClosed_closedBall (fun z hz => hwout z (le_of_lt (not_le.mp hz)))
  intro c hc k
  have h := hdec u' L hL ψL hψLc htr' hmod hE' hqm c hc k
  rwa [integral_congr_ae (Eventually.of_forall hdens)] at h

end DifferentialGeometry.Geometry
