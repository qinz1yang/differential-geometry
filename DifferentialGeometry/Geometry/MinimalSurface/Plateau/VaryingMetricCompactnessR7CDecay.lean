import DifferentialGeometry.Geometry.MinimalSurface.Plateau.VaryingMetricCompactnessR7CHoleFilling
import DifferentialGeometry.Analysis.Asymptotics.SmallDrop

/-!
# R7C L4：内部一致 Morrey decay（无 energy concentration）

由 `interior_hole_filling_R7C`（每个 Morrey 盘、常数只依赖 completion buffer）出发：
- 纯实数引理 `dyadic_decay_of_hole_filling_R7C`：单调序列 `e_j = E(B̄_{R/2^j}(b))`，若"环能量 `< ε₀` ⇒
  `e_{j+1} ≤ K (e_j − e_{j+1})`"，且 `e_0 ≤ Λ`，则存在只依赖 `(ε₀, K, Λ)` 的 `N` 使
  `e_{N+k} ≤ θ^k ε₀`（`θ = K/(1+K)`）——小下降引理（树内 `exists_uniform_index_energy_le_of_small_drop`，
  defect 取 0）给出起点，之后 hole-filling 逐级生效；
- 盘版本 `interior_dyadic_decay_R7C`：对一切满足比较假设的 `(g, Γ, u)`（`E_G(u) ≤ Λ`）与内部球
  `B̄_R(b) ⊆ D°`，`E_G(u, B̄_{R/2^{N+k}}(b)) ≤ θ^k ε₀`。`N, θ` 与 `u, g, b, R` 无关——这就是
  "concentration set = ∅" 的一致定量形（route M，`design-R7-compactness-20261006.md` §0）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Bundle Manifold TopologicalSpace
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

/-- 二进 hole-filling 的一致 decay（纯实数，R7C）：见文件头。 -/
theorem dyadic_decay_of_hole_filling_R7C {ε₀ K Λ : ℝ} (hε₀ : 0 < ε₀) (hK : 0 < K)
    (hΛ : 0 ≤ Λ) :
    ∃ N : ℕ, ∀ e : ℕ → ℝ, Antitone e → (∀ k, 0 ≤ e k) → e 0 ≤ Λ →
      (∀ j, e j - e (j + 1) < ε₀ → e (j + 1) ≤ K * (e j - e (j + 1))) →
      ∀ k, e (N + k) ≤ (K / (1 + K)) ^ k * ε₀ := by
  obtain ⟨N, _, hN⟩ := DifferentialGeometry.Analysis.exists_uniform_index_energy_le_of_small_drop
    hε₀ hK hΛ (half_pos hε₀)
  refine ⟨N, fun e he he0 heΛ hdrop k => ?_⟩
  have hdrop0 : ∀ j, e j - e (j + 1) < ε₀ → e (j + 1) ≤ K * (e j - e (j + 1)) + 0 :=
    fun j hj => by rw [add_zero]; exact hdrop j hj
  have heN : e N ≤ ε₀ / 2 + 0 := hN e 0 he he0 heΛ hdrop0
  rw [add_zero] at heN
  induction k with
  | zero => simpa only [add_zero, pow_zero, one_mul] using heN.trans (half_le_self hε₀.le)
  | succ k ih =>
    have hlt : e (N + k) - e (N + k + 1) < ε₀ := by
      have h1 := he0 (N + k + 1)
      have h2 : e (N + k) ≤ ε₀ / 2 := (he (Nat.le_add_right N k)).trans heN
      linarith
    have hstep := hdrop (N + k) hlt
    have hθ : e (N + k + 1) ≤ K / (1 + K) * e (N + k) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      nlinarith
    rw [← add_assoc, pow_succ]
    calc e (N + k + 1) ≤ K / (1 + K) * e (N + k) := hθ
      _ ≤ K / (1 + K) * ((K / (1 + K)) ^ k * ε₀) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (K / (1 + K)) ^ k * (K / (1 + K)) * ε₀ := by ring

/-- 环能量 = 两闭球能量之差（R7C，同树内 private `integral_annulus_eq_sub_closedBall`）。 -/
theorem integral_annulus_eq_sub_closedBall_R7C
    {f : ℂ → ℝ} {b : ℂ} {r R : ℝ} (hrR : r ≤ R)
    (hf : IntegrableOn f (closedBall b R)) :
    (∫ z in {z : ℂ | dist z b ∈ Icc r R}, f z) =
      (∫ z in closedBall b R, f z) - ∫ z in closedBall b r, f z := by
  have heq : {z : ℂ | dist z b ∈ Icc r R} =ᵐ[volume]
      closedBall b R \ closedBall b r := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp (Measure.addHaar_sphere volume b r)]
      with z hz
    have hne : dist z b ≠ r := by simpa only [mem_sphere] using hz
    apply propext
    change (r ≤ dist z b ∧ dist z b ≤ R) ↔ (dist z b ≤ R ∧ ¬ dist z b ≤ r)
    constructor
    · rintro ⟨hr, hR⟩
      exact ⟨hR, not_le.mpr (lt_of_le_of_ne hr (Ne.symm hne))⟩
    · rintro ⟨hR, hr⟩
      exact ⟨(lt_of_not_ge hr).le, hR⟩
  rw [setIntegral_congr_set heq]
  exact setIntegral_sdiff measurableSet_closedBall hf (closedBall_subset_closedBall hrR)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **L4 内部一致 Morrey decay**（R7C）：completion buffer `(W, Ĝ, O)` 固定，对一切满足
`g ≤ 2Ĝ`（于 `W`）、`G ≤ 2g`（于 `O`）的度量 `g`、smooth embedded `Γ`、像在 `O` 且 `E_G(u) ≤ Λ` 的
`(M, g)`-Morrey 盘 `u`，以及内部球 `‖b‖ + R < 1`：`E_G(u, B̄_{R/2^{N+k}}(b)) ≤ θ^k ε₀`，`N, θ < 1, ε₀`
只依赖 `(W, Ĝ, Λ)`。 -/
theorem interior_dyadic_decay_R7C [T3Space M] {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (W : Opens M) (Ghat : SmoothRiemannianMetric 𝓘(ℝ, E) W) {O : Set M}
    (hHR : HomogeneouslyRegularMetric Ghat) (hOW : O ⊆ (W : Set M))
    (hagree : ∀ x : W, (x : M) ∈ O → Ghat.inner x = G.inner x) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ∃ (N : ℕ) (θ ε₀ : ℝ), 0 ≤ θ ∧ θ < 1 ∧ 0 < ε₀ ∧ ∀ g : SmoothRiemannianMetric 𝓘(ℝ, E) M,
      (∀ (x : W) (v : TangentSpace 𝓘(ℝ, E) x), g.inner x v v ≤ 2 * Ghat.inner x v v) →
      (∀ x ∈ O, ∀ v : TangentSpace 𝓘(ℝ, E) x, G.inner x v v ≤ 2 * g.inner x v v) →
      ∀ (Γ : freeLoop M) (u : C(closedDisk, M)), IsSmoothEmbeddedLoop (E := E) Γ →
      IsMorreyDisk g Γ u → range u ⊆ O →
      (∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity G (diskExtension u) z) ≤ Λ →
      ∀ (b : ℂ) (R : ℝ), 0 < R → ‖b‖ + R < 1 → ∀ k : ℕ,
        (∫ z in closedBall b (R / 2 ^ (N + k)), diskMapEnergyDensity G (diskExtension u) z) ≤
          θ ^ k * ε₀ := by
  obtain ⟨ε₀, K, hε₀, hK, hhole⟩ := interior_hole_filling_R7C W Ghat hHR hOW hagree
  obtain ⟨N, hN⟩ := dyadic_decay_of_hole_filling_R7C hε₀ hK hΛ
  refine ⟨N, K / (1 + K), ε₀, by positivity, by rw [div_lt_one (by linarith)]; linarith, hε₀,
    ?_⟩
  intro g hup hlo Γ u hΓ hu huO hΛu b R hR hbR k
  set e : ℕ → ℝ := fun j =>
    ∫ z in closedBall b (R / 2 ^ j), diskMapEnergyDensity G (diskExtension u) z with hedef
  -- 可积性：`e_G(u) = e_Ĝ(u')`，后者因 `u'` 的 `Ĝ`-Lipschitz 可积
  have huW : range u ⊆ (W : Set M) := huO.trans hOW
  obtain ⟨σ, hσ, htr⟩ := hu.trace
  obtain ⟨Q, hQ⟩ := exists_smooth_extension_of_conformal_harmonic_disk g hΓ u hu.smoothInterior
    hu.conformal hu.harmonic σ htr
  obtain ⟨V, hV, _⟩ := smoothDiskExtension_liftToOpen_ADP hQ huW
  obtain ⟨L, hL⟩ := hV.lipschitz Ghat
  have hint : IntegrableOn (diskMapEnergyDensity G (diskExtension u)) (closedBall (0 : ℂ) 1) :=
    (integrable_diskMapEnergyDensity Ghat hL).congr_fun
      (fun z _ => diskMapEnergyDensity_lift_eq_R7C W Ghat hagree huO _ (fun _ => rfl) z)
      measurableSet_closedBall
  have hn : ∀ z, 0 ≤ diskMapEnergyDensity G (diskExtension u) z := fun z =>
    div_nonneg (add_nonneg (metric_inner_self_nonneg G _ _) (metric_inner_self_nonneg G _ _))
      (by norm_num)
  have hrad : ∀ j : ℕ, 0 < R / 2 ^ j := fun j => by positivity
  have hradanti : Antitone fun j : ℕ => R / 2 ^ j := fun i j hij =>
    div_le_div_of_nonneg_left hR.le (by positivity) (pow_le_pow_right₀ (by norm_num) hij)
  have hball : ∀ j : ℕ, closedBall b (R / 2 ^ j) ⊆ closedBall (0 : ℂ) 1 := by
    intro j z hz
    have h1 := mem_closedBall.mp hz
    have h2 : R / 2 ^ j ≤ R := by simpa using hradanti (Nat.zero_le j)
    have h3 : ‖z‖ ≤ dist z b + ‖b‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - b) b
    exact mem_closedBall.mpr (by rw [dist_zero_right]; linarith)
  have he0 : ∀ j, 0 ≤ e j := fun j => integral_nonneg hn
  have heanti : Antitone e := fun i j hij =>
    setIntegral_mono_set (hint.mono_set (hball i)) (Eventually.of_forall hn)
      (Eventually.of_forall (closedBall_subset_closedBall (hradanti hij)))
  have heΛ : e 0 ≤ Λ := (setIntegral_mono_set hint (Eventually.of_forall hn)
    (Eventually.of_forall (hball 0))).trans hΛu
  have hdrop : ∀ j, e j - e (j + 1) < ε₀ → e (j + 1) ≤ K * (e j - e (j + 1)) := by
    intro j hj
    have hstep : R / 2 ^ j = 2 * (R / 2 ^ (j + 1)) := by
      rw [pow_succ]
      field_simp
    have hann := integral_annulus_eq_sub_closedBall_R7C (b := b)
      (r := R / 2 ^ (j + 1)) (R := 2 * (R / 2 ^ (j + 1))) (by linarith [hrad (j + 1)])
      (by rw [← hstep]; exact hint.mono_set (hball j))
    rw [← hstep] at hann
    have hbr : ‖b‖ + 2 * (R / 2 ^ (j + 1)) < 1 := by
      rw [← hstep]
      linarith [hradanti (Nat.zero_le j), show R / 2 ^ 0 = R by simp]
    have h := hhole g hup hlo Γ u hΓ hu huO b (R / 2 ^ (j + 1)) (hrad _) hbr
      (by rw [← hstep, hann]; exact hj)
    rw [← hstep, hann] at h
    exact h
  exact hN e heanti he0 heΛ hdrop k

/-- **G2 consumer**（R7C）：R7 设定（`[SecondCountableTopology M]`、`finrank E = 3`、`C ⊆ int B`、R7A 的
相对度量收敛 `hrel` 于 `B`）下，`Gₙ`-Morrey 盘列 `uₙ`（像在 `C`、`E_G(uₙ) ≤ Λ`）**终将**满足一致内部
Morrey decay：`E_G(uₙ, B̄_{R/2^{N+k}}(b)) ≤ θ^k ε₀`，`N, θ < 1, ε₀` 与 `n, b, R` 无关。completion buffer
（`exists_completion_buffer_R7C`）+ `hrel`（`ε = 1/2`）给出 `Gₙ ≤ 2Ĝ`、`G ≤ 2Gₙ`。 -/
theorem eventually_interior_dyadic_decay_R7C [T3Space M] [SecondCountableTopology M]
    (hdim : Module.finrank ℝ E = 3) {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {B C : Set M} (hC : IsCompact C)
    (hCB : C ⊆ interior B)
    (hrel : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ B, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      |(Gn n).inner x v v - G.inner x v v| ≤ ε * G.inner x v v)
    {Γ : freeLoop M} (hΓ : IsSmoothEmbeddedLoop (E := E) Γ)
    {u : ℕ → C(closedDisk, M)} (hu : ∀ n, IsMorreyDisk (Gn n) Γ (u n))
    (huC : ∀ n, range (u n) ⊆ C) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hE : ∀ n, (∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity G (diskExtension (u n)) z) ≤ Λ) :
    ∃ (N : ℕ) (θ ε₀ : ℝ), 0 ≤ θ ∧ θ < 1 ∧ 0 < ε₀ ∧ ∀ᶠ n in atTop,
      ∀ (b : ℂ) (R : ℝ), 0 < R → ‖b‖ + R < 1 → ∀ k : ℕ,
        (∫ z in closedBall b (R / 2 ^ (N + k)), diskMapEnergyDensity G (diskExtension (u n)) z) ≤
          θ ^ k * ε₀ := by
  obtain ⟨W, Ghat, O, _, hCO, hOW, hWB, _, hHR, hGle, hgerm⟩ :=
    exists_completion_buffer_R7C hdim G hC hCB
  have hagree : ∀ x : W, (x : M) ∈ O → Ghat.inner x = G.inner x := by
    intro x hx
    have h := (hgerm x hx).self_of_nhds
    rw [h]
    ext v w
    exact SmoothRiemannianMetric.restrictOpen_inner G W x v w
  obtain ⟨N, θ, ε₀, hθ0, hθ1, hε₀, hdec⟩ := interior_dyadic_decay_R7C W Ghat hHR hOW hagree hΛ
  refine ⟨N, θ, ε₀, hθ0, hθ1, hε₀, ?_⟩
  have hWB' : (W : Set M) ⊆ B := subset_closure.trans (hWB.trans interior_subset)
  filter_upwards [hrel (1 / 2) (by norm_num)] with n hn
  have hup : ∀ (x : W) (v : TangentSpace 𝓘(ℝ, E) x),
      (Gn n).inner x v v ≤ 2 * Ghat.inner x v v := by
    intro x v
    have h1 := (abs_le.mp (hn x (hWB' x.property) v)).2
    have h2 := hGle x v
    rw [SmoothRiemannianMetric.restrictOpen_inner] at h2
    have h3 := metric_inner_self_nonneg G (x : M) v
    linarith
  have hlo : ∀ x ∈ O, ∀ v : TangentSpace 𝓘(ℝ, E) x, G.inner x v v ≤ 2 * (Gn n).inner x v v := by
    intro x hx v
    have h1 := (abs_le.mp (hn x (hWB' (hOW hx)) v)).1
    linarith
  exact hdec (Gn n) hup hlo Γ (u n) hΓ (hu n) ((huC n).trans hCO) (hE n)

end DifferentialGeometry.Geometry
