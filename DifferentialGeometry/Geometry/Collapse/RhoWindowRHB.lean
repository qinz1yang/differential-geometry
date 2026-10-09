import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4RealizationC14Z
import DifferentialGeometry.Geometry.Comparison.Volume.FirstCrossingScale

/-!
# LPA01's scale window `ρ_bounds`, unfolded (lane S-RHOBOUNDS, finding F-REG-1, G1)

`ClosedFamilyInstanceC14ZV4.ρ_bounds` asks, at every `p`,
`firstVolumeScale g p w / 2 < ρ p ∧ ρ p < 2 * firstVolumeScale g p w'` with
`w' = closedWPrime scale`.

* `firstVolumeScale_lt_iff_RHB`, `lt_firstVolumeScale_iff_RHB`: the two halves in terms of the ball
  volume itself (`s < c` iff some `r < c` has `V r ≤ w r³`; `c < s` iff `w r³ < V r` for all
  `r ≤ c`);
* `rhoWindow_iff_RHB`, `rhoWindowOne_iff_RHB`: the window at a scale `ρ` (at `ρ ≡ 1`);
* `firstVolumeScale_mem_window_RHB`: the window is never empty (`ρ = firstVolumeScale w'`);
* register inequalities: `β₂` is chosen before `Λ, w`, `Δ > 100/β₂` and `100 Δ Λ < 10⁻⁸` give
  `Λ < β₂/10¹²`, hence `w' < w Λ³/16 < β₂³/10³⁶` (`ClosedLaterV4.wPrime_lt_beta2_cube_RHB`);
* `ClosedFamilyInstanceC14ZV4.rhoWindow_RHB`: the unfolded window for an actual instance.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Collapse

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- `firstVolumeScale w < c` iff some radius `r < c` has `V r ≤ w r³`. -/
theorem firstVolumeScale_lt_iff_RHB {g : SmoothRiemannianMetric I M}
    (hdim : Module.finrank ℝ E = 3) {p : M} {w : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3)
    {c : ℝ} :
    firstVolumeScale g p w < c ↔
      ∃ r, 0 < r ∧ r < c ∧ (ballVolume g p r).toReal ≤ w * r ^ 3 := by
  obtain ⟨hpos, heq, hbefore⟩ := firstVolumeScale_spec g hdim p hw hwc
  constructor
  · intro h
    exact ⟨_, hpos, h, heq.le⟩
  · rintro ⟨r, hr, hrc, hV⟩
    by_contra hcon
    have hcs : c ≤ firstVolumeScale g p w := not_lt.mp hcon
    exact absurd (hbefore r hr (hrc.trans_le hcs)) (not_lt.mpr hV)

/-- `c < firstVolumeScale w` iff `w r³ < V r` for every `0 < r ≤ c`. -/
theorem lt_firstVolumeScale_iff_RHB {g : SmoothRiemannianMetric I M}
    (hdim : Module.finrank ℝ E = 3) {p : M} {w : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3)
    {c : ℝ} :
    c < firstVolumeScale g p w ↔
      ∀ r, 0 < r → r ≤ c → w * r ^ 3 < (ballVolume g p r).toReal := by
  obtain ⟨hpos, heq, hbefore⟩ := firstVolumeScale_spec g hdim p hw hwc
  constructor
  · intro h r hr hrc
    exact hbefore r hr (hrc.trans_lt h)
  · intro h
    by_contra hcon
    have hsc : firstVolumeScale g p w ≤ c := not_lt.mp hcon
    have h2 := h _ hpos hsc
    rw [heq] at h2
    exact lt_irrefl _ h2

/-- **LPA01's window at a scale `ρ`, in terms of the ball volume.** -/
theorem rhoWindow_iff_RHB {g : SmoothRiemannianMetric I M} (hdim : Module.finrank ℝ E = 3)
    {p : M} {w w' : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) (hw' : 0 < w')
    (hw'c : w' < 4 * Real.pi / 3) {ρ : ℝ} :
    (firstVolumeScale g p w / 2 < ρ ∧ ρ < 2 * firstVolumeScale g p w') ↔
      ((∃ r, 0 < r ∧ r < 2 * ρ ∧ (ballVolume g p r).toReal ≤ w * r ^ 3) ∧
        ∀ r, 0 < r → r ≤ ρ / 2 → w' * r ^ 3 < (ballVolume g p r).toReal) := by
  rw [← firstVolumeScale_lt_iff_RHB (g := g) (p := p) (c := 2 * ρ) hdim hw hwc,
    ← lt_firstVolumeScale_iff_RHB (g := g) (p := p) (c := ρ / 2) hdim hw' hw'c]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The window at the constant scale `ρ ≡ 1` (the flat-torus fixture). -/
theorem rhoWindowOne_iff_RHB {g : SmoothRiemannianMetric I M} (hdim : Module.finrank ℝ E = 3)
    {p : M} {w w' : ℝ} (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) (hw' : 0 < w')
    (hw'c : w' < 4 * Real.pi / 3) :
    (firstVolumeScale g p w / 2 < 1 ∧ 1 < 2 * firstVolumeScale g p w') ↔
      ((∃ r, 0 < r ∧ r < 2 ∧ (ballVolume g p r).toReal ≤ w * r ^ 3) ∧
        ∀ r, 0 < r → r ≤ 1 / 2 → w' * r ^ 3 < (ballVolume g p r).toReal) := by
  have h := rhoWindow_iff_RHB (g := g) (p := p) (ρ := 1) hdim hw hwc hw' hw'c
  rwa [mul_one] at h

/-- The window is never empty: `ρ = firstVolumeScale w'` lies in it (`w' < w`). -/
theorem firstVolumeScale_mem_window_RHB (g : SmoothRiemannianMetric I M)
    (hdim : Module.finrank ℝ E = 3) (p : M) {w w' : ℝ} (hw' : 0 < w') (hw'w : w' < w)
    (hwc : w < 4 * Real.pi / 3) :
    firstVolumeScale g p w / 2 < firstVolumeScale g p w' ∧
      firstVolumeScale g p w' < 2 * firstVolumeScale g p w' := by
  have hw : 0 < w := hw'.trans hw'w
  have hanti := firstVolumeScale_strictAntiOn g hdim p ⟨hw', hw'w.trans hwc⟩ ⟨hw, hwc⟩ hw'w
  have hpos := (firstVolumeScale_spec g hdim p hw hwc).1
  have hpos' := (firstVolumeScale_spec g hdim p hw' (hw'w.trans hwc)).1
  exact ⟨by linarith, by linarith⟩

end Abstract

section Register

/-- `w'` is below `w Λ³ / 16`. -/
theorem closedWPrime_lt_cube_RHB (sc : ClosedScales) (hΛ : 0 < sc.Λ) (hw : 0 < sc.w) :
    closedWPrime sc < sc.w * sc.Λ ^ 3 / 16 := by
  unfold closedWPrime
  have h1 : 2 * sc.Λ⁻¹ < 1 + 2 * sc.Λ⁻¹ := by linarith
  have h2 : 0 < 2 * sc.Λ⁻¹ := by positivity
  have h3 : (2 * sc.Λ⁻¹) ^ 3 < (1 + 2 * sc.Λ⁻¹) ^ 3 := pow_lt_pow_left₀ h1 h2.le (by norm_num)
  have h4 : (2 * sc.Λ⁻¹) ^ 3 = 8 / sc.Λ ^ 3 := by
    rw [mul_pow, inv_pow]; ring
  have hpos : 0 < 2 * (1 + 2 * sc.Λ⁻¹) ^ 3 := by positivity
  rw [div_lt_iff₀ hpos]
  have h5 : sc.w * sc.Λ ^ 3 / 16 * (2 * (1 + 2 * sc.Λ⁻¹) ^ 3) >
      sc.w * sc.Λ ^ 3 / 16 * (2 * (8 / sc.Λ ^ 3)) := by
    have : 0 < sc.w * sc.Λ ^ 3 / 16 := by positivity
    have : 2 * (8 / sc.Λ ^ 3) < 2 * (1 + 2 * sc.Λ⁻¹) ^ 3 := by rw [← h4]; linarith
    exact mul_lt_mul_of_pos_left this ‹0 < sc.w * sc.Λ ^ 3 / 16›
  have h6 : sc.w * sc.Λ ^ 3 / 16 * (2 * (8 / sc.Λ ^ 3)) = sc.w := by
    field_simp
    norm_num
  linarith

theorem closedWPrime_pos_RHB (sc : ClosedScales) (hΛ : 0 < sc.Λ) (hw : 0 < sc.w) :
    0 < closedWPrime sc := by
  unfold closedWPrime
  positivity

theorem closedWPrime_lt_half_RHB (sc : ClosedScales) (hΛ : 0 < sc.Λ) (hw : 0 < sc.w) :
    closedWPrime sc < sc.w / 2 := by
  unfold closedWPrime
  have h1 : 1 < (1 + 2 * sc.Λ⁻¹) ^ 3 := by
    have : 1 < 1 + 2 * sc.Λ⁻¹ := by have : 0 < sc.Λ⁻¹ := inv_pos.mpr hΛ; linarith
    exact one_lt_pow₀ this (by norm_num)
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

variable {D : ClosedEarlyData} {T : ClosedThresholdsV4 D} {st : ClosedStage D}
  (L : ClosedLaterV4 D T st)

/-- **`Λ` is far below `β₂`**: `Δ > 100/β₂` and `100 Δ Λ < 10⁻⁸`. -/
theorem ClosedLaterV4.lambda_lt_beta2_RHB : L.scale.Λ < L.excl.β₂ / 10 ^ 12 := by
  have hβ := L.β₂_pos
  have hΛ := L.Λ_pos
  have hΔ : 100 / L.excl.β₂ < L.excl.Δ := by
    have h1 : max (100 / L.excl.β₂) (T.ΔLow st L.circle L.excl.β₃ L.excl.β₂) < L.excl.Δ :=
      lt_of_le_of_lt (le_max_right _ _) L.Δ_gt
    exact lt_of_le_of_lt (le_max_left _ _) h1
  have hΔ' : 100 < L.excl.Δ * L.excl.β₂ := by
    rwa [div_lt_iff₀ hβ] at hΔ
  have hΔpos : 0 < L.excl.Δ := (div_pos (by norm_num) hβ).trans hΔ
  have h100 := L.regScale_100
  rw [lt_div_iff₀ (by positivity)]
  have key : L.scale.Λ * 10 ^ 12 * L.excl.Δ < L.excl.β₂ * L.excl.Δ := by
    nlinarith
  exact lt_of_mul_lt_mul_right key hΔpos.le

/-- The volume parameter lies below the Euclidean unit-ball volume. -/
theorem ClosedLaterV4.w_lt_unitBall_RHB : L.scale.w < 4 * Real.pi / 3 :=
  (L.w_lt.trans_le (min_le_right _ _)).trans_eq rfl

/-- **`w'` is far below `β₂³`**: `w' < w Λ³/16 < β₂³ / 10³⁶`. So the right half of the window is
automatic for a circle stage of fibre `≳ w'`: the earlier estimate "`w'` is not small in `β₂`" is
wrong. -/
theorem ClosedLaterV4.wPrime_lt_beta2_cube_RHB :
    closedWPrime L.scale < L.excl.β₂ ^ 3 / 10 ^ 36 := by
  have hβ := L.β₂_pos
  have hΛ := L.Λ_pos
  have hw := L.w_pos
  have hwc := L.w_lt_unitBall_RHB
  have h1 := closedWPrime_lt_cube_RHB L.scale hΛ hw
  have h2 := L.lambda_lt_beta2_RHB
  have h3 : L.scale.Λ ^ 3 < (L.excl.β₂ / 10 ^ 12) ^ 3 := pow_lt_pow_left₀ h2 hΛ.le (by norm_num)
  have h4 : (L.excl.β₂ / 10 ^ 12) ^ 3 = L.excl.β₂ ^ 3 / 10 ^ 36 := by
    rw [div_pow]; norm_num
  have hpi := Real.pi_lt_d2
  have h5 : L.scale.w * L.scale.Λ ^ 3 / 16 ≤ 4 * Real.pi / 3 * L.scale.Λ ^ 3 / 16 := by
    have : 0 < L.scale.Λ ^ 3 := by positivity
    gcongr
  have h6 : 4 * Real.pi / 3 * L.scale.Λ ^ 3 / 16 ≤ L.scale.Λ ^ 3 := by
    have : 0 < L.scale.Λ ^ 3 := by positivity
    nlinarith
  linarith

/-- The sharper form: `w' < w β₂³ / 10³⁶`. -/
theorem ClosedLaterV4.wPrime_lt_w_beta2_cube_RHB :
    closedWPrime L.scale < L.scale.w * L.excl.β₂ ^ 3 / 10 ^ 36 := by
  have hβ := L.β₂_pos
  have hΛ := L.Λ_pos
  have hw := L.w_pos
  have h1 := closedWPrime_lt_cube_RHB L.scale hΛ hw
  have h3 : L.scale.Λ ^ 3 < (L.excl.β₂ / 10 ^ 12) ^ 3 :=
    pow_lt_pow_left₀ L.lambda_lt_beta2_RHB hΛ.le (by norm_num)
  have h4 : (L.excl.β₂ / 10 ^ 12) ^ 3 = L.excl.β₂ ^ 3 / 10 ^ 36 := by
    rw [div_pow]; norm_num
  have h5 : 0 < L.excl.β₂ ^ 3 / 10 ^ 36 := by positivity
  have h6 : L.scale.w * L.scale.Λ ^ 3 / 16 ≤ L.scale.w * L.scale.Λ ^ 3 := by
    have : 0 < L.scale.w * L.scale.Λ ^ 3 := by positivity
    linarith
  have h7 : L.scale.w * L.scale.Λ ^ 3 ≤ L.scale.w * (L.excl.β₂ ^ 3 / 10 ^ 36) :=
    mul_le_mul_of_nonneg_left (by linarith) hw.le
  calc closedWPrime L.scale < L.scale.w * L.scale.Λ ^ 3 / 16 := h1
    _ ≤ L.scale.w * (L.excl.β₂ ^ 3 / 10 ^ 36) := h6.trans h7
    _ = L.scale.w * L.excl.β₂ ^ 3 / 10 ^ 36 := by ring

end Register

section Instance

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u

/-- **The window of an actual instance, unfolded**: at every `p`, `ρ p` is such that some radius
`r < 2 ρ p` has `V r ≤ w r³`, and `w' r³ < V r` for every `r ≤ ρ p / 2`. -/
theorem ClosedFamilyInstanceC14ZV4.rhoWindow_RHB {K : ℕ} {D : ClosedEarlyData}
    {T : ClosedThresholdsV4 D} {R : ClosedRegisterV4 D T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (F : ClosedFamilyInstanceC14ZV4 K R M δ εr Λz) (p : M.X) :
    (∃ r, 0 < r ∧ r < 2 * F.ρ p ∧
        (ballVolume M.gX p r).toReal ≤ R.later.scale.w * r ^ 3) ∧
      ∀ r, 0 < r → r ≤ F.ρ p / 2 →
        closedWPrime R.later.scale * r ^ 3 < (ballVolume M.gX p r).toReal := by
  have hΛ := R.later.Λ_pos
  have hw := R.later.w_pos
  have hwc := R.later.w_lt_unitBall_RHB
  have hw'c : closedWPrime R.later.scale < 4 * Real.pi / 3 :=
    ((closedWPrime_lt_half_RHB R.later.scale hΛ hw).trans (by linarith)).trans hwc
  exact (rhoWindow_iff_RHB (g := M.gX) (p := p) (ρ := F.ρ p) finrank_euclideanSpace_fin hw hwc
    (closedWPrime_pos_RHB R.later.scale hΛ hw) hw'c).mp (F.ρ_bounds p)

end Instance

end DifferentialGeometry.Geometry.Collapse
