/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Calculus.Quasiconformal.AbsoluteContinuityOnLines
import DifferentialGeometry.Analysis.Calculus.Quasiconformal.DirectionalEnergy

noncomputable section

open Set Filter Metric MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal

namespace DifferentialGeometry.QuasiconformalNull

open MetricDifferentiability QuasiconformalACL CurveAbsoluteContinuity DirectionalEnergy

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

def vertical : V × ℝ := (0, 1)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] in
theorem norm_vertical : ‖(vertical : V × ℝ)‖ ≤ 1 := by
  simp [vertical, Prod.norm_def]

theorem ae_vertical_derivative (ρ : Measure V) [IsAddHaarMeasure ρ]
    (f : (V × ℝ) ≃ₜ (V × ℝ)) (hf : HasGlobalDistortion f) :
    ∀ᵐ z ∂ρ, ∀ᵐ t ∂volume, HasDerivAt (fun s => f (z, s))
      (fderiv ℝ f (z, t) vertical) t := by
  have hd := ae_differentiableAt (ρ.prod volume) f hf.local
  filter_upwards [ae_ae_of_ae_prod hd] with z hz
  filter_upwards [hz] with t ht
  exact ht.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t z).prodMk (hasDerivAt_id t))

theorem ae_line_increment_pow_bound (ρ : Measure V) [IsAddHaarMeasure ρ]
    (f : (V × ℝ) ≃ₜ (V × ℝ)) (hf : HasGlobalDistortion f) :
    ∀ᵐ z ∂ρ, ∀ a b : ℝ,
      ENNReal.ofReal (dist (f (z, a)) (f (z, b)) ^ Module.finrank ℝ (V × ℝ)) ≤
        ENNReal.ofReal (|b - a| ^ Module.finrank ℝ V) *
          ∫⁻ t in uIoc a b, density f vertical (z, t) := by
  filter_upwards [ae_absolutelyContinuousOn_all_intervals (ρ.prod volume) ρ f hf,
    ae_vertical_derivative ρ f hf] with z hzac hzderiv
  intro a b
  have hm : 1 ≤ Module.finrank ℝ (V × ℝ) := by
    rw [Module.finrank_prod, Module.finrank_self]
    omega
  have hmeas : Measurable (fun t : ℝ => ‖fderiv ℝ f (z, t) (vertical : V × ℝ)‖) :=
    ((measurable_fderiv_apply_const ℝ f vertical).comp
      (measurable_const.prodMk measurable_id)).norm
  have h := dist_pow_le_lintegral_derivative_pow (hzac a b) hzderiv hmeas hm
  simpa only [density, Module.finrank_prod, Module.finrank_self, Nat.add_sub_cancel] using h

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem image_closedBall_subset_endpoint_ball
    (f : (V × ℝ) ≃ₜ (V × ℝ)) {H : ℝ} (hH : 0 < H)
    (hf : ∀ x y w : V × ℝ, dist y x ≤ dist w x →
      dist (f y) (f x) ≤ H * dist (f w) (f x))
    (z w : V) (t : ℝ) {r : ℝ} (hr : 0 < r) (hw : dist w z ≤ r / 2) :
    f '' closedBall (z, t) r ⊆ closedBall (f (w, t - r / 2))
      ((H + 1) * H * dist (f (w, t - r / 2)) (f (w, t + r / 2))) := by
  have hd : dist (w, t + r / 2) (w, t - r / 2) = r := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq]
    have he : t + r / 2 - (t - r / 2) = r := by ring
    rw [he, abs_of_pos hr, max_eq_right hr.le]
  have hcenter : dist (z, t) (w, t - r / 2) ≤ r / 2 := by
    rw [Prod.dist_eq, max_le_iff, Real.dist_eq]
    refine ⟨by simpa [dist_comm] using hw, ?_⟩
    have he : t - (t - r / 2) = r / 2 := by ring
    rw [he, abs_of_pos (half_pos hr)]
  rintro _ ⟨y, hy, rfl⟩
  have hy' : dist y (w, t - r / 2) ≤ (2 : ℝ) ^ 1 * dist (w, t + r / 2) (w, t - r / 2) := by
    have ht := dist_triangle y (z, t) (w, t - r / 2)
    change dist y (z, t) ≤ r at hy
    rw [hd, pow_one]
    linarith
  have hb := radius_comparison_pow_two hH hf 1 (w, t - r / 2) y (w, t + r / 2) hy'
  simpa only [mem_closedBall, pow_one, dist_comm (f (w, t + r / 2))] using hb

omit [Nontrivial V] in
theorem image_ball_measure_le_increment (μ : Measure (V × ℝ)) [IsAddHaarMeasure μ]
    (f : (V × ℝ) ≃ₜ (V × ℝ)) {H : ℝ} (hH : 0 < H)
    (hf : ∀ x y w : V × ℝ, dist y x ≤ dist w x →
      dist (f y) (f x) ≤ H * dist (f w) (f x))
    (z w : V) (t : ℝ) {r : ℝ} (hr : 0 < r) (hw : dist w z ≤ r / 2) :
    imageMeasure μ f (closedBall (z, t) r) ≤
      (ENNReal.ofReal (((H + 1) * H) ^ Module.finrank ℝ (V × ℝ)) *
        μ (ball (0 : V × ℝ) 1)) *
          ENNReal.ofReal (dist (f (w, t - r / 2)) (f (w, t + r / 2)) ^
            Module.finrank ℝ (V × ℝ)) := by
  rw [imageMeasure_apply]
  apply (measure_mono (image_closedBall_subset_endpoint_ball f hH hf z w t hr hw)).trans
  rw [addHaar_closedBall μ _ (by positivity), mul_pow,
    ENNReal.ofReal_mul (pow_nonneg (by positivity : 0 ≤ (H + 1) * H) _)]
  exact le_of_eq (by ring)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] in
theorem cylinder_subset_closedBall (z : V) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    closedBall z (r / 2) ×ˢ uIoc (t - r / 2) (t + r / 2) ⊆ closedBall (z, t) r := by
  intro x hx
  rw [mem_closedBall, Prod.dist_eq, max_le_iff]
  rw [uIoc_of_le (by linarith : t - r / 2 ≤ t + r / 2)] at hx
  have hw : dist x.1 z ≤ r / 2 := hx.1
  refine ⟨by linarith, ?_⟩
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [hx.2.1, hx.2.2]

omit [Nontrivial V] in
theorem lintegral_line_energy_le (ρ : Measure V) [IsAddHaarMeasure ρ]
    (f : (V × ℝ) → (V × ℝ)) (z : V) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫⁻ w in closedBall z (r / 2),
        (∫⁻ s in uIoc (t - r / 2) (t + r / 2), density f vertical (w, s)) ∂ρ) ≤
      energyMeasure (ρ.prod volume) f vertical (closedBall (z, t) r) := by
  rw [← lintegral_prod _ (measurable_density f vertical).aemeasurable, Measure.prod_restrict]
  change (∫⁻ x in closedBall z (r / 2) ×ˢ uIoc (t - r / 2) (t + r / 2),
    density f vertical x ∂ρ.prod volume) ≤ _
  rw [energyMeasure, withDensity_apply _ measurableSet_closedBall]
  exact lintegral_mono_set (cylinder_subset_closedBall z t hr)

def volumeComparisonConstant (ρ : Measure V) (H : ℝ) : ℝ :=
  ((H + 1) * H) ^ Module.finrank ℝ (V × ℝ) *
      ((ρ.prod volume) (ball (0 : V × ℝ) 1)).toReal *
      (2 : ℝ) ^ Module.finrank ℝ V / (ρ (ball (0 : V) 1)).toReal

omit [BorelSpace V] [Nontrivial V] in
theorem volumeComparisonConstant_pos (ρ : Measure V) [IsAddHaarMeasure ρ]
    {H : ℝ} (hH : 0 < H) : 0 < volumeComparisonConstant ρ H := by
  have hρ : 0 < (ρ (ball (0 : V) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos ρ 0 zero_lt_one).ne' measure_ball_lt_top.ne
  have hμ : 0 < ((ρ.prod volume) (ball (0 : V × ℝ) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos (ρ.prod volume) 0 zero_lt_one).ne'
      measure_ball_lt_top.ne
  dsimp [volumeComparisonConstant]
  positivity

theorem image_closedBall_le_energy (ρ : Measure V) [IsAddHaarMeasure ρ]
    (f : (V × ℝ) ≃ₜ (V × ℝ)) {H : ℝ} (hH : 0 < H)
    (hf : ∀ x y w : V × ℝ, dist y x ≤ dist w x →
      dist (f y) (f x) ≤ H * dist (f w) (f x))
    (z : V) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    imageMeasure (ρ.prod volume) f (closedBall (z, t) r) ≤
      ENNReal.ofReal (volumeComparisonConstant ρ H) *
        energyMeasure (ρ.prod volume) f vertical (closedBall (z, t) r) := by
  let μ := ρ.prod (volume : Measure ℝ)
  let ν := imageMeasure μ f
  let η := energyMeasure μ f (vertical : V × ℝ)
  have hglobal : HasGlobalDistortion f := ⟨H, hH, hf⟩
  let : IsLocallyFiniteMeasure η := energyMeasure_isLocallyFinite μ f hglobal vertical norm_vertical
  let A : ℝ≥0∞ := ENNReal.ofReal (((H + 1) * H) ^ Module.finrank ℝ (V × ℝ)) *
    μ (ball (0 : V × ℝ) 1)
  have hA : A ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  have hν : ν (closedBall (z, t) r) ≠ ⊤ :=
    (isCompact_closedBall (z, t) r).measure_lt_top.ne
  have hη : η (closedBall (z, t) r) ≠ ⊤ :=
    (isCompact_closedBall (z, t) r).measure_lt_top.ne
  have hpoint : ∀ᵐ w ∂ρ.restrict (closedBall z (r / 2)),
      ν (closedBall (z, t) r) ≤ A * ENNReal.ofReal (r ^ Module.finrank ℝ V) *
        ∫⁻ s in uIoc (t - r / 2) (t + r / 2), density f vertical (w, s) := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall,
      ae_restrict_of_ae (ae_line_increment_pow_bound ρ f hglobal)] with w hw hline
    have hl := hline (t - r / 2) (t + r / 2)
    have hlen : |t + r / 2 - (t - r / 2)| = r := by
      have : t + r / 2 - (t - r / 2) = r := by ring
      rw [this, abs_of_pos hr]
    rw [hlen] at hl
    apply (image_ball_measure_le_increment μ f hH hf z w t hr hw).trans
    change A * ENNReal.ofReal (dist (f (w, t - r / 2)) (f (w, t + r / 2)) ^
        Module.finrank ℝ (V × ℝ)) ≤ _
    exact (mul_le_mul_of_nonneg_left hl (show (0 : ℝ≥0∞) ≤ A from bot_le)).trans_eq
      (mul_assoc _ _ _).symm
  have hsum := lintegral_mono_ae hpoint
  rw [lintegral_const, Measure.restrict_apply_univ,
    lintegral_const_mul' _ _ (ENNReal.mul_ne_top hA ENNReal.ofReal_ne_top)] at hsum
  have hb : ν (closedBall (z, t) r) * ρ (closedBall z (r / 2)) ≤
      A * ENNReal.ofReal (r ^ Module.finrank ℝ V) * η (closedBall (z, t) r) :=
    hsum.trans (by
      gcongr
      exact lintegral_line_energy_le ρ f z t hr)
  have hbReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hA ENNReal.ofReal_ne_top) hη) hb
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _)] at hbReal
  rw [addHaar_closedBall ρ z (half_pos hr).le, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (half_pos hr).le _)] at hbReal
  have hρ : 0 < (ρ (ball (0 : V) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos ρ 0 zero_lt_one).ne' measure_ball_lt_top.ne
  have hcancel : (ν (closedBall (z, t) r)).toReal * (ρ (ball (0 : V) 1)).toReal ≤
      A.toReal * (2 : ℝ) ^ Module.finrank ℝ V * (η (closedBall (z, t) r)).toReal := by
    apply (mul_le_mul_iff_right₀ (pow_pos hr (Module.finrank ℝ V))).mp
    calc
      _ = ((ν (closedBall (z, t) r)).toReal *
          ((r / 2) ^ Module.finrank ℝ V * (ρ (ball (0 : V) 1)).toReal)) *
            (2 : ℝ) ^ Module.finrank ℝ V := by
        rw [div_pow]
        field_simp
      _ ≤ (A.toReal * r ^ Module.finrank ℝ V * (η (closedBall (z, t) r)).toReal) *
          (2 : ℝ) ^ Module.finrank ℝ V :=
        mul_le_mul_of_nonneg_right hbReal (by positivity)
      _ = _ := by ring
  apply (ENNReal.toReal_le_toReal hν (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hη)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (volumeComparisonConstant_pos ρ hH).le]
  calc
    _ ≤ (A.toReal * (2 : ℝ) ^ Module.finrank ℝ V *
        (η (closedBall (z, t) r)).toReal) / (ρ (ball (0 : V) 1)).toReal :=
      (le_div_iff₀ hρ).mpr hcancel
    _ = _ := by
      dsimp [A, volumeComparisonConstant, μ, η]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (by positivity) _)]
      ring

theorem imageMeasure_le_energy (ρ : Measure V) [IsAddHaarMeasure ρ]
    (f : (V × ℝ) ≃ₜ (V × ℝ)) {H : ℝ} (hH : 0 < H)
    (hf : ∀ x y w : V × ℝ, dist y x ≤ dist w x →
      dist (f y) (f x) ≤ H * dist (f w) (f x)) :
    imageMeasure (ρ.prod volume) f ≤ ENNReal.ofReal (volumeComparisonConstant ρ H) •
      energyMeasure (ρ.prod volume) f vertical := by
  let ν := imageMeasure (ρ.prod volume) f
  let η := energyMeasure (ρ.prod volume) f (vertical : V × ℝ)
  let : IsLocallyFiniteMeasure η :=
    energyMeasure_isLocallyFinite (ρ.prod volume) f ⟨H, hH, hf⟩ vertical norm_vertical
  let : IsFiniteMeasureOnCompacts (ENNReal.ofReal (volumeComparisonConstant ρ H) • η) :=
    IsFiniteMeasureOnCompacts.smul η ENNReal.ofReal_ne_top
  apply Measure.le_iff.mpr
  intro s _
  apply (Besicovitch.vitaliFamily ν).measure_le_of_frequently_le
    (ENNReal.ofReal (volumeComparisonConstant ρ H) • η) Measure.AbsolutelyContinuous.rfl s
  intro x _
  apply Filter.Eventually.frequently
  filter_upwards [(Besicovitch.vitaliFamily ν).eventually_filterAt_mem_setsAt x] with U hU
  change U ∈ (fun r : ℝ => closedBall x r) '' Ioi (0 : ℝ) at hU
  obtain ⟨r, hr, rfl⟩ := hU
  exact image_closedBall_le_energy ρ f hH hf x.1 x.2 hr

theorem imageMeasure_absolutelyContinuous (ρ : Measure V) [IsAddHaarMeasure ρ]
    (f : (V × ℝ) ≃ₜ (V × ℝ)) (hf : HasGlobalDistortion f) :
    imageMeasure (ρ.prod volume) f ≪ ρ.prod volume := by
  obtain ⟨H, hH, hcomp⟩ := hf
  exact (Measure.absolutelyContinuous_of_le (imageMeasure_le_energy ρ f hH hcomp)).trans
    ((energyMeasure_absolutelyContinuous (ρ.prod volume) f vertical).smul_left _)

theorem image_null (ρ : Measure V) [IsAddHaarMeasure ρ]
    (f : (V × ℝ) ≃ₜ (V × ℝ)) (hf : HasGlobalDistortion f)
    {s : Set (V × ℝ)} (hs : (ρ.prod volume) s = 0) :
    (ρ.prod volume) (f '' s) = 0 := by
  rw [← imageMeasure_apply]
  exact imageMeasure_absolutelyContinuous ρ f hf hs

theorem image_null_in_linear_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ρ : Measure V) [IsAddHaarMeasure ρ] (μ : Measure E) [IsAddHaarMeasure μ]
    (e : (V × ℝ) ≃L[ℝ] E) (f : E ≃ₜ E) (hf : HasGlobalDistortion f)
    {s : Set E} (hs : μ s = 0) : μ (f '' s) = 0 := by
  let σ := (ρ.prod (volume : Measure ℝ)).map e
  have hσμ : σ ≪ μ := absolutelyContinuous_isAddHaarMeasure σ μ
  have hμσ : μ ≪ σ := absolutelyContinuous_isAddHaarMeasure μ σ
  have hmap (U : Set E) : σ U = (ρ.prod volume) (e ⁻¹' U) :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.map_apply _ _
  have hsource : (ρ.prod volume) (e ⁻¹' s) = 0 := by
    rw [← hmap]
    exact hσμ hs
  let g := (e.toHomeomorph.trans f).trans e.symm.toHomeomorph
  have hnull := image_null ρ g (hf.conjugate e f) hsource
  apply hμσ
  rw [hmap]
  have he : e ⁻¹' (f '' s) = g '' (e ⁻¹' s) := by
    ext x
    constructor
    · rintro ⟨y, hy, hfy⟩
      refine ⟨e.symm y, by simpa using hy, ?_⟩
      change e.symm (f (e (e.symm y))) = x
      rw [e.apply_symm_apply, hfy, e.symm_apply_apply]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨e y, hy, ?_⟩
      change f (e y) = e (e.symm (f (e y)))
      rw [e.apply_symm_apply]
  rw [he]
  exact hnull

end DifferentialGeometry.QuasiconformalNull

namespace DifferentialGeometry.MetricDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem HasGlobalDistortion.image_null (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E ≃ₜ E) (hf : HasGlobalDistortion f) (hdim : 2 ≤ Module.finrank ℝ E)
    {s : Set E} (hs : μ s = 0) : μ (f '' s) = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (by omega : Module.finrank ℝ E ≠ 0)
  let : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  let P : ((Fin k → ℝ) × ℝ) ≃L[ℝ] (Fin (k + 1) → ℝ) :=
    (ContinuousLinearEquiv.prodComm ℝ (Fin k → ℝ) ℝ).trans
      (Fin.consEquivL ℝ (fun _ => ℝ))
  have P' : ((Fin k → ℝ) × ℝ) ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    hk.symm ▸ P
  let e := P'.trans (Module.finBasis ℝ E).equivFunL.symm
  exact QuasiconformalNull.image_null_in_linear_coordinates volume μ e f hf hs

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem quasiMeasurePreserving_symm_of_image_null (μ : Measure E) (f : E ≃ₜ E)
    (hN : ∀ s : Set E, μ s = 0 → μ (f '' s) = 0) :
    QuasiMeasurePreserving f.symm μ μ where
  measurable := f.symm.continuous.measurable
  absolutelyContinuous := Measure.AbsolutelyContinuous.mk fun s hs hnull => by
    rw [Measure.map_apply f.symm.continuous.measurable hs]
    have he : f.symm ⁻¹' s = f '' s := by
      ext x
      constructor
      · intro hx
        exact ⟨f.symm x, hx, f.apply_symm_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [he]
    exact hN s hnull

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem ae_inverse_fderiv_comp (μ : Measure E) (f : E ≃ₜ E)
    (hmap : QuasiMeasurePreserving f μ μ)
    (hf : ∀ᵐ x ∂μ, DifferentiableAt ℝ f x)
    (hi : ∀ᵐ y ∂μ, DifferentiableAt ℝ f.symm y) :
    ∀ᵐ x ∂μ,
      (fderiv ℝ f.symm (f x)).comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ E ∧
      (fderiv ℝ f x).comp (fderiv ℝ f.symm (f x)) = ContinuousLinearMap.id ℝ E := by
  have hid (z : E) : fderiv ℝ (fun y : E => y) z = ContinuousLinearMap.id ℝ E := fderiv_id
  filter_upwards [hf, hmap.ae hi] with x hx hy
  constructor
  · have hd := hy.hasFDerivAt.comp x hx.hasFDerivAt
    simpa only [Function.comp_def, Homeomorph.symm_apply_apply, hid] using hd.fderiv.symm
  · have hx' : HasFDerivAt f (fderiv ℝ f x) (f.symm (f x)) := by
      simpa only [Homeomorph.symm_apply_apply] using hx.hasFDerivAt
    have hd := hx'.comp (f x) hy.hasFDerivAt
    simpa only [Function.comp_def, Homeomorph.apply_symm_apply, hid] using hd.fderiv.symm

end DifferentialGeometry.MetricDifferentiability
