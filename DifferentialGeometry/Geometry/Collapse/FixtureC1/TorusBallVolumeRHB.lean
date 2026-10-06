import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusEll
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Euclidean
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.AreaFormula
import DifferentialGeometry.Geometry.Comparison.Volume.FirstCrossingScale

/-!
# Ball volumes of the flat lattice torus (lane S-RHOBOUNDS, finding F-REG-1, G2)

The covering map `torPi_FXC1 : ℝ³ → T³` preserves the Riemannian volume on every Borel set on which
it is injective (`torVolume_image_eq_RHB`) and does not increase it on compact sets
(`torVolume_image_le_RHB`).  With the Lebesgue volume of a coordinate box (`volume_box_RHB`):

* `ballVolume_torMetric_ge_RHB`: for `0 < t ≤ r`, `0.9 r < L₀, L₁`, `0.9 t < L₂`:
  `0.729 · t · r² ≤ vol B(p, r)` (a box of sides `0.9 r, 0.9 r, 0.9 t` injects and lies in the
  ball);
* `ballVolume_torMetric_toReal_le_slab_RHB`: `vol B(p, r) ≤ 4 r² L₂`;
* `ballVolume_torMetric_toReal_le_total_RHB`: `vol B(p, r) ≤ L₀ L₁ L₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric MeasureTheory
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-! ### Lebesgue volume of a coordinate box -/

/-- The closed coordinate box of centre `x` and sides `s`. -/
def torBox_RHB (x : E3) (s : Fin 3 → ℝ) : Set E3 :=
  {y : E3 | ∀ i, x i - s i / 2 ≤ y i ∧ y i ≤ x i + s i / 2}

/-- The Lebesgue volume of a coordinate box of `ℝ³`. -/
theorem volume_box_RHB (x : E3) (s : Fin 3 → ℝ) :
    (volume : Measure E3) (torBox_RHB x s) =
      ENNReal.ofReal (s 0) * ENNReal.ofReal (s 1) * ENNReal.ofReal (s 2) := by
  have h : torBox_RHB x s = (WithLp.ofLp : E3 → (Fin 3 → ℝ)) ⁻¹'
      Set.Icc (fun i => x i - s i / 2) (fun i => x i + s i / 2) := by
    ext y
    simp [torBox_RHB, Pi.le_def, forall_and]
  rw [h, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi, Fin.prod_univ_three]
  have e : ∀ i, x i + s i / 2 - (x i - s i / 2) = s i := fun i => by ring
  simp only [e]

/-- The coordinate box is compact. -/
theorem isCompact_torBox_RHB (x : E3) (s : Fin 3 → ℝ) : IsCompact (torBox_RHB x s) := by
  have h : torBox_RHB x s = (WithLp.toLp 2 : (Fin 3 → ℝ) → E3) ''
      Set.Icc (fun i => x i - s i / 2) (fun i => x i + s i / 2) := by
    ext y
    constructor
    · intro hy
      exact ⟨WithLp.ofLp y, by simpa [torBox_RHB, Pi.le_def, forall_and] using hy, by simp⟩
    · rintro ⟨z, hz, rfl⟩
      simpa [torBox_RHB, Pi.le_def, forall_and] using hz
  rw [h]
  exact isCompact_Icc.image (PiLp.continuous_toLp 2 _)

/-- The volume measure of `ℝ³` does not depend on the Borel structure used to build it. -/
theorem volume_instance_irrel_RHB (m₁ m₂ : MeasurableSpace E3) (h₁ : @BorelSpace E3 _ m₁)
    (h₂ : @BorelSpace E3 _ m₂) (K : Set E3) :
    (@volume E3 (@measureSpaceOfInnerProductSpace E3 _ _ _ m₁ h₁)) K =
      (@volume E3 (@measureSpaceOfInnerProductSpace E3 _ _ _ m₂ h₂)) K := by
  have h : m₁ = m₂ := h₁.measurable_eq.trans h₂.measurable_eq.symm
  subst h
  rfl

/-! ### The covering map and the Riemannian volume -/

section Borel

private local instance borelE3_RHB : MeasurableSpace E3 := borel E3
private local instance borelE3Borel_RHB : BorelSpace E3 := ⟨rfl⟩
private local instance borelTor_RHB (Λ : TorusPeriods_FXC1) : MeasurableSpace (Tor_FXC1 Λ) :=
  borel _
private local instance borelTorBorel_RHB (Λ : TorusPeriods_FXC1) : BorelSpace (Tor_FXC1 Λ) :=
  ⟨rfl⟩

private theorem paramDensity_torPi_RHB (Λ : TorusPeriods_FXC1) (x : E3) :
    paramDensity (I := 𝓘(ℝ, E3)) (torMetric_FXC1 Λ) (torPi_FXC1 Λ) x =
      paramDensity (I := 𝓘(ℝ, E3)) (euclideanMetric (E := E3)) (id : E3 → E3) x := by
  unfold paramDensity
  congr 2
  ext i j
  rw [paramGramMatrix_apply, paramGramMatrix_apply]
  have h := localPullMetric_inner (I := 𝓘(ℝ, E3)) (J := 𝓘(ℝ, E3)) (torMetric_FXC1 Λ)
    (torPi_FXC1 Λ) (torPi_isLocalDiffeomorph_FXC1 Λ) x
    (Tensor.Coordinates.chartModelBasis E3 i) (Tensor.Coordinates.chartModelBasis E3 j)
  rw [torMetric_localPull_FXC1] at h
  refine h.symm.trans ?_
  simp only [mfderiv_id, id_eq]
  exact euclideanMetric_inner _ _ _

private theorem lintegral_paramDensity_torPi_RHB (Λ : TorusPeriods_FXC1) {K : Set E3}
    (hK : MeasurableSet K) :
    ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := 𝓘(ℝ, E3)) (torMetric_FXC1 Λ)
        (torPi_FXC1 Λ) x) ∂(modelHaar (E := E3)) = (volume : Measure E3) K := by
  calc ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := 𝓘(ℝ, E3)) (torMetric_FXC1 Λ)
        (torPi_FXC1 Λ) x) ∂(modelHaar (E := E3))
      = ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := 𝓘(ℝ, E3))
          (euclideanMetric (E := E3)) (id : E3 → E3) x) ∂(modelHaar (E := E3)) := by
        refine lintegral_congr fun x => ?_
        rw [paramDensity_torPi_RHB]
    _ = riemannianVolumeMeasure 𝓘(ℝ, E3) E3 (euclideanMetric (E := E3)) (id '' K) :=
        (riemannianVolumeMeasure_image_eq (I := 𝓘(ℝ, E3)) (M := E3)
          (euclideanMetric (E := E3)) (f := (id : E3 → E3)) (U := univ) (K := K) isOpen_univ
          hK (subset_univ _) contMDiffOn_id (injOn_id K)).symm
    _ = (volume : Measure E3) K := by
        rw [image_id, riemannianVolumeMeasure_euclideanMetric]

private theorem torVolume_le_aux_RHB (Λ : TorusPeriods_FXC1) {K : Set E3} (hK : IsCompact K) :
    riemannianVolumeMeasure 𝓘(ℝ, E3) (Tor_FXC1 Λ) (torMetric_FXC1 Λ) (torPi_FXC1 Λ '' K) ≤
      (volume : Measure E3) K := by
  have h := riemannianVolumeMeasure_image_le_of_isCompact (I := 𝓘(ℝ, E3)) (torMetric_FXC1 Λ)
    (f := torPi_FXC1 Λ) (U := univ) isOpen_univ hK (subset_univ _)
    ((contMDiff_torPi_FXC1 Λ).contMDiffOn.of_le (by norm_num))
  exact h.trans (le_of_eq (lintegral_paramDensity_torPi_RHB Λ hK.isClosed.measurableSet))

private theorem torVolume_eq_aux_RHB (Λ : TorusPeriods_FXC1) {K : Set E3} (hK : IsCompact K)
    (hinj : InjOn (torPi_FXC1 Λ) K) :
    riemannianVolumeMeasure 𝓘(ℝ, E3) (Tor_FXC1 Λ) (torMetric_FXC1 Λ) (torPi_FXC1 Λ '' K) =
      (volume : Measure E3) K := by
  rw [riemannianVolumeMeasure_image_eq (I := 𝓘(ℝ, E3)) (torMetric_FXC1 Λ)
    (f := torPi_FXC1 Λ) (U := univ) isOpen_univ hK.isClosed.measurableSet (subset_univ _)
    ((contMDiff_torPi_FXC1 Λ).contMDiffOn.of_le (by norm_num)) hinj]
  exact lintegral_paramDensity_torPi_RHB Λ hK.isClosed.measurableSet

end Borel

/-- **The covering map does not increase the Riemannian volume of a compact set.** -/
theorem torVolume_image_le_RHB (Λ : TorusPeriods_FXC1) {K : Set E3} (hK : IsCompact K) :
    riemannianVolumeMeasure 𝓘(ℝ, E3) (Tor_FXC1 Λ) (torMetric_FXC1 Λ) (torPi_FXC1 Λ '' K) ≤
      (volume : Measure E3) K :=
  (torVolume_le_aux_RHB Λ hK).trans (le_of_eq
    (volume_instance_irrel_RHB borelE3_RHB _ borelE3Borel_RHB _ K))

/-- **The covering map preserves the Riemannian volume of a compact set on which it is
injective.** -/
theorem torVolume_image_eq_RHB (Λ : TorusPeriods_FXC1) {K : Set E3} (hK : IsCompact K)
    (hinj : InjOn (torPi_FXC1 Λ) K) :
    riemannianVolumeMeasure 𝓘(ℝ, E3) (Tor_FXC1 Λ) (torMetric_FXC1 Λ) (torPi_FXC1 Λ '' K) =
      (volume : Measure E3) K :=
  (torVolume_eq_aux_RHB Λ hK hinj).trans
    (volume_instance_irrel_RHB borelE3_RHB _ borelE3Borel_RHB _ K)

/-! ### Balls of the torus -/

/-- **A box that injects fills part of every large enough ball**: a closed coordinate box of
sides `sᵢ < Lᵢ` and circumscribed radius `< r` has its volume below `vol B(π x, r)`. -/
theorem ballVolume_torMetric_ge_box_RHB (Λ : TorusPeriods_FXC1) (x : E3) (s : Fin 3 → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hsL : ∀ i, s i < Λ.L i) {r : ℝ} (hr0 : 0 < r)
    (hr : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 < 4 * r ^ 2) :
    ENNReal.ofReal (s 0 * s 1 * s 2) ≤ ballVolume (torMetric_FXC1 Λ) (torPi_FXC1 Λ x) r := by
  have hinj : InjOn (torPi_FXC1 Λ) (torBox_RHB x s) := by
    intro y hy y' hy' hyy
    obtain ⟨n, hn⟩ := torPi_eq_iff_FXC1.mp hyy
    have hcoord : ∀ i, ((n.toInts i : ℤ) : ℝ) * Λ.L i = y' i - y i := by
      intro i
      rw [hn]
      simp [latticeVec_apply_FXC1]
    have hn0 : ∀ i, n.toInts i = 0 := by
      intro i
      have h1 := hy i
      have h2 := hy' i
      have hL := Λ.pos i
      have hsi := hsL i
      have habs : |((n.toInts i : ℤ) : ℝ) * Λ.L i| < Λ.L i := by
        rw [hcoord, abs_lt]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      by_contra hne
      have h1le : (1 : ℝ) ≤ |((n.toInts i : ℤ) : ℝ)| := by
        have : (1 : ℤ) ≤ |n.toInts i| := Int.one_le_abs hne
        exact_mod_cast this
      rw [abs_mul, abs_of_pos hL] at habs
      nlinarith
    rw [hn]
    ext i
    simp [latticeVec_apply_FXC1, hn0 i]
  have hsub : torPi_FXC1 Λ '' torBox_RHB x s ⊆
      riemannianBallOf (torMetric_FXC1 Λ) (torPi_FXC1 Λ x) r := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := edist_torPi_le_FXC1 Λ x y
    have hnorm : ‖x - y‖ < r := by
      rw [EuclideanSpace.norm_eq, Real.sqrt_lt' hr0, Fin.sum_univ_three]
      simp only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply]
      have a0 := sq_le_sq' (a := x 0 - y 0) (b := s 0 / 2) (by linarith [(hy 0).2])
        (by linarith [(hy 0).1])
      have a1 := sq_le_sq' (a := x 1 - y 1) (b := s 1 / 2) (by linarith [(hy 1).2])
        (by linarith [(hy 1).1])
      have a2 := sq_le_sq' (a := x 2 - y 2) (b := s 2 / 2) (by linarith [(hy 2).2])
        (by linarith [(hy 2).1])
      nlinarith
    exact lt_of_le_of_lt h1 ((ENNReal.ofReal_lt_ofReal_iff hr0).mpr hnorm)
  calc ENNReal.ofReal (s 0 * s 1 * s 2)
      = ENNReal.ofReal (s 0) * ENNReal.ofReal (s 1) * ENNReal.ofReal (s 2) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (hs 0) (hs 1)), ENNReal.ofReal_mul (hs 0)]
    _ = (volume : Measure E3) (torBox_RHB x s) := (volume_box_RHB x s).symm
    _ = riemannianVolumeMeasure 𝓘(ℝ, E3) (Tor_FXC1 Λ) (torMetric_FXC1 Λ)
          (torPi_FXC1 Λ '' torBox_RHB x s) :=
        (torVolume_image_eq_RHB Λ (isCompact_torBox_RHB x s) hinj).symm
    _ ≤ ballVolume (torMetric_FXC1 Λ) (torPi_FXC1 Λ x) r := measure_mono hsub

/-- **Lower ball-volume bound `0.729 · t · r²`** (a box of sides `0.9 r, 0.9 r, 0.9 t` with
`t ≤ r`). -/
theorem ballVolume_torMetric_ge_RHB (Λ : TorusPeriods_FXC1) (x : E3) {r t : ℝ} (hr : 0 < r)
    (ht : 0 < t) (htr : t ≤ r) (h0 : 9 / 10 * r < Λ.L 0) (h1 : 9 / 10 * r < Λ.L 1)
    (h2 : 9 / 10 * t < Λ.L 2) :
    729 / 1000 * t * r ^ 2 ≤
      (ballVolume (torMetric_FXC1 Λ) (torPi_FXC1 Λ x) r).toReal := by
  have hs0 : (0 : ℝ) ≤ 9 / 10 * r := by positivity
  have hs2 : (0 : ℝ) ≤ 9 / 10 * t := by positivity
  have hb := ballVolume_torMetric_ge_box_RHB Λ x ![9 / 10 * r, 9 / 10 * r, 9 / 10 * t]
    (fun i => by fin_cases i; exacts [hs0, hs0, hs2])
    (fun i => by fin_cases i; exacts [h0, h1, h2]) hr (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      nlinarith)
  have hne := ballVolume_ne_top (torMetric_FXC1 Λ) (torPi_FXC1 Λ x) r
  have := ENNReal.toReal_mono hne hb
  rw [ENNReal.toReal_ofReal (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; positivity)] at this
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at this
  nlinarith

/-- **Total volume bound**: every ball of the torus has volume at most `L₀ L₁ L₂`. -/
theorem ballVolume_torMetric_toReal_le_total_RHB (Λ : TorusPeriods_FXC1) (p : Tor_FXC1 Λ)
    (r : ℝ) :
    (ballVolume (torMetric_FXC1 Λ) p r).toReal ≤ Λ.L 0 * Λ.L 1 * Λ.L 2 := by
  let c : E3 := WithLp.toLp 2 fun i => Λ.L i / 2
  have hsurj : torPi_FXC1 Λ '' torBox_RHB c (fun i => Λ.L i) = univ := by
    refine eq_univ_of_forall fun q => ?_
    obtain ⟨x, rfl⟩ := torPi_surjective_FXC1 Λ q
    let m : Fin 3 → ℤ := fun i => -⌊x i / Λ.L i⌋
    let n : TorusGroup_FXC1 Λ := TorusGroup_FXC1.ofInts Λ m
    refine ⟨x + latticeVec_FXC1 Λ n, ?_, (torPi_eq_iff_FXC1.mpr ⟨n, rfl⟩).symm⟩
    intro i
    have hL := Λ.pos i
    have h1 := Int.floor_le (x i / Λ.L i)
    have h2 := Int.lt_floor_add_one (x i / Λ.L i)
    rw [le_div_iff₀ hL] at h1
    rw [div_lt_iff₀ hL] at h2
    have hv : (x + latticeVec_FXC1 Λ n) i = x i - (⌊x i / Λ.L i⌋ : ℤ) * Λ.L i := by
      simp [latticeVec_apply_FXC1, n, m, toInts_ofInts_FXC1]
      ring
    rw [hv]
    simp only [c]
    constructor <;> nlinarith
  have hle : riemannianVolumeMeasure 𝓘(ℝ, E3) (Tor_FXC1 Λ) (torMetric_FXC1 Λ) univ ≤
      ENNReal.ofReal (Λ.L 0 * Λ.L 1 * Λ.L 2) := by
    rw [← hsurj]
    refine (torVolume_image_le_RHB Λ (isCompact_torBox_RHB c _)).trans (le_of_eq ?_)
    rw [volume_box_RHB, ← ENNReal.ofReal_mul (Λ.pos 0).le,
      ← ENNReal.ofReal_mul (mul_nonneg (Λ.pos 0).le (Λ.pos 1).le)]
  have h2 : ballVolume (torMetric_FXC1 Λ) p r ≤ ENNReal.ofReal (Λ.L 0 * Λ.L 1 * Λ.L 2) :=
    (measure_mono (subset_univ _)).trans hle
  have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
  rwa [ENNReal.toReal_ofReal (by
    have := Λ.pos 0; have := Λ.pos 1; have := Λ.pos 2; positivity)] at h3

section Slab

attribute [local instance] torMS_FXC1

/-- **Slab volume bound**: `vol B(p, r) ≤ 4 r² L₂` (every point of the ball has a lift in the box of
sides `2r, 2r, L₂` around a lift of the centre). -/
theorem ballVolume_torMetric_toReal_le_slab_RHB (Λ : TorusPeriods_FXC1) (p : Tor_FXC1 Λ)
    {r : ℝ} (hr : 0 < r) :
    (ballVolume (torMetric_FXC1 Λ) p r).toReal ≤ 4 * r ^ 2 * Λ.L 2 := by
  obtain ⟨x, rfl⟩ := torPi_surjective_FXC1 Λ p
  have hf := Λ.pos 2
  let s : Fin 3 → ℝ := ![2 * r, 2 * r, Λ.L 2]
  have hsub : riemannianBallOf (torMetric_FXC1 Λ) (torPi_FXC1 Λ x) r ⊆
      torPi_FXC1 Λ '' torBox_RHB x s := by
    intro q hq
    have hq' : riemannianEDistOf (torMetric_FXC1 Λ) (torPi_FXC1 Λ x) q <
        ENNReal.ofReal r := hq
    rw [torMS_hmetric_FXC1 Λ] at hq'
    have hd : dist (torPi_FXC1 Λ x) q < r := (ENNReal.ofReal_lt_ofReal_iff hr).mp hq'
    obtain ⟨y, rfl, hy⟩ := exists_lift_of_dist_lt_FXC1 Λ x q hd
    let k : ℤ := ⌊(y 2 - x 2) / Λ.L 2 + 1 / 2⌋
    let n : TorusGroup_FXC1 Λ := TorusGroup_FXC1.ofInts Λ ![0, 0, -k]
    refine ⟨y + latticeVec_FXC1 Λ n, ?_, (torPi_eq_iff_FXC1.mpr ⟨n, rfl⟩).symm⟩
    have hcoord : ∀ i, |y i - x i| ≤ ‖x - y‖ := fun i => by
      have h := PiLp.norm_apply_le (x - y) i
      rw [Real.norm_eq_abs, PiLp.sub_apply, abs_sub_comm] at h
      exact h
    have h1 := Int.floor_le ((y 2 - x 2) / Λ.L 2 + 1 / 2)
    have h2 := Int.lt_floor_add_one ((y 2 - x 2) / Λ.L 2 + 1 / 2)
    have e2 : (y + latticeVec_FXC1 Λ n) 2 = y 2 - (k : ℝ) * Λ.L 2 := by
      simp [latticeVec_apply_FXC1, n, toInts_ofInts_FXC1]
      ring
    have e0 : (y + latticeVec_FXC1 Λ n) 0 = y 0 := by
      simp [latticeVec_apply_FXC1, n, toInts_ofInts_FXC1]
    have e1 : (y + latticeVec_FXC1 Λ n) 1 = y 1 := by
      simp [latticeVec_apply_FXC1, n, toInts_ofInts_FXC1]
    have hs0 : s 0 = 2 * r := rfl
    have hs1 : s 1 = 2 * r := rfl
    have hs2 : s 2 = Λ.L 2 := rfl
    have ha : (y 2 - x 2) / Λ.L 2 * Λ.L 2 = y 2 - x 2 := div_mul_cancel₀ _ hf.ne'
    have h1' := mul_le_mul_of_nonneg_right h1 hf.le
    have h2' := mul_lt_mul_of_pos_right h2 hf
    intro i
    fin_cases i
    · have := abs_le.mp ((hcoord 0).trans hy.le)
      change x 0 - s 0 / 2 ≤ (y + latticeVec_FXC1 Λ n) 0 ∧
        (y + latticeVec_FXC1 Λ n) 0 ≤ x 0 + s 0 / 2
      rw [e0, hs0]
      constructor <;> linarith [this.1, this.2]
    · have := abs_le.mp ((hcoord 1).trans hy.le)
      change x 1 - s 1 / 2 ≤ (y + latticeVec_FXC1 Λ n) 1 ∧
        (y + latticeVec_FXC1 Λ n) 1 ≤ x 1 + s 1 / 2
      rw [e1, hs1]
      constructor <;> linarith [this.1, this.2]
    · change x 2 - s 2 / 2 ≤ (y + latticeVec_FXC1 Λ n) 2 ∧
        (y + latticeVec_FXC1 Λ n) 2 ≤ x 2 + s 2 / 2
      rw [e2, hs2]
      constructor <;> nlinarith [ha]
  have hle : ballVolume (torMetric_FXC1 Λ) (torPi_FXC1 Λ x) r ≤
      ENNReal.ofReal (2 * r) * ENNReal.ofReal (2 * r) * ENNReal.ofReal (Λ.L 2) :=
    (measure_mono hsub).trans ((torVolume_image_le_RHB Λ (isCompact_torBox_RHB x s)).trans
      (le_of_eq (volume_box_RHB x s)))
  have h3 := ENNReal.toReal_mono (by finiteness) hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal hf.le, show 2 * r * (2 * r) * Λ.L 2 = 4 * r ^ 2 * Λ.L 2 by ring]
    at h3

end Slab

end DifferentialGeometry.Geometry.Collapse
