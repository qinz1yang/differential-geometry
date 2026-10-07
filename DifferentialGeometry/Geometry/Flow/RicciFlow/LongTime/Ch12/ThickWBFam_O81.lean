import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SingleTimeFam_O81
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BGModel_O81
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HConvS_O32
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.NewLimCore_O68

set_option autoImplicit false

/-! # CH12-O81 G4: P-fam producer of `hthickW'F` ([FROZEN] CH12-O81 P-fam, FINDING O81-F1).

`thickWB_fam_O81 F : ∃ K₀ ≥ 1, ∀ wstar > 0, ∀ H S Φ C hcan, IsWThickSequence_S13 S (K₀ * wstar) → <body>`.
(A) sequence side: `hconvS_O32` (δ = 1/10000, radius 2·10⁴, orders ≤ 2) gives the single-time map
`sliceApprox_O32 S H Φ I`, whose base point is `S.point I` (`basepoint_map`); `thickTransport_O68`
identifies the thickness data, `thick_core_single_O81` gives `ρ ∈ [1, √8]` and
`vol B(x_I, ρ) ≤ 2 vol_H B(base, 4)`, so `K₀ wstar ≤ 2 vol_H B(base, 4)`.
(B) body: `thick_core_single_O81` at `q`, `y ∈ B(base, 2)`: `r ∈ [1, √8]`,
`vol B(q y, r) ≥ (2/3) vol_H B(y, 1/2)`; `B(base, 4) ⊆ B(y, 6)` and `bishopGromov_model_O81`
(`vol B(y,6) V(1/2) ≤ V(6) vol B(y,1/2)`); `K₀ := max 1 (81 V(6) / V(1/2))` closes
`wstar r³ ≤ 27 wstar ≤ (2/3) vol_H B(y, 1/2)`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- **G4 ([FROZEN] CH12-O81 P-fam).** -/
theorem thickWB_fam_O81 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ wstar : ℝ, 0 < wstar → ∀ (H : FiniteVolumeHyperbolicModel.{u}) (S : LatePointSequence_S13 F)
      (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id)
      (C : MetricConvergenceData Φ),
      (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k) →
      IsWThickSequence_S13 S (K₀ * wstar) →
      ∃ (ε₀ R₀ T₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ ∃ hT₀ : 0 < T₀,
        ∀ (s : ℝ) (hs : T₀ ≤ s) (q : H.Carrier → (postStage F.observation s).Carrier) (R'' : ℝ),
          R₀ ≤ R'' →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (1 + 1), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT₀ hs))
              (postMetric F.observation s)) (q y) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le hT₀ hs)) (postMetric F.observation s)) (q y) r := by
  set V : ℝ → ℝ := fun r => modelVolume (-(1 / 4 : ℝ)) 3 r with hVdef
  have hVpos : ∀ r : ℝ, 0 < r → 0 < V r := fun r hr =>
    modelVolume_pos (by norm_num) hr ⟨hr.le, fun hpos => absurd hpos (by norm_num)⟩
  have hV6 := hVpos 6 (by norm_num)
  have hV2 := hVpos (1 / 2) (by norm_num)
  set K₀ : ℝ := max 1 (81 * V 6 / V (1 / 2)) with hK₀
  refine ⟨K₀, le_max_left _ _, fun wstar hw H S Φ C hcan hW => ?_⟩
  have hK₀pos : 0 < K₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK₀ge : 81 * V 6 / V (1 / 2) ≤ K₀ := le_max_right _ _
  set δ : ℝ := (10000 : ℝ)⁻¹ with hδdef
  have hδ : 0 < δ := by norm_num [hδdef]
  have hacc1 : δ ≤ 1 / 10000 := by norm_num [hδdef]
  have hδinv : δ⁻¹ = 10000 := by rw [hδdef, inv_inv]
  clear_value δ V K₀
  -- (A) sequence side: `K₀ wstar ≤ 2 vol_H B(base, 4)`
  have hA : ENNReal.ofReal (K₀ * wstar) ≤
      ENNReal.ofReal 2 * ballVolume H.metric H.basepoint 4 := by
    obtain ⟨I, hI⟩ := hconvS_O32 F H S Φ C hcan δ (2 * δ⁻¹) 2 hδ (by positivity)
    obtain ⟨U, hUB, hsm, hemb, hck⟩ := hI I le_rfl
    have hs : 0 < (S.slices I).time := (S.slices I).positive
    have hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => sliceApprox_O32 S H Φ I x) ∧
        Function.Injective (fun x : U => sliceApprox_O32 S H Φ I x) :=
      ⟨isLocalDiffeomorph_of_injective_mfderiv _ hemb.contMDiff
        (fun q => injective_mfderiv_of_isImmersionAt _ _ _ q (hemb.isImmersion.isImmersionAt q)) rfl,
        hemb.isEmbedding.injective⟩
    have hbase : H.basepoint ∈ riemannianBallOf H.metric H.basepoint δ⁻¹ := by
      change riemannianEDistOf H.metric H.basepoint H.basepoint < ENNReal.ofReal δ⁻¹
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (inv_pos.mpr hδ)
    obtain ⟨r, hr, hcr, hr1, hr8, -, hup⟩ :=
      thick_core_single_O81 hs hsm hf hUB hck hδ hacc1 H.basepoint hbase
    obtain ⟨ρ, hρ, hcrρ, hvolρ⟩ := hW I
    have hpt : cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier)
        (postStage_eq_sliceStage_CX4 (S.slices I))) (sliceApprox_O32 S H Φ I H.basepoint) =
        S.point I := by
      have key : ∀ {X Y Z : Type u} (e₁ : X = Y) (e₂ : Y = Z) (a : X) (b : Z),
          HEq a b → cast e₂ (cast e₁ a) = b := by
        intro X Y Z e₁ e₂ a b hab
        subst e₁ e₂
        exact eq_of_heq hab
      exact key _ _ _ _ (heq_of_eq (Φ.basepoint_map I))
    have T := thickTransport_O68 (postStage_eq_sliceStage_CX4 (S.slices I))
      (postMetric F.observation (S.slices I).time) (S.slices I).metric
      (postMetric_regularSlice F.observation (S.slices I)) (S.slices I).time⁻¹
      (inv_pos.mpr (S.slices I).positive) (inv_pos.mpr hs) (sliceApprox_O32 S H Φ I H.basepoint) ρ
    rw [hpt] at T
    have hcrρ' : curvatureRadius (scaleMetric (S.slices I).time⁻¹ (inv_pos.mpr hs)
        (postMetric F.observation (S.slices I).time)) (sliceApprox_O32 S H Φ I H.basepoint) =
        ENNReal.ofReal ρ := by
      rw [← T.1]; exact hcrρ
    have hρr : ρ = r := by
      rw [hcr] at hcrρ'
      exact ((ENNReal.ofReal_eq_ofReal_iff hr.le hρ.le).mp hcrρ').symm
    subst hρr
    have hvol' : ENNReal.ofReal (K₀ * wstar * ρ ^ 3) ≤ ballVolume (scaleMetric (S.slices I).time⁻¹
        (inv_pos.mpr hs) (postMetric F.observation (S.slices I).time))
        (sliceApprox_O32 S H Φ I H.basepoint) ρ := by
      rw [← T.2]; exact hvolρ
    have hρ3 : 1 ≤ ρ ^ 3 := one_le_pow₀ hr1
    have hKw : 0 ≤ K₀ * wstar := by positivity
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hvol'.trans hup)
    nlinarith
  -- (B) the body
  refine ⟨δ, δ⁻¹, 1, 2, hδ, one_pos, fun s hs q R'' hR'' hsm hinj hck y hy => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hsub : riemannianBallOf H.metric H.basepoint (2 * δ⁻¹) ⊆
      riemannianBallOf H.metric H.basepoint (4 * R'') :=
    riemannianBallOf_mono _ _ (by rw [hδinv] at hR'' ⊢; linarith)
  let U : TopologicalSpace.Opens H.Carrier :=
    ⟨riemannianBallOf H.metric H.basepoint (2 * δ⁻¹), isOpen_riemannianBallOf _ _ _⟩
  have hck' : ∀ k : ℕ, k ≤ 2 → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * δ⁻¹),
      ckErr_S45 H (postMetric F.observation s) s⁻¹ q k p < δ :=
    fun k hk p hp => hck k hk p (hsub hp)
  have hf := localDiffeo_single_O81 (U := U) (hsm.mono hsub) (hinj.mono hsub)
    (fun p hp => (hck' 0 (Nat.zero_le _) p hp).trans_le (hacc1.trans (by norm_num)))
  have hyδ : y ∈ riemannianBallOf H.metric H.basepoint δ⁻¹ :=
    riemannianBallOf_mono _ _ (by rw [hδinv]; norm_num) hy
  obtain ⟨r, hr, hcr, hr1, hr8, hlow, -⟩ :=
    thick_core_single_O81 hs0 (hsm.mono hsub) hf subset_rfl hck' hδ hacc1 y hyδ
  refine ⟨r, hr, hcr, le_trans ?_ hlow⟩
  -- Bishop–Gromov at `y`, `B(base, 4) ⊆ B(y, 6)`
  have hBG : ballVolume H.metric y 6 * ENNReal.ofReal (V (1 / 2)) ≤
      ENNReal.ofReal (V 6) * ballVolume H.metric y (1 / 2) := by
    rw [hVdef]
    exact bishopGromov_model_O81 H y (s := 1 / 2) (R := 6) (by norm_num) (by norm_num)
  have hball : riemannianBallOf H.metric H.basepoint 4 ⊆ riemannianBallOf H.metric y 6 := by
    intro z hz
    have hy' : riemannianEDistOf H.metric H.basepoint y < ENNReal.ofReal (1 + 1) := hy
    have hz' : riemannianEDistOf H.metric H.basepoint z < ENNReal.ofReal 4 := hz
    change riemannianEDistOf H.metric y z < ENNReal.ofReal 6
    calc riemannianEDistOf H.metric y z
        ≤ riemannianEDistOf H.metric y H.basepoint + riemannianEDistOf H.metric H.basepoint z :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (1 + 1) + ENNReal.ofReal 4 := by
          rw [riemannianEDistOf_comm]
          exact ENNReal.add_lt_add hy' hz'
      _ = ENNReal.ofReal 6 := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
  have hvol6 : ballVolume H.metric H.basepoint 4 ≤ ballVolume H.metric y 6 :=
    MeasureTheory.measure_mono hball
  set X := ballVolume H.metric y (1 / 2) with hX
  -- `ofReal (81 V(6) wstar) ≤ ofReal (2 V(6)) * X`
  have hkey : ENNReal.ofReal (81 * V 6 * wstar) ≤ ENNReal.ofReal (2 * V 6) * X := by
    have h1 : ENNReal.ofReal (K₀ * wstar) * ENNReal.ofReal (V (1 / 2)) ≤
        ENNReal.ofReal 2 * (ENNReal.ofReal (V 6) * X) :=
      calc ENNReal.ofReal (K₀ * wstar) * ENNReal.ofReal (V (1 / 2))
          ≤ ENNReal.ofReal 2 * ballVolume H.metric y 6 * ENNReal.ofReal (V (1 / 2)) :=
            mul_le_mul' (hA.trans (mul_le_mul' le_rfl hvol6)) le_rfl
        _ = ENNReal.ofReal 2 * (ballVolume H.metric y 6 * ENNReal.ofReal (V (1 / 2))) :=
            mul_assoc _ _ _
        _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (V 6) * X) := mul_le_mul' le_rfl hBG
    have hle : 81 * V 6 * wstar ≤ K₀ * wstar * V (1 / 2) := by
      have hK : 81 * V 6 / V (1 / 2) ≤ K₀ := hK₀ge
      have : 81 * V 6 ≤ K₀ * V (1 / 2) := by
        rwa [div_le_iff₀ hV2] at hK
      nlinarith
    calc ENNReal.ofReal (81 * V 6 * wstar) ≤ ENNReal.ofReal (K₀ * wstar * V (1 / 2)) :=
          ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal (K₀ * wstar) * ENNReal.ofReal (V (1 / 2)) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (V 6) * X) := h1
      _ = ENNReal.ofReal (2 * V 6) * X := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
  have hr3 : r ≤ 3 := by nlinarith
  have hr27 : r ^ 3 ≤ 27 := by
    calc r ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ hr.le hr3 3
      _ = 27 := by norm_num
  have h3V : (0 : ℝ) < 3 * V 6 := by positivity
  have hne0 : ENNReal.ofReal (3 * V 6) ≠ 0 := (ENNReal.ofReal_pos.mpr h3V).ne'
  refine (ENNReal.mul_le_mul_iff_right hne0 ENNReal.ofReal_ne_top).mp ?_
  calc ENNReal.ofReal (3 * V 6) * ENNReal.ofReal (wstar * r ^ 3)
      = ENNReal.ofReal (3 * V 6 * (wstar * r ^ 3)) := (ENNReal.ofReal_mul h3V.le).symm
    _ ≤ ENNReal.ofReal (81 * V 6 * wstar) := ENNReal.ofReal_le_ofReal (by
        have hVw : 0 ≤ V 6 * wstar := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hr27 hVw])
    _ ≤ ENNReal.ofReal (2 * V 6) * X := hkey
    _ = ENNReal.ofReal (3 * V 6) * (ENNReal.ofReal (2 / 3) * X) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul h3V.le]
        congr 2
        ring

end GC.LongTime.Ch12
