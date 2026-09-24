import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.HighCurvatureModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureBlowup
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarControl
import DifferentialGeometry.Analysis.ODE.QuadraticCrossing
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

noncomputable section
open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem lt_uniformStandardLifetime_of_uniform_scalar_bound
    {T B : ℝ} (hT : 0 < T) (hT1 : T < 1)
    (hbound : ∀ S : StandardSolution, ∀ t ∈ S.val.domain, t < T → ∀ x : E3,
      metricScalarAt (S.val.metric t) x ≤ B) :
    ENNReal.ofReal T < uniformStandardLifetime := by
  obtain ⟨C, hC, hderivative⟩ := exists_standard_high_scalar_time_derivative_bound
  obtain ⟨Q₀, hQ₀, hderiv⟩ := hderivative (T / 2) (half_pos hT)
  let A := max B Q₀ + 1
  have hA : 0 < A := by dsimp [A]; linarith [le_max_right B Q₀]
  have hBA : B < A := by dsimp [A]; linarith [le_max_left B Q₀]
  have hQA : Q₀ < A := by dsimp [A]; linarith [le_max_right B Q₀]
  let d := min (T / 4) (min ((1 - T) / 4) (1 / (16 * C * A)))
  have hd : 0 < d := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hdT : d ≤ T / 4 := min_le_left _ _
  have hd1 : d ≤ (1 - T) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hdA : d ≤ 1 / (16 * C * A) := (min_le_right _ _).trans (min_le_right _ _)
  let a := T - d
  let H := T + d
  have ha : 0 < a := by dsimp [a]; linarith
  have haT : a < T := by dsimp [a]; linarith
  have hhalf : T / 2 ≤ a := by dsimp [a]; linarith
  have hTH : T < H := by dsimp [H]; linarith
  have hH1 : H < 1 := by dsimp [H]; linarith
  have hH : 0 < H := hT.trans hTH
  have hbudget : C * (H - a) < 1 / (2 * A) := by
    have hm := mul_le_mul_of_nonneg_left hdA (by positivity : 0 ≤ 2 * C)
    have he : (2 * C) * (1 / (16 * C * A)) = 1 / (8 * A) := by field_simp; ring
    rw [he] at hm
    have hinv : 1 / (8 * A) < 1 / (2 * A) :=
      one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
    dsimp [H, a]
    nlinarith
  have hscalar (S : StandardSolution) (t : ℝ) (ht : t ∈ S.val.domain) (htH : t < H)
      (x : E3) : metricScalarAt (S.val.metric t) x < 2 * A := by
    by_cases hta : t < a
    · have hb := hbound S t ht (hta.trans haT) x
      linarith
    · have hat : a ≤ t := le_of_not_gt hta
      have hdom : Icc a t ⊆ S.val.domain := by
        intro v hv
        exact (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos v).mpr
          ⟨ha.le.trans hv.1, (ENNReal.ofReal_le_ofReal hv.2).trans_lt
            ((mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos t).mp ht).2⟩
      by_contra hlarge
      have hcross : A⁻¹ - (2 * A)⁻¹ ≤ C * (t - a) := by
        apply DifferentialGeometry.Analysis.ODE.inv_sub_inv_le_mul_sub_of_deriv_le_sq
          hat hA (by linarith)
          (fun v hv => (S.val.scalarTime hv hdom x).continuousWithinAt)
          ((hbound S a (hdom ⟨le_rfl, hat⟩) haT x).trans hBA.le) (le_of_not_gt hlarge)
        intro v hv hAv
        have hvdom := hdom ⟨hv.1.le, hv.2.le⟩
        have hregular : v ∈ (lifetimeInterval S.val.lifetime S.val.lifetime_pos).regular :=
          (mem_lifetimeInterval_regular S.val.lifetime S.val.lifetime_pos v).mpr
            ⟨ha.trans hv.1,
              ((mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos v).mp hvdom).2⟩
        have hd : DifferentiableAt ℝ (fun r => metricScalarAt (S.val.metric r) x) v :=
          (S.val.scalarTime hvdom (fun _ hs => hs) x).differentiableAt
            ((lifetimeInterval S.val.lifetime S.val.lifetime_pos).regular_mem_nhds hregular)
        exact ⟨hd, (le_abs_self _).trans (hderiv S.val x v hvdom (hhalf.trans hv.1.le)
          (hv.2.trans (htH.trans hH1)) (hQA.le.trans hAv.le))⟩
      have hinverse : A⁻¹ - (2 * A)⁻¹ = 1 / (2 * A) := by field_simp; ring
      rw [hinverse] at hcross
      exact (not_le_of_gt hbudget) (hcross.trans
        (mul_le_mul_of_nonneg_left (sub_le_sub_right htH.le a) hC.le))
  have hRm (S : StandardSolution) (t : ℝ) (ht : t ∈ S.val.domain) (htH : t < H) (x : E3) :
      Real.sqrt (normSq0S (S.val.metric t) x 4 (metricRm04 (S.val.metric t) x)) ≤ 200 * A := by
    have hRpos := S.val.one_le_scalar t ht x
    have hb := S.val.normSq_rm_le_scalar_sq t ht x
    have hs := hscalar S t ht htH x
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (100 * metricScalarAt (S.val.metric t) x - 200 * A)]
  have hlife (S : StandardSolution) : ENNReal.ofReal H < S.val.lifetime := by
    by_contra hn
    have hle : S.val.lifetime ≤ ENNReal.ofReal H := le_of_not_gt hn
    have hfinite : S.val.lifetime ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    let V := S.val.lifetime.toReal
    have hV : 0 < V := ENNReal.toReal_pos S.val.lifetime_pos.ne' hfinite
    have hVeq : S.val.lifetime = ENNReal.ofReal V := (ENNReal.ofReal_toReal hfinite).symm
    have hVH : V ≤ H := by
      rw [hVeq] at hle
      exact (ENNReal.ofReal_le_ofReal_iff hH.le).mp hle
    obtain ⟨t, ht, x, hx⟩ := standard_curvature_unbounded_before_finite_lifetime
      S V hV hVeq 0 ⟨le_rfl, hV⟩ (200 * A)
    have htdom : t ∈ S.val.domain :=
      (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos t).mpr
        ⟨ht.1.le, by rw [hVeq]; exact (ENNReal.ofReal_lt_ofReal_iff hV).mpr ht.2⟩
    exact hx.not_ge (hRm S t htdom (ht.2.trans_le hVH) x)
  have hcommon : IsUniformStandardLifetime H := by
    refine ⟨hH, ?_⟩
    intro θ hθ hθH
    refine ⟨fun S => (ENNReal.ofReal_le_ofReal hθH.le).trans_lt (hlife S),
      200 * A, by positivity, ?_⟩
    intro S t ht x
    have htdom : t ∈ S.val.domain :=
      (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos t).mpr
        ⟨ht.1, (ENNReal.ofReal_le_ofReal (ht.2.trans hθH.le)).trans_lt (hlife S)⟩
    exact hRm S t htdom (ht.2.trans_lt hθH) x
  exact ((ENNReal.ofReal_lt_ofReal_iff hH).mpr hTH).trans_le (le_uniformStandardLifetime H hcommon)


theorem standard_family_scalar_unbounded_before_uniform_lifetime
    {T : ℝ} (hT : 0 < T) (hT1 : T < 1)
    (hLifetime : uniformStandardLifetime = ENNReal.ofReal T)
    (θ : ℝ) (hθ : θ ∈ Ico 0 T) (B : ℝ) :
    ∃ (S : StandardSolution) (t : ℝ) (x : E3), t ∈ Ioo θ T ∧
      B < metricScalarAt (S.val.metric t) x := by
  by_contra hno
  have htail : ∀ (S : StandardSolution) (t : ℝ), t ∈ Ioo θ T → ∀ x : E3,
      metricScalarAt (S.val.metric t) x ≤ B := by
    intro S t ht x
    exact le_of_not_gt (fun hx => hno ⟨S, t, x, ht, hx⟩)
  have hθLife : ENNReal.ofReal θ < uniformStandardLifetime := by
    rw [hLifetime]
    exact (ENNReal.ofReal_lt_ofReal_iff hT).mpr hθ.2
  obtain ⟨_, K, _, hprefix⟩ := uniformStandardLifetime_slab θ hθ.1 hθLife
  have hprefixScalar (S : StandardSolution) (t : ℝ) (ht : t ∈ Icc 0 θ) (x : E3) :
      metricScalarAt (S.val.metric t) x ≤ 9 * K := by
    have hs := scalar_abs_le_rm (S.val.metric t) x
    change |metricScalarAt (S.val.metric t) x| ≤ (Module.finrank ℝ E3 : ℝ) ^ 2 * _ at hs
    norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] at hs
    exact (le_abs_self _).trans (hs.trans
      (mul_le_mul_of_nonneg_left (hprefix S t ht x) (by norm_num)))
  have hwhole : ∀ (S : StandardSolution) (t : ℝ), t ∈ S.val.domain → t < T → ∀ x : E3,
      metricScalarAt (S.val.metric t) x ≤ max (9 * K) B := by
    intro S t ht htT x
    by_cases htθ : t ≤ θ
    · exact (hprefixScalar S t
        ⟨((mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos t).mp ht).1, htθ⟩ x).trans
        (le_max_left _ _)
    · exact (htail S t ⟨lt_of_not_ge htθ, htT⟩ x).trans (le_max_right _ _)
  have hlt := lt_uniformStandardLifetime_of_uniform_scalar_bound hT hT1 hwhole
  rw [hLifetime] at hlt
  exact lt_irrefl _ hlt

theorem standard_family_scalar_blowup_sequence
    {T : ℝ} (hT : 0 < T) (hT1 : T < 1)
    (hLifetime : uniformStandardLifetime = ENNReal.ofReal T) :
    ∃ (S : ℕ → StandardSolution) (t : ℕ → ℝ) (x : ℕ → E3),
      (∀ n, t n ∈ Ioo 0 T) ∧
      (∀ n, t n ∈ (S n).val.domain) ∧ Tendsto t atTop (𝓝[<] T) ∧
      Tendsto (fun n => metricScalarAt ((S n).val.metric (t n)) (x n)) atTop atTop := by
  have hθ (n : ℕ) : max 0 (T - 1 / ((n : ℝ) + 1)) ∈ Ico 0 T := by
    refine ⟨le_max_left _ _, max_lt hT ?_⟩
    have hd : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose S t x ht hx using fun n : ℕ =>
    standard_family_scalar_unbounded_before_uniform_lifetime hT hT1 hLifetime
      (max 0 (T - 1 / ((n : ℝ) + 1))) (hθ n) ((n : ℝ) + 1)
  have hmem (n : ℕ) : t n ∈ Ioo 0 T :=
    ⟨(le_max_left _ _).trans_lt (ht n).1, (ht n).2⟩
  have hdom (n : ℕ) : t n ∈ (S n).val.domain := by
    apply (mem_lifetimeInterval_carrier (S n).val.lifetime (S n).val.lifetime_pos (t n)).mpr
    refine ⟨(hmem n).1.le, ?_⟩
    have htime := (ENNReal.ofReal_lt_ofReal_iff hT).mpr (hmem n).2
    rw [← hLifetime] at htime
    exact htime.trans_le (uniformStandardLifetime_le_lifetime (S n))
  have htlim : Tendsto t atTop (𝓝 T) := by
    have hnat := (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using (tendsto_const_nhds (x := T)).sub hnat) tendsto_const_nhds
    · intro n
      simpa only [one_div] using
        (le_max_right (0 : ℝ) (T - 1 / ((n : ℝ) + 1))).trans (ht n).1.le
    · intro n
      exact (hmem n).2.le
  refine ⟨S, t, x, hmem, hdom,
    tendsto_nhdsWithin_iff.mpr ⟨htlim, Eventually.of_forall (fun n => (hmem n).2)⟩, ?_⟩
  exact tendsto_atTop_mono (fun n => (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith).trans (hx n).le)
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

end DifferentialGeometry.PDE.RicciFlow
