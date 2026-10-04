import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA3Ode
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA3Volume

/-!
# The normalized scalar curvature of a positively curved surface flow is bounded

Chapter 7, packet P8, surface lemma U1, route (a), lane a3 (review 17 §4.3, backward window).
For a Ricci flow on `[0, T)` on a compact connected surface with positive initial scalar curvature,
with `C₀ = ∫ R dμ`, `A₀ = Area` at time `0` and `T* = A₀ / C₀`,
`surfaceFlow_normalized_scalar_upper` bounds `R(t, x) · 2 (T* - t)` uniformly. No maximality of the
flow is assumed.

At a time `t` with `Q = max R(t, ·)`, `Q t ≥ 1` and `Q ≥ 1/4`, put `a = t - 1 / (4Q)`, `o = t / 2`
(`surfaceFlow_area_bound_main`):
* same-point Harnack gives `R ≤ 2Q` on `[a, t]`;
* the ODE comparison gives `q = max R(a, ·) ≥ (4/5) Q` at a point `x_a`;
* with `r = 1 / (2 √Q)` the window `[t - r², t]` is `[a, t]` and `r⁴ |Rm|² ≤ 1/4`, so
  non-collapsing gives `Area_{g(t)} B_{g(t)}(x_a, r) ≥ κ r²`;
* distances shrink by at most `e^{1/4}` from `a` to `t`, so Harnack from `(a, x_a)` gives
  `R(t, ·) ≥ b Q` on that ball, `b = (2/5) exp (-e^{1/2} / 4)`;
* the entropy lower bound at the same time `t` and monotonicity give `Q · Area(g t) ≤ K`.
The remaining cases (`t ≤ T / 2`, `Q t < 1`, `Q < 1/4`) are bounded directly.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Tensor0SBundle
open MeasureTheory Filter Topology Set
open scoped Manifold ContDiff ENNReal

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]
  {T : ℝ} {hT : 0 < T}

private local instance a3Measurable : MeasurableSpace M := borel M
private local instance a3Borel : BorelSpace M := ⟨rfl⟩

def harnackBallConstant : ℝ := 2 / 5 * Real.exp (-(Real.exp (1 / 2) / 4))

theorem harnackBallConstant_pos : 0 < harnackBallConstant := by
  unfold harnackBallConstant
  positivity

theorem surfaceFlow_area_bound_main (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) {κ : ℝ} (hκ : 0 < κ)
    (hvol : ∀ t ∈ Ioo 0 T, ∀ (x : M) (r : ℝ), 0 < r → r ≤ 1 → r ^ 2 ≤ t →
      (∀ u ∈ Icc (t - r ^ 2) t, ∀ y,
        r ^ 4 * normSq0S (S.family.metric u) y 4 (metricRm04At (S.family.metric u) y) ≤ 1) →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 2 ≤
        riemannianVolumeMeasure I M (S.family.metric t)
          {y | riemannianEDistOf (S.family.metric t) x y < ENNReal.ofReal r})
    {t : ℝ} (ht : 0 < t) (htT : t < T) {xt : M} (hmax : ∀ x, S.scalar t x ≤ S.scalar t xt)
    (hQt : 1 ≤ S.scalar t xt * t) (hQ : 1 / 4 ≤ S.scalar t xt) :
    S.scalar t xt * surfaceArea (S.family.metric t) ≤
      max (1 / harnackBallConstant)
        (Real.exp (4 * (surfaceEntropy (S.family.metric 0) + 1) / (harnackBallConstant * κ)) /
          harnackBallConstant) := by
  set Q := S.scalar t xt with hQdef
  set b := harnackBallConstant
  have hb : 0 < b := harnackBallConstant_pos
  have hQpos : 0 < Q := by linarith
  have hRpos : ∀ u ∈ Ico 0 T, ∀ x, 0 < S.scalar u x := fun u hu x =>
    surfaceFlow_scalar_pos S hS hscal hu x
  set a := t - 1 / (4 * Q) with hadef
  set o := t / 2 with hodef
  have hθ : 1 / (4 * Q) ≤ t / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have ha : 3 * t / 4 ≤ a := by rw [hadef]; linarith
  have hapos : 0 < a := by linarith
  have hat : a < t := by
    have : 0 < 1 / (4 * Q) := by positivity
    linarith
  have hoa : o < a := by rw [hodef]; linarith
  have ho : 0 < o := by rw [hodef]; linarith
  have hta : t - a = 1 / (4 * Q) := by rw [hadef]; ring
  have hback : ∀ u ∈ Icc a t, ∀ x, 0 ≤ S.scalar u x ∧ S.scalar u x ≤ 2 * Q := by
    intro u hu x
    have hu0 : u ∈ Ico 0 T := ⟨hapos.le.trans hu.1, lt_of_le_of_lt hu.2 htT⟩
    refine ⟨(hRpos u hu0 x).le, ?_⟩
    rcases hu.2.eq_or_lt with hut | hut
    · rw [hut]
      linarith [hmax x]
    have hh := surfaceFlow_harnack hdim S hS hscal ho (hoa.trans_le hu.1) hut htT x x
    rw [riemannianEDistOf_self, ENNReal.toReal_zero] at hh
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, neg_zero,
      Real.exp_zero, mul_one] at hh
    have hcoef : 1 / 2 ≤ (u - o) / (t - o) := by
      rw [le_div_iff₀ (by rw [hodef]; linarith)]
      rw [hodef]
      linarith [hu.1]
    have hRu := hRpos u hu0 x
    nlinarith [hmax x]
  obtain ⟨xa, -, hxa⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty (α := M))
    (scalarSmoothOfSolution S a).continuous.continuousOn
  set q := S.scalar a xa with hqdef
  have hqmax : ∀ x, S.scalar a x ≤ q := fun x => hxa (Set.mem_univ x)
  have hqle : q ≤ 2 * Q := (hback a ⟨le_rfl, hat.le⟩ xa).2
  have hqpos : 0 < q := hRpos a ⟨hapos.le, hat.trans htT⟩ xa
  have hqt : q * (t - a) < 1 := by
    rw [hta]
    have : q * (1 / (4 * Q)) ≤ 2 * Q * (1 / (4 * Q)) :=
      mul_le_mul_of_nonneg_right hqle (by positivity)
    have h2 : 2 * Q * (1 / (4 * Q)) = 1 / 2 := by field_simp; ring
    linarith
  have hode := surfaceFlow_scalar_le_of_ode hdim S hS hapos hat htT hqmax hqpos hqt xt
  have hqlow : 4 / 5 * Q ≤ q := by
    rw [← hQdef, hta] at hode
    have hden : 0 < 1 - q * (1 / (4 * Q)) := by rw [← hta]; linarith
    rw [le_div_iff₀ hden] at hode
    have : Q * (1 - q * (1 / (4 * Q))) = Q - q / 4 := by field_simp
    rw [this] at hode
    linarith
  set r := 1 / (2 * Real.sqrt Q) with hrdef
  have hsq : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQpos.le
  have hsqpos : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
  have hr : 0 < r := by positivity
  have hr2 : r ^ 2 = 1 / (4 * Q) := by
    rw [hrdef, div_pow, mul_pow, hsq]
    ring
  have hr1 : r ≤ 1 := by
    rw [hrdef, div_le_one (by positivity)]
    have : (1 : ℝ) / 2 ≤ Real.sqrt Q := by
      rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
        rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hQ
    linarith
  have hrt : r ^ 2 ≤ t := by rw [hr2]; linarith
  have hwin : t - r ^ 2 = a := by rw [hr2, hadef]
  have hcurv : ∀ u ∈ Icc (t - r ^ 2) t, ∀ y,
      r ^ 4 * normSq0S (S.family.metric u) y 4 (metricRm04At (S.family.metric u) y) ≤ 1 := by
    intro u hu y
    rw [hwin] at hu
    rw [normSq0S_metricRm04At_eq_sq_of_finrank_two hdim]
    obtain ⟨h0, h2⟩ := hback u hu y
    have hR2 : metricScalarAt (S.family.metric u) y ^ 2 ≤ (2 * Q) ^ 2 :=
      pow_le_pow_left₀ h0 h2 2
    have hr4 : r ^ 4 = 1 / (16 * Q ^ 2) := by
      rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr2]
      field_simp
      ring
    rw [hr4]
    calc 1 / (16 * Q ^ 2) * metricScalarAt (S.family.metric u) y ^ 2
        ≤ 1 / (16 * Q ^ 2) * (2 * Q) ^ 2 := mul_le_mul_of_nonneg_left hR2 (by positivity)
      _ = 1 / 4 := by field_simp; ring
      _ ≤ 1 := by norm_num
  have hball := hvol t ⟨ht, htT⟩ xa r hr hr1 hrt hcurv
  have hlowball : ∀ y, riemannianEDistOf (S.family.metric t) xa y < ENNReal.ofReal r →
      b * Q ≤ S.scalar t y := by
    intro y hy
    have hfin : riemannianEDistOf (S.family.metric t) xa y ≠ ⊤ := ne_top_of_lt hy
    have hdt : (riemannianEDistOf (S.family.metric t) xa y).toReal < r :=
      (ENNReal.lt_ofReal_iff_toReal_lt hfin).mp hy
    have hle := surfaceFlow_edist_le hdim S hS hapos hat.le htT hback xa y
    have hexp : 2 * Q / 2 * (t - a) = 1 / 4 := by
      rw [hta]
      field_simp
    rw [hexp] at hle
    have hda : (riemannianEDistOf (S.family.metric a) xa y).toReal ≤
        Real.exp (1 / 4) * (riemannianEDistOf (S.family.metric t) xa y).toReal := by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hle
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
    have hda' : (riemannianEDistOf (S.family.metric a) xa y).toReal ^ 2 ≤
        Real.exp (1 / 2) * (t - a) := by
      have h0 := ENNReal.toReal_nonneg (a := riemannianEDistOf (S.family.metric a) xa y)
      have h1 : (riemannianEDistOf (S.family.metric a) xa y).toReal ≤ Real.exp (1 / 4) * r :=
        hda.trans (mul_le_mul_of_nonneg_left hdt.le (Real.exp_pos _).le)
      calc (riemannianEDistOf (S.family.metric a) xa y).toReal ^ 2
          ≤ (Real.exp (1 / 4) * r) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = Real.exp (1 / 4) ^ 2 * r ^ 2 := by ring
        _ = Real.exp (1 / 2) * (t - a) := by
          rw [← Real.exp_nat_mul, hr2, hta]
          norm_num
    have hh := surfaceFlow_harnack hdim S hS hscal ho hoa hat htT xa y
    have hcoef : 1 / 2 ≤ (a - o) / (t - o) := by
      rw [le_div_iff₀ (by rw [hodef]; linarith), hodef]
      linarith
    have hexparg : -(Real.exp (1 / 2) / 4) ≤
        -((riemannianEDistOf (S.family.metric a) xa y).toReal ^ 2 / (4 * (t - a))) := by
      have hpos : 0 < 4 * (t - a) := by linarith
      rw [neg_le_neg_iff, div_le_div_iff₀ hpos (by norm_num)]
      nlinarith
    have hE := Real.exp_le_exp.mpr hexparg
    have hEpos := Real.exp_pos (-(Real.exp (1 / 2) / 4))
    calc b * Q = 1 / 2 * Real.exp (-(Real.exp (1 / 2) / 4)) * (4 / 5 * Q) := by
          simp only [b, harnackBallConstant]
          ring
      _ ≤ (a - o) / (t - o) *
            Real.exp (-((riemannianEDistOf (S.family.metric a) xa y).toReal ^ 2 /
              (4 * (t - a)))) * q := by
          apply mul_le_mul _ hqlow (by positivity) (by positivity)
          exact mul_le_mul hcoef hE hEpos.le (by linarith)
      _ ≤ S.scalar t y := hh
  let μ := riemannianVolumeMeasure I M (S.family.metric t)
  let _ : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) _
  set B' : Set M := {y | b * Q ≤ S.scalar t y} with hB'def
  have hB' : MeasurableSet B' :=
    (isClosed_le continuous_const (scalarSmoothOfSolution S t).continuous).measurableSet
  have hsub : {y | riemannianEDistOf (S.family.metric t) xa y < ENNReal.ofReal r} ⊆ B' :=
    fun y hy => hlowball y hy
  have hvolB' : κ * r ^ 2 ≤ (μ B').toReal := by
    have h := hball.trans (measure_mono hsub)
    have h2 := ENNReal.toReal_mono (measure_ne_top μ B') h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ.le, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr.le] at h2
  set A := surfaceArea (S.family.metric t) with hAdef
  have hApos : 0 < A := surfaceArea_pos (I := I) (M := M) _
  have hN := surfaceFlow_entropy_le_initial hdim S hS hscal (t := t) ⟨ht.le, htT⟩
  by_cases hcase : 1 ≤ b * Q * A
  · have hE := surfaceEntropy_ge_of_ball (S.family.metric t)
      (fun y => hRpos t ⟨ht.le, htT⟩ y) hB' (mul_pos hb hQpos) (fun y hy => hy)
      (by rw [mul_assoc] at hcase ⊢; exact hcase)
    have hlog : 0 ≤ Real.log (b * Q * A) := Real.log_nonneg hcase
    have hkr : κ * r ^ 2 = κ / (4 * Q) := by rw [hr2]; ring
    have hmain : b * κ / 4 * Real.log (b * Q * A) ≤ surfaceEntropy (S.family.metric 0) + 1 := by
      have h1 : b * Q * Real.log (b * Q * A) * (κ / (4 * Q)) ≤
          b * Q * Real.log (b * Q * A) * (μ B').toReal :=
        mul_le_mul_of_nonneg_left (hkr ▸ hvolB') (by positivity)
      have h2 : b * Q * Real.log (b * Q * A) * (κ / (4 * Q)) =
          b * κ / 4 * Real.log (b * Q * A) := by field_simp
      have h3 : b * Q * Real.log (b * Q * A) * (μ B').toReal - 1 ≤
          surfaceEntropy (S.family.metric t) := by
        simpa only [mul_assoc] using hE
      linarith
    have hlogle : Real.log (b * Q * A) ≤
        4 * (surfaceEntropy (S.family.metric 0) + 1) / (b * κ) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hbQA : b * Q * A ≤ Real.exp (4 * (surfaceEntropy (S.family.metric 0) + 1) / (b * κ)) :=
      (Real.log_le_iff_le_exp (by positivity)).mp hlogle
    refine le_max_of_le_right ?_
    rw [le_div_iff₀ hb]
    linarith
  · refine le_max_of_le_left ?_
    rw [le_div_iff₀ hb]
    push Not at hcase
    linarith

theorem surfaceFlow_normalized_scalar_upper (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) :
    ∃ C : ℝ, ∀ t ∈ Ico 0 T, ∀ x, S.scalar t x *
      (2 * (surfaceArea (S.family.metric 0) / totalScalarCurvature (S.family.metric 0) - t)) ≤
        C := by
  obtain ⟨κ, hκ, hvol⟩ := surfaceFlow_exists_ball_volume_lower hdim S hS one_pos
  set b := harnackBallConstant
  have hb : 0 < b := harnackBallConstant_pos
  set K₁ := max (1 / b)
    (Real.exp (4 * (surfaceEntropy (S.family.metric 0) + 1) / (b * κ)) / b) with hK₁
  have hK₁pos : 0 < K₁ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set C₀ := totalScalarCurvature (S.family.metric 0)
  set A₀ := surfaceArea (S.family.metric 0)
  have hC₀ : 0 < C₀ := totalScalarCurvature_pos _ hscal
  set Tst := A₀ / C₀ with hTst
  have hTT : T ≤ Tst := surfaceFlow_le_extinctionTime hT S hS hdim hscal
  have hTstpos : 0 < Tst := hT.trans_le hTT
  have hslab : IsCompact (Icc (0 : ℝ) (T / 2) ×ˢ (Set.univ : Set M)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨Q₀, hQ₀⟩ := (hslab.image_of_continuousOn (hS.scalarCont.mono (Set.prod_mono
    (fun s hs => (⟨hs.1, by linarith [hs.2]⟩ : s ∈ Ico 0 T)) le_rfl))).bddAbove
  set Q₁ := max Q₀ 0
  refine ⟨2 * Tst * Q₁ + 4 * Tst / T + Tst / 2 + 2 * K₁ / C₀, fun t ht x => ?_⟩
  obtain ⟨xt, -, hxt⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty (α := M))
    (scalarSmoothOfSolution S t).continuous.continuousOn
  have hmax : ∀ y, S.scalar t y ≤ S.scalar t xt := fun y => hxt (Set.mem_univ y)
  set Q := S.scalar t xt with hQdef
  have hQpos : 0 < Q := surfaceFlow_scalar_pos S hS hscal ht xt
  have hgap : 0 < Tst - t := by linarith [ht.2]
  have hgap' : Tst - t ≤ Tst := by linarith [ht.1]
  have h1 : 0 ≤ 2 * Tst * Q₁ := by positivity
  have h2 : 0 ≤ 4 * Tst / T := by positivity
  have h3 : 0 ≤ Tst / 2 := by positivity
  have h4 : 0 ≤ 2 * K₁ / C₀ := by positivity
  have hreduce : S.scalar t x * (2 * (Tst - t)) ≤ Q * (2 * (Tst - t)) :=
    mul_le_mul_of_nonneg_right (hmax x) (by positivity)
  refine hreduce.trans ?_
  by_cases hearly : t ≤ T / 2
  · have hQQ : Q ≤ Q₁ := (hQ₀ ⟨(t, xt), ⟨⟨ht.1, hearly⟩, trivial⟩, rfl⟩).trans (le_max_left _ _)
    have : Q * (2 * (Tst - t)) ≤ Q₁ * (2 * Tst) :=
      mul_le_mul hQQ (by linarith) (by positivity) (le_max_right _ _)
    linarith
  push Not at hearly
  have htpos : 0 < t := by linarith
  by_cases hQt : Q * t < 1
  · have hQle : Q ≤ 2 / T := by
      rw [le_div_iff₀ hT]
      nlinarith
    have : Q * (2 * (Tst - t)) ≤ 2 / T * (2 * Tst) :=
      mul_le_mul hQle (by linarith) (by positivity) (by positivity)
    have heq : 2 / T * (2 * Tst) = 4 * Tst / T := by ring
    linarith
  push Not at hQt
  by_cases hQs : Q < 1 / 4
  · have : Q * (2 * (Tst - t)) ≤ 1 / 4 * (2 * Tst) :=
      mul_le_mul hQs.le (by linarith) (by positivity) (by norm_num)
    linarith
  push Not at hQs
  have hmain := surfaceFlow_area_bound_main hdim S hS hscal hκ
    (fun s hs y r hr hr1 hrs hc => hvol s hs y r hr hr1 hrs hc) htpos ht.2 hmax hQt hQs
  have hA : surfaceArea (S.family.metric t) = C₀ * (Tst - t) := by
    rw [surfaceFlow_area_eq_initial_sub hT S hS hdim ht, hTst]
    field_simp
    ring
  rw [hA] at hmain
  have : Q * (2 * (Tst - t)) = 2 * (Q * (C₀ * (Tst - t))) / C₀ := by
    field_simp
  rw [this]
  have : 2 * (Q * (C₀ * (Tst - t))) / C₀ ≤ 2 * K₁ / C₀ := by
    apply div_le_div_of_nonneg_right _ hC₀.le
    linarith
  linarith

end GC.Geometry
