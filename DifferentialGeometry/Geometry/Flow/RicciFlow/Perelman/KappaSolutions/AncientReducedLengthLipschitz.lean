import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricMonotonicity
import DifferentialGeometry.Geometry.Metric.ChartLipschitz.Spacetime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.Lipschitz

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_redLength_spacetime_lipschitz_bound_on_ball
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p o : F.M)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℝ) :
    ∃ K : ℝ≥0, ∀ x ∈ riemannianClosedBallOf (F.S.base.metric (-b)) o R,
      ∀ y ∈ riemannianClosedBallOf (F.S.base.metric (-b)) o R,
      ∀ s t : Icc a b,
        |redLength F.S 0 p x s - redLength F.S 0 p y t| ≤
          (K : ℝ) * ((riemannianEDistOf (F.S.base.metric (-b)) x y).toReal + |(s : ℝ) - t|) := by
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, z, hz⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) z (by norm_num : 0 < 4) _ hz⟩
  let _ : ConnectedSpace F.M := hF.connected
  let g := F.S.base.metric (-b)
  have hb : 0 < b := ha.trans_le hab
  have hg : RiemannianMetricComplete g :=
    ⟨MetricComplete.complete (F.atTime (-b)) (hF.complete (-b) (neg_nonpos.mpr hb.le))⟩
  let B := riemannianClosedBallOf g o R
  have hB : IsCompact B := hg.closedEBall_isCompact o R
  obtain ⟨A, hA⟩ := (isCompact_Icc.prod hB).bddAbove_image
    ((continuousOn_redLength_space_time_of_ancient F hF p).mono
      (fun z hz => ⟨ha.trans_le hz.1.1, mem_univ _⟩))
  have hbound (x : F.M) (hx : x ∈ B) (t : Icc a b) :
      redLength F.S 0 p x t ≤ A := hA ⟨(t, x), ⟨t.2, hx⟩, rfl⟩
  have hratio : 1 ≤ b / a := (le_div_iff₀ ha).mpr (by simpa only [one_mul] using hab)
  obtain ⟨Kt, hKt⟩ := exists_lipschitzOnWith_redLength_rescaled_time F hF p (A := A) hratio
  let Ks : ℝ := Real.sqrt 3 / 2 * (Real.sqrt a)⁻¹
  have hKs : 0 ≤ Ks := by positivity
  let K : ℝ≥0 := ⟨Ks * (2 * Real.sqrt A) + (Kt : ℝ) / a, by positivity⟩
  refine ⟨K, ?_⟩
  intro x hx y hy s t
  have htime : |redLength F.S 0 p y s - redLength F.S 0 p y t| ≤
      ((Kt : ℝ) / a) * |(s : ℝ) - t| := by
    have hs : (s : ℝ) / a ∈ Icc 1 (b / a) :=
      ⟨(le_div_iff₀ ha).mpr (by simpa only [one_mul] using s.2.1), (div_le_div_iff_of_pos_right ha).mpr s.2.2⟩
    have ht : (t : ℝ) / a ∈ Icc 1 (b / a) :=
      ⟨(le_div_iff₀ ha).mpr (by simpa only [one_mul] using t.2.1), (div_le_div_iff_of_pos_right ha).mpr t.2.2⟩
    have hh := (hKt a ha y (hbound y hy ⟨a, le_rfl, hab⟩)).dist_le_mul _ hs _ ht
    simpa only [mul_div_cancel₀ _ ha.ne', Real.dist_eq, ← sub_div, abs_div,
      abs_of_pos ha, div_mul_eq_mul_div, mul_div_assoc] using hh
  have hspace : |Real.sqrt (redLength F.S 0 p x s) - Real.sqrt (redLength F.S 0 p y s)| ≤
      Ks * (riemannianEDistOf g x y).toReal := by
    have hs : 0 < (s : ℝ) := ha.trans_le s.2.1
    have hd := edistOf_mono (F.S.base.metric (-(s : ℝ))) g
      (fun z v => ancientModel_metric_inner_antitoneOn F hF z v
        (neg_nonpos.mpr hb.le) (neg_nonpos.mpr hs.le) (neg_le_neg s.2.2)) x y
    have hdr := ENNReal.toReal_mono (riemannianEDistOf_ne_top g x y) hd
    have hh := abs_sqrt_redLength_sub_le_rescaled_distance F hF p x y hs
    rw [edistOf_scale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      Real.sqrt_inv] at hh
    calc
      _ ≤ Real.sqrt 3 / 2 * ((Real.sqrt (s : ℝ))⁻¹ *
          (riemannianEDistOf (F.S.base.metric (-(s : ℝ))) x y).toReal) := hh
      _ ≤ Real.sqrt 3 / 2 * ((Real.sqrt a)⁻¹ * (riemannianEDistOf g x y).toReal) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (inv_anti₀ (Real.sqrt_pos.mpr ha) (Real.sqrt_le_sqrt s.2.1)) hdr
            ENNReal.toReal_nonneg (by positivity)) (by positivity)
      _ = _ := by dsimp only [Ks]; ring
  have hn (z : F.M) : 0 ≤ redLength F.S 0 p z s := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    apply div_nonneg _ (by positivity)
    apply lCost_nonneg_of_scalar_nonneg F.S 0 (ha.le.trans s.2.1)
    intro r hr w
    simpa only [zero_sub] using (hC (-r) (neg_nonpos.mpr hr.1) w).1
  have hsum : Real.sqrt (redLength F.S 0 p x s) + Real.sqrt (redLength F.S 0 p y s) ≤
      2 * Real.sqrt A := by
    linarith only [Real.sqrt_le_sqrt (hbound x hx s), Real.sqrt_le_sqrt (hbound y hy s)]
  have hspace' : |redLength F.S 0 p x s - redLength F.S 0 p y s| ≤
      Ks * (2 * Real.sqrt A) * (riemannianEDistOf g x y).toReal := by
    have heq : redLength F.S 0 p x s - redLength F.S 0 p y s =
        (Real.sqrt (redLength F.S 0 p x s) - Real.sqrt (redLength F.S 0 p y s)) *
          (Real.sqrt (redLength F.S 0 p x s) + Real.sqrt (redLength F.S 0 p y s)) := by
      nlinarith only [Real.sq_sqrt (hn x), Real.sq_sqrt (hn y)]
    calc
      _ = |Real.sqrt (redLength F.S 0 p x s) - Real.sqrt (redLength F.S 0 p y s)| *
          (Real.sqrt (redLength F.S 0 p x s) + Real.sqrt (redLength F.S 0 p y s)) := by
        rw [heq, abs_mul, abs_of_nonneg (by positivity :
          0 ≤ Real.sqrt (redLength F.S 0 p x s) + Real.sqrt (redLength F.S 0 p y s))]
      _ ≤ (Ks * (riemannianEDistOf g x y).toReal) * (2 * Real.sqrt A) :=
        mul_le_mul hspace hsum (by positivity) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ |redLength F.S 0 p x s - redLength F.S 0 p y s| +
        |redLength F.S 0 p y s - redLength F.S 0 p y t| := abs_sub_le _ _ _
    _ ≤ Ks * (2 * Real.sqrt A) * (riemannianEDistOf g x y).toReal +
        ((Kt : ℝ) / a) * |(s : ℝ) - t| := add_le_add hspace' htime
    _ ≤ _ := by
      change _ ≤ (Ks * (2 * Real.sqrt A) + (Kt : ℝ) / a) *
        ((riemannianEDistOf g x y).toReal + |(s : ℝ) - t|)
      nlinarith only [mul_nonneg (show 0 ≤ Ks * (2 * Real.sqrt A) by positivity)
        (abs_nonneg ((s : ℝ) - t)), mul_nonneg (show 0 ≤ (Kt : ℝ) / a by positivity)
        (ENNReal.toReal_nonneg (a := riemannianEDistOf g x y))]

theorem ancient_redLength_locallyLipschitzOn_in_chart
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p alpha : F.M) :
    LocallyLipschitzOn (Ioi 0 ×ˢ (extChartAt I alpha).target)
      (fun z : ℝ × E => redLength F.S 0 p ((extChartAt I alpha).symm z.2) z.1) := by
  let _ : ConnectedSpace F.M := hF.connected
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace F.M := ChartedSpace.locallyCompactSpace H F.M
  intro z hz
  let a := z.1 / 2
  let b := z.1 + 1
  have ha : 0 < a := half_pos hz.1
  have haz : a < z.1 := half_lt_self hz.1
  have hzb : z.1 < b := by dsimp only [b]; linarith
  have hab : a ≤ b := (haz.trans hzb).le
  let ell : F.M × Icc a b → ℝ := fun w => redLength F.S 0 p w.1 w.2
  have hLip := Geometry.Riemannian.locallyLipschitzOn_comp_extChartAt_symm_of_spacetime_bounds
    (F.S.base.metric (-b)) p hab ell
    (fun R _ => exists_redLength_spacetime_lipschitz_bound_on_ball F hF p p ha hab R) alpha
  obtain ⟨K, U, hU, hKU⟩ := hLip ⟨mem_univ _, hz.2⟩
  have hUn : U ∈ 𝓝[Ioi 0 ×ˢ (extChartAt I alpha).target] z :=
    nhdsWithin_mono _ (prod_mono (subset_univ _) Subset.rfl) hU
  have ht : {w : ℝ × E | w.1 ∈ Ioo a b} ∈ 𝓝 z :=
    continuous_fst.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds ⟨haz, hzb⟩)
  refine ⟨K, U ∩ {w : ℝ × E | w.1 ∈ Ioo a b},
    inter_mem hUn (mem_nhdsWithin_of_mem_nhds ht), ?_⟩
  intro x hx y hy
  have h := hKU hx.1 hy.1
  simpa only [ell, projIcc_of_mem hab (Ioo_subset_Icc_self hx.2),
    projIcc_of_mem hab (Ioo_subset_Icc_self hy.2)] using h

theorem ancient_perelmanDensity_locallyLipschitzOn_in_chart
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p alpha : F.M) :
    LocallyLipschitzOn (Ioi 0 ×ˢ (extChartAt I alpha).target)
      (fun z : ℝ × E => Entropy.perelmanDensity (Module.finrank ℝ E) z.1
        (fun x => redLength F.S 0 p x z.1) ((extChartAt I alpha).symm z.2)) :=
  Entropy.locallyLipschitzOn_perelmanDensity
    LipschitzWith.prod_fst.locallyLipschitz.locallyLipschitzOn
    (ancient_redLength_locallyLipschitzOn_in_chart F hF p alpha)
    (fun _ hz => hz.1) (Module.finrank ℝ E)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
